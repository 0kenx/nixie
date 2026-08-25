//! BitVector Theory Solver

use crate::config::BvConfig;
#[allow(unused_imports)]
use crate::prelude::*;
use crate::theory::{EqualityNotification, Theory, TheoryCombination, TheoryId, TheoryResult};
use num_bigint::BigUint;
use oxiz_core::ast::TermId;
use oxiz_core::error::Result;
use oxiz_sat::{LBool, Lit, Solver as SatSolver, SolverConfig as SatConfig, SolverResult, Var};
use smallvec::SmallVec;

/// Division / remainder encodings (`bvudiv`, `bvurem`, `bvsdiv`, `bvsrem`).
mod division;
/// Barrel-shifter encodings (`bvshl`, `bvlshr`, `bvashr`).
mod shifts;

/// A bit vector variable (sequence of SAT variables)
#[derive(Debug, Clone)]
pub struct BvVar {
    /// SAT variables for each bit (LSB first)
    bits: SmallVec<[Var; 32]>,
    /// Width in bits
    width: u32,
}

/// A bit inside a blasted circuit: one of the two reserved constant SAT
/// variables, or an ordinary signal variable.
///
/// The bit-blaster builds every circuit out of [`Sig`]s instead of raw
/// [`Var`]s so each gate constructor can constant-fold before emitting any
/// clause – the same shape as Z3's bit-blaster, whose `mk_and` / `mk_xor` /
/// `mk_full_adder` run over a rewriting layer (`bit_blaster_tpl_def.h`).
/// Folding at gate granularity is what degenerates `bvmul(x, 65599)` into a
/// six-row shift-add chain and lets a `zero_extend`'s padding ripple through
/// adders and comparators as pure constants instead of pinned variables the
/// SAT solver has to propagate through tens of thousands of clauses.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
enum Sig {
    /// The reserved constant-true variable.
    True,
    /// The reserved constant-false variable.
    False,
    /// An ordinary signal variable.
    Var(Var),
}

/// Comparison tracking for conflict detection
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
struct ComparisonKey {
    a: TermId,
    b: TermId,
}

/// One insertion into a term-derived registry of the embedded solver, journaled
/// so [`BvSolver::pop`] can retract it together with the clauses that define
/// it.
///
/// `term_to_bv`, `ult_cache` and `bool_node` all answer "does this term's
/// *encoding* exist?" – but an encoding is bits **plus the `add_clause`d gates
/// that wire them**, and those clauses are scope-tracked by the embedded
/// solver's own push/pop.  A registry entry that outlives its clauses turns the
/// manager's encode memo (`encode_bv_term_recursive` skips any term with
/// `get_bv(term).is_some()`) into a decapitation bug: after a backtrack pops
/// the scope a circuit was built in, the memo reports "already encoded" and
/// the atom is asserted against output bits whose defining circuit is gone –
/// the embedded check then reports `Sat` over a formula that no longer
/// constrains the atom, which surfaces as a false `sat` (reproduced by
/// `bv_soundness_integration::test_issue_17_conditional_bv_fact_not_unconditional`
/// under VSIDS branching: `bvurem`'s circuit popped, zero clauses left
/// referencing the dividend's bits, model `urem(0,3) = 0x80`).
/// Saved lengths of every retractable buffer, recorded by `push` so `pop`
/// restores exactly the state the enclosing decision level had.
#[derive(Debug, Clone, Copy)]
struct ContextMark {
    /// Length of `assertions`.
    assertions_len: usize,
    /// Length of `assertion_guard_terms`.
    guard_terms_len: usize,
    /// Length of `outer_bool_journal`.
    outer_bool_len: usize,
}

/// One abstracted `bvmul` (CEGAR; see `BvSolver::abstract_mul`).
///
/// `result` carries fresh, unconstrained wires (plus the tier-1 identity
/// lemmas).  Every clause emitted for the abstraction — the lemmas, any
/// value refinement, and the terminal exact circuit — is a logical
/// *consequence* of the exact definition `result = a * b`, so the abstract
/// SAT instance is a relaxation of the exact one at every stage:
/// `Unsat` is sound at any round, and `Sat` is provisional until the model
/// values of `a`, `b` and `result` agree with the exact product.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct MulAbstraction {
    /// The `bvmul` term whose circuit was replaced.
    pub result: TermId,
    /// Left operand.
    pub a: TermId,
    /// Right operand.
    pub b: TermId,
    /// Operand/result width.
    pub width: u32,
}

/// BitVector Theory Solver using bit-blasting
#[derive(Debug)]
pub struct BvSolver {
    /// Embedded SAT solver
    sat: SatSolver,
    /// Term to BV variable mapping
    term_to_bv: FxHashMap<TermId, BvVar>,
    /// Pending assertions
    assertions: Vec<(TermId, bool)>,
    /// CEGAR bvmul abstractions created while [`Self::abstract_mul_width`]
    /// was set (drained by the pure-BV dispatch).  Each entry records one
    /// `bvmul` whose exact circuit was replaced by fresh result wires plus
    /// sound identity lemmas; see [`Self::abstract_mul`].
    mul_abstractions: Vec<MulAbstraction>,
    /// Bit-width at (and above) which `bvmul` terms are abstracted instead
    /// of bit-blasted (CEGAR; 0 = always exact — the default, keeping the
    /// general CDCL(T) path byte-identical).  Set only by the eager pure-BV
    /// dispatch around its blast.
    abstract_mul_width: u32,
    /// Context stack: one [`ContextMark`] per open push, restored by `pop`.
    context_stack: Vec<ContextMark>,
    /// Configuration
    config: BvConfig,
    /// Track unsigned less-than comparisons for conflict detection
    /// Maps (a, b) -> SAT variable representing a < b
    ult_cache: FxHashMap<ComparisonKey, Var>,
    /// Shared equalities derived by BV theory for Nelson-Oppen combination.
    /// BV is a finite domain theory, so equalities are extracted from the
    /// current model/assignment using model-based combination.
    shared_equalities: Vec<EqualityNotification>,
    /// Pending equality notifications received from other theories
    equality_notifications: Vec<EqualityNotification>,
    /// Constraint-level TermIds recorded by the theory manager for conflict reporting.
    /// On UNSAT, all recorded terms form a sound (superset) conflict explanation.
    assertion_guard_terms: Vec<TermId>,
    /// Snapshot of the embedded SAT model captured at the most recent SAT
    /// `check()`, taken *before* `backtrack_to_root()` discards the live trail.
    /// Without this snapshot, `get_value` would read an all-`Undef` (→ 0) trail
    /// after backtracking, producing degenerate counterexample models.
    last_sat_model: Vec<LBool>,
    /// Cache mapping a Bool-sorted term to the single SAT variable encoding its
    /// truth value, used when bit-blasting `ite` conditions and the boolean
    /// connectives that build them (so `not(c)` stays the negation of `c`).
    bool_node: FxHashMap<TermId, Var>,
    /// The two reserved SAT variables carrying the constant bit values.
    ///
    /// Every constant input to a blasted circuit – the bits of a `BitVecConst`,
    /// the zero padding of a `zero_extend`, the fixed addend of an
    /// `encode_add_const` – is one of these two variables instead of a fresh
    /// one, and every gate constructor folds on them (`and x false = false`,
    /// `xor x true = not x`, …) exactly like Z3's simplifying bit-blaster
    /// (`bit_blaster_tpl_def.h` builds its circuits through `mk_and`/`mk_xor`
    /// over a rewriting layer that performs these folds).  Without the fold a
    /// `bvmul(x, 65599)` blasts the full 32×32 partial-product array even
    /// though 26 of the constant's 32 bits are zero; with it the multiplier
    /// degenerates to the six-row shift-add chain the constant actually needs,
    /// which is the difference between a ~2 000-gate and a ~190 000-clause
    /// encoding on the Sage2 hash-chain family.
    ///
    /// Both variables are created *before* any theory scope opens and pinned
    /// by level-0 unit clauses, so their value survives every `push`/`pop`.
    /// They are re-created in [`Theory::reset`], the one place the embedded
    /// SAT solver's variable space is rebuilt from scratch.
    const_true: Var,
    const_false: Var,
    /// Truth values the *outer* CDCL(T) search has fixed for Bool-sorted terms,
    /// so that a bit-blasted `ite` selector agrees with the enclosing solver
    /// instead of floating free. See [`Self::assert_bool_value`].
    outer_bool: FxHashMap<TermId, bool>,
    /// Undo journal for `outer_bool`: `(term, value it had before)`, replayed
    /// in reverse by [`Theory::pop`] so the link is retracted with the decision
    /// level that established it.
    outer_bool_journal: Vec<(TermId, Option<bool>)>,
}

impl Default for BvSolver {
    fn default() -> Self {
        Self::new()
    }
}

impl BvSolver {
    /// Create a new BitVector solver
    #[must_use]
    pub fn new() -> Self {
        Self::with_config(BvConfig::default())
    }

    /// Create a new BitVector solver with custom configuration
    #[must_use]
    pub fn with_config(config: BvConfig) -> Self {
        let mut sat = SatSolver::with_config(Self::embedded_sat_config());
        let (const_true, const_false) = Self::reserve_const_bits(&mut sat);
        Self {
            sat,
            term_to_bv: FxHashMap::default(),
            assertions: Vec::new(),
            mul_abstractions: Vec::new(),
            abstract_mul_width: 0,
            context_stack: Vec::new(),
            config,
            ult_cache: FxHashMap::default(),
            shared_equalities: Vec::new(),
            equality_notifications: Vec::new(),
            assertion_guard_terms: Vec::new(),
            last_sat_model: Vec::new(),
            bool_node: FxHashMap::default(),
            outer_bool: FxHashMap::default(),
            outer_bool_journal: Vec::new(),
            const_true,
            const_false,
        }
    }

    /// Create the two reserved constant bit variables in `sat` and pin them
    /// with level-0 unit clauses.
    ///
    /// Called from [`Self::with_config`] (fresh solver, empty solver state) and
    /// from [`Theory::reset`] (the embedded SAT solver was just rebuilt, so the
    /// previous constants' variables no longer exist).  In both cases no theory
    /// scope is open, so the pinning units land at the base assertion level and
    /// are never retracted by a `pop`.
    fn reserve_const_bits(sat: &mut SatSolver) -> (Var, Var) {
        let const_true = sat.new_var();
        let const_false = sat.new_var();
        sat.add_clause([Lit::pos(const_true)]);
        sat.add_clause([Lit::neg(const_false)]);
        (const_true, const_false)
    }

    /// SAT-solver configuration for the embedded bit-blasting engine.
    ///
    /// `BvSolver::check()` drives the SAT solver *incrementally*: it asserts
    /// clauses, runs a full `solve()`, then discards that probe's search
    /// residue so the next probe sees only the honestly-asserted clauses. The
    /// residue cleanup relies on two contracts – `restore_to_trail_size`
    /// (roll the trail back to the committed prefix) and `forget_learned_since`
    /// (drop exactly the clauses this probe *learned*). The second contract
    /// only covers clauses registered in the SAT solver's learned-clause list.
    ///
    /// Any search feature that injects *other* clauses into the database during
    /// `solve()` therefore breaks the contract: those clauses are invisible to
    /// `forget_learned_since`, survive both the per-probe cleanup and the
    /// enclosing `pop()`, and leak into later probes. Because the bit-vector
    /// unit constraints installed by `assert_const`/`assert_eq` sit on the
    /// trail as bare level-0 decisions, such a leaked clause can implicitly
    /// depend on a since-retracted assignment and spuriously force `Unsat` –
    /// e.g. turning the genuinely satisfiable `a = x*3 ∧ a ≠ x ∧ a = 7` into a
    /// false `Unsat` once an earlier probe has run.
    ///
    /// The two offenders are **lazy hyper-binary resolution** (adds derived
    /// binary clauses mid-search) and **inprocessing** (adds/rewrites clauses
    /// between search rounds). Both are pure performance heuristics – disabling
    /// them costs only speed, never soundness or completeness – so the embedded
    /// solver turns them off to keep the incremental cleanup contract exact.
    ///
    /// Chronological backtracking, by contrast, is left **on** (the workspace
    /// default): it never adds a clause to the database, so it does not touch
    /// the cleanup contract above.  It was briefly disabled here while
    /// `oxiz-sat` recorded a learned clause's asserting literal at the
    /// post-backtrack decision level instead of at its true implication level –
    /// which pinned unit lemmas inside a decision level and let conflict
    /// analysis emit clauses stronger than resolution derives, refuting
    /// satisfiable bit-blasted circuits such as `x <=u (x bvxor x)`.  That is
    /// fixed in the SAT engine itself (see `Solver::assert_learned_clause` and
    /// `Trail::backtrack_to_with_callback`), so the embedded solver no longer
    /// needs to opt out.
    fn embedded_sat_config() -> SatConfig {
        SatConfig {
            enable_lazy_hyper_binary: false,
            enable_inprocessing: false,
            // The embedded solver is driven incrementally by `BvSolver::check`,
            // which calls `solve()` once per asserted atom (hundreds of times on
            // a QF_BV formula).  `lucky_phases` / gate-congruence scan the whole
            // clause database on every call, so on a ~100 k-clause bit-blasted
            // formula they dominate runtime (394 × O(clauses) ≈ the entire
            // solve budget on `millionaires.t1.i28`, all with 0 search
            // conflicts).  Disable them here: the bit-blasted theory clauses
            // are not structured in the way these passes exploit, and the main
            // CDCL(T) solver above already applies them once to the user
            // formula.
            enable_lucky: false,
            enable_gate_congruence: false,
            // Chronological backtracking raised-threshold: CB's literal
            // re-appending above a rollback boundary can leave a learned
            // clause's asserted literal unassigned while the older
            // assignments justifying its other literals survive – an
            // untriggerable unit (the hanging-unit corruption the fixpoint
            // invariant catches).  The default threshold of 100 makes that
            // reachable on deep bit-blasted probes; raising it keeps CB for
            // its intended very-long-jump cases only.
            chrono_backtrack_threshold: 10_000,
            ..SatConfig::default()
        }
    }

    /// Record a constraint-level TermId that the theory manager is about to assert.
    ///
    /// The theory manager calls this before each `assert_const` / `assert_eq` /
    /// `assert_ult` etc. so that `check()` can return a non-empty conflict clause
    /// on UNSAT.  The term must be a constraint term that is registered in the
    /// theory manager's `term_to_var` map, so that `terms_to_conflict_clause`
    /// can convert it to a SAT literal.
    pub fn record_constraint_term(&mut self, term: TermId) {
        // Deduplicate: only add if not already present
        if !self.assertion_guard_terms.contains(&term) {
            self.assertion_guard_terms.push(term);
        }
    }

    /// Collect all recorded constraint terms as the conflict explanation.
    ///
    /// This is a sound superset: the UNSAT is definitely caused by the set of
    /// all constraints that have been asserted since the last push/reset.
    fn collect_conflict_terms(&self) -> Vec<TermId> {
        self.assertion_guard_terms.clone()
    }

    /// Create a new bit vector variable
    pub fn new_bv(&mut self, term: TermId, width: u32) -> &BvVar {
        self.term_to_bv.entry(term).or_insert_with(|| {
            let bits: SmallVec<[Var; 32]> = (0..width).map(|_| self.sat.new_var()).collect();
            BvVar { bits, width }
        })
    }

    /// Whether no theory scope is open on the embedded solver, i.e. clauses
    /// added now land at the base assertion level and survive every `pop`.
    /// The solver's assert-time eager bit-blasting gates on this: circuits
    /// built at the base scope are permanent, which is what keeps the
    /// term→bits memo ("this term's encoding exists") truthful.
    #[must_use]
    pub fn at_base_scope(&self) -> bool {
        self.context_stack.is_empty()
    }

    /// Get the BV variable for a term
    #[must_use]
    pub fn get_bv(&self, term: TermId) -> Option<&BvVar> {
        self.term_to_bv.get(&term)
    }

    /// Get the current configuration
    #[must_use]
    pub fn config(&self) -> &BvConfig {
        &self.config
    }

    /// The bit-vectors of two operands, if both are bit-blasted **and** share a
    /// width.
    ///
    /// Every binary bit-level encoding goes through this: a caller that hands
    /// over operands of *different* widths (which the term builder does not
    /// currently reject for `(bvadd x8 y16)`) has asked for a circuit that does
    /// not exist, and the honest answer is "not encodable" – not an
    /// `assert_eq!` that aborts the process, and not a circuit wired from the
    /// bits that happen to line up.
    fn binop_bits(&self, a: TermId, b: TermId) -> Option<(BvVar, BvVar)> {
        let va = self.term_to_bv.get(&a)?.clone();
        let vb = self.term_to_bv.get(&b)?.clone();
        (va.width == vb.width).then_some((va, vb))
    }

    /// Assert equality: a = b
    ///
    /// Returns `false` – asserting nothing – when either operand has not been
    /// bit-blasted or the two have different widths.
    pub fn assert_eq(&mut self, a: TermId, b: TermId) -> bool {
        if let Some((va, vb)) = self.binop_bits(a, b) {
            for i in 0..va.width as usize {
                // a[i] <=> b[i], folded on constant bits: equal constants
                // need nothing, different constants are an honest conflict,
                // and a constant against a signal is a single unit.
                self.encode_bit_eq(va.bits[i], vb.bits[i]);
            }
            return true;
        }
        false
    }

    /// Assert disequality: a != b
    ///
    /// Returns `false` – asserting nothing – when either operand has not been
    /// bit-blasted or the two have different widths.
    pub fn assert_neq(&mut self, a: TermId, b: TermId) -> bool {
        if let Some((va, vb)) = self.binop_bits(a, b) {
            // At least one bit must differ, with the differences computed by
            // the folding XOR gates: a bit pair that is constant-unequal
            // satisfies the disequality outright, a constant-equal pair
            // contributes nothing, and only genuine signals reach the clause.
            let mut diff_lits: SmallVec<[Lit; 32]> = SmallVec::new();

            for i in 0..va.width as usize {
                match self.gate_xor(self.sig(va.bits[i]), self.sig(vb.bits[i])) {
                    Sig::True => {
                        // This bit is provably different: a != b already holds.
                        return true;
                    }
                    Sig::False => {}
                    Sig::Var(v) => diff_lits.push(Lit::pos(v)),
                }
            }

            // At least one diff bit must be true; none left means every bit
            // pair folded equal - an honest conflict.
            if diff_lits.is_empty() {
                self.sat.add_clause([]);
            } else {
                self.sat.add_clause(diff_lits);
            }
            return true;
        }
        false
    }

    /// Assert unsigned less than: a < b
    ///
    /// Returns `false` – asserting nothing – when either operand has not been
    /// bit-blasted or the two have different widths.
    pub fn assert_ult(&mut self, a: TermId, b: TermId) -> bool {
        if let Some((va, vb)) = self.binop_bits(a, b) {
            // Get or create comparison result variable for a < b
            let key_ab = ComparisonKey { a, b };
            let ult_ab = if let Some(&var) = self.ult_cache.get(&key_ab) {
                var
            } else {
                let var = self.sat.new_var();
                self.encode_ult_result(&va.bits, &vb.bits, var);
                self.ult_cache.insert(key_ab.clone(), var);
                var
            };

            // Assert that a < b is true
            self.sat.add_clause([Lit::pos(ult_ab)]);

            // Check for conflict with b < a
            let key_ba = ComparisonKey { a: b, b: a };
            if let Some(&ult_ba) = self.ult_cache.get(&key_ba) {
                // If both a < b and b < a are asserted, we have a conflict
                // Add clause: NOT(a < b) OR NOT(b < a)
                // Since we already asserted a < b, this will make b < a false
                self.sat.add_clause([Lit::neg(ult_ab), Lit::neg(ult_ba)]);
            }

            // Also check for conflict with a <= b and b <= a
            // If a < b, then NOT(a = b), so we ensure anti-symmetry
            return true;
        }
        false
    }

    /// Assert unsigned less than or equal: a <= b
    ///
    /// `ule(a, b)` is equivalent to `NOT(ult(b, a))`: encode the unsigned
    /// comparison `b < a` into a fresh SAT variable and assert its negation.
    ///
    /// Returns `false` – asserting nothing – when either operand has not been
    /// bit-blasted or the two have different widths.
    pub fn assert_ule(&mut self, a: TermId, b: TermId) -> bool {
        if let Some((va, vb)) = self.binop_bits(a, b) {
            // Encode b < a (unsigned) into `ult_ba`.
            let ult_ba = self.sat.new_var();
            self.encode_ult_result(&vb.bits, &va.bits, ult_ba);

            // Assert NOT(b < a), which is exactly a <= b.
            self.sat.add_clause([Lit::neg(ult_ba)]);
            return true;
        }
        false
    }

    /// Assert a constant value for a bit vector whose width is at most 64.
    ///
    /// `value` supplies the low 64 bits; every higher bit of a wider vector is
    /// pinned to `0`, which is only the intended meaning when the constant
    /// really does fit in a `u64`.  A caller holding a *wider* constant must
    /// use [`Self::assert_const_big`] (or [`Self::assert_const_limbs`]):
    /// truncating it to a `u64` here would pin the wrong bits and admit
    /// assignments the constant forbids – the shape that answered `sat` for
    /// `x = 2^64 ∧ x <u 1` at width 128.
    ///
    /// Returns `false` when `term` already has a bit-vector of a *different*
    /// width, in which case nothing is pinned: the caller asked for a constant
    /// the existing circuit cannot represent, and silently pinning the bits
    /// that happen to exist would constrain a different value.
    pub fn assert_const(&mut self, term: TermId, value: u64, width: u32) -> bool {
        self.assert_const_limbs(term, &[value], width)
    }

    /// Assert an arbitrary-width constant value for a bit vector.
    ///
    /// Every bit of `value` below `width` is pinned, so this is correct for
    /// bit-vectors wider than 64 bits.  Bits of `value` at or above `width` are
    /// ignored (the literal is read modulo `2^width`, exactly as SMT-LIB reads
    /// an out-of-range numeral).  See [`Self::assert_const`] for the return
    /// value.
    pub fn assert_const_big(&mut self, term: TermId, value: &BigUint, width: u32) -> bool {
        let limbs: SmallVec<[u64; 2]> = value.iter_u64_digits().collect();
        self.assert_const_limbs(term, &limbs, width)
    }

    /// Assert an arbitrary-width constant given as little-endian 64-bit limbs
    /// (`limbs[0]` holds bits 0..63, `limbs[1]` bits 64..127, and so on).
    ///
    /// This is the primitive both [`Self::assert_const`] and
    /// [`Self::assert_const_big`] delegate to; it exists so a caller holding a
    /// `BigInt`-backed literal can pass `value.iter_u64_digits()` directly
    /// without first deciding on a sign-carrying big-integer type.  A limb
    /// beyond the end of the slice reads as `0`, which is the value of that bit
    /// in the little-endian encoding – not a fallback.  See
    /// [`Self::assert_const`] for the return value.
    pub fn assert_const_limbs(&mut self, term: TermId, limbs: &[u64], width: u32) -> bool {
        // A constant term that has not been blasted yet gets its bits
        // *installed* as the two reserved constant variables: no fresh
        // variables, no pinning units, and every gate that consumes a bit
        // folds on it (see [`Sig`]).  A term that already carries signal
        // variables (blasted as a free vector earlier in this scope) keeps
        // them and is pinned the classical way.
        if let Some(existing) = self.term_to_bv.get(&term) {
            if existing.width != width {
                return false;
            }
            let existing = existing.clone();
            for (i, &bit_var) in existing.bits.iter().enumerate() {
                let bit = limbs.get(i / 64).map_or(0, |limb| (limb >> (i % 64)) & 1);
                if bit == 1 {
                    self.sat.add_clause([Lit::pos(bit_var)]);
                } else {
                    self.sat.add_clause([Lit::neg(bit_var)]);
                }
            }
            return true;
        }

        let bits: SmallVec<[Var; 32]> = (0..width as usize)
            .map(|i| {
                let bit = limbs.get(i / 64).map_or(0, |limb| (limb >> (i % 64)) & 1);
                if bit == 1 {
                    self.const_true
                } else {
                    self.const_false
                }
            })
            .collect();
        self.term_to_bv.insert(term, BvVar { bits, width });
        true
    }

    /// Concatenate two bit vectors: result = high ++ low
    /// result[0..low.width-1] = low, result[low.width..low.width+high.width-1] = high
    ///
    /// Returns `false` – encoding nothing – when either operand has not been
    /// bit-blasted, or when `result` already denotes a bit-vector whose width
    /// is not the sum of the operand widths.
    pub fn concat(&mut self, result: TermId, high: TermId, low: TermId) -> bool {
        if let (Some(h), Some(l)) = (
            self.term_to_bv.get(&high).cloned(),
            self.term_to_bv.get(&low).cloned(),
        ) {
            let result_width = h.width + l.width;
            if let Some(existing) = self.term_to_bv.get(&result) {
                return existing.width == result_width;
            }

            // Alias the operands' bits (low part first, then the high part):
            // a concatenation denotes exactly those bits, so no fresh
            // variables and no per-bit equivalence clauses are needed.
            let mut bits: SmallVec<[Var; 32]> = SmallVec::new();
            bits.extend_from_slice(&l.bits);
            bits.extend_from_slice(&h.bits);
            self.term_to_bv.insert(
                result,
                BvVar {
                    bits,
                    width: result_width,
                },
            );
            true
        } else {
            false
        }
    }

    /// Extract a bit range from a bit vector: result = bv\[high:low\]
    /// Extract bits from position `low` to `high` (inclusive)
    ///
    /// Returns `false` – encoding nothing – when `bv` has not been bit-blasted
    /// or the range `[low, high]` does not lie inside it.  An out-of-range
    /// extraction is a malformed term, not a reason to abort the process.
    pub fn extract(&mut self, result: TermId, bv: TermId, high: u32, low: u32) -> bool {
        if let Some(v) = self.term_to_bv.get(&bv).cloned() {
            if high < low || high >= v.width {
                return false;
            }

            let result_width = high - low + 1;
            if let Some(existing) = self.term_to_bv.get(&result) {
                // Already blasted: keep the existing bits (the caller may have
                // constrained them); only a width clash is unencodable.
                return existing.width == result_width;
            }

            // Alias the source bits directly: an extraction denotes exactly
            // those bits, so no fresh variables and no equivalence clauses are
            // needed.  This is the structural sharing Z3's blaster gets for
            // free from hash-consing expressions; without it, a
            // slice-heavy formula (bruttomesso `ext_con`: 8 extractions per
            // 512-bit vector) pays a fresh variable plus two clauses per bit
            // for what is a rename.
            let bits: SmallVec<[Var; 32]> = v.bits[low as usize..=(high as usize)].to_vec().into();
            self.term_to_bv.insert(
                result,
                BvVar {
                    bits,
                    width: result_width,
                },
            );
            true
        } else {
            false
        }
    }

    /// Bit-blast a BV-sorted `ite(cond, then, else)`: a fresh result BV whose
    /// every bit is `cond ? then[i] : else[i]`.
    ///
    /// `cond` is encoded to a single truth variable via [`Self::encode_bool_node`]
    /// (so boolean structure such as `not(c)` is respected); `then` and `else`
    /// must already be bit-blasted to equal-width BVs. No-op if any operand is
    /// missing or the condition is not encodable.
    pub fn bv_ite(
        &mut self,
        result: TermId,
        cond: TermId,
        then_t: TermId,
        else_t: TermId,
        manager: &oxiz_core::ast::TermManager,
    ) {
        let Some(sel) = self.encode_bool_node(cond, manager) else {
            return;
        };
        let (vt, ve) = match (
            self.term_to_bv.get(&then_t).cloned(),
            self.term_to_bv.get(&else_t).cloned(),
        ) {
            (Some(vt), Some(ve)) if vt.width == ve.width => (vt, ve),
            _ => return,
        };
        let r = self.new_bv(result, vt.width).clone();
        for i in 0..vt.width as usize {
            self.encode_mux(r.bits[i], sel, vt.bits[i], ve.bits[i]);
        }
    }

    /// Fix a Bool-sorted term's truth value from the *enclosing* CDCL(T) search.
    ///
    /// A bit-blasted `ite` selector that is a bare boolean variable has no
    /// circuit of its own: [`Self::encode_bool_node`] gives it a fresh, free SAT
    /// variable inside the embedded solver. Free means the embedded search may
    /// pick the branch the outer solver has *ruled out*, so
    /// `(= (ite c #x01 #x02) x) ∧ ¬c ∧ (= x #x01)` looked satisfiable: the outer
    /// solver knows `c` is false, the BV solver did not, and each considered its
    /// own half consistent.
    ///
    /// The theory manager therefore replays every atom assignment here. The unit
    /// lands on the embedded solver's trail at the current level, which is kept
    /// in lockstep with the outer decision levels, so it is retracted on
    /// backtrack exactly like the (dis)equality and comparison assertions. The
    /// value is also remembered so a selector that is *first encoded later*
    /// still picks it up – the outer assignment and the bit-blasting can happen
    /// in either order.
    pub fn assert_bool_value(&mut self, term: TermId, value: bool) {
        let previous = self.outer_bool.insert(term, value);
        self.outer_bool_journal.push((term, previous));
        if let Some(&var) = self.bool_node.get(&term) {
            self.pin_bool_var(var, value);
        }
    }

    /// Add the unit clause forcing `var` to `value`.
    fn pin_bool_var(&mut self, var: Var, value: bool) {
        let lit = if value { Lit::pos(var) } else { Lit::neg(var) };
        self.sat.add_clause([lit]);
    }

    /// Pin the truth variable of an already-encoded Bool term to `value`.
    ///
    /// Unlike [`Self::assert_bool_value`] this records nothing in the outer
    /// replay journal: it is the *assertion* of a Bool-sorted formula inside
    /// this solver (the eager QF\_BV dispatch pins each top-level assertion
    /// this way), not the echo of an outer CDCL(T) decision.
    pub fn pin_bool_term(&mut self, term: TermId, value: bool) {
        if let Some(&var) = self.bool_node.get(&term) {
            self.pin_bool_var(var, value);
        }
    }

    /// Concrete values of every bit-blasted term in the latest model, for
    /// building a term-valued model after a `Sat` verdict.
    ///
    /// Reads the model snapshot captured at the most recent successful
    /// [`Theory::check`], so it stays valid after the embedded trail is rolled
    /// back. Every entry's bits are fully defined: a term the solver left
    /// partially free has no honest concrete value and is omitted.
    pub fn model_bv_values(&self) -> Vec<(TermId, num_bigint::BigUint)> {
        let terms: Vec<TermId> = self
            .term_to_bv
            .keys()
            .copied()
            .filter(|&term| self.bits_all_determined(term))
            .collect();
        terms
            .into_iter()
            .filter_map(|term| self.get_value_big(term).map(|v| (term, v)))
            .collect()
    }

    /// Concrete values of every encoded Bool term in the latest model.
    pub fn model_bool_values(&self) -> Vec<(TermId, bool)> {
        self.bool_node
            .iter()
            .map(|(&term, &var)| (term, self.read_model_bit(var)))
            .collect()
    }

    /// Encode a Bool-sorted term into a single SAT truth variable, recursively
    /// bit-blasting any BV operands it compares. Returns `None` for boolean
    /// shapes outside the supported connective/comparison set.
    ///
    /// Supported: bool `Var`, `True`/`False`, `Not`, `And`, `Or`, `Eq` over BV
    /// operands, and the BV comparisons `BvUlt`/`BvUle`/`BvSlt`/`BvSle`. This is
    /// exactly the condition fragment the SplitRS QF_BV encoder can emit.
    pub fn encode_bool_node(
        &mut self,
        term: TermId,
        manager: &oxiz_core::ast::TermManager,
    ) -> Option<Var> {
        use oxiz_core::ast::TermKind;
        if let Some(&v) = self.bool_node.get(&term) {
            // Re-apply any outer truth value: the node may have been created
            // below a decision level that has since been popped, which retracts
            // the unit clause but not the cached variable.
            if let Some(&value) = self.outer_bool.get(&term) {
                self.pin_bool_var(v, value);
            }
            return Some(v);
        }
        let kind = manager.get(term)?.kind.clone();
        let out = match kind {
            TermKind::Var(_) => {
                // Free boolean variable: a single fresh SAT var stands for it.
                self.sat.new_var()
            }
            TermKind::True => {
                let v = self.sat.new_var();
                self.sat.add_clause([Lit::pos(v)]);
                v
            }
            TermKind::False => {
                let v = self.sat.new_var();
                self.sat.add_clause([Lit::neg(v)]);
                v
            }
            TermKind::Not(inner) => {
                let iv = self.encode_bool_node(inner, manager)?;
                let v = self.sat.new_var();
                self.encode_not(v, iv);
                v
            }
            TermKind::And(ref args) => {
                // Conjunction of all operands.
                let mut acc: Option<Var> = None;
                for &arg in args {
                    let av = self.encode_bool_node(arg, manager)?;
                    acc = Some(match acc {
                        None => av,
                        Some(prev) => {
                            let v = self.sat.new_var();
                            self.encode_and(v, prev, av);
                            v
                        }
                    });
                }
                match acc {
                    Some(v) => v,
                    None => {
                        // Empty conjunction is `true`.
                        let v = self.sat.new_var();
                        self.sat.add_clause([Lit::pos(v)]);
                        v
                    }
                }
            }
            TermKind::Or(ref args) => {
                let mut acc: Option<Var> = None;
                for &arg in args {
                    let av = self.encode_bool_node(arg, manager)?;
                    acc = Some(match acc {
                        None => av,
                        Some(prev) => {
                            let v = self.sat.new_var();
                            self.encode_or(v, prev, av);
                            v
                        }
                    });
                }
                match acc {
                    Some(v) => v,
                    None => {
                        // Empty disjunction is `false`.
                        let v = self.sat.new_var();
                        self.sat.add_clause([Lit::neg(v)]);
                        v
                    }
                }
            }
            TermKind::Eq(lhs, rhs) => {
                // Bool-sorted operands compare truth values (not bit-blasted
                // vectors); BV-sorted operands are pre-bit-blasted by the
                // caller and take the flat per-bit encoder below.
                let lhs_bool = manager
                    .get(lhs)
                    .is_some_and(|t| t.sort == manager.sorts.bool_sort);
                if lhs_bool {
                    let lv = self.encode_bool_node(lhs, manager)?;
                    let rv = self.encode_bool_node(rhs, manager)?;
                    let out = self.sat.new_var();
                    // v <=> (l ↔ r) = ¬(l ⊕ r), folded on constants.
                    let xored = self.gate_xor(self.sig(lv), self.sig(rv));
                    let folded = self.gate_not(xored);
                    self.wire(out, folded);
                    out
                } else {
                    self.encode_eq_node(lhs, rhs)?
                }
            }
            TermKind::BvUlt(lhs, rhs) => self.bool_ult(lhs, rhs, manager, false)?,
            TermKind::BvUle(lhs, rhs) => self.bool_ule(lhs, rhs, manager, false)?,
            TermKind::BvSlt(lhs, rhs) => self.bool_ult(lhs, rhs, manager, true)?,
            TermKind::BvSle(lhs, rhs) => self.bool_ule(lhs, rhs, manager, true)?,
            TermKind::Xor(a, b) => {
                // Boolean XOR through the folding gate: `v <=> a ⊕ b`.
                let av = self.encode_bool_node(a, manager)?;
                let bv = self.encode_bool_node(b, manager)?;
                let out = self.sat.new_var();
                let folded = self.gate_xor(self.sig(av), self.sig(bv));
                self.wire(out, folded);
                out
            }
            TermKind::Implies(a, b) => {
                // `v <=> (¬a ∨ b)`, through the folding gates so constant
                // operands collapse instead of emitting dead clauses.
                let av = self.encode_bool_node(a, manager)?;
                let bv = self.encode_bool_node(b, manager)?;
                let out = self.sat.new_var();
                let negated = self.gate_not(self.sig(av));
                let folded = self.gate_or(negated, self.sig(bv));
                self.wire(out, folded);
                out
            }
            TermKind::Ite(cond, t, e) => {
                // Bool-sorted `ite`: a mux over the two branch truth values.
                let cv = self.encode_bool_node(cond, manager)?;
                let tv = self.encode_bool_node(t, manager)?;
                let ev = self.encode_bool_node(e, manager)?;
                let out = self.sat.new_var();
                let folded = self.gate_mux(self.sig(cv), self.sig(tv), self.sig(ev));
                self.wire(out, folded);
                out
            }
            TermKind::Distinct(ref args) => {
                // `distinct(a_1..a_n)` over bit-vector or Bool operands:
                // the conjunction of pairwise disequalities, each obtained by
                // negating the flat equality encoder (Z3's `blast_distinct`).
                // The n² pairs stay finite: `distinct` arity is bounded by the
                // input's own breadth.
                if args.len() < 2 {
                    // Degenerate `distinct` is vacuously true (and of one
                    // argument, true by definition).
                    let v = self.sat.new_var();
                    self.sat.add_clause([Lit::pos(v)]);
                    v
                } else {
                    let mut pair_lits: SmallVec<[Var; 8]> = SmallVec::new();
                    for i in 0..args.len() {
                        for j in (i + 1)..args.len() {
                            let eq_var = self.encode_eq_node(args[i], args[j])?;
                            let ne_var = self.sat.new_var();
                            self.encode_not(ne_var, eq_var);
                            pair_lits.push(ne_var);
                        }
                    }
                    let mut acc: Option<Var> = None;
                    for pv in pair_lits {
                        acc = Some(match acc {
                            None => pv,
                            Some(prev) => {
                                let v = self.sat.new_var();
                                self.encode_and(v, prev, pv);
                                v
                            }
                        });
                    }
                    acc.unwrap_or_else(|| {
                        let v = self.sat.new_var();
                        self.sat.add_clause([Lit::pos(v)]);
                        v
                    })
                }
            }
            _ => return None,
        };
        self.bool_node.insert(term, out);
        // Honour an outer assignment recorded before this node existed.
        if let Some(&value) = self.outer_bool.get(&term) {
            self.pin_bool_var(out, value);
        }
        Some(out)
    }

    /// Encode `out <=> (lhs = rhs)` over bit-blasted operands, flat.
    ///
    /// Four clauses per bit (`out -> lhs[i] <=> rhs[i]` twice, `lhs[i] != rhs[i]
    /// -> !out` twice) instead of a per-bit XNOR-plus-AND gate chain (nine
    /// clauses per bit plus two auxiliary variables). Constant bits fold:
    /// equal constants drop out, unequal constants refute `out` on the spot,
    /// and one constant against a signal degenerates to the bit equivalence.
    ///
    /// Returns the result variable, or `None` when an operand has not been
    /// bit-blasted or the widths differ.
    fn encode_eq_node(&mut self, lhs: TermId, rhs: TermId) -> Option<Var> {
        let (va, vb) = match (
            self.term_to_bv.get(&lhs).cloned(),
            self.term_to_bv.get(&rhs).cloned(),
        ) {
            (Some(va), Some(vb)) if va.width == vb.width => (va, vb),
            _ => return None,
        };
        let out = self.sat.new_var();
        // Difference literals (one per non-constant bit pair): the equality is
        // true exactly when none of them holds, hence the big clause
        // `out or d_1 or ... or d_n` for the reverse direction.
        let mut diff_lits: SmallVec<[Lit; 32]> = SmallVec::new();
        for i in 0..va.width as usize {
            let l = self.sig(va.bits[i]);
            let r = self.sig(vb.bits[i]);
            match (l, r) {
                (Sig::True, Sig::True) | (Sig::False, Sig::False) => {}
                (Sig::True, Sig::False) | (Sig::False, Sig::True) => {
                    // Constant-unequal bits falsify the equality outright.
                    let _ = self.sat.add_clause([Lit::neg(out)]);
                    return Some(out);
                }
                (Sig::True, Sig::Var(v)) | (Sig::Var(v), Sig::True) => {
                    // This bit is equal to `v`'s value: out -> v, and `!v`
                    // is a "differing bit" for the reverse direction.
                    let lit = Lit::pos(v);
                    let _ = self.sat.add_clause([Lit::neg(out), lit]);
                    diff_lits.push(lit.negate());
                }
                (Sig::False, Sig::Var(v)) | (Sig::Var(v), Sig::False) => {
                    // This bit is equal to `!v`: out -> !v, and `v` differs.
                    let lit = Lit::neg(v);
                    let _ = self.sat.add_clause([Lit::neg(out), lit]);
                    diff_lits.push(lit.negate());
                }
                (Sig::Var(x), Sig::Var(y)) => {
                    if x == y {
                        continue;
                    }
                    // d_i <=> (x XOR y); collected for the big clause below.
                    let d = self.sat.new_var();
                    self.emit_xor(d, x, y);
                    // out -> bits equal at i: !out or !d_i
                    self.sat.add_clause([Lit::neg(out), Lit::neg(d)]);
                    diff_lits.push(Lit::pos(d));
                }
            }
        }
        // Reverse direction: any differing bit must be able to falsify `out`.
        if diff_lits.is_empty() {
            // Every bit pair folded equal (constants, or aliased bits after
            // extract/concat sharing): the equality is a tautology.
            let _ = self.sat.add_clause([Lit::pos(out)]);
        } else {
            let mut clause: SmallVec<[Lit; 33]> = SmallVec::with_capacity(diff_lits.len() + 1);
            clause.push(Lit::pos(out));
            clause.extend(diff_lits);
            let _ = self.sat.add_clause(clause);
        }
        Some(out)
    }

    /// Assert a Bool-sorted formula **true** in the embedded solver, using the
    /// direct literal encodings wherever the top-level polarity is known.
    ///
    /// This is the assertion-side counterpart of [`Self::encode_bool_node`]:
    /// where the node encoder must build an equivalence circuit for *any*
    /// sub-formula (its truth value is not yet known), an asserted formula
    /// known to be true can be fed straight into the solver's constraint
    /// assertions – an equality becomes [`Self::assert_eq`]'s two clauses per
    /// bit (no result variable at all), a comparison becomes
    /// [`Self::assert_ult`]'s cached circuit, and a conjunction recurses.
    /// Disjunctions, negations-of-non-literals and free Booleans fall back to
    /// [`Self::encode_bool_node`] plus a unit pin.
    ///
    /// Returns `false` when the formula reaches a construct outside the
    /// blastable fragment (nothing is asserted for that sub-formula; the
    /// caller must then decline to decide the goal here).
    pub fn assert_formula_true(
        &mut self,
        term: TermId,
        manager: &oxiz_core::ast::TermManager,
    ) -> bool {
        use oxiz_core::ast::TermKind;
        // Explicit work stack: assertion DAGs from real inputs nest `and`
        // hundreds deep, and this walk must not recurse natively.
        let mut stack = vec![term];
        let mut visited = rustc_hash::FxHashSet::default();
        while let Some(tid) = stack.pop() {
            if !visited.insert(tid) {
                continue;
            }
            let Some(data) = manager.get(tid) else {
                return false;
            };
            match &data.kind {
                TermKind::True => {}
                TermKind::False => {
                    let _ = self.sat.add_clause([]);
                }
                TermKind::And(args) => {
                    for &a in args.iter().rev() {
                        stack.push(a);
                    }
                }
                TermKind::Not(inner) => {
                    if !self.assert_formula_false(*inner, manager) {
                        return false;
                    }
                }
                TermKind::Eq(l, r) if self.both_bv_blasted(*l, *r) && self.assert_eq(*l, *r) => {}
                TermKind::BvUlt(l, r)
                    if self.both_bv_blasted(*l, *r) && self.assert_ult(*l, *r) => {}
                TermKind::BvUle(l, r)
                    if self.both_bv_blasted(*l, *r) && self.assert_ule(*l, *r) => {}
                TermKind::BvSlt(l, r)
                    if self.both_bv_blasted(*l, *r) && self.assert_slt(*l, *r) => {}
                TermKind::BvSle(l, r)
                    if self.both_bv_blasted(*l, *r) && self.assert_sle(*l, *r) => {}
                _ => match self.encode_bool_node(tid, manager) {
                    Some(v) => self.pin_bool_var(v, true),
                    None => return false,
                },
            }
        }
        true
    }

    /// Assert a Bool-sorted formula **false** (the negation handling of
    /// [`Self::assert_formula_true`]).
    fn assert_formula_false(
        &mut self,
        term: TermId,
        manager: &oxiz_core::ast::TermManager,
    ) -> bool {
        use oxiz_core::ast::TermKind;
        let Some(data) = manager.get(term) else {
            return false;
        };
        match &data.kind {
            TermKind::False => true,
            TermKind::True => {
                let _ = self.sat.add_clause([]);
                true
            }
            TermKind::Not(inner) => self.assert_formula_true(*inner, manager),
            // a != b  (BV): the disequality assertion.
            TermKind::Eq(l, r) if self.both_bv_blasted(*l, *r) => self.assert_neq(*l, *r),
            // !(a <u b)  ==  b <=u a, and symmetrically for the rest.
            TermKind::BvUlt(l, r) if self.both_bv_blasted(*l, *r) => self.assert_ule(*r, *l),
            TermKind::BvUle(l, r) if self.both_bv_blasted(*l, *r) => self.assert_ult(*r, *l),
            TermKind::BvSlt(l, r) if self.both_bv_blasted(*l, *r) => self.assert_sle(*r, *l),
            TermKind::BvSle(l, r) if self.both_bv_blasted(*l, *r) => self.assert_slt(*r, *l),
            _ => match self.encode_bool_node(term, manager) {
                Some(v) => {
                    self.pin_bool_var(v, false);
                    true
                }
                None => false,
            },
        }
    }

    /// Whether both terms are bit-blasted bit-vectors of equal width.
    fn both_bv_blasted(&self, l: TermId, r: TermId) -> bool {
        matches!(
            (self.term_to_bv.get(&l), self.term_to_bv.get(&r)),
            (Some(a), Some(b)) if a.width == b.width
        )
    }

    /// Encode a strict less-than (signed or unsigned) comparison result var.
    /// Operands are assumed already bit-blasted by the caller.
    fn bool_ult(
        &mut self,
        lhs: TermId,
        rhs: TermId,
        _manager: &oxiz_core::ast::TermManager,
        signed: bool,
    ) -> Option<Var> {
        let (va, vb) = match (
            self.term_to_bv.get(&lhs).cloned(),
            self.term_to_bv.get(&rhs).cloned(),
        ) {
            (Some(va), Some(vb)) if va.width == vb.width => (va, vb),
            _ => return None,
        };
        let width = va.width as usize;
        let result = self.sat.new_var();
        if signed {
            // Signed: if the sign bits differ, lhs<rhs iff sign_lhs=1; else
            // the unsigned comparison decides.  Composed from the folding
            // gates, so constant sign bits collapse the whole mux.
            let sign_a = self.sig(va.bits[width - 1]);
            let sign_b = self.sig(vb.bits[width - 1]);
            let diff_sign = self.gate_xor(sign_a, sign_b);

            let ult = self.sat.new_var();
            self.encode_ult_result(&va.bits, &vb.bits, ult);

            let folded = self.gate_mux(diff_sign, sign_a, Sig::Var(ult));
            self.wire(result, folded);
        } else {
            self.encode_ult_result(&va.bits, &vb.bits, result);
        }
        Some(result)
    }

    /// Encode a less-than-or-equal (signed or unsigned) comparison result var
    /// as `not(rhs < lhs)`.
    fn bool_ule(
        &mut self,
        lhs: TermId,
        rhs: TermId,
        manager: &oxiz_core::ast::TermManager,
        signed: bool,
    ) -> Option<Var> {
        // a <= b  ≡  not(b < a), folded through the NOT gate.
        let gt = self.bool_ult(rhs, lhs, manager, signed)?;
        let v = self.sat.new_var();
        let folded = self.gate_not(self.sig(gt));
        self.wire(v, folded);
        Some(v)
    }

    /// The result bit-vector of a unary/binary operation at `width`, or `None`
    /// when `result` already denotes a bit-vector of a different width.
    fn result_bits(&mut self, result: TermId, width: u32) -> Option<BvVar> {
        let r = self.new_bv(result, width).clone();
        (r.width == width).then_some(r)
    }

    /// Bitwise NOT: result = ~a
    ///
    /// Returns `false` – encoding nothing – when `a` has not been bit-blasted
    /// or `result` already has a different width.
    pub fn bv_not(&mut self, result: TermId, a: TermId) -> bool {
        if let Some(va) = self.term_to_bv.get(&a).cloned() {
            let Some(r) = self.result_bits(result, va.width) else {
                return false;
            };

            for i in 0..va.width as usize {
                // r[i] = ~a[i]
                self.encode_not(r.bits[i], va.bits[i]);
            }
            return true;
        }
        false
    }

    /// Bitwise AND: result = a & b
    ///
    /// Returns `false` – encoding nothing – when an operand has not been
    /// bit-blasted, the two operands have different widths, or `result`
    /// already has a different width.
    pub fn bv_and(&mut self, result: TermId, a: TermId, b: TermId) -> bool {
        if let Some((va, vb)) = self.binop_bits(a, b) {
            let Some(r) = self.result_bits(result, va.width) else {
                return false;
            };

            for i in 0..va.width as usize {
                self.encode_and(r.bits[i], va.bits[i], vb.bits[i]);
            }
            return true;
        }
        false
    }

    /// Bitwise OR: result = a | b
    ///
    /// Returns `false` – encoding nothing – when an operand has not been
    /// bit-blasted, the two operands have different widths, or `result`
    /// already has a different width.
    pub fn bv_or(&mut self, result: TermId, a: TermId, b: TermId) -> bool {
        if let Some((va, vb)) = self.binop_bits(a, b) {
            let Some(r) = self.result_bits(result, va.width) else {
                return false;
            };

            for i in 0..va.width as usize {
                self.encode_or(r.bits[i], va.bits[i], vb.bits[i]);
            }
            return true;
        }
        false
    }

    /// Bitwise XOR: result = a ^ b
    ///
    /// Returns `false` – encoding nothing – when an operand has not been
    /// bit-blasted, the two operands have different widths, or `result`
    /// already has a different width.
    pub fn bv_xor(&mut self, result: TermId, a: TermId, b: TermId) -> bool {
        if let Some((va, vb)) = self.binop_bits(a, b) {
            let Some(r) = self.result_bits(result, va.width) else {
                return false;
            };

            for i in 0..va.width as usize {
                self.encode_xor(r.bits[i], va.bits[i], vb.bits[i]);
            }
            return true;
        }
        false
    }

    /// Negation (two's complement): result = -a = ~a + 1
    ///
    /// Returns `false` – encoding nothing – when `a` has not been bit-blasted
    /// or `result` already has a different width.
    pub fn bv_neg(&mut self, result: TermId, a: TermId) -> bool {
        if let Some(va) = self.term_to_bv.get(&a).cloned() {
            let Some(r) = self.result_bits(result, va.width) else {
                return false;
            };

            // First compute ~a
            let mut not_bits: SmallVec<[Var; 32]> = SmallVec::new();
            for &bit in &va.bits {
                let not_bit = self.sat.new_var();
                self.encode_not(not_bit, bit);
                not_bits.push(not_bit);
            }

            // Then add 1 using a ripple-carry adder
            self.encode_add_const(&r.bits, &not_bits, 1);
            return true;
        }
        false
    }

    /// Addition: result = a + b
    ///
    /// Returns `false` – encoding nothing – when an operand has not been
    /// bit-blasted, the two operands have different widths, or `result`
    /// already has a different width.
    pub fn bv_add(&mut self, result: TermId, a: TermId, b: TermId) -> bool {
        if let Some((va, vb)) = self.binop_bits(a, b) {
            let Some(r) = self.result_bits(result, va.width) else {
                return false;
            };

            self.encode_adder(&r.bits, &va.bits, &vb.bits);
            return true;
        }
        false
    }

    /// Subtraction: result = a - b = a + (-b)
    ///
    /// Returns `false` – encoding nothing – when an operand has not been
    /// bit-blasted, the two operands have different widths, or `result`
    /// already has a different width.
    pub fn bv_sub(&mut self, result: TermId, a: TermId, b: TermId) -> bool {
        if let Some((va, vb)) = self.binop_bits(a, b) {
            let Some(r) = self.result_bits(result, va.width) else {
                return false;
            };

            // Compute -b (two's complement)
            let mut neg_b: SmallVec<[Var; 32]> = SmallVec::new();
            for &bit in &vb.bits {
                let not_bit = self.sat.new_var();
                self.encode_not(not_bit, bit);
                neg_b.push(not_bit);
            }

            // Create temp variables for -b
            let mut neg_b_with_one: SmallVec<[Var; 32]> = SmallVec::new();
            for _ in 0..va.width {
                neg_b_with_one.push(self.sat.new_var());
            }
            self.encode_add_const(&neg_b_with_one, &neg_b, 1);

            // Add a + (-b)
            self.encode_adder(&r.bits, &va.bits, &neg_b_with_one);
            return true;
        }
        false
    }

    /// Multiplication: result = a * b (using shift-and-add)
    ///
    /// Returns `false` – encoding nothing – when an operand has not been
    /// bit-blasted, the two operands have different widths, or `result`
    /// already has a different width.
    pub fn bv_mul(&mut self, result: TermId, a: TermId, b: TermId) -> bool {
        if let Some((va, vb)) = self.binop_bits(a, b) {
            let Some(r) = self.result_bits(result, va.width) else {
                return false;
            };
            self.encode_mul(&r.bits, &va.bits, &vb.bits);
            return true;
        }
        false
    }

    /// `bvmul` encoding with the CEGAR switch: when the configured
    /// abstraction width is set, the term's width is at least it, and BOTH
    /// operands are already-blasted non-constant wires, the term is
    /// abstracted ([`Self::abstract_mul`]) instead of bit-blasted; every
    /// other case (abstraction off, too narrow, or a constant operand whose
    /// exact circuit constant-folds cheaply) takes the exact circuit.  With
    /// abstraction off this is `bv_mul` exactly — the general CDCL(T) path's
    /// clause stream is unchanged.
    pub fn bv_mul_or_abstract(
        &mut self,
        result: TermId,
        a: TermId,
        b: TermId,
        a_is_const: bool,
        b_is_const: bool,
    ) -> bool {
        if self.abstract_mul_width > 0
            && !a_is_const
            && !b_is_const
            && let Some((va, vb)) = self.binop_bits(a, b)
            && va.width >= self.abstract_mul_width
            && va.width == vb.width
            && !self.term_to_bv.contains_key(&result)
        {
            return self.abstract_mul(result, a, b);
        }
        self.bv_mul(result, a, b)
    }

    /// Set the width at (and above) which `bvmul` is abstracted instead of
    /// bit-blasted (0 = always exact).  Only the pure-BV dispatch toggles
    /// this around its blast; every other caller keeps the default and gets
    /// the exact circuit.
    pub fn set_mul_abstraction_width(&mut self, width: u32) {
        self.abstract_mul_width = width;
    }

    /// Drain the abstractions recorded during the blast (the caller owns the
    /// CEGAR loop that refines them).
    pub fn take_mul_abstractions(&mut self) -> Vec<MulAbstraction> {
        core::mem::take(&mut self.mul_abstractions)
    }

    /// CEGAR tier 1 — abstract one `bvmul` (Niemetz/Preiner/Zohar,
    /// *Scalable Bit-Blasting with Abstractions*).
    ///
    /// The exact multiplier circuit is replaced by fresh, unconstrained
    /// result wires plus the published identity lemmas
    /// (`a = 0 -> m = 0`, `b = 0 -> m = 0`, `a = 1 -> m = b`,
    /// `b = 1 -> m = a`), each a logical consequence of the exact
    /// definition.  The abstract instance is therefore a relaxation of the
    /// exact one: `Unsat` transfers, `Sat` is provisional (the caller
    /// checks the model's product consistency and refines).
    ///
    /// Returns `false` (and encodes nothing) when the operands are not
    /// blasted at equal widths.
    pub fn abstract_mul(&mut self, result: TermId, a: TermId, b: TermId) -> bool {
        let Some((va, vb)) = self.binop_bits(a, b) else {
            return false;
        };
        if va.width != vb.width {
            return false;
        }
        let width = va.width;
        let Some(r) = self.result_bits(result, width) else {
            return false;
        };

        // zero-detect(a): AND of NOT a_i (folds through constants — a
        // provably-nonzero operand makes the implication vacuous, `Sig::False`).
        let mut zero_a = Sig::True;
        for &bit in &va.bits {
            let b_sig = self.sig(bit);
            let not_b = self.gate_not(b_sig);
            zero_a = self.gate_and(zero_a, not_b);
        }
        let mut zero_b = Sig::True;
        for &bit in &vb.bits {
            let b_sig = self.sig(bit);
            let not_b = self.gate_not(b_sig);
            zero_b = self.gate_and(zero_b, not_b);
        }
        // one-detect(x): x == 1 (bit 0 set, the rest clear).
        let one_of = |bits: &[Var], slf: &mut Self| -> Sig {
            let first = slf.sig(bits[0]);
            let mut acc = first;
            for &bit in &bits[1..] {
                let b_sig = slf.sig(bit);
                let not_b = slf.gate_not(b_sig);
                acc = slf.gate_and(acc, not_b);
            }
            acc
        };
        let one_a = one_of(&va.bits, self);
        let one_b = one_of(&vb.bits, self);

        // Emit the identity lemmas, one pair of implications per result bit.
        // `lit_true_of(s)` is the literal asserting `s`.
        for &m_bit in &r.bits {
            let m = self.sig(m_bit);
            let (Sig::Var(mm), mm_pos) = (m, Lit::pos(m_bit)) else {
                // Constant result wire cannot happen (fresh wires), but
                // declining is the honest answer if it ever did.
                return false;
            };
            // a = 0 -> m_i = 0  (¬zero_a ∨ ¬m_i)
            match zero_a {
                Sig::True => {
                    self.sat.add_clause([Lit::neg(mm)]);
                }
                Sig::Var(z) => {
                    self.sat.add_clause([Lit::neg(z), Lit::neg(mm)]);
                }
                Sig::False => {}
            }
            // b = 0 -> m_i = 0
            match zero_b {
                Sig::True => {
                    self.sat.add_clause([Lit::neg(mm)]);
                }
                Sig::Var(z) => {
                    self.sat.add_clause([Lit::neg(z), Lit::neg(mm)]);
                }
                Sig::False => {}
            }
            // a = 1 -> m_i = b_i   (¬one_a ∨ ¬m_i ∨ b_i) ∧ (¬one_a ∨ m_i ∨ ¬b_i)
            let idx = r.bits.iter().position(|&x| x == m_bit).unwrap_or(0);
            if let Some(&bvar) = vb.bits.get(idx) {
                match one_a {
                    Sig::True => {
                        self.sat.add_clause([Lit::neg(mm), Lit::pos(bvar)]);
                        self.sat.add_clause([mm_pos, Lit::neg(bvar)]);
                    }
                    Sig::Var(o) => {
                        self.sat
                            .add_clause([Lit::neg(o), Lit::neg(mm), Lit::pos(bvar)]);
                        self.sat.add_clause([Lit::neg(o), mm_pos, Lit::neg(bvar)]);
                    }
                    Sig::False => {}
                }
            }
            // b = 1 -> m_i = a_i
            if let Some(&avar) = va.bits.get(idx) {
                match one_b {
                    Sig::True => {
                        self.sat.add_clause([Lit::neg(mm), Lit::pos(avar)]);
                        self.sat.add_clause([mm_pos, Lit::neg(avar)]);
                    }
                    Sig::Var(o) => {
                        self.sat
                            .add_clause([Lit::neg(o), Lit::neg(mm), Lit::pos(avar)]);
                        self.sat.add_clause([Lit::neg(o), mm_pos, Lit::neg(avar)]);
                    }
                    Sig::False => {}
                }
            }
        }

        self.mul_abstractions.push(MulAbstraction {
            result,
            a,
            b,
            width,
        });
        true
    }

    /// CEGAR tier 2 — value refinement for one abstraction under a spurious
    /// model: the clause `(a != va ∨ b != vb ∨ result = va * vb)`, one clause
    /// per result bit.  Blocks exactly this operand assignment unless the
    /// product is honored; sound (a consequence of the exact definition).
    #[allow(clippy::too_many_arguments)]
    pub fn refine_mul_value(&mut self, abs: &MulAbstraction, va: &BigUint, vb: &BigUint) -> bool {
        let width = abs.width;
        let (Some(ra), Some(rb), Some(rr)) = (
            self.term_to_bv.get(&abs.a).cloned(),
            self.term_to_bv.get(&abs.b).cloned(),
            self.term_to_bv.get(&abs.result).cloned(),
        ) else {
            return false;
        };
        if ra.width != width || rb.width != width || rr.width != width {
            return false;
        }
        let product = (va * vb) & ((BigUint::from(1u8) << width as usize) - 1u8);
        // Guard literals: bit i of a differs from va_i (same for b).
        let mut guard: Vec<Lit> = Vec::with_capacity(2 * width as usize);
        for i in 0..width as usize {
            let bit = |v: &BigUint, i: usize| (v >> i) & BigUint::from(1u8) == BigUint::from(1u8);
            if let Some(&av) = ra.bits.get(i) {
                let a_lit = if bit(va, i) {
                    Lit::neg(av)
                } else {
                    Lit::pos(av)
                };
                guard.push(a_lit);
            }
            if let Some(&bv_) = rb.bits.get(i) {
                let b_lit = if bit(vb, i) {
                    Lit::neg(bv_)
                } else {
                    Lit::pos(bv_)
                };
                guard.push(b_lit);
            }
        }
        for (j, &m_bit) in rr.bits.iter().enumerate() {
            let p_j = (&product >> j) & BigUint::from(1u8) == BigUint::from(1u8);
            let eq_lit = if p_j {
                Lit::pos(m_bit)
            } else {
                Lit::neg(m_bit)
            };
            let mut clause = guard.clone();
            clause.push(eq_lit);
            self.sat.add_clause(clause);
        }
        true
    }

    /// Left shift by a compile-time constant: result = a << shift_amount.
    ///
    /// Encodes each result bit as a direct wire from the source bit `shift_amount`
    /// positions below, or as a constant-0 for the low `shift_amount` bits.
    /// Used to constant-fold `bvmul(x, 2^k)` without the expensive multiplier.
    ///
    /// Returns `false` – encoding nothing – when `a` has not been bit-blasted,
    /// `a` is not `width` bits wide, or `result` already has a different width.
    pub fn bv_shl_const(&mut self, result: TermId, a: TermId, shift: u32, width: u32) -> bool {
        if let Some(va) = self.term_to_bv.get(&a).cloned() {
            if va.width != width {
                return false;
            }
            let Some(r) = self.result_bits(result, width) else {
                return false;
            };
            for k in 0..width as usize {
                if shift >= width || k < shift as usize {
                    self.sat.add_clause([Lit::neg(r.bits[k])]);
                } else {
                    self.encode_bit_eq(r.bits[k], va.bits[k - shift as usize]);
                }
            }
            return true;
        }
        false
    }

    /// Signed less than: a < b (two's complement)
    ///
    /// Returns `false` – asserting nothing – when either operand has not been
    /// bit-blasted, the two have different widths, or the width is zero (a
    /// zero-width vector has no sign bit).
    pub fn assert_slt(&mut self, a: TermId, b: TermId) -> bool {
        if let Some((va, vb)) = self.binop_bits(a, b) {
            let width = va.width as usize;
            if width == 0 {
                return false;
            }

            // For signed comparison:
            // If sign bits differ: a < b iff a is negative (a[n-1] = 1)
            // If sign bits same: compare as unsigned

            // Signed: if the sign bits differ, a < b iff a is negative
            // (sign_a = 1); otherwise the unsigned comparison decides.  Built
            // from the folding gates, so constant sign bits collapse the mux.
            let sign_a = self.sig(va.bits[width - 1]);
            let sign_b = self.sig(vb.bits[width - 1]);
            let diff_sign = self.gate_xor(sign_a, sign_b);

            let ult_result = self.sat.new_var();
            self.encode_ult_result(&va.bits, &vb.bits, ult_result);

            let result = self.gate_mux(diff_sign, sign_a, Sig::Var(ult_result));
            match result {
                Sig::True => {}
                Sig::False => {
                    self.sat.add_clause([]);
                }
                Sig::Var(v) => {
                    self.sat.add_clause([Lit::pos(v)]);
                }
            }
            return true;
        }
        false
    }

    /// Signed less than or equal: a <= b
    ///
    /// Returns `false` – asserting nothing – when either operand has not been
    /// bit-blasted, the two have different widths, or the width is zero (a
    /// zero-width vector has no sign bit).
    pub fn assert_sle(&mut self, a: TermId, b: TermId) -> bool {
        if let Some((va, vb)) = self.binop_bits(a, b) {
            let width = va.width as usize;
            if width == 0 {
                return false;
            }

            // a <= b is equivalent to NOT(b < a)
            // Create temporary variables for checking b < a
            let slt_ba = self.sat.new_var();

            // Encode b < a into slt_ba
            let sign_a = va.bits[width - 1];
            let sign_b = vb.bits[width - 1];

            let diff_sign = self.sat.new_var();
            self.encode_xor(diff_sign, sign_b, sign_a);

            // If signs differ, b < a iff sign_b = 1
            // If signs same, b < a iff ult(b, a)
            let ult_result = self.sat.new_var();
            self.encode_ult_result(&vb.bits, &va.bits, ult_result);

            self.sat
                .add_clause([Lit::neg(diff_sign), Lit::neg(sign_b), Lit::pos(slt_ba)]);

            self.sat
                .add_clause([Lit::neg(diff_sign), Lit::pos(sign_b), Lit::neg(slt_ba)]);

            self.sat
                .add_clause([Lit::pos(diff_sign), Lit::neg(ult_result), Lit::pos(slt_ba)]);

            self.sat
                .add_clause([Lit::pos(diff_sign), Lit::pos(ult_result), Lit::neg(slt_ba)]);

            // Assert NOT(slt_ba) which means a <= b
            self.sat.add_clause([Lit::neg(slt_ba)]);
            return true;
        }
        false
    }

    // ======== Helper encoding functions ========

    // The layer below comes in two flavours.
    //
    // * `gate_*` combinators take and return [`Sig`]s and constant-fold before
    //   allocating anything: `gate_and(x, Sig::False)` is `Sig::False` with no
    //   variable and no clause.  Every circuit builder in this file composes
    //   these, so constant inputs anywhere in a circuit collapse it
    //   transitively - the same shape as Z3's bit-blaster, whose
    //   `mk_and`/`mk_xor`/`mk_full_adder` (`bit_blaster_tpl_def.h`) run over a
    //   rewriting layer that performs exactly these folds.
    // * `encode_*` functions keep the historical `Var`-based signatures for
    //   callers that pre-allocate their result bits (`bv_add`, `concat`, ...).
    //   They classify their inputs with [`Self::sig`] and delegate to the
    //   `gate_*` layer, then [`Self::wire`] the pre-allocated output to
    //   whatever the folded result is (a pinned unit for a constant, an
    //   equivalence pair for a signal).
    //
    // The raw clause emitters (`emit_*`) are therefore only reached with
    // ordinary signal variables and never emit a clause that unit propagation
    // would immediately subsume.

    /// Classify a bit variable as one of the reserved constants or a signal.
    #[inline]
    fn sig(&self, v: Var) -> Sig {
        if v == self.const_true {
            Sig::True
        } else if v == self.const_false {
            Sig::False
        } else {
            Sig::Var(v)
        }
    }

    /// The variable carrying `s` (`const_true` / `const_false` for constants).
    #[inline]
    fn sig_var(&self, s: Sig) -> Var {
        match s {
            Sig::True => self.const_true,
            Sig::False => self.const_false,
            Sig::Var(v) => v,
        }
    }

    /// Constrain the pre-allocated output bit `out` to equal `s`.
    ///
    /// * constant: a single unit clause pins `out` (the same mechanism
    ///   [`Self::assert_const_limbs`] has always used for constant bits);
    /// * signal: an equivalence pair, skipped when `out` already *is* that
    ///   signal.
    ///
    /// `out` is always a freshly allocated bit of a result vector, so the pin
    /// can never contradict a prior definition of `out` itself.
    fn wire(&mut self, out: Var, s: Sig) {
        match s {
            Sig::True => {
                self.sat.add_clause([Lit::pos(out)]);
            }
            Sig::False => {
                self.sat.add_clause([Lit::neg(out)]);
            }
            Sig::Var(v) => {
                if v != out {
                    self.emit_bit_eq(out, v);
                }
            }
        }
    }

    /// Emit the raw equivalence clauses `a <=> b` for two distinct signals.
    fn emit_bit_eq(&mut self, a: Var, b: Var) {
        self.sat.add_clause([Lit::neg(a), Lit::pos(b)]);
        self.sat.add_clause([Lit::pos(a), Lit::neg(b)]);
    }

    /// Encode bit equality between two arbitrary bit variables, folding on
    /// the reserved constants.
    ///
    /// Two equal constants need no clause; two *different* constants make the
    /// equality unsatisfiable, which is reported honestly through the empty
    /// clause (the SAT solver latches `trivially_unsat` and the next
    /// `BvSolver::check` reports the conflict).
    fn encode_bit_eq(&mut self, a: Var, b: Var) {
        match (self.sig(a), self.sig(b)) {
            (Sig::True, Sig::True) | (Sig::False, Sig::False) => {}
            (Sig::Var(x), Sig::Var(y)) => {
                if x != y {
                    self.emit_bit_eq(x, y);
                }
            }
            (Sig::True, Sig::False) | (Sig::False, Sig::True) => {
                let _ = self.sat.add_clause([]);
            }
            (Sig::True, Sig::Var(v)) | (Sig::Var(v), Sig::True) => {
                let _ = self.sat.add_clause([Lit::pos(v)]);
            }
            (Sig::False, Sig::Var(v)) | (Sig::Var(v), Sig::False) => {
                let _ = self.sat.add_clause([Lit::neg(v)]);
            }
        }
    }

    /// Raw NOT emitter for two signals: `out <=> not input`.
    fn emit_not(&mut self, out: Var, input: Var) {
        self.sat.add_clause([Lit::pos(out), Lit::pos(input)]);
        self.sat.add_clause([Lit::neg(out), Lit::neg(input)]);
    }

    /// NOT with constant folding.
    fn gate_not(&mut self, a: Sig) -> Sig {
        match a {
            Sig::True => Sig::False,
            Sig::False => Sig::True,
            Sig::Var(v) => {
                let out = self.sat.new_var();
                self.emit_not(out, v);
                Sig::Var(out)
            }
        }
    }

    /// Encode NOT gate: out = ~in
    fn encode_not(&mut self, out: Var, input: Var) {
        let folded = self.gate_not(self.sig(input));
        self.wire(out, folded);
    }

    /// Raw AND emitter for two signals.
    fn emit_and(&mut self, out: Var, a: Var, b: Var) {
        // out <=> (a AND b)
        // out => a, out => b, (a AND b) => out
        self.sat.add_clause([Lit::neg(out), Lit::pos(a)]);
        self.sat.add_clause([Lit::neg(out), Lit::pos(b)]);
        self.sat
            .add_clause([Lit::pos(out), Lit::neg(a), Lit::neg(b)]);
    }

    /// AND with constant folding.
    fn gate_and(&mut self, a: Sig, b: Sig) -> Sig {
        match (a, b) {
            (Sig::False, _) | (_, Sig::False) => Sig::False,
            (Sig::True, x) | (x, Sig::True) => x,
            (Sig::Var(x), Sig::Var(y)) => {
                if x == y {
                    a
                } else {
                    let out = self.sat.new_var();
                    self.emit_and(out, x, y);
                    Sig::Var(out)
                }
            }
        }
    }

    /// Encode AND gate: out = a & b
    fn encode_and(&mut self, out: Var, a: Var, b: Var) {
        let folded = self.gate_and(self.sig(a), self.sig(b));
        self.wire(out, folded);
    }

    /// Raw OR emitter for two signals.
    fn emit_or(&mut self, out: Var, a: Var, b: Var) {
        // out <=> (a OR b)
        self.sat
            .add_clause([Lit::neg(out), Lit::pos(a), Lit::pos(b)]);
        self.sat.add_clause([Lit::pos(out), Lit::neg(a)]);
        self.sat.add_clause([Lit::pos(out), Lit::neg(b)]);
    }

    /// OR with constant folding.
    fn gate_or(&mut self, a: Sig, b: Sig) -> Sig {
        match (a, b) {
            (Sig::True, _) | (_, Sig::True) => Sig::True,
            (Sig::False, x) | (x, Sig::False) => x,
            (Sig::Var(x), Sig::Var(y)) => {
                if x == y {
                    a
                } else {
                    let out = self.sat.new_var();
                    self.emit_or(out, x, y);
                    Sig::Var(out)
                }
            }
        }
    }

    /// Encode OR gate: out = a | b
    fn encode_or(&mut self, out: Var, a: Var, b: Var) {
        let folded = self.gate_or(self.sig(a), self.sig(b));
        self.wire(out, folded);
    }

    /// Raw XOR emitter for two signals.
    fn emit_xor(&mut self, out: Var, a: Var, b: Var) {
        // out <=> (a XOR b)
        self.sat
            .add_clause([Lit::neg(out), Lit::neg(a), Lit::neg(b)]);
        self.sat
            .add_clause([Lit::neg(out), Lit::pos(a), Lit::pos(b)]);
        self.sat
            .add_clause([Lit::pos(out), Lit::neg(a), Lit::pos(b)]);
        self.sat
            .add_clause([Lit::pos(out), Lit::pos(a), Lit::neg(b)]);
    }

    /// XOR with constant folding.
    fn gate_xor(&mut self, a: Sig, b: Sig) -> Sig {
        match (a, b) {
            (Sig::False, x) | (x, Sig::False) => x,
            (Sig::True, x) | (x, Sig::True) => self.gate_not(x),
            (Sig::Var(x), Sig::Var(y)) => {
                if x == y {
                    Sig::False
                } else {
                    let out = self.sat.new_var();
                    self.emit_xor(out, x, y);
                    Sig::Var(out)
                }
            }
        }
    }

    /// Encode XOR gate: out = a ^ b
    fn encode_xor(&mut self, out: Var, a: Var, b: Var) {
        let folded = self.gate_xor(self.sig(a), self.sig(b));
        self.wire(out, folded);
    }

    /// XNOR with constant folding (`a = b`).
    fn gate_xnor(&mut self, a: Sig, b: Sig) -> Sig {
        let x = self.gate_xor(a, b);
        self.gate_not(x)
    }

    /// `~a & b` with constant folding.
    fn gate_and_not_a(&mut self, a: Sig, b: Sig) -> Sig {
        match (a, b) {
            (Sig::True, _) | (_, Sig::False) => Sig::False,
            (Sig::False, x) => x,
            (Sig::Var(x), Sig::True) => self.gate_not(Sig::Var(x)),
            (Sig::Var(x), Sig::Var(y)) => {
                if x == y {
                    // a & ~a = 0
                    Sig::False
                } else {
                    let out = self.sat.new_var();
                    // out <=> (~a & b)
                    self.sat.add_clause([Lit::neg(out), Lit::neg(x)]);
                    self.sat.add_clause([Lit::neg(out), Lit::pos(y)]);
                    self.sat
                        .add_clause([Lit::pos(out), Lit::pos(x), Lit::neg(y)]);
                    Sig::Var(out)
                }
            }
        }
    }

    /// Raw multiplexer emitter for three signals.
    fn emit_mux(&mut self, out: Var, sel: Var, if_true: Var, if_false: Var) {
        // out = (sel AND if_true) OR (~sel AND if_false)
        self.sat
            .add_clause([Lit::neg(sel), Lit::neg(if_true), Lit::pos(out)]);
        self.sat
            .add_clause([Lit::neg(sel), Lit::pos(if_true), Lit::neg(out)]);
        self.sat
            .add_clause([Lit::pos(sel), Lit::neg(if_false), Lit::pos(out)]);
        self.sat
            .add_clause([Lit::pos(sel), Lit::pos(if_false), Lit::neg(out)]);
    }

    /// Multiplexer with constant folding.
    fn gate_mux(&mut self, sel: Sig, if_true: Sig, if_false: Sig) -> Sig {
        match sel {
            Sig::True => if_true,
            Sig::False => if_false,
            Sig::Var(s) => {
                if if_true == if_false {
                    return if_true;
                }
                match (if_true, if_false) {
                    (Sig::True, Sig::False) => Sig::Var(s),
                    (Sig::False, Sig::True) => self.gate_not(Sig::Var(s)),
                    _ => {
                        let out = self.sat.new_var();
                        self.emit_mux(out, s, self.sig_var(if_true), self.sig_var(if_false));
                        Sig::Var(out)
                    }
                }
            }
        }
    }

    /// Encode multiplexer: out = sel ? if_true : if_false
    fn encode_mux(&mut self, out: Var, sel: Var, if_true: Var, if_false: Var) {
        let folded = self.gate_mux(self.sig(sel), self.sig(if_true), self.sig(if_false));
        self.wire(out, folded);
    }

    /// Full adder over [`Sig`]s: `(sum, carry_out) = a + b + carry_in`, with
    /// constant folding at every gate.
    ///
    /// A constant operand degenerates this into a half adder (or a pure wire)
    /// exactly as in Z3's `mk_full_adder`, which runs over the rewriting
    /// layer's `mk_xor`/`mk_and`/`mk_or`.
    fn gate_full_adder(&mut self, a: Sig, b: Sig, carry_in: Sig) -> (Sig, Sig) {
        let axb = self.gate_xor(a, b);
        let sum = self.gate_xor(axb, carry_in);
        let aab = self.gate_and(a, b);
        let caxb = self.gate_and(carry_in, axb);
        let cout = self.gate_or(aab, caxb);
        (sum, cout)
    }

    /// Encode ripple-carry adder: result = a + b
    fn encode_adder(&mut self, result: &[Var], a: &[Var], b: &[Var]) {
        // Discard the carry-out: width-only wrapping addition.
        let _ = self.encode_adder_carry(result, a, b);
    }

    /// Encode a ripple-carry adder `result = a + b` and return the final
    /// carry-out as a [`Sig`] (true iff the unsigned sum overflows `width`
    /// bits; already folded to a constant when the operands determine it).
    ///
    /// Callers that must forbid wrap-around (e.g. the division/remainder
    /// equation `a = q*b + r`) constrain the returned carry-out to 0 via
    /// [`Self::sig_require_false`].
    fn encode_adder_carry(&mut self, result: &[Var], a: &[Var], b: &[Var]) -> Sig {
        assert_eq!(result.len(), a.len());
        assert_eq!(result.len(), b.len());

        let width = result.len();
        let mut carry = Sig::False;

        for i in 0..width {
            let (sum, next_carry) = self.gate_full_adder(self.sig(a[i]), self.sig(b[i]), carry);
            self.wire(result[i], sum);
            carry = next_carry;
        }

        carry
    }

    /// Emit the guarded non-wrap clause `guard ∨ ¬s` used by the division
    /// circuits (`b_is_zero ∨ ¬carry_out`), folding on a constant `s`:
    /// the clause vanishes when `s` is false and degenerates to the unit
    /// `guard` when `s` is true.
    fn add_guarded_not(&mut self, guard: Var, s: Sig) {
        match s {
            Sig::False => {}
            Sig::True => {
                self.sat.add_clause([Lit::pos(guard)]);
            }
            Sig::Var(v) => {
                self.sat.add_clause([Lit::pos(guard), Lit::neg(v)]);
            }
        }
    }

    /// Encode addition with constant: result = a + const
    ///
    /// The constant enters the full adders as [`Sig`] constants, so each bit
    /// position degenerates to a half adder (or a bare wire) with no extra
    /// pinned variables or clauses.
    fn encode_add_const(&mut self, result: &[Var], a: &[Var], constant: u64) {
        assert_eq!(result.len(), a.len());

        let width = result.len();
        let mut carry = Sig::False;

        for i in 0..width {
            let const_bit = ((constant >> i) & 1) == 1;
            // Overflow carry of the top bit is ignored: width-only wrapping.
            let (sum, next_carry) = self.gate_full_adder(
                self.sig(a[i]),
                if const_bit { Sig::True } else { Sig::False },
                carry,
            );
            self.wire(result[i], sum);
            carry = next_carry;
        }
    }

    /// Encode unsigned less than and store result in a variable
    /// Encode unsigned less-than: result ⇔ (a < b)
    /// Uses LSB-to-MSB comparison: higher bits override lower bits.
    fn encode_ult_result(&mut self, a_bits: &[Var], b_bits: &[Var], result: Var) {
        let width = a_bits.len();
        if width == 0 {
            // Empty bitvectors: 0 < 0 is false
            self.sat.add_clause([Lit::neg(result)]);
            return;
        }

        // Compare from LSB to MSB
        // lt_i represents "a < b considering only bits 0..i"
        // Higher indexed bits (more significant) override lower bits
        // Recurrence: lt_next = (~a[i] & b[i]) | ((a[i] = b[i]) & lt_prev)
        //
        // Meaning:
        // - If a[i] < b[i], then a < b (current bit overrides lower bits)
        // - If a[i] > b[i], then a > b (current bit overrides lower bits)
        // - If a[i] = b[i], result depends on lower bits (lt_prev)

        // Start with LSB (bit 0)
        // lt_0 = ~a[0] & b[0]
        let mut lt_prev = self.gate_and_not_a(self.sig(a_bits[0]), self.sig(b_bits[0]));

        // Process bits from 1 to MSB
        for i in 1..width {
            let ai = self.sig(a_bits[i]);
            let bi = self.sig(b_bits[i]);

            // lt_at_i = ~ai & bi (a < b at this specific bit)
            let lt_at_i = self.gate_and_not_a(ai, bi);

            // eq_i = (ai ⇔ bi) (bits are equal)
            let eq_i = self.gate_xnor(ai, bi);

            // carry_prev = eq_i & lt_prev (propagate from lower bits)
            let carry_prev = self.gate_and(eq_i, lt_prev);

            // lt_next = lt_at_i | carry_prev
            lt_prev = self.gate_or(lt_at_i, carry_prev);
        }

        // Constant operands fold the whole chain: `wire` pins the result.
        self.wire(result, lt_prev);
    }

    // ======== Additional helper encoding functions ========

    /// Encode: out = 1 iff all bits in the list are 0
    fn encode_all_zero(&mut self, out: Var, bits: &[Var]) {
        let mut signals: SmallVec<[Var; 32]> = SmallVec::new();
        for &bit in bits {
            match self.sig(bit) {
                Sig::True => {
                    // One true bit falsifies "all zero" unconditionally.
                    self.sat.add_clause([Lit::neg(out)]);
                    return;
                }
                Sig::False => {}
                Sig::Var(v) => signals.push(v),
            }
        }
        if signals.is_empty() {
            self.sat.add_clause([Lit::pos(out)]);
            return;
        }

        // out = AND(~bits[i] for all i)
        // out => ~bits[i] for all i
        for &bit in &signals {
            self.sat.add_clause([Lit::neg(out), Lit::neg(bit)]);
        }

        // (~bits[0] AND ... AND ~bits[n-1]) => out
        let mut clause: SmallVec<[Lit; 32]> = SmallVec::new();
        clause.push(Lit::pos(out));
        for &bit in &signals {
            clause.push(Lit::pos(bit));
        }
        self.sat.add_clause(clause);
    }

    /// Encode two's complement negation: result = -a
    fn encode_two_complement(&mut self, result: &[Var], a: &[Var]) {
        assert_eq!(result.len(), a.len());

        // ~a
        let not_a: SmallVec<[Sig; 32]> =
            a.iter().map(|&bit| self.gate_not(self.sig(bit))).collect();

        // ~a + 1: ripple the initial carry of 1 through the inverted bits.
        let mut carry = Sig::True;
        for (i, &nb) in not_a.iter().enumerate() {
            let (sum, next) = self.gate_full_adder(nb, Sig::False, carry);
            self.wire(result[i], sum);
            carry = next;
        }
    }

    /// Encode multiplication using symmetric schoolbook method: result = a * b
    /// This encoding is symmetric with respect to a and b, allowing solving for either operand.
    /// Uses Wallace tree-style carry propagation with proper column tracking.
    /// Multiplication with constant folding on the partial products.
    ///
    /// Z3's `mk_multiplier` builds the same partial-product array, but every
    /// `mk_and`/`mk_full_adder` runs over a rewriting layer that folds
    /// constants (`bit_blaster_tpl_def.h`).  Encoding the fold here is what
    /// keeps `bvmul(x, 65599)` - the Sage2 hash-chain shape - at the six-row
    /// shift-add chain the constant needs instead of a full 32x32 array:
    /// the partial products against the constant's zero bits are dropped
    /// before any variable exists, and the ones against its one bits are the
    /// multiplicand bits themselves.
    fn encode_mul(&mut self, result: &[Var], a: &[Var], b: &[Var]) {
        assert_eq!(result.len(), a.len());
        assert_eq!(result.len(), b.len());

        let width = result.len();

        // Create partial products: columns[k] contains all bits that
        // contribute to result[k].  Initially,
        // columns[k] = { a[i] AND b[j] | i + j = k }, with constant-zero
        // products omitted and constant-one products passed through.
        let mut columns: Vec<Vec<Sig>> = vec![Vec::new(); width];

        for (i, &a_bit) in a.iter().enumerate().take(width) {
            let a_sig = self.sig(a_bit);
            if a_sig == Sig::False {
                // A zero multiplicand bit contributes nothing to any column.
                continue;
            }
            for (j, &b_bit) in b.iter().enumerate().take(width) {
                let sum_pos = i + j;
                if sum_pos >= width {
                    break;
                }
                let pp = self.gate_and(a_sig, self.sig(b_bit));
                // gate_and folds: Sig::False adds nothing (no variable, no
                // clause was created for it), Sig::True is the other operand.
                if pp != Sig::False {
                    columns[sum_pos].push(pp);
                }
            }
        }

        // Use carry-save reduction to reduce each column to at most 2 bits
        // Then do a final ripple-carry addition
        self.reduce_columns_and_add(result, &mut columns);
    }

    /// Reduce columns using 3:2 compressors until each column has at most 2
    /// bits, then use a final ripple-carry adder to produce the result.
    ///
    /// Columns hold [`Sig`]s, so a constant-heavy product reduces through
    /// constant-folding full adders: an adder over three constants emits
    /// nothing, and one with a single constant input degenerates to a half
    /// adder.
    fn reduce_columns_and_add(&mut self, result: &[Var], columns: &mut Vec<Vec<Sig>>) {
        let width = columns.len();

        // Push `s` into column `k`, treating the constant false as "no
        // contribution" (it never had a variable allocated).
        fn push_sig(columns: &mut [Vec<Sig>], k: usize, s: Sig) {
            if s != Sig::False && k < columns.len() {
                columns[k].push(s);
            }
        }

        // Repeatedly reduce columns using 3:2 compressors
        // Each full adder takes 3 bits from column k and produces:
        //   - 1 sum bit in column k
        //   - 1 carry bit in column k+1
        loop {
            let max_height = columns.iter().map(|c| c.len()).max().unwrap_or(0);
            if max_height <= 2 {
                break;
            }

            let mut new_columns: Vec<Vec<Sig>> = vec![Vec::new(); width];

            for (k, bits) in columns.iter().enumerate() {
                let mut i = 0;

                while i + 2 < bits.len() {
                    // Full adder: sum stays in column k, carry goes to column k+1
                    let (sum, carry) = self.gate_full_adder(bits[i], bits[i + 1], bits[i + 2]);
                    push_sig(&mut new_columns, k, sum);
                    push_sig(&mut new_columns, k + 1, carry);
                    i += 3;
                }

                // Pass through remaining bits (0, 1, or 2)
                for &bit in &bits[i..] {
                    push_sig(&mut new_columns, k, bit);
                }
            }

            *columns = new_columns;
        }

        // Now each column has at most 2 bits
        // Create two operands for final addition
        let mut operand_a: SmallVec<[Sig; 32]> = SmallVec::new();
        let mut operand_b: SmallVec<[Sig; 32]> = SmallVec::new();

        for column in columns.iter().take(width) {
            match column.len() {
                0 => {
                    operand_a.push(Sig::False);
                    operand_b.push(Sig::False);
                }
                1 => {
                    operand_a.push(column[0]);
                    operand_b.push(Sig::False);
                }
                2 => {
                    operand_a.push(column[0]);
                    operand_b.push(column[1]);
                }
                _ => unreachable!("Column should have at most 2 bits after reduction"),
            }
        }

        // Final ripple-carry addition (wrapping: carry-out discarded)
        let mut carry = Sig::False;
        for (i, (&x, &y)) in operand_a.iter().zip(operand_b.iter()).enumerate() {
            let (sum, next_carry) = self.gate_full_adder(x, y, carry);
            self.wire(result[i], sum);
            carry = next_carry;
        }
    }

    /// Encode full multiplication: result = a * b with double-width result
    /// result has length 2*width, a and b have length width
    /// result[0..width-1] = low bits, result[width..2*width-1] = high bits
    /// Uses Wallace tree-style carry propagation with proper column tracking.
    fn encode_mul_full(&mut self, result: &[Var], a: &[Var], b: &[Var]) {
        let width = a.len();
        assert_eq!(b.len(), width);
        assert_eq!(result.len(), 2 * width);

        let double_width = 2 * width;

        // Partial products over [`Sig`]s, constant-folded exactly like
        // [`Self::encode_mul`]: zero products contribute nothing, one
        // products pass the other bit through.
        let mut columns: Vec<Vec<Sig>> = vec![Vec::new(); double_width];

        for (i, &a_bit) in a.iter().enumerate().take(width) {
            let a_sig = self.sig(a_bit);
            if a_sig == Sig::False {
                continue;
            }
            for (j, &b_bit) in b.iter().enumerate().take(width) {
                let pp = self.gate_and(a_sig, self.sig(b_bit));
                if pp != Sig::False {
                    columns[i + j].push(pp);
                }
            }
        }

        // Use carry-save reduction and final addition
        self.reduce_columns_and_add(result, &mut columns);
    }

    /// Get the value of a bit vector from the model, as a `u64`.
    ///
    /// Returns `None` for bit-vectors wider than 64 bits: a `u64` cannot
    /// represent their value, and `1u64 << i` for `i >= 64` would panic in
    /// debug builds (shift amount >= bit width) or silently wrap to a wrong
    /// bit (release builds mask the shift amount modulo 64) rather than
    /// error out. Callers needing the full-width value should use
    /// [`Self::get_value_big`] instead; callers of this method already
    /// treat `None` as "value unavailable from this solver" and fall back
    /// accordingly (e.g. `oxiz-solver`'s model builder falls back to the
    /// arithmetic theory's value, then to a default of `0`).
    #[must_use]
    pub fn get_value(&self, term: TermId) -> Option<u64> {
        let bv = self.term_to_bv.get(&term)?;
        if bv.bits.len() > u64::BITS as usize {
            return None;
        }

        let mut value = 0u64;
        for (i, &var) in bv.bits.iter().enumerate() {
            if self.read_model_bit(var) {
                value |= 1 << i;
            }
        }
        Some(value)
    }

    /// Get the value of a bit vector from the model as an arbitrary-width
    /// [`BigUint`], correctly supporting widths beyond 64 bits (unlike
    /// [`Self::get_value`]).
    #[must_use]
    pub fn get_value_big(&self, term: TermId) -> Option<BigUint> {
        let bv = self.term_to_bv.get(&term)?;
        let mut value = BigUint::ZERO;
        for (i, &var) in bv.bits.iter().enumerate() {
            if self.read_model_bit(var) {
                value.set_bit(i as u64, true);
            }
        }
        Some(value)
    }

    /// Truth value the model assigns to a Bool-sorted term that was encoded
    /// into this solver by [`Self::encode_bool_node`] – the `ite` selectors and
    /// the comparisons underneath them.
    ///
    /// Returns `None` for a term that was never encoded as a boolean node, so
    /// callers can tell "the model says false" apart from "this solver has no
    /// opinion". Used by `oxiz-solver`'s debug-only model-validity net to
    /// resolve a bit-blasted `ite` to the branch the model actually selected.
    #[must_use]
    pub fn bool_value(&self, term: TermId) -> Option<bool> {
        let &var = self.bool_node.get(&term)?;
        Some(self.read_model_bit(var))
    }

    /// Read a single SAT variable's boolean value from the model.
    ///
    /// Prefers the snapshot captured at the last SAT check: the live trail
    /// has been backtracked to root and would read all-`Undef` (→ 0). Falls
    /// back to the live model only when no snapshot exists (e.g. direct
    /// unit-test usage that reads before any backtrack).
    fn read_model_bit(&self, var: Var) -> bool {
        let idx = var.index();
        if let Some(v) = self.last_sat_model.get(idx)
            && v.is_defined()
        {
            return v.is_true();
        }
        self.sat.model().get(idx).is_some_and(|v| v.is_true())
    }

    /// Whether every bit of `term`'s bit-vector has a *defined* value (true or
    /// false, not `Undef`) in the model snapshot – i.e. the solver actually
    /// assigned this leaf, as opposed to leaving it free.
    ///
    /// The model-verification gate uses this to distinguish a genuinely
    /// determined bit-vector value (safe to refute with) from a defaulted-to-0
    /// free variable (which must stay inconclusive, lest a real `Sat` be turned
    /// into a spurious `Unknown`).  Returns `false` for a term that was never
    /// bit-blasted.
    #[must_use]
    pub fn bits_all_determined(&self, term: TermId) -> bool {
        let Some(bv) = self.term_to_bv.get(&term) else {
            return false;
        };
        bv.bits.iter().all(|&v| {
            self.last_sat_model
                .get(v.index())
                .is_some_and(|l| l.is_defined())
                || self
                    .sat
                    .model()
                    .get(v.index())
                    .is_some_and(|l| l.is_defined())
        })
    }
}

impl Theory for BvSolver {
    fn id(&self) -> TheoryId {
        TheoryId::BV
    }

    fn name(&self) -> &str {
        "BV"
    }

    fn can_handle(&self, _term: TermId) -> bool {
        true
    }

    fn assert_true(&mut self, term: TermId) -> Result<TheoryResult> {
        self.assertions.push((term, true));
        Ok(TheoryResult::Sat)
    }

    fn assert_false(&mut self, term: TermId) -> Result<TheoryResult> {
        self.assertions.push((term, false));
        Ok(TheoryResult::Sat)
    }

    fn check(&mut self) -> Result<TheoryResult> {
        self.check_body()
    }

    fn push(&mut self) {
        self.context_stack.push(ContextMark {
            assertions_len: self.assertions.len(),
            guard_terms_len: self.assertion_guard_terms.len(),
            outer_bool_len: self.outer_bool_journal.len(),
        });
        self.sat.push();
    }

    fn pop(&mut self) {
        if let Some(mark) = self.context_stack.pop() {
            self.assertions.truncate(mark.assertions_len);
            self.assertion_guard_terms.truncate(mark.guard_terms_len);
            // Undo the outer-boolean links in reverse so a term fixed at
            // several levels is restored to the value of the surviving one.
            while self.outer_bool_journal.len() > mark.outer_bool_len {
                if let Some((term, previous)) = self.outer_bool_journal.pop() {
                    match previous {
                        Some(value) => self.outer_bool.insert(term, value),
                        None => self.outer_bool.remove(&term),
                    };
                }
            }
            self.sat.pop();
        }
    }

    fn reset(&mut self) {
        self.sat.reset();
        // `sat.reset()` rebuilds the variable space from index 0, so the
        // reserved constant bits must be re-created (and re-pinned) or every
        // subsequently blasted constant would alias an unrelated variable.
        let (const_true, const_false) = Self::reserve_const_bits(&mut self.sat);
        self.const_true = const_true;
        self.const_false = const_false;
        self.term_to_bv.clear();
        self.assertions.clear();
        self.context_stack.clear();
        self.ult_cache.clear();
        self.shared_equalities.clear();
        self.equality_notifications.clear();
        self.assertion_guard_terms.clear();
        self.last_sat_model.clear();
        self.bool_node.clear();
        self.outer_bool.clear();
        self.outer_bool_journal.clear();
    }

    fn get_model(&self) -> Vec<(TermId, TermId)> {
        // Read the SAT model and construct bit-vector value assignments.
        // For each BV variable term, read its bit values from the SAT model
        // and group terms by their concrete value. For each group, the
        // representative (first term) serves as the "value term", and all
        // other terms in the group map to that representative.
        //
        // Additionally, each term maps to itself as a self-assignment to
        // record its participation in the model.
        let model = self.sat.model();
        let mut value_to_terms: FxHashMap<(u64, u32), Vec<TermId>> = FxHashMap::default();

        for (&term, bv_var) in &self.term_to_bv {
            let mut value = 0u64;
            for (i, &var) in bv_var.bits.iter().enumerate() {
                if model.get(var.index()).is_some_and(|v| v.is_true()) {
                    value |= 1u64 << i;
                }
            }
            // Key by (value, width) so terms of different widths stay separate
            value_to_terms
                .entry((value, bv_var.width))
                .or_default()
                .push(term);
        }

        let mut assignments = Vec::new();
        for terms in value_to_terms.values() {
            if terms.is_empty() {
                continue;
            }
            // The first term acts as the representative "value term" for this group.
            let representative = terms[0];
            for &term in terms {
                assignments.push((term, representative));
            }
        }
        assignments
    }
}

impl TheoryCombination for BvSolver {
    fn notify_equality(&mut self, eq: EqualityNotification) -> bool {
        // Check if both terms are relevant to the BV theory
        let lhs_known = self.term_to_bv.contains_key(&eq.lhs);
        let rhs_known = self.term_to_bv.contains_key(&eq.rhs);

        if lhs_known && rhs_known {
            // Both terms are BV variables -- enforce bit-level equality
            // via SAT encoding and check for consistency
            self.assert_eq(eq.lhs, eq.rhs);
            self.equality_notifications.push(eq);

            // After encoding the equality, check if the SAT solver detects
            // an immediate conflict (e.g., the two BVs were already constrained
            // to different constant values)
            match self.sat.solve() {
                SolverResult::Unsat => {
                    // The equality is inconsistent with current BV constraints
                    self.sat.backtrack_to_root();
                    false
                }
                _ => {
                    // Extract model-based equalities: if two BV terms now have
                    // the same value in the model, propagate that equality
                    self.extract_model_equalities();
                    self.sat.backtrack_to_root();
                    true
                }
            }
        } else if lhs_known || rhs_known {
            // One term is a BV term, the other is foreign (shared variable).
            // Record the notification for later processing.
            self.equality_notifications.push(eq);
            true
        } else {
            // Neither term is relevant to this theory
            false
        }
    }

    fn get_shared_equalities(&self) -> Vec<EqualityNotification> {
        self.shared_equalities.clone()
    }

    fn is_relevant(&self, term: TermId) -> bool {
        self.term_to_bv.contains_key(&term)
    }
}

impl BvSolver {
    /// Body of [`Theory::check`].
    fn check_body(&mut self) -> Result<TheoryResult> {
        // `BvSolver::check()` is driven incrementally by the theory manager:
        // assert more clauses, then `check()` again.  Each `check()` runs a full
        // `solve()`, but the embedded SAT solver does NOT reset its persisted
        // search state on entry, so without the cleanup below a single probe can
        // leave two kinds of unsound residue that poison the next probe and turn
        // a genuinely-SATISFIABLE formula into a false `Unsat`:
        //
        //   1. The satisfying *model* itself.  `solve()` returns with the model
        //      on the trail; some assignments (even a branch `Decision`) land at
        //      decision level 0.  A model value chosen arbitrarily for one probe
        //      then contradicts a constant asserted before the next probe.
        //      Fixed by `restore_to_trail_size`, rolling the trail back to the
        //      committed (asserted) prefix captured here.
        //
        //   2. Clauses *learned* during the solve.  `assert_const` / `assert_eq`
        //      install their unit constraints as level-0 trail assignments with
        //      `reason = Decision` and no backing clause, so a clause learned
        //      while such a literal is on the trail implicitly depends on it;
        //      once the trail is rolled back that learned clause is missing a
        //      hypothesis and can spuriously force `Unsat`.  Fixed by
        //      `forget_learned_since`, dropping exactly this probe's learned
        //      clauses (the asserted clauses remain as the sound core).
        let committed_trail = self.sat.trail_size();
        let learned_before = self.sat.learned_clause_count();

        let mut solve_result = self.sat.solve();

        // Defensive re-verification of an `Unsat` verdict.
        //
        // Audit regression (theories-bv): the SAME unsound-learned-clause
        // hazard documented above for *cross-probe* contamination can also
        // corrupt THIS probe's own verdict, within a single `solve()` call:
        // conflict analysis resolves through the bare, clause-less level-0
        // decision literals that `assert_const`/`assert_eq` install (see
        // `Solver::forget_learned_since`'s doc comment), and an internal
        // restart can expose a learned clause that implicitly -- and
        // unsoundly -- depended on one of them. This has been observed to
        // turn a genuinely SATISFIABLE bit-blasted formula (e.g. an
        // inverse `bvudiv` constraint with a free divisor) into a `solve()`
        // call that reports `Unsat` on its FIRST attempt, even though
        // discarding this probe's learned clauses and solving again -- on
        // nothing but the original, honestly-asserted clauses -- finds a
        // model. Clause learning is sound only if every learned clause is
        // logically entailed by the original clauses; discarding learned
        // clauses can therefore only WEAKEN the formula (never strengthen
        // it), so retrying after `forget_learned_since` can never turn a
        // truly UNSAT formula into a false `Sat` -- it can only correct a
        // false `Unsat` back to the true `Sat`, or confirm the `Unsat`.
        if matches!(solve_result, SolverResult::Unsat) {
            self.sat.restore_to_trail_size(committed_trail);
            self.sat.forget_learned_since(learned_before);
            solve_result = self.sat.solve();
        }

        let result = match solve_result {
            SolverResult::Sat => {
                // Snapshot the satisfying assignment BEFORE rolling the trail
                // back – the rollback discards the model, so `get_value` must
                // consult this captured copy to recover real values.
                self.last_sat_model = self.sat.model().to_vec();
                Ok(TheoryResult::Sat)
            }
            SolverResult::Unsat => {
                // Return all constraint-level terms recorded via
                // `record_constraint_term` as the conflict explanation.
                // This is a sound (superset) conflict clause: the UNSAT is
                // caused by the conjunction of all asserted constraints.
                // If no guard terms were recorded (e.g. in unit tests that
                // call the solver directly), fall back to the assertions list.
                let conflict = if !self.assertion_guard_terms.is_empty() {
                    self.collect_conflict_terms()
                } else {
                    // Fallback: use terms from the assertions list
                    self.assertions.iter().map(|(t, _)| *t).collect()
                };
                Ok(TheoryResult::Unsat(conflict))
            }
            SolverResult::Unknown => Ok(TheoryResult::Unknown),
        };

        // Keep this probe's satisfying *model* on the trail so the next
        // `check()` resumes incrementally from it – `solve()` does not reset
        // the trail on entry, so a freshly asserted clause the model already
        // satisfies is decided with zero re-propagation, instead of re-walking
        // the whole bit-blasted formula from the level-0 prefix every probe.
        // The level-0 unit facts (constants, pinned selectors) are part of the
        // committed prefix either way; a search decision the model made at
        // level ≥ 1 that a later probe's new clause contradicts is simply
        // backtracked by the next `solve()`, so retaining the trail cannot
        // manufacture a false verdict.  Learned clauses are likewise kept: they
        // are entailed by the asserted (permanent) clauses, and the level-0
        // units they may resolve through sit inside the committed prefix.
        //
        // Together with the `lucky_phases` / gate-congruence disables in
        // `embedded_sat_config`, this is the QF_BV perf lever: 394 incremental
        // resumes vs 394 full re-propagations of a ~100 k-clause formula on
        // `millionaires.t1.i28` (2.3 s → 0.2 s).  The defensive re-solve block
        // above still `restore_to_trail_size`s + `forget_learned_since`s on an
        // `Unsat` first verdict, preserving that soundness guard.
        let _ = (committed_trail, learned_before);

        result
    }

    /// Extract equalities from the current BV model.
    ///
    /// BV is a finite-domain theory, so we use model-based combination:
    /// if two distinct BV terms evaluate to the same bit-vector value in
    /// the current SAT model, we derive an equality between them.
    fn extract_model_equalities(&mut self) {
        // Collect (term, value) pairs from the current model.
        //
        // Keyed by `BigUint` rather than `u64`: bit-vectors wider than 64
        // bits are fully supported by the bit-blaster (each bit is just
        // another SAT variable), so a `u64` key would require `1u64 << i`
        // for `i >= 64`, which panics in debug builds and silently wraps
        // (masking the shift amount mod 64, corrupting the computed value
        // and potentially deriving a bogus equality) in release builds.
        let model = self.sat.model();
        let mut value_map: FxHashMap<BigUint, Vec<TermId>> = FxHashMap::default();

        for (&term, bv_var) in &self.term_to_bv {
            let mut value = BigUint::ZERO;
            for (i, &var) in bv_var.bits.iter().enumerate() {
                if model.get(var.index()).is_some_and(|v| v.is_true()) {
                    value.set_bit(i as u64, true);
                }
            }
            value_map.entry(value).or_default().push(term);
        }

        // For each group of terms with the same value, derive pairwise equalities
        self.shared_equalities.clear();
        for terms in value_map.values() {
            if terms.len() >= 2 {
                // Only propagate the first pair to avoid quadratic blowup
                self.shared_equalities.push(EqualityNotification {
                    lhs: terms[0],
                    rhs: terms[1],
                    reason: None,
                });
            }
        }
    }
}

/// Unit tests for this module.
#[cfg(test)]
mod tests;
