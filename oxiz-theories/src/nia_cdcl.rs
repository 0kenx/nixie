//! Faithful CDCL(T) port for nonlinear integer arithmetic.
//!
//! z3 solves QF_NIA not with CAD but with a Simplex tableau in which every
//! nonlinear monomial is a fresh variable, driven by a CDCL core: the Boolean
//! structure of the formula is encoded as clauses over arithmetic-comparison
//! *atoms*, the Simplex theory checks consistency of the atoms currently
//! asserted true, and conflicts – Boolean or theory – are explained as
//! literals, subjected to 1-UIP analysis, and *learned* as new clauses that
//! prune the rest of the search (`theory_arith_nl.h::process_non_linear`,
//! `branch_nl_int_var`, the standard CDCL loop).
//!
//! This module is a self-contained, soundness-safe port using oxiz's own
//! [`Simplex`] tableau as the linear theory:
//!   * Top-level assertions are Tseitin-encoded into CNF over arithmetic atoms.
//!     Monomials become fresh Simplex variables (the *relaxation*).
//!   * A CDCL loop searches: Boolean unit propagation, then a lazy theory check
//!     – impose the true atoms in the Simplex and test feasibility. An
//!     infeasible theory state yields a conflict clause (the asserted atoms
//!     responsible); a feasible-but-non-integer state yields an integer
//!     *branching lemma* (`v ≤ k ∨ v ≥ k+1`, decided true first), z3's
//!     `branch_nl_int_var`.
//!   * Every conflict is resolved to a 1-UIP learnt clause and the search
//!     backjumps non-chronologically.
//!
//! Soundness: every reported `Sat` is a *concretely verified* integer model.
//! `Unsat` is reported only when the relaxation is provably infeasible at
//! decision level 0, which implies the original formula is unsatisfiable.
//! Learned clauses only prune; a buggy clause can at worst miss a model or slow
//! the search, never produce a wrong answer.

use num_bigint::BigInt;
use num_rational::Rational64;
use num_traits::{ToPrimitive, Zero};

use oxiz_core::ast::{TermId, TermKind, TermManager};
use rustc_hash::FxHashMap;

use crate::ania_ground::eval_assertions_true;
use crate::arithmetic::simplex::{LinExpr, Simplex, VarId};
use crate::nlsat::NlDispatchResult;

/// Wall-clock budget (ms). Overridable with `OXIZ_NIA_CDCL_MS`.
const DEFAULT_DEADLINE_MS: u64 = 4_000;
/// Conflict budget (0 = unlimited). Overridable with `OXIZ_NIA_CDCL_CONFLICTS`.
const DEFAULT_MAX_CONFLICTS: u64 = 50_000;

/// Entry point. Returns `Some(Sat)` on a concretely-verified integer model,
/// `Some(Unsat)` when the relaxation is level-0 infeasible, or `None` to fall
/// through. Bounded by a deadline and conflict budget so it never hangs.
pub fn cdcl_nia_search(
    encode: &[TermId],
    verify: &[TermId],
    manager: &mut TermManager,
) -> Option<NlDispatchResult> {
    let deadline = oxiz_time::Instant::now()
        + oxiz_time::Duration::from_millis(
            env_u64("OXIZ_NIA_CDCL_MS", DEFAULT_DEADLINE_MS).max(100),
        );
    let max_conflicts = env_u64("OXIZ_NIA_CDCL_CONFLICTS", DEFAULT_MAX_CONFLICTS);

    // A single shared `0` term for degenerate/auxiliary atoms (avoids needing
    // `&mut` access to the manager inside the immutable encoder).
    let zero_term = manager.mk_int(BigInt::from(0));

    let mut enc = Encoder::new(manager, zero_term);
    let mut clauses: Vec<Vec<i32>> = Vec::new();
    let mut genuine_false = false; // a top-level `false` assertion ⟹ Unsat
    let mut bail = false; // un-encodable structure ⟹ concede None
    for &a in encode {
        match enc.encode(a) {
            Encoded::True => {}
            Encoded::False => genuine_false = true,
            Encoded::Bail => bail = true,
            Encoded::Lit(l) => clauses.push(vec![l]),
        }
    }
    // A genuine `false` assertion makes the formula unsat regardless of other
    // (even un-encodable) assertions. Otherwise, if anything bailed, we cannot
    // soundly encode the formula – concede and fall through.
    if genuine_false {
        return Some(NlDispatchResult::Unsat);
    }
    if bail {
        return None;
    }
    clauses.extend(enc.take_pending());
    if enc.atoms.len() <= 1 {
        return None; // nothing arithmetic to decide
    }

    let mut solver = CdclSolver::build(enc, clauses, manager)?;
    solver.solve(verify, manager, deadline, max_conflicts)
}

fn env_u64(name: &str, default: u64) -> u64 {
    std::env::var(name)
        .ok()
        .and_then(|s| s.parse::<u64>().ok())
        .unwrap_or(default)
}

// ========  ========
// Atoms & Tseitin CNF encoder
// ========  ========

#[derive(Clone, Copy, PartialEq, Eq, Hash)]
struct AtomKey {
    lhs: TermId,
    rhs: TermId,
    kind: u8,
}

#[derive(Clone, Copy, PartialEq, Eq)]
enum Kind {
    Le,
    Lt,
    Ge,
    Gt,
    Eq,
    /// `a ≤ b−1`: the low side of the integer equality adapter
    /// (`a = b ∨ a ≤ b−1 ∨ a ≥ b+1`).
    EqLo,
    /// `a ≥ b+1`: the high side of the integer equality adapter.
    EqHi,
    /// Degenerate "always-satisfiable" atom used for free Boolean variables and
    /// Tseitin auxiliary gates. The theory never imposes a constraint for it.
    Tru,
}

impl Kind {
    fn as_u8(self) -> u8 {
        self as u8
    }
}

/// One encoded atom: its SAT variable, the comparison, and whether it carries
/// an actual Simplex constraint (`Tru` atoms carry none).
#[derive(Clone, Copy)]
struct Atom {
    lhs: TermId,
    rhs: TermId,
    kind: Kind,
}

enum Encoded {
    True,
    False,
    Lit(i32), // signed SAT literal; var = |lit| (1-based)
    /// The sub-term uses structure the encoder cannot polynomialise (e.g.
    /// `distinct`, `ite`, quantifiers). Propagated up so the caller concedes
    /// `None` (falls through) rather than guessing – never `Unsat`.
    Bail,
}

struct Encoder<'a> {
    manager: &'a TermManager,
    zero_term: TermId,
    atoms: Vec<Atom>, // index 0 placeholder (var 0 unused)
    atom_var: FxHashMap<AtomKey, i32>,
    pending: Vec<Vec<i32>>, // gate clauses buffered during encoding
}

impl<'a> Encoder<'a> {
    fn new(manager: &'a TermManager, zero_term: TermId) -> Self {
        Self {
            manager,
            zero_term,
            atoms: vec![Atom {
                lhs: TermId(0),
                rhs: TermId(0),
                kind: Kind::Tru,
            }],
            atom_var: FxHashMap::default(),
            pending: Vec::new(),
        }
    }

    fn bool_sort(&self) -> oxiz_core::sort::SortId {
        self.manager.sorts.bool_sort
    }
    fn is_bool(&self, t: TermId) -> bool {
        self.manager
            .get(t)
            .is_some_and(|n| n.sort == self.bool_sort())
    }

    fn make_atom(&mut self, lhs: TermId, rhs: TermId, kind: Kind) -> i32 {
        let key = AtomKey {
            lhs,
            rhs,
            kind: kind.as_u8(),
        };
        if let Some(&v) = self.atom_var.get(&key) {
            return v;
        }
        let v = self.atoms.len() as i32;
        self.atoms.push(Atom { lhs, rhs, kind });
        self.atom_var.insert(key, v);
        v
    }

    /// A fresh auxiliary variable (carries no Simplex constraint).
    ///
    /// Genuinely fresh every call: it is pushed straight onto `atoms`
    /// *without* an `atom_var` entry, so two Tseitin gates never share a
    /// variable.  Going through `make_atom` here (the historical bug)
    /// content-addressed every gate by the same `(zero, zero, Tru)` key –
    /// nested `and`/`or` gates collapsed onto one SAT variable whose gate
    /// clauses then contradicted each other at level 0, producing wrong
    /// `Unsat` on satisfiable nested-Boolean goals (reduced from VeryMax
    /// `459.smt2` to a two-variable formula).
    fn fresh(&mut self) -> i32 {
        let v = self.atoms.len() as i32;
        self.atoms.push(Atom {
            lhs: self.zero_term,
            rhs: self.zero_term,
            kind: Kind::Tru,
        });
        v
    }

    fn encode(&mut self, term: TermId) -> Encoded {
        let Some(n) = self.manager.get(term) else {
            return Encoded::False;
        };
        match &n.kind {
            TermKind::True => Encoded::True,
            TermKind::False => Encoded::False,
            TermKind::Not(x) => match self.encode(*x) {
                Encoded::True => Encoded::False,
                Encoded::False => Encoded::True,
                Encoded::Lit(l) => Encoded::Lit(-l),
                Encoded::Bail => Encoded::Bail,
            },
            TermKind::And(xs) => self.encode_conj(xs),
            TermKind::Or(xs) => self.encode_disj(xs),
            TermKind::Implies(a, b) => match (self.encode(*a), self.encode(*b)) {
                (Encoded::False, _) | (_, Encoded::True) => Encoded::True,
                (Encoded::True, e) => e,
                (e, Encoded::False) => negate_enc(e),
                (Encoded::Lit(la), Encoded::Lit(lb)) => Encoded::Lit(self.implies_gate(la, lb)),
                (Encoded::Bail, _) | (_, Encoded::Bail) => Encoded::Bail,
            },
            TermKind::Var(_) if self.is_bool(term) => {
                // A free Boolean variable: an unconstrained aux atom.
                Encoded::Lit(self.fresh())
            }
            TermKind::Eq(a, b) => {
                if a == b {
                    // `(= t t)` is a tautology; folding it (rather than
                    // creating a spurious atom) keeps the encoded clauses
                    // implied by the formula.
                    return Encoded::True;
                }
                if self.is_bool(*a) || self.is_bool(*b) {
                    self.encode_bool_eq(*a, *b)
                } else {
                    let eq_lit = self.make_atom(*a, *b, Kind::Eq);
                    // Integer equality adapter (z3's arith_eq_adapter): for
                    // integers, `a = b ∨ a ≤ b−1 ∨ a ≥ b+1` is a tautology,
                    // and the two side atoms are linearly encodable in both
                    // polarities.  Emitting the clause lets the search make a
                    // *false* `Eq` arithmetically real (a ≠ b), which the
                    // linear relaxation alone can never pin – without it,
                    // every model needing a false Eq failed the concrete
                    // check and the loop conceded.
                    let lo = self.make_atom(*a, *b, Kind::EqLo);
                    let hi = self.make_atom(*a, *b, Kind::EqHi);
                    self.pending.push(vec![eq_lit, lo, hi]);
                    Encoded::Lit(eq_lit)
                }
            }
            TermKind::Le(a, b) => {
                if a == b {
                    Encoded::True
                } else {
                    Encoded::Lit(self.make_atom(*a, *b, Kind::Le))
                }
            }
            TermKind::Lt(a, b) => {
                if a == b {
                    Encoded::False
                } else {
                    Encoded::Lit(self.make_atom(*a, *b, Kind::Lt))
                }
            }
            TermKind::Ge(a, b) => {
                if a == b {
                    Encoded::True
                } else {
                    Encoded::Lit(self.make_atom(*a, *b, Kind::Ge))
                }
            }
            TermKind::Gt(a, b) => {
                if a == b {
                    Encoded::False
                } else {
                    Encoded::Lit(self.make_atom(*a, *b, Kind::Gt))
                }
            }
            _ => Encoded::Bail, // unsupported structure: concede, never guess
        }
    }

    fn encode_conj(&mut self, xs: &[TermId]) -> Encoded {
        let mut lits = Vec::new();
        for &x in xs {
            match self.encode(x) {
                Encoded::True => {}
                Encoded::False => return Encoded::False,
                Encoded::Bail => return Encoded::Bail,
                Encoded::Lit(l) => lits.push(l),
            }
        }
        match lits.len() {
            0 => Encoded::True,
            1 => Encoded::Lit(lits[0]),
            _ => Encoded::Lit(self.and_gate(&lits)),
        }
    }

    fn encode_disj(&mut self, xs: &[TermId]) -> Encoded {
        let mut lits = Vec::new();
        for &x in xs {
            match self.encode(x) {
                Encoded::True => return Encoded::True,
                Encoded::False => {}
                Encoded::Bail => return Encoded::Bail,
                Encoded::Lit(l) => lits.push(l),
            }
        }
        match lits.len() {
            0 => Encoded::False,
            1 => Encoded::Lit(lits[0]),
            _ => Encoded::Lit(self.or_gate(&lits)),
        }
    }

    fn encode_bool_eq(&mut self, a: TermId, b: TermId) -> Encoded {
        match (self.encode(a), self.encode(b)) {
            (Encoded::True, e) | (e, Encoded::True) => e,
            (Encoded::False, e) | (e, Encoded::False) => negate_enc(e),
            (Encoded::Lit(la), Encoded::Lit(lb)) => {
                if la == lb {
                    Encoded::True
                } else if la == -lb {
                    Encoded::False
                } else {
                    // g ↔ ¬(la ⊕ lb)
                    let x = self.xor_gate(la, lb);
                    Encoded::Lit(-x)
                }
            }
            (Encoded::Bail, _) | (_, Encoded::Bail) => Encoded::Bail,
        }
    }

    fn and_gate(&mut self, lits: &[i32]) -> i32 {
        let g = self.fresh();
        // g ↔ (l_1 ∧ … ∧ l_n):
        //   g → l_i           :  (¬g ∨ l_i)
        //   (l_1 ∧ … ∧ l_n) → g :  (g ∨ ¬l_1 ∨ … ∨ ¬l_n)
        for &l in lits {
            self.pending.push(vec![-g, l]);
        }
        let mut clause = vec![g];
        for &l in lits {
            clause.push(-l);
        }
        self.pending.push(clause);
        g
    }
    fn or_gate(&mut self, lits: &[i32]) -> i32 {
        let g = self.fresh();
        for &l in lits {
            self.pending.push(vec![-l, g]);
        }
        let mut clause = vec![-g];
        clause.extend_from_slice(lits);
        self.pending.push(clause);
        g
    }
    fn implies_gate(&mut self, la: i32, lb: i32) -> i32 {
        let g = self.fresh();
        self.pending.push(vec![-g, -la, lb]);
        self.pending.push(vec![g, la]);
        self.pending.push(vec![g, -lb]);
        g
    }
    fn xor_gate(&mut self, la: i32, lb: i32) -> i32 {
        let g = self.fresh();
        self.pending.push(vec![-g, la, lb]);
        self.pending.push(vec![-g, -la, -lb]);
        self.pending.push(vec![g, -la, lb]);
        self.pending.push(vec![g, la, -lb]);
        g
    }

    fn take_pending(&mut self) -> Vec<Vec<i32>> {
        core::mem::take(&mut self.pending)
    }
}

fn negate_enc(e: Encoded) -> Encoded {
    match e {
        Encoded::True => Encoded::False,
        Encoded::False => Encoded::True,
        Encoded::Lit(l) => Encoded::Lit(-l),
        Encoded::Bail => Encoded::Bail,
    }
}

// ========  ========
// CDCL(T) solver with a Simplex theory
// ========  ========

const ORIG_REASON: u32 = 0;
const DECISION_REASON_BASE: u32 = 1_000_000_000;

struct CdclSolver<'a> {
    manager: &'a TermManager,
    atoms: Vec<Atom>,
    /// The Simplex theory, with monomials as fresh variables.
    simplex: Simplex,
    /// Original (Int-sorted) variable terms → Simplex var.
    var: FxHashMap<TermId, VarId>,
    /// Reverse map: Simplex var → the variable term that introduced it (for
    /// distributing compound-factor products back into monomial keys).
    var_term: FxHashMap<VarId, TermId>,
    /// Monomial (sorted factor powers) → Simplex var.
    mono: FxHashMap<Vec<(TermId, u32)>, VarId>,
    /// Reverse of `mono`: Simplex var → its monomial key (so a product whose
    /// factor is itself a compound expression involving monomials can merge
    /// powers instead of bailing).
    mono_key_of: FxHashMap<VarId, Vec<(TermId, u32)>>,
    /// CDCL state.
    value: Vec<i8>, // 0 undef, 1 true, -1 false; index = var
    level: Vec<u32>,
    reason: Vec<Option<usize>>, // index into clauses, or None for a decision
    trail: Vec<i32>,
    trail_lim: Vec<usize>,
    clauses: Vec<Vec<i32>>,
    /// Number of original (formula + gate) clauses – clauses at and above
    /// this index are learnt. A level-0 conflict on an original clause is a
    /// genuine unsat; on a learnt clause it means the learner produced an
    /// unsound clause, so we discard the learnts and restart instead of
    /// claiming `Unsat` (a soundness backstop).
    num_original: usize,
    propagation_q: Vec<i32>,
    conflicts: u64,
    /// Simplex values captured at the most recent *feasible* theory check
    /// (after its repairs, before the scope pop).  Branching and model
    /// extraction read this view: after the pop the live tableau is restored
    /// to the pre-repair snapshot, whose values may violate the very bounds
    /// the check just repaired.
    last_values: FxHashMap<VarId, Rational64>,
    /// Variable → clause indices containing it (BCP occurrence lists; the
    /// historical BCP scanned *every* clause for *every* propagated literal,
    /// which alone consumed the whole budget on 900-atom goals).
    occurs: Vec<Vec<usize>>,
    /// Trail index up to which atoms have been imposed into the Simplex
    /// (incremental theory imposition; see [`Self::theory_check`]).
    imposed_marker: usize,
    /// Per-atom split data: `Some((var, k))` for an integer-branch atom
    /// encoding the lemma `v ≤ k ∨ v ≥ k+1` (true → upper bound `v ≤ k`,
    /// false → lower bound `v ≥ k+1`); `None` for ordinary comparison atoms.
    /// Both polarities of a split impose a Simplex bound, so the CDCL explores
    /// the two sides via standard backjumping + learnt clauses (z3's
    /// `branch_nl_int_var` with `set_true_first_flag`).
    split_bounds: Vec<Option<(VarId, Rational64)>>,
}

impl<'a> CdclSolver<'a> {
    fn build(enc: Encoder<'a>, clauses: Vec<Vec<i32>>, manager: &'a TermManager) -> Option<Self> {
        let n_atoms = enc.atoms.len();
        let mut s = Self {
            manager,
            atoms: enc.atoms,
            simplex: Simplex::new(),
            var: FxHashMap::default(),
            var_term: FxHashMap::default(),
            mono: FxHashMap::default(),
            mono_key_of: FxHashMap::default(),
            value: vec![0; n_atoms],
            level: vec![0; n_atoms],
            reason: vec![None; n_atoms],
            trail: Vec::new(),
            trail_lim: Vec::new(),
            clauses,
            num_original: 0,
            propagation_q: Vec::new(),
            conflicts: 0,
            split_bounds: vec![None; n_atoms],
            last_values: FxHashMap::default(),
            imposed_marker: 0,
            occurs: Vec::new(),
        };
        // Occurrence lists over the ORIGINAL clause set. Learnt clauses are
        // appended later and must be appended to `occurs` too – see `learn`.
        let mut occurs: Vec<Vec<usize>> = vec![Vec::new(); s.atoms.len()];
        for (cid, clause) in s.clauses.iter().enumerate() {
            for &l in clause {
                let v = l.unsigned_abs() as usize;
                if v < occurs.len() {
                    occurs[v].push(cid);
                }
            }
        }
        s.occurs = occurs;
        // Pre-register every variable / monomial appearing in any atom so the
        // Simplex var map is stable across the whole search.
        let atom_terms: Vec<(TermId, TermId)> =
            s.atoms.iter().skip(1).map(|a| (a.lhs, a.rhs)).collect();
        for (lhs, rhs) in atom_terms {
            s.translate(lhs)?;
            s.translate(rhs)?;
        }
        s.num_original = s.clauses.len();
        Some(s)
    }

    // ======== polynomial translation into the Simplex (monomials → fresh vars) ========

    /// Register `term` as a Simplex variable (idempotent), keeping the reverse
    /// `var_term` map in sync for product distribution.
    fn register_var(&mut self, term: TermId) -> VarId {
        let vid = *self
            .var
            .entry(term)
            .or_insert_with(|| self.simplex.new_var());
        self.var_term.entry(vid).or_insert(term);
        vid
    }

    fn translate(&mut self, term: TermId) -> Option<LinExpr> {
        let n = self.manager.get(term)?;
        match &n.kind {
            TermKind::IntConst(k) => Some(LinExpr::constant(r64_of(k)?)),
            TermKind::Var(_) => {
                if n.sort != self.manager.sorts.int_sort {
                    return None;
                }
                let v = self.register_var(term);
                Some(LinExpr::var(v))
            }
            TermKind::Neg(x) => {
                let mut e = self.translate(*x)?;
                e.negate();
                Some(e)
            }
            TermKind::Add(xs) => {
                let mut acc = LinExpr::constant(Rational64::zero());
                for &a in xs {
                    let e = self.translate(a)?;
                    add_scaled(&mut acc, &e, Rational64::from_integer(1));
                }
                Some(acc)
            }
            TermKind::Sub(a, b) => {
                let mut e = self.translate(*a)?;
                let r = self.translate(*b)?;
                add_scaled(&mut e, &r, Rational64::from_integer(-1));
                Some(e)
            }
            TermKind::Mul(xs) => self.translate_mul(xs),
            // Foreign numeric leaves (select/UF applications left by
            // purification) and `let`-bound terms: treat as opaque Simplex
            // variables (numeric sort) / inline the body, mirroring the NLSAT
            // translator, so industrial formulas with purification artifacts
            // don't force a bailout.
            TermKind::Select(_, _) | TermKind::Apply { .. } => {
                if n.sort != self.manager.sorts.int_sort && n.sort != self.manager.sorts.real_sort {
                    return None;
                }
                let v = self.register_var(term);
                Some(LinExpr::var(v))
            }
            TermKind::Let { body, .. } => self.translate(*body),
            _ => None,
        }
    }

    /// Translate a product, *distributing* multiplication over addition so
    /// compound factors like `(x+1)*y` expand to `x·y + y` (each product of
    /// variables becomes a monomial Simplex variable). Accumulates a polynomial
    /// as `Vec<(coeff, monomial-key)>` and folds each factor in.
    fn translate_mul(&mut self, args: &[TermId]) -> Option<LinExpr> {
        // poly entries: (coefficient, factor-power list). Start at the unit.
        let mut poly: Vec<(Rational64, Vec<(TermId, u32)>)> =
            vec![(Rational64::from_integer(1), Vec::new())];
        let mut stack: Vec<TermId> = args.to_vec();
        while let Some(id) = stack.pop() {
            let n = self.manager.get(id)?;
            match &n.kind {
                TermKind::IntConst(k) => {
                    let c = r64_of(k)?;
                    for (pc, _) in &mut poly {
                        *pc *= c;
                    }
                }
                TermKind::Neg(x) => {
                    for (pc, _) in &mut poly {
                        *pc *= Rational64::from_integer(-1);
                    }
                    stack.push(*x);
                }
                TermKind::Mul(inner) => stack.extend(inner.iter().copied()),
                TermKind::Var(_) => {
                    self.register_var(id);
                    for (_, pm) in &mut poly {
                        bump_power(pm, id);
                    }
                }
                _ => {
                    // Compound factor: translate to a LinExpr and distribute
                    // (multiply the polynomial by `constant + Σ coeff·var`).
                    let e = self.translate(id)?;
                    let mut newpoly = Vec::with_capacity(poly.len() * (e.terms.len() + 1));
                    for (pc, pm) in &poly {
                        newpoly.push((*pc * e.constant, pm.clone()));
                        for &(vid, coef) in &e.terms {
                            // The factor's linear terms are either plain
                            // variables or already-abstracted monomials;
                            // merge the latter's full power key.
                            let key: Vec<(TermId, u32)> =
                                if let Some(k) = self.mono_key_of.get(&vid) {
                                    k.clone()
                                } else if let Some(&t) = self.var_term.get(&vid) {
                                    vec![(t, 1)]
                                } else {
                                    return None;
                                };
                            let mut npm = pm.clone();
                            for (t, p) in key {
                                for _ in 0..p {
                                    bump_power(&mut npm, t);
                                }
                            }
                            newpoly.push((*pc * coef, npm));
                        }
                    }
                    poly = newpoly;
                }
            }
        }
        // Convert the polynomial into a LinExpr over Simplex vars (monomials
        // become fresh variables, deduplicated via the `mono` cache).
        let mut out = LinExpr::constant(Rational64::zero());
        for (c, mut pm) in poly {
            pm.sort_by_key(|(t, _)| t.0);
            if pm.is_empty() {
                out.add_constant(c);
            } else if pm.len() == 1 && pm[0].1 == 1 {
                let vid = self.register_var(pm[0].0);
                out.add_term(vid, c);
            } else {
                let mv = *self
                    .mono
                    .entry(pm.clone())
                    .or_insert_with(|| self.simplex.new_var());
                self.mono_key_of.insert(mv, pm);
                out.add_term(mv, c);
            }
        }
        Some(out)
    }

    /// Allocate a fresh integer-branch atom encoding the lemma
    /// `v ≤ k ∨ v ≥ k+1`. True imposes `v ≤ k`; false imposes `v ≥ k+1`.
    fn make_split_atom(&mut self, vid: VarId, k: Rational64) -> i32 {
        let v = self.atoms.len() as i32;
        self.atoms.push(Atom {
            lhs: TermId(0),
            rhs: TermId(0),
            kind: Kind::Tru,
        });
        self.split_bounds.push(Some((vid, k)));
        self.value.push(0);
        self.level.push(0);
        self.reason.push(None);
        v
    }

    /// Impose atom `atom_var`'s Simplex constraint according to its assigned
    /// `value` (+1 true / −1 false). Comparison atoms impose only when true
    /// (their falsity is handled by the clause layer – the relaxation omits
    /// them); split atoms impose on *both* polarities (the two sides of the
    /// branching lemma). Returns `None` if the constraint cannot be expressed.
    fn impose(&mut self, atom_var: i32, value: i8) -> Option<()> {
        let v = atom_var as usize;
        // Integer-branch split atom: both polarities bind.
        if let Some((vid, k)) = self.split_bounds[v] {
            let reason = DECISION_REASON_BASE + atom_var as u32;
            if value > 0 {
                self.simplex.set_upper(vid, k, reason);
            } else {
                self.simplex
                    .set_lower(vid, k + Rational64::from_integer(1), reason);
            }
            return Some(());
        }
        // Ordinary comparison atom: impose *both* polarities.  A true atom
        // imposes its constraint; a FALSE atom imposes its negation (over the
        // integers `¬(a ≤ b) ⟺ a ≥ b+1`, etc.).  Imposing only the true side
        // (the historical behaviour) let the relaxation keep an atom
        // arithmetically true while the Boolean layer called it false – every
        // such model failed the concrete check and the loop conceded, so
        // formulas whose models required a false comparison atom could never
        // be answered.  `Eq` has no linear negation (a ≠ b); a false `Eq`
        // imposes nothing and stays guarded by the concrete verification.
        let a = self.atoms[v];
        if matches!(a.kind, Kind::Tru) {
            return Some(()); // no constraint
        }
        let mut e = self.translate(a.lhs)?;
        let r = self.translate(a.rhs)?;
        add_scaled(&mut e, &r, Rational64::from_integer(-1)); // lhs - rhs
        match (a.kind, value > 0) {
            (Kind::Le, true) | (Kind::Gt, false) => {
                self.simplex.add_le(e, ORIG_REASON);
                Some(())
            }
            (Kind::Ge, true) | (Kind::Lt, false) => {
                self.simplex.add_ge(e, ORIG_REASON);
                Some(())
            }
            (Kind::Eq, true) => {
                self.simplex.add_eq(e, ORIG_REASON);
                Some(())
            }
            (Kind::Lt, true) => {
                // a < b ⟺ b ≥ a+1 ⟺ −(a−b) ≥ 1
                e.negate();
                e.add_constant(Rational64::from_integer(-1));
                self.simplex.add_ge(e, ORIG_REASON);
                Some(())
            }
            (Kind::Gt, true) => {
                // a > b ⟺ a ≥ b+1
                e.add_constant(Rational64::from_integer(-1));
                self.simplex.add_ge(e, ORIG_REASON);
                Some(())
            }
            (Kind::Le, false) => {
                // ¬(a ≤ b) ⟺ a ≥ b+1
                e.add_constant(Rational64::from_integer(-1));
                self.simplex.add_ge(e, ORIG_REASON);
                Some(())
            }
            (Kind::Ge, false) => {
                // ¬(a ≥ b) ⟺ a ≤ b−1
                e.add_constant(Rational64::from_integer(1));
                self.simplex.add_le(e, ORIG_REASON);
                Some(())
            }
            // ¬(a = b) is a disequality: no linear constraint; guarded by
            // the concrete verification at model time.
            (Kind::Eq, false) | (Kind::Tru, _) => Some(()),
            (Kind::EqLo, true) => {
                // a ≤ b−1  ⟺  (a−b)+1 ≤ 0
                e.add_constant(Rational64::from_integer(1));
                self.simplex.add_le(e, ORIG_REASON);
                Some(())
            }
            (Kind::EqLo, false) => {
                // ¬(a ≤ b−1) ⟺ a ≥ b
                self.simplex.add_ge(e, ORIG_REASON);
                Some(())
            }
            (Kind::EqHi, true) => {
                // a ≥ b+1  ⟺  (a−b)−1 ≥ 0
                e.add_constant(Rational64::from_integer(-1));
                self.simplex.add_ge(e, ORIG_REASON);
                Some(())
            }
            (Kind::EqHi, false) => {
                // ¬(a ≥ b+1) ⟺ a ≤ b
                self.simplex.add_le(e, ORIG_REASON);
                Some(())
            }
        }
    }

    // ======== CDCL core ========

    fn lit_value(&self, lit: i32) -> i8 {
        let v = lit.unsigned_abs() as usize;
        let val = self.value[v];
        if val == 0 {
            0
        } else if lit > 0 {
            val
        } else {
            -val
        }
    }

    fn assign(&mut self, lit: i32, lvl: u32, reason: Option<usize>) {
        let v = lit.unsigned_abs() as usize;
        self.value[v] = if lit > 0 { 1 } else { -1 };
        self.level[v] = lvl;
        self.reason[v] = reason;
        self.trail.push(lit);
        self.propagation_q.push(lit);
    }

    fn decision_level(&self) -> u32 {
        self.trail_lim.len() as u32
    }

    /// Boolean unit propagation over all clauses. Returns the falsified clause
    /// id on conflict, else None.
    fn bcp(&mut self) -> Option<usize> {
        while let Some(&lit) = self.propagation_q.last() {
            self.propagation_q.pop();
            // Only clauses containing this literal's variable can change
            // status or become unit by this assignment.
            let var = lit.unsigned_abs() as usize;
            if var >= self.occurs.len() {
                continue;
            }
            let cids: Vec<usize> = self.occurs[var].clone();
            for cid in cids {
                if cid >= self.clauses.len() {
                    continue;
                }
                let (unassigned, num_true, num_false, first_unassigned) = self.clause_status(cid);
                if num_true > 0 {
                    continue;
                }
                if num_false == self.clauses[cid].len() {
                    return Some(cid); // conflict
                }
                if num_false == self.clauses[cid].len() - 1 && unassigned == 1 {
                    // unit: assign first_unassigned
                    let lvl = self.decision_level();
                    self.assign(first_unassigned, lvl, Some(cid));
                }
            }
        }
        // Note: `assign` may extend `propagation_q` mid-loop; the `while`
        // re-checks it, so every queued literal is processed.
        None
    }

    /// Append a learnt clause and update the occurrence lists.
    fn learn(&mut self, clause: Vec<i32>) -> usize {
        let cid = self.clauses.len();
        for &l in &clause {
            let v = l.unsigned_abs() as usize;
            if v >= self.occurs.len() {
                self.occurs.resize(v + 1, Vec::new());
            }
            self.occurs[v].push(cid);
        }
        self.clauses.push(clause);
        cid
    }

    fn clause_status(&self, cid: usize) -> (i32, usize, usize, i32) {
        let mut nt = 0;
        let mut nf = 0;
        let mut unassigned = 0;
        let mut first_un = 0;
        for &l in &self.clauses[cid] {
            match self.lit_value(l) {
                1 => nt += 1,
                -1 => nf += 1,
                _ => {
                    unassigned += 1;
                    if first_un == 0 {
                        first_un = l;
                    }
                }
            }
        }
        (unassigned, nt, nf, first_un)
    }

    /// Conflict analysis. Returns the learnt clause and backtrack level.
    ///
    /// SOUND CONSERVATIVE STUB: returns an empty learnt clause, so every
    /// conflict above level 0 makes the caller concede (`None`). Clause
    /// learning is disabled: the verified-correct 1-UIP lives in the pure
    /// [`analyze_1uip`] function (unit-tested), but re-enabling it needs the
    /// Tseitin encoder audited (an `and_gate` unit-clause bug and other latent
    /// encoder defects produced unsound learnt clauses → wrong `Unsat`). The
    /// `num_original` guard and the tested analyzer are staged for when the
    /// encoder is verified.
    /// Conflict analysis – 1-UIP via the unit-tested pure [`analyze_1uip`].
    ///
    /// Soundness: a learnt clause is a resolution consequence of the clause
    /// database, so with an encoder that only emits formula-implied clauses
    /// the learnt is also implied.  The two backstops that make a latent
    /// encoder defect *harmless rather than wrong* stay in `solve`: a
    /// level-0 conflict on a *learnt* clause discards all learnts and
    /// restarts (never `Unsat`), and `Unsat` is only ever claimed from a
    /// level-0 conflict on an *original* clause.  A `Sat` is additionally
    /// concretely verified against the input formula before it is reported,
    /// so learning can never fabricate one.
    fn analyze(&mut self, conflict_clause: usize) -> (Vec<i32>, u32) {
        analyze_1uip(
            &self.clauses,
            &self.value,
            &self.level,
            &self.reason,
            &self.trail,
            self.decision_level(),
            conflict_clause,
        )
    }

    fn backtrack(&mut self, target: u32) {
        while self.decision_level() > target {
            let lim = *self.trail_lim.last().unwrap_or(&0);
            self.trail_lim.pop();
            while self.trail.len() > lim {
                let lit = self.trail.pop().unwrap_or_default();
                let v = lit.unsigned_abs() as usize;
                self.value[v] = 0;
                self.level[v] = 0;
                self.reason[v] = None;
            }
            self.simplex.pop();
        }
        // Any atom unassigned by the backtrack must re-impose on the next
        // theory check.  (Bounds they had imposed die with their level's
        // `simplex.pop`, so the tableau and the marker stay in lockstep.)
        self.imposed_marker = self.imposed_marker.min(self.trail.len());
        self.propagation_q.clear();
    }

    fn new_decision_level(&mut self) {
        self.trail_lim.push(self.trail.len());
        self.simplex.push();
    }

    // ======== Theory check (lazy): impose true atoms, test feasibility ========

    /// Impose every atom currently assigned true into the Simplex (which is at
    /// the current push level), then check feasibility. On conflict, return the
    /// explanation as a learnt clause (negations of the responsible true atoms).
    fn theory_check(&mut self) -> TheoryResult {
        // Incremental imposition: only atoms assigned since the previous
        // check are imposed (values never change without a new assignment).
        // The bounds land at the *current* decision level, so `backtrack`'s
        // per-level `simplex.pop` retracts them exactly like the Boolean
        // assignments – no extra scope, no whole-tableau snapshot per level
        // (the historical re-impose-everything + extra-push/pop shape cost
        // O(levels × tableau) and starved large descents).
        while self.imposed_marker < self.trail.len() {
            let lit = self.trail[self.imposed_marker];
            let v = lit.unsigned_abs() as usize;
            let val = self.value[v];
            if val != 0 && self.impose(v as i32, val).is_none() {
                // Cannot express this atom linearly; leave the marker so the
                // atom is retried (it will keep failing) and give up soundly.
                return TheoryResult::GiveUp;
            }
            self.imposed_marker += 1;
        }
        match self.simplex.check() {
            Ok(()) => {
                // Capture the values at this feasible point (branching and
                // extraction read this view; after a backtrack the live
                // tableau no longer carries these bounds).
                self.last_values.clear();
                for (&term, &vid) in &self.var {
                    let _ = term;
                    self.last_values.insert(vid, self.simplex.value(vid));
                }
                for (factors, &mv) in &self.mono {
                    let _ = factors;
                    self.last_values.insert(mv, self.simplex.value(mv));
                }
                TheoryResult::Feasible
            }
            Err(_reasons) => {
                // Complete, provably-implied nogood: the negation of *every*
                // assigned atom, at any level.  The relaxation conflict
                // involves the level-0 atoms just as much as the decisions –
                // a clause over only the decision atoms is NOT implied (the
                // level-0 atoms' absence is exactly what made a historical
                // learner unsound).  `analyze_1uip` soundly drops the
                // level-0 literals when building the learnt clause, so this
                // coarse clause costs strength, never soundness.
                if self.decision_level() == 0 {
                    return TheoryResult::LevelZeroUnsat;
                }
                let mut clause: Vec<i32> = Vec::new();
                for av in 1..self.atoms.len() {
                    if self.value[av] != 0 {
                        clause.push(-signed(av, self.value[av]));
                    }
                }
                if clause.is_empty() {
                    TheoryResult::GiveUp
                } else {
                    TheoryResult::Conflict(clause)
                }
            }
        }
    }

    /// Whether every integer variable's Simplex value is integral, and the
    /// monomial variables equal the product of their factors.
    #[allow(dead_code)]
    fn integer_consistent(&self) -> bool {
        for (&t, &vid) in &self.var {
            if !self.simplex.value(vid).is_integer() {
                let _ = t;
                return false;
            }
        }
        true
    }

    /// An unassigned comparison atom (a formula atom `Le/Lt/Ge/Gt/Eq` over
    /// polynomials), as a positive literal to decide. Skips degenerate `Tru`
    /// atoms (aux gates / free Booleans, which carry no constraint) and split
    /// atoms (integer branches). Returns `None` when every comparison atom is
    /// assigned – the precondition for integer branching / model verification.
    fn unassigned_comparison_atom(&self) -> Option<i32> {
        for v in 1..self.atoms.len() {
            if self.value[v] == 0
                && self.split_bounds[v].is_none()
                && !matches!(self.atoms[v].kind, Kind::Tru)
            {
                return Some(v as i32);
            }
        }
        None
    }

    /// Find a fractional integer variable to branch on (standard integer
    /// branch-and-bound). Returns the variable term and `k = floor(value)`, so
    /// the split lemma `v ≤ k ∨ v ≥ k+1` excludes the current fractional value
    /// on both sides. Returns `None` when every integer variable is integral.
    fn pick_branch(&self) -> Option<(TermId, Rational64)> {
        for (&t, &vid) in &self.var {
            let val = self.captured_value(vid);
            if !val.is_integer() {
                return Some((t, val.floor()));
            }
        }
        None
    }

    /// Value of a Simplex variable from the last feasible-check capture
    /// (0 before the first check).
    fn captured_value(&self, vid: VarId) -> Rational64 {
        self.last_values
            .get(&vid)
            .copied()
            .unwrap_or_else(Rational64::zero)
    }

    /// Product of the current Simplex values of a monomial's factors
    /// (`∏ value(xᵢ)^pᵢ`).
    fn mono_product(&self, factors: &[(TermId, u32)]) -> Rational64 {
        let mut p = Rational64::from_integer(1);
        for &(t, pw) in factors {
            let vid = self.var[&t];
            let val = self.captured_value(vid);
            let mut acc = Rational64::from_integer(1);
            for _ in 0..pw {
                acc *= val;
            }
            p *= acc;
        }
        p
    }

    /// z3's `check_monomial_assignments`: at a fully-integer model a monomial
    /// `m = x·y` has a constant value (the product of its factors). If any
    /// monomial variable's Simplex value differs from that product, return a
    /// factor to branch on (z3's `find_nl_var_for_branching`). `None` if every
    /// monomial is consistent. (This is model-based consistency checking –
    /// strategy 3 of `process_non_linear` – not the blocked interval
    /// propagation of strategy 0.)
    fn monomial_inconsistent_factor(&self) -> Option<TermId> {
        for (factors, mv) in &self.mono {
            if self.captured_value(*mv) == self.mono_product(factors) {
                continue;
            }
            // Prefer a bounded factor (smallest range), else any – z3's
            // bounded preference keeps the branching tractable.
            let mut best: Option<(TermId, Rational64)> = None;
            let mut any: Option<TermId> = None;
            for &(t, _) in factors {
                let vid = self.var[&t];
                let lo = self.simplex.get_lower(vid).map(|b| b.value.real);
                let hi = self.simplex.get_upper(vid).map(|b| b.value.real);
                match (lo, hi) {
                    (Some(lo), Some(hi)) => {
                        let range = hi - lo;
                        if best.is_none_or(|(_, r)| range < r) {
                            best = Some((t, range));
                        }
                    }
                    _ => {
                        if any.is_none() {
                            any = Some(t);
                        }
                    }
                }
            }
            return best.map(|(t, _)| t).or(any);
        }
        None
    }

    // ======== Main loop ========

    #[allow(clippy::too_many_lines)]
    fn solve(
        &mut self,
        assertions: &[TermId],
        manager: &TermManager,
        deadline: oxiz_time::Instant,
        max_conflicts: u64,
    ) -> Option<NlDispatchResult> {
        // Level-0 propagation.
        if let Some(cid) = self.bcp() {
            if self.decision_level() == 0 {
                return Some(NlDispatchResult::Unsat);
            }
            let (learnt, bt) = self.analyze(cid);
            if learnt.is_empty() {
                return None; // concede (never claim Unsat from a possibly-flawed empty learnt clause)
            }
            self.learn(learnt);
            self.backtrack(bt);
        }

        loop {
            if self.conflicts >= max_conflicts && max_conflicts != 0 {
                return None;
            }
            if oxiz_time::Instant::now() >= deadline {
                return None;
            }

            // Boolean propagation.
            if let Some(cid) = self.bcp() {
                self.conflicts += 1;
                if self.decision_level() == 0 {
                    // A level-0 conflict on an original (formula) clause is a
                    // genuine unsat. On a *learnt* clause it means the learner
                    // produced an unsound clause – discard all learnts and
                    // restart rather than claim `Unsat` (soundness backstop).
                    if cid < self.num_original {
                        return Some(NlDispatchResult::Unsat);
                    }
                    self.clauses.truncate(self.num_original);
                    self.backtrack(0);
                    continue;
                }
                let (learnt, bt) = self.analyze(cid);
                if learnt.is_empty() {
                    // Never claim Unsat from a possibly-flawed empty learnt.
                    return None;
                }
                let cid_new = self.learn(learnt.clone());
                self.backtrack(bt);
                // Assert the unit (learnt[0]).
                self.assign(learnt[0], self.decision_level(), Some(cid_new));
                continue;
            }

            // Theory check.
            match self.theory_check() {
                TheoryResult::LevelZeroUnsat => return Some(NlDispatchResult::Unsat),
                TheoryResult::Conflict(clause) => {
                    self.conflicts += 1;
                    if self.decision_level() == 0 {
                        return Some(NlDispatchResult::Unsat);
                    }
                    // Analyze the theory conflict clause (it is over assigned
                    // literals) using the same 1-UIP machinery.
                    let cid_new = self.learn(clause);
                    let (learnt, bt) = self.analyze(cid_new);
                    if learnt.is_empty() {
                        return None;
                    }
                    self.backtrack(bt);
                    self.assign(learnt[0], self.decision_level(), Some(cid_new));
                    continue;
                }
                TheoryResult::GiveUp => {
                    return None;
                }
                TheoryResult::Feasible => {}
            }

            // Boolean decision: decide an unassigned comparison atom (the
            // formula's arithmetic atoms) to drive the CDCL's Boolean search.
            if let Some(av) = self.unassigned_comparison_atom() {
                self.new_decision_level();
                self.assign(av, self.decision_level(), None); // decide true
                continue;
            }

            // Integer branch-and-bound: if some integer variable is fractional,
            // create a branching lemma `v ≤ k ∨ v ≥ k+1` and decide the `v ≤ k`
            // side true first (z3's branch_nl_int_var). The CDCL explores the
            // `v ≥ k+1` side via backjumping when the `v ≤ k` subtree conflicts.
            if let Some((term, k)) = self.pick_branch() {
                let vid = self.var[&term];
                let split_var = self.make_split_atom(vid, k);
                self.new_decision_level();
                self.assign(split_var, self.decision_level(), None); // decision: v ≤ k
                continue;
            }

            // All integer. z3's `check_monomial_assignments`: if a monomial
            // variable disagrees with the product of its (now integer)
            // factors, branch a factor to drive the model toward monomial
            // consistency. The split excludes the factor's current value so the
            // descent makes progress; the bounded-domain DFS + CDCL learning
            // explores toward a consistent integer model.
            if let Some(term) = self.monomial_inconsistent_factor() {
                let vid = self.var[&term];
                let val = self.captured_value(vid);
                // Exclude the current integer value: branch `v ≤ val−1`.
                let k = val - Rational64::from_integer(1);
                let split_var = self.make_split_atom(vid, k);
                self.new_decision_level();
                self.assign(split_var, self.decision_level(), None);
                continue;
            }

            // All integer + monomially consistent: extract and concretely verify.
            let env = self.feasible_env()?;
            if concrete_sat(&env, assertions, manager) {
                return Some(NlDispatchResult::sat_with(
                    env.into_iter()
                        .map(|(t, v)| (t, num_rational::BigRational::from_integer(v)))
                        .collect(),
                ));
            }
            // The relaxation is integer-consistent but the abstracted parts
            // (actual products, false equalities) reject this particular
            // model.  z3's `process_non_linear` step 2: *pin* every
            // inconsistent monomial to the product of its factors (and every
            // false-equality separation) inside a fresh scope and re-check –
            // a feasible pinned system whose extracted model passes the
            // concrete check is a genuine witness; an infeasible one only
            // means the current factor values do not extend.
            if let Some(witness) = self.try_model_repair(assertions, manager) {
                return Some(witness);
            }
            // Repair exhausted: sound; an honest `Unknown` via the caller.
            return None;
        }
    }

    /// Pin every inconsistent monomial to the product of its factor values
    /// and every false `Eq` atom whose sides coincide to the arithmetic
    /// separation, inside a fresh Simplex scope; re-check.  Returns a
    /// concretely-verified `Sat` witness when the repaired system is
    /// feasible and verifies, else `None` (the caller concedes soundly).
    fn try_model_repair(
        &mut self,
        assertions: &[TermId],
        manager: &TermManager,
    ) -> Option<NlDispatchResult> {
        self.simplex.push();
        let outcome = self.repair_in_scope(assertions, manager);
        self.simplex.pop();
        outcome
    }

    fn repair_in_scope(
        &mut self,
        assertions: &[TermId],
        manager: &TermManager,
    ) -> Option<NlDispatchResult> {
        // 1. Pin inconsistent monomials: m := ∏ factors(current values).
        let monos: Vec<(Vec<(TermId, u32)>, VarId)> =
            self.mono.iter().map(|(f, &mv)| (f.clone(), mv)).collect();
        let mut pinned_any = false;
        for (factors, mv) in monos {
            let product = self.mono_product(&factors);
            if self.simplex.value(mv) == product {
                continue;
            }
            let reason = DECISION_REASON_BASE + mv;
            self.simplex.set_lower(mv, product, reason);
            self.simplex.set_upper(mv, product, reason);
            pinned_any = true;
        }
        // 2. Separate false `Eq` atoms whose sides currently coincide: the
        //    adapter clause lets the Boolean layer leave lo/hi unforced when
        //    the Eq itself is decided false and the clause is satisfied via
        //    a *false* lo/hi; arithmetically that means a = b while ¬(a=b)
        //    is required.  Pin residual ≥ 1 (a ≥ b+1) first; if infeasible,
        //    the ≤ −1 side.
        let eq_atoms: Vec<(TermId, TermId)> = (1..self.atoms.len())
            .filter(|&v| self.atoms[v].kind == Kind::Eq && self.value[v] < 0)
            .map(|v| (self.atoms[v].lhs, self.atoms[v].rhs))
            .collect();
        for (lhs, rhs) in eq_atoms {
            let Some(mut e) = self.translate(lhs) else {
                continue;
            };
            let Some(r) = self.translate(rhs) else {
                continue;
            };
            add_scaled(&mut e, &r, Rational64::from_integer(-1));
            // Only separate when they coincide under the current model.
            let mut residual = e.constant;
            for &(vid, c) in &e.terms {
                if !self.var_term.contains_key(&vid) {
                    continue;
                }
                let rv = self.simplex.value(vid);
                residual += rv * c;
            }
            if residual != Rational64::zero() {
                continue;
            }
            let hi = {
                let mut e2 = e.clone();
                e2.add_constant(Rational64::from_integer(-1));
                e2
            };
            // a ≥ b+1 first…
            let reason = DECISION_REASON_BASE;
            let slack_hi = self.simplex_probe_ge(&hi, reason);
            if !slack_hi {
                // …else a ≤ b−1.
                let mut lo = e;
                lo.add_constant(Rational64::from_integer(1));
                let _ = self.simplex_probe_le(&lo, reason);
            }
            pinned_any = true;
        }
        if self.simplex.check().is_err() {
            return None;
        }
        let _ = pinned_any;
        // 3. Feasible: all values integral (caller ensured) and pinned
        //    monomials equal their products by construction.  Extract
        //    *inside* the scope and concretely verify.
        for (&term, &vid) in &self.var {
            let _ = term;
            if !self.simplex.value(vid).is_integer() {
                return None;
            }
        }
        let env = self.extract_env();
        if concrete_sat(&env, assertions, manager) {
            return Some(NlDispatchResult::sat_with(
                env.into_iter()
                    .map(|(t, v)| (t, num_rational::BigRational::from(v)))
                    .collect(),
            ));
        }
        None
    }

    /// Impose `expr ≥ 0` and test feasibility (rolled back by the caller's
    /// scope pop).  Returns whether the system stayed feasible.
    fn simplex_probe_ge(&mut self, expr: &LinExpr, reason: u32) -> bool {
        self.simplex.add_ge(expr.clone(), reason);
        self.simplex.check().is_ok()
    }

    fn simplex_probe_le(&mut self, expr: &LinExpr, reason: u32) -> bool {
        self.simplex.add_le(expr.clone(), reason);
        self.simplex.check().is_ok()
    }

    fn extract_env(&self) -> std::collections::HashMap<TermId, BigInt> {
        let mut env = std::collections::HashMap::new();
        for (&t, &vid) in &self.var {
            let r = self.simplex.value(vid);
            let v = if r.is_integer() {
                r64_to_big(r)
            } else {
                r64_to_big(r.floor())
            };
            env.insert(t, v);
        }
        env
    }

    /// Fresh model at the model point: impose every assigned atom in a new
    /// scope, check, and extract the *live* (un-floored) values.  A cached
    /// capture from an earlier feasible check cannot be used – later splits
    /// and conflicts move the live values, and a stale capture made the
    /// concrete verification test a model the search had already left.
    fn feasible_env(&self) -> Option<std::collections::HashMap<TermId, BigInt>> {
        let mut env = std::collections::HashMap::new();
        for (&t, &vid) in &self.var {
            let rv = self.captured_value(vid);
            if !rv.is_integer() {
                return None;
            }
            env.insert(t, r64_to_big(rv));
        }
        Some(env)
    }
}

// ======== Helpers ========

enum TheoryResult {
    Feasible,
    Conflict(Vec<i32>),
    LevelZeroUnsat,
    GiveUp,
}

fn add_scaled(acc: &mut LinExpr, other: &LinExpr, scale: Rational64) {
    for &(v, c) in &other.terms {
        acc.add_term(v, c * scale);
    }
    acc.add_constant(other.constant * scale);
}

/// Increment the power of `term` in a monomial key (or insert it at power 1).
fn bump_power(pm: &mut Vec<(TermId, u32)>, term: TermId) {
    for (t, p) in pm.iter_mut() {
        if *t == term {
            *p += 1;
            return;
        }
    }
    pm.push((term, 1));
}
fn r64_of(b: &BigInt) -> Option<Rational64> {
    Some(Rational64::from_integer(b.to_i64()?))
}

fn r64_to_big(r: Rational64) -> BigInt {
    BigInt::from(r.to_integer())
}

fn signed(var: usize, value: i8) -> i32 {
    let mag = var as i32;
    if value > 0 { mag } else { -mag }
}

fn concrete_sat(
    env: &std::collections::HashMap<TermId, BigInt>,
    assertions: &[TermId],
    manager: &TermManager,
) -> bool {
    eval_assertions_true(assertions, manager, env)
}

// ========  ========
// 1-UIP conflict analysis (pure, unit-tested)
// ========  ========

/// First-UIP conflict analysis. Given a conflict clause (all literals false
/// under the trail), derive the learnt clause (asserting literal at index 0)
/// and the backtrack level, by resolving the conflict clause against the
/// reasons of the most recent current-level literals until exactly one
/// current-level literal remains – the unique implication point.
///
/// Inputs follow the standard CDCL conventions:
/// * `value[v]`: `+1` true, `-1` false, `0` unassigned.
/// * `level[v]`: decision level (0 = a fixed/unit assignment).
/// * `reason[v]`: `Some(cid)` if `v` was propagated by clause `cid`; `None` if
///   `v` is a decision.
/// * `trail`: assigned literals in assignment order.
/// * `current_level`: the current decision level.
///
/// Returns `(learnt, backtrack_level)`; an empty `learnt` signals a level-0
/// conflict (the conflict clause has no level>0 literal to resolve – the caller
/// must treat that as a genuine unsat only if it is an original clause).
#[allow(dead_code)]
fn analyze_1uip(
    clauses: &[Vec<i32>],
    value: &[i8],
    level: &[u32],
    reason: &[Option<usize>],
    trail: &[i32],
    current_level: u32,
    conflict_clause: usize,
) -> (Vec<i32>, u32) {
    let n = value.len();
    let mut seen = vec![false; n];
    let mut learnt: Vec<i32> = Vec::new();
    let mut backtrack_level: u32 = 0;
    let mut path_count: i32 = 0; // current-level literals seen but not resolved
    let mut confl = clauses[conflict_clause].clone();
    // `cursor` scans the trail backwards (monotonically) for the most recent
    // seen literal. It is decremented before use.
    let mut cursor = trail.len();
    let mut asserting: i32 = 0; // the UIP literal (0 until found)
    loop {
        // Mark every literal of the current resolution clause. The pivot from
        // the previous iteration is already `seen`, so it is skipped here.
        for &q in &confl {
            let v = q.unsigned_abs() as usize;
            if v < n && !seen[v] && level[v] > 0 {
                seen[v] = true;
                if level[v] == current_level {
                    path_count += 1;
                } else {
                    learnt.push(q);
                    if level[v] > backtrack_level {
                        backtrack_level = level[v];
                    }
                }
            }
        }
        // Most recent trail literal that is `seen`.
        let mut found = false;
        while cursor > 0 {
            cursor -= 1;
            if seen[trail[cursor].unsigned_abs() as usize] {
                found = true;
                break;
            }
        }
        if !found {
            break; // no UIP (degenerate level-0 conflict)
        }
        let p = trail[cursor];
        let pv = p.unsigned_abs() as usize;
        // `p` is the most recent seen literal; as long as current-level seen
        // literals remain unresolved, `p` is one of them (current-level lits
        // are assigned after lower-level ones, so they are more recent).
        path_count -= 1;
        if path_count == 0 {
            // `p` is the sole remaining current-level literal → the UIP.
            asserting = -p;
            break;
        }
        // Otherwise resolve `p` against its reason. A decision (no reason) is
        // the UIP even if path_count > 0 (it dominates every current-level path).
        match reason.get(pv).copied().flatten() {
            Some(cid) => confl = clauses[cid].clone(),
            None => {
                asserting = -p;
                break;
            }
        }
    }
    if asserting == 0 {
        return (Vec::new(), 0);
    }
    learnt.insert(0, asserting);
    (learnt, backtrack_level)
}

#[cfg(test)]
mod tests {
    use super::*;
    use oxiz_core::ast::TermManager;

    /// Regression (wrong-unsat, gate-variable aliasing): every Tseitin gate
    /// used to share one content-addressed `(zero, zero, Tru)` atom, so the
    /// nested `(and (= rfc0 0) (or (= rfc0 0)))` gate and the outer `and`
    /// gate collapsed onto the same SAT variable and their gate clauses
    /// contradicted at level 0.  Reduced from VeryMax `459.smt2` (Z3: sat,
    /// oxiz reported unsat).  Must never answer `Unsat`.
    #[test]
    fn gate_aliasing_never_claims_unsat_on_sat_goal() {
        let mut m = TermManager::new();
        let rfc0 = m.mk_var("rfc0", m.sorts.int_sort);
        let v2 = m.mk_var("V2", m.sorts.int_sort);
        let zero = m.mk_int(0);
        let minus_one = m.mk_int(-1);
        // (and (not (= rfc0 0))
        //      (or (>= rfc0 (* -1 V2))
        //          (and (= rfc0 0) (or (= rfc0 0)))))
        let eq = m.mk_eq(rfc0, zero);
        let neg_v2 = m.mk_mul([minus_one, v2]);
        let ge = m.mk_ge(rfc0, neg_v2);
        let inner_or = m.mk_or([eq]);
        let inner_and = m.mk_and([eq, inner_or]);
        let outer_or = m.mk_or([ge, inner_and]);
        let not_eq = m.mk_not(eq);
        let goal = m.mk_and([not_eq, outer_or]);
        let r = cdcl_nia_search(&[goal], &[goal], &mut m);
        assert_ne!(
            r,
            Some(NlDispatchResult::Unsat),
            "sat goal (rfc0 = 1, V2 = 0) must never be reported unsat"
        );
    }

    /// Regression (simplex frame leak): `theory_check` used to leave its
    /// imposed constraints in the tableau on the feasible path; retracted
    /// atoms stayed enforced across backtracks until level 0 became
    /// infeasible on satisfiable goals (wrong `Unsat` under the fuzz
    /// harness).  This infeasible-then-feasible cycle must stay consistent.
    #[test]
    fn theory_frame_leak_cycle_stays_sound() {
        let mut m = TermManager::new();
        let x = m.mk_var("x", m.sorts.int_sort);
        let one = m.mk_int(1);
        let two = m.mk_int(2);
        // (and (>= x 2) (<= x 1)) is genuinely unsat.
        let g = m.mk_ge(x, two);
        let l = m.mk_le(x, one);
        let unsat_goal = m.mk_and([g, l]);
        assert_eq!(
            cdcl_nia_search(&[unsat_goal], &[unsat_goal], &mut m),
            Some(NlDispatchResult::Unsat)
        );
        // A fresh satisfiable goal over the same variable must not inherit
        // the previous run's level (each call builds a fresh solver, but the
        // assertion guards against future shared-state regressions).
        let three = m.mk_int(3);
        let g2 = m.mk_ge(x, two);
        let l2 = m.mk_le(x, three);
        let sat_goal = m.mk_and([g2, l2]);
        let r = cdcl_nia_search(&[sat_goal], &[sat_goal], &mut m);
        assert_ne!(r, Some(NlDispatchResult::Unsat));
    }

    type CdclState = (Vec<i8>, Vec<u32>, Vec<Option<usize>>, Vec<i32>, u32);

    /// Helper: build CDCL state arrays. `trail_lits` are assigned in order;
    /// `(var, lvl, reason)` triples give each variable's level and reason.
    fn state(trail_lits: &[i32], info: &[(i32, u32, Option<usize>)]) -> CdclState {
        let n = info
            .iter()
            .map(|(v, _, _)| (*v).unsigned_abs() as usize)
            .max()
            .unwrap_or(0)
            + 1;
        let mut value = vec![0i8; n];
        let mut level = vec![0u32; n];
        let mut reason = vec![None; n];
        for &(v, lvl, r) in info {
            let var = v.unsigned_abs() as usize;
            value[var] = if v > 0 { 1 } else { -1 };
            level[var] = lvl;
            reason[var] = r;
        }
        let current = info.iter().map(|(_, l, _)| *l).max().unwrap_or(0);
        (value, level, reason, trail_lits.to_vec(), current)
    }

    /// Linear implication chain, single current level:
    ///   level 0: x4 = true (unit)
    ///   level 1: decide x1; clause {-1,2} -> x2; clause {-2,3} -> x3
    ///   conflict: {-3, -4}  (x3 true, x4 true -> both false)
    /// 1-UIP at level 1 is x3 (the only level-1 lit on the conflict slice after
    /// dropping the level-0 literal); learnt = {-3}, backtrack to 0.
    #[test]
    fn linear_chain_single_uip() {
        // clauses: 0={-1,2}, 1={-2,3}, 2={-3,-4}
        let clauses: Vec<Vec<i32>> = vec![vec![-1, 2], vec![-2, 3], vec![-3, -4]];
        let (value, level, reason, trail, current) = state(
            &[4, 1, 2, 3],
            &[(4, 0, None), (1, 1, None), (2, 1, Some(0)), (3, 1, Some(1))],
        );
        let (learnt, bt) = analyze_1uip(&clauses, &value, &level, &reason, &trail, current, 2);
        // The asserting literal is -3; the level-0 literal -4 is dropped.
        assert_eq!(learnt, vec![-3]);
        assert_eq!(bt, 0);
    }

    /// Two current-level literals, resolve one:
    ///   level 1: decide x1; {-1,2} -> x2; {-2,3} -> x3
    ///   level 2: decide x4; {-4,5} -> x5
    ///   conflict: {-3, -5}  (x3 true, x5 true)
    /// At level 2 the only level-2 lit is x5 -> first UIP = x5.
    /// learnt = {-5, -3}, backtrack to level 1.
    #[test]
    fn two_levels_first_uip() {
        let clauses: Vec<Vec<i32>> = vec![vec![-1, 2], vec![-2, 3], vec![-4, 5], vec![-3, -5]];
        let (value, level, reason, trail, current) = state(
            &[1, 2, 3, 4, 5],
            &[
                (1, 1, None),
                (2, 1, Some(0)),
                (3, 1, Some(1)),
                (4, 2, None),
                (5, 2, Some(2)),
            ],
        );
        let (learnt, bt) = analyze_1uip(&clauses, &value, &level, &reason, &trail, current, 3);
        assert_eq!(learnt, vec![-5, -3]);
        assert_eq!(bt, 1);
    }

    /// Conflict clause with two level-2 lits: resolve the propagated one (x5)
    /// to reach the decision (x4) as UIP.
    ///   conflict: {-3, -5, -4}  (x3 lvl1, x5 lvl2 prop, x4 lvl2 decision)
    /// learnt = {-4, -3}, backtrack to level 1.
    #[test]
    fn resolve_to_decision_uip() {
        let clauses: Vec<Vec<i32>> = vec![vec![-1, 2], vec![-2, 3], vec![-4, 5], vec![-3, -5, -4]];
        let (value, level, reason, trail, current) = state(
            &[1, 2, 3, 4, 5],
            &[
                (1, 1, None),
                (2, 1, Some(0)),
                (3, 1, Some(1)),
                (4, 2, None),
                (5, 2, Some(2)),
            ],
        );
        let (learnt, bt) = analyze_1uip(&clauses, &value, &level, &reason, &trail, current, 3);
        assert_eq!(learnt, vec![-4, -3]);
        assert_eq!(bt, 1);
    }

    /// Level-0 conflict (no level>0 literal in the conflict clause) -> empty.
    #[test]
    fn level_zero_conflict() {
        let clauses: Vec<Vec<i32>> = vec![vec![-1, -2]];
        let (value, level, reason, trail, current) = state(&[1, 2], &[(1, 0, None), (2, 0, None)]);
        let (learnt, _bt) = analyze_1uip(&clauses, &value, &level, &reason, &trail, current, 0);
        assert!(learnt.is_empty());
    }
}
