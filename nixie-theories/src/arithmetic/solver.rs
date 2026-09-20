//! Arithmetic Theory Solver

use super::delta::{BoundValue, DeltaRational};
use super::nla::checked_neg_r64;
use super::simplex::{
    Bound, LinExpr, RowInternMode, Simplex, SimplexOptStatus, VarId, checked_add_r64,
    checked_div_r64, checked_mul_r64, checked_sub_r64,
};
#[allow(unused_imports)]
use crate::prelude::*;
use crate::theory::{EqualityNotification, Theory, TheoryCombination, TheoryId, TheoryResult};
use nixie_core::ast::TermId;
use nixie_core::error::Result;
use num_rational::Rational64;
use num_traits::{CheckedAdd, CheckedSub, One, Signed, Zero};
use smallvec::SmallVec;

/// Arithmetic equality solver's verdict on `a = b` from the current bounds.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ArithEqualityStatus {
    /// Both sides are fixed to the same value ⇒ `a = b` entailed.
    EntailedEqual,
    /// Both sides are fixed to distinct values ⇒ `a ≠ b` entailed.
    EntailedDisequal,
    /// Arithmetic has not (yet) determined the equality.
    Unknown,
}

/// If the lower and upper bounds coincide, the variable is *fixed* to that
/// value; return it.
fn fixed_value(
    lo: Option<&super::simplex::Bound>,
    hi: Option<&super::simplex::Bound>,
) -> Option<super::delta::DeltaRational> {
    // Exact equality (equal wide pairs included); the NARROW form is
    // returned — a fixed value beyond width has no i64 constant to name
    // it, and the caller (`fixed_to_const_reason`) is an i64-consumer
    // optimization that declines.
    let (l, u) = (lo?, hi?);
    if l.value == u.value {
        l.value.narrow()
    } else {
        None
    }
}

/// Compute GCD of two i64 values
fn gcd_i64(mut a: i64, mut b: i64) -> i64 {
    a = a.abs();
    b = b.abs();
    while b != 0 {
        let temp = b;
        b = a % b;
        a = temp;
    }
    a
}

/// The comparison flavour a slack's defining atom asserted — kept so the
/// stranded-bound re-homing sweep can re-assert the ATOM's own bound on a
/// rebuilt row (see [`ArithSolver::rehome_stranded_row_bounds`]).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum SlackDir {
    /// `lhs <= rhs`: the atom's own bound is `slack <= 0`.
    Le,
    /// `lhs >= rhs`: the atom's own bound is `slack >= 0`.
    Ge,
    /// `lhs = rhs`: the atom's own bound is `slack = 0`.
    Eq,
    /// `lhs < rhs` (the delta-encoded strict path of `assert_lt`): the
    /// atom's own bound is the STRICT `slack < 0`.
    Lt,
    /// `lhs > rhs` (the delta-encoded strict path of `assert_gt`): the
    /// atom's own bound is the STRICT `slack > 0`.
    Gt,
}

/// The linear form that interned a row slack, kept for the stranded-bound
/// re-homing sweep (see [`ArithSolver::rehome_stranded_row_bounds`]).
#[derive(Clone, Debug)]
struct SlackForm {
    lhs: Vec<(TermId, Rational64)>,
    rhs: Rational64,
    dir: SlackDir,
    /// The atom whose assertion interned the row.  Only bounds justified by
    /// THIS term may be re-homed (see the sweep's soundness gates).
    reason: TermId,
    /// The row was interned through the EXACT path (`-rhs` beyond
    /// `Rational64`, the `i64::MIN` corner): the stranded-bound sweep must
    /// re-intern through the same exact path, never the narrow one whose
    /// `add_constant(-rhs)` would wrap to a different row.
    exact: bool,
}

/// Arithmetic Theory Solver (LRA/LIA)
#[derive(Debug)]
pub struct ArithSolver {
    /// Simplex instance
    simplex: Simplex,
    /// Term to variable mapping
    term_to_var: FxHashMap<TermId, VarId>,
    /// Variable to term mapping
    var_to_term: Vec<TermId>,
    /// Reason counter
    reason_counter: u32,
    /// Reason to term mapping
    reasons: Vec<TermId>,
    /// Integrality regime (LRA / LIA / mixed-integer); see [`ArithMode`].
    mode: ArithMode,
    /// Context stack
    context_stack: Vec<ContextState>,
    /// Accumulated shared equalities (from notify_equality calls)
    shared_equalities: Vec<EqualityNotification>,
    /// Integral model recorded by the LIA branch-and-bound search.
    ///
    /// Populated only when the most recent `check()` proved `Sat` in integer
    /// mode.  `value()` consults this first for Int terms so it returns the
    /// integral assignment found by branch-and-bound rather than the (possibly
    /// fractional) LP-relaxation optimum.  Cleared at the start of every
    /// `check()` and on `reset()`.
    lia_model: FxHashMap<VarId, num_rational::BigRational>,
    /// Integer equalities asserted in LIA mode, kept as raw
    /// `(sum a_i·x_i = b)` rows so that a linear Diophantine consistency check
    /// can detect cross-constraint parity infeasibility (e.g. `y=2x ∧ y=2z+1`)
    /// that per-equation GCD reasoning and pure branch-and-bound over unbounded
    /// variables miss.  Push/pop-scoped via `ContextState`.
    int_equalities: Vec<IntEquation>,
    /// Cached result of [`Self::int_equalities_infeasible`].  That Diophantine
    /// consistency check is a pure function of `int_equalities` (it neither
    /// reads nor depends on the live simplex assignment), but it performs an
    /// O(rows·cols) fraction-free Gaussian elimination, so re-running it on
    /// every theory check – which for an integer logic fires once per CDCL
    /// propagation – dominates runtime on saturated LIA/DL inputs (e.g. the
    /// mathsat `vhard` family, where it alone was ~80% of wall time).  The
    /// equality set changes only when an equality is asserted (`intern`-time)
    /// or retracted by `pop`, so the cache is invalidated at exactly those
    /// points and recomputed lazily.  `None` ⇒ dirty.  Caches the complete
    /// [`IntEqVerdict`] (the one-sided infeasibility-only cache it replaces
    /// was subsumed by the Hermite solve).
    int_eq_verdict_cache: Option<IntEqCache>,
    /// Propagation-only single-variable constant bounds, maintained in
    /// parallel with the simplex.  The simplex encodes every constraint
    /// (`add_le`/`add_eq`) as a *slack row* with the bound on the slack, so its
    /// `lower`/`upper` arrays carry **no** bound on the original variables –
    /// which defeats cheap bound propagation.  This tracker records the direct
    /// single-variable constant bound each `assert_*` implies on its variable
    /// (e.g. `assert_eq([(x,1)], k)` ⇒ `x ∈ [k,k]`), so
    /// [`Self::derive_expr_bound_reasons`] can force atoms without an LP solve.
    ///
    /// SOUND: every entry is a direct consequence of one asserted atom (its
    /// `reason` id).  Push/pop-scoped via the `prop_undo` trail (parallel to
    /// the simplex's own trail).  Used for propagation only – never consulted
    /// by `check()`/feasibility, so it cannot affect soundness of the solve.
    prop_lower: Vec<Option<PropBoundEntry>>,
    /// See [`Self::prop_lower`].
    prop_upper: Vec<Option<PropBoundEntry>>,
    /// Undo trail for `prop_lower`/`prop_upper`, with a `Scope` marker pushed
    /// at every `push()` and replayed at every `pop()`.
    prop_undo: Vec<PropBoundUndo>,
    /// Variables known to take integer values in every model: the Int-sorted
    /// terms (all interned terms in LIA mode) plus row slacks whose defining
    /// linear form is integral over integer variables.  Drives Gomory-cut
    /// integrality and the branch-and-bound variable scan; treating a genuine
    /// integer variable as continuous only weakens cuts (sound), so slacks of
    /// non-integral form are simply absent from this set.
    int_vars: FxHashSet<VarId>,
    /// TERMS declared integer-valued (Int-sorted) by the registration sites
    /// that can see the sort.  Mixed mode's per-term integrality memory: the
    /// simplex is rebuilt (variables renumbered, `int_vars` cleared) on every
    /// theory-layer `reset()`/replay, but a term's sort is a structural fact,
    /// so this registry lets `intern` re-mark the fresh variable without the
    /// replay having to know anything about sorts.
    /// Sticky honesty flag: an assertion whose row could not be represented
    /// in `Rational64` was DECLINED instead of wrapped — the `x <= i64::MIN`
    /// corner, where the row `lhs - rhs` needs the constant `+2^63` (the
    /// negation of `i64::MIN` does not fit; found by the debug-panic sweep
    /// on `QF_ANIA/diskperf`, where the release build silently wrapped the
    /// row's constant to a DIFFERENT constraint).  While set, `check()`
    /// answers `Unknown`: the declined atom is unconstrained in the
    /// tableau, so neither `Sat` nor `Unsat` may be trusted.  Sticky for
    /// the solver instance's lifetime (like a parse-overflow atom): a
    /// re-asserted atom re-declines, and `reset()` keeps the flag for the
    /// same reason it keeps `int_terms`.
    int_terms: FxHashSet<TermId>,
    /// Per-ATOM tableau-row cache: `(linear form, assertion term) -> slack`.
    ///
    /// The SAME atom re-asserted (CDCL re-sends a literal after every
    /// backtrack; the rebase replays the trail) reuses its row instead of
    /// interning a duplicate – on cmodelsdiff-style inputs the re-sends
    /// otherwise grow the tableau by hundreds of rows per theory round and
    /// every pivot walks them all.  Deliberately NOT keyed by form alone:
    /// two DIFFERENT atoms over one linear form must keep separate rows
    /// (each atom's bounds then constrain its own slack; sharing one slack
    /// across atoms measurably changes which equalities the fixed-variable
    /// analysis derives and, through it, the search trajectory – see the
    /// regression note in `assert_explained_equality`).  Entries are
    /// invalidated when the slack's row was pivoted out of the tableau
    /// (`row_defines_var`) and cleared on `reset`.
    atom_rows: FxHashMap<(RowKey, TermId), VarId>,
    /// Reverse of the row cache's slack allocation: slack var → the
    /// (lhs, rhs, equality, reason) form that interned it.  The stranded-
    /// bound re-homing sweep (`rehome_stranded_row_bounds`) uses it to
    /// rebuild a lost row and re-attach its bounds.
    slack_forms: FxHashMap<VarId, SlackForm>,
    /// Real-atom reason ids seen in any LP conflict during the current
    /// branch-and-bound / cut search.  When the search refutes the integer
    /// problem, this set (not the full reason list) is the unsat core: each
    /// leaf's Farkas certificate names the atoms whose bounds made that
    /// branch's relaxation infeasible, the split disjunctions
    /// `x ≤ k ∨ x ≥ k+1` are integer tautologies that need no reason, and a
    /// completed tree therefore proves `used_atoms ⊢ no integer solution`.
    /// Tighter than [`Self::full_unsat_core`] (which cites every atom),
    /// which made CDCL learn trivially-true clauses and re-derive the same
    /// refutation thousands of times on conjunction-shaped input (rings).
    bnb_used_reasons: FxHashSet<u32>,
    /// Whether cuts are being derived *inside* a free-variable split
    /// scope (see [`Self::close_free_vars_then_bnb`]): there, a nonbasic
    /// resting at a `BRANCH_REASON` bound is fine – the cut is scoped to
    /// the branch and dropped with it – so [`Self::gomory_cut`] may use
    /// such bounds.  At the root (the default) the old refusal stands: a
    /// cut resting on a case-split bound must never be asserted globally.
    cuts_in_split_scope: bool,
}

/// A linear equality over the integers: `sum(coeff_i · var_i) = rhs`.
#[derive(Debug, Clone)]
struct IntEquation {
    terms: Vec<(VarId, i64)>,
    rhs: i64,
    /// The atom/lemma whose assertion recorded this row — names the row
    /// in Diophantine infeasibility cores.
    reason: TermId,
}

/// A propagation-only single-variable constant bound (see
/// `ArithSolver::prop_lower`).
#[derive(Debug, Clone, Copy)]
struct PropBoundEntry {
    value: DeltaRational,
    reason: u32,
}

/// One undo step for the propagation-bound trail.
#[derive(Debug, Clone, Copy)]
enum PropBoundUndo {
    Lower(VarId, Option<PropBoundEntry>),
    Upper(VarId, Option<PropBoundEntry>),
    /// Scope marker inserted by the matching `push()`.
    Scope,
}

/// Comparison flavour for [`ArithSolver::record_prop_bound`].
#[derive(Debug, Clone, Copy)]
enum PropCmp {
    Le,
    Ge,
    Lt,
    Gt,
}

/// One directional expression bound paired with the atoms that justify it.
type ExplainedBound = Option<(DeltaRational, Vec<TermId>)>;

/// Reason id marking a branch-and-bound case-split bound (`x ≤ k` / `x ≥ k+1`
/// inside [`ArithSolver::bnb_recurse`]).  It names no asserted atom: the split
/// is an integer tautology, so a conflict citing it stays valid when the
/// marker is dropped from the core.  `u32::MAX` can never collide with a real
/// `add_reason` id (bounded by `reasons.len()`), so every reason-id → term
/// mapping safely yields `None` for it.
pub(crate) const BRANCH_REASON: u32 = u32::MAX;

/// Complete verdict of the recorded integer-equality subsystem
/// ([`ArithSolver::int_equalities`]), decided by the Hermite
/// (column-echelon) solve in `lia::hnf::solve_integer_eq_system`.
///
/// * `Infeasible` is a proof: the equality subsystem has no integer
///   solution, so neither does the full problem.
/// * `Incumbent` is a witness (free variables set to zero). It satisfies
///   the equalities; whether it satisfies every OTHER active row is
///   decided by re-pinning it through a scoped LP re-solve
///   ([`ArithSolver::try_eq_incumbent`]) — never by trusting it.
/// * `GiveUp` defers to branch-and-bound (magnitude/size guard).
#[derive(Debug, Clone, PartialEq)]
enum IntEqVerdict {
    /// Proven infeasible, with the responsible equations' reason terms
    /// (the small infeasibility core; a full core teaches CDCL nothing).
    Infeasible(Vec<TermId>),
    Incumbent(Vec<(VarId, Rational64)>),
    GiveUp,
}

/// Memoized verdict + incumbent-rejection marker.  `rejected` is set when
/// the rows beyond the recorded equalities refused the witness; the
/// attempt is then skipped until the equality set changes (which resets
/// the whole entry) — a rejected pinning is one LP wasted per theory
/// check otherwise.  This trades a missed rescue in the rare case where
/// only non-equality rows changed in the witness's favour for not
/// re-paying the probe at every check.
#[derive(Debug, Clone)]
struct IntEqCache {
    verdict: IntEqVerdict,
    rejected: bool,
}

/// Canonical key of a linear form over TermIds: terms sorted by TermId
/// with coefficients merged and zero coefficients dropped, plus the
/// constant.  Two assertions of the same (or scaled-identical after
/// parsing) atom map to the same key, hence the same tableau row.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
struct RowKey {
    terms: Vec<(TermId, Rational64)>,
    constant: Rational64,
}

/// State for push/pop
#[derive(Debug, Clone)]
struct ContextState {
    num_reasons: usize,
    num_shared_equalities: usize,
    num_int_equalities: usize,
}

/// How the tableau treats integrality.  The mirror of Z3's `theory_lra` /
/// `theory_lia` / `theory_mi_arith` split, selected by the *declared* logic:
///
/// * [`ArithMode::Lra`] – every variable continuous (QF_LRA).
/// * [`ArithMode::Lia`] – every interned term integer-valued (QF_LIA).
/// * [`ArithMode::Mixed`] – per-variable integrality from each term's sort:
///   `Int`-sorted terms are integer variables, `Real`-sorted terms are
///   continuous, and rows that mix them keep the real semantics for the
///   continuous part while branch-and-bound closes the integer part
///   (Z3's `theory_mi_arith`, the default for an unset / `ALL` logic).
///
/// The mode is a *configuration*, not a per-row fact: what a row may
/// legitimately assume is decided per row by [`ArithSolver::is_integral_form`]
/// over the [`ArithSolver::int_vars`] set the mode populated.  A solver that
/// ran Lra but was handed `Int`-sorted atoms (a bare `Solver::new()` before
/// the mixed default existed) had no integrality anywhere: `x:Int ∧ x>3 ∧
/// x<4` was answered `sat` from the LP point `x = 3.5` – a wrong answer on
/// the most basic integer query, and the reason the *default* mode is mixed.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum ArithMode {
    Lra,
    Lia,
    Mixed,
}

impl Default for ArithSolver {
    fn default() -> Self {
        Self::new(false)
    }
}

/// What branch-and-bound may do with one integer variable (see
/// `ArithSolver::find_fractional_int_var`): exact branch bounds, or a value
/// that is neither readable nor branch-bounded (decline).
#[derive(Debug)]
enum FracVar {
    /// A fractional variable with EXACT branch bounds (floor/ceil of the
    /// exact value — from the narrow `DeltaRational`, or from the wide
    /// store's un-narrowed exact value).  The bounds are integral
    /// `BigRational`s: a bound beyond `i64` (the `2^63`-scale class that
    /// used to hit `Underivable`) stores exactly on the widened bound
    /// store, so the branch exists wherever the value does.
    Branch {
        var: VarId,
        floor: num_rational::BigRational,
        ceil: num_rational::BigRational,
    },
    /// No sound acceptance and no sound branch exist — the search must
    /// decline to `Unknown`.
    Underivable,
}

impl ArithSolver {
    /// Create a new arithmetic solver
    #[must_use]
    pub fn new(is_integer: bool) -> Self {
        Self::with_mode(if is_integer {
            ArithMode::Lia
        } else {
            ArithMode::Lra
        })
    }

    #[must_use]
    fn with_mode(mode: ArithMode) -> Self {
        Self {
            simplex: Simplex::new(),
            term_to_var: FxHashMap::default(),
            var_to_term: Vec::new(),
            reason_counter: 0,
            reasons: Vec::new(),
            mode,
            context_stack: Vec::new(),
            shared_equalities: Vec::new(),
            lia_model: FxHashMap::default(),
            int_equalities: Vec::new(),
            int_eq_verdict_cache: None,
            prop_lower: Vec::new(),
            prop_upper: Vec::new(),
            prop_undo: Vec::new(),
            int_vars: FxHashSet::default(),
            int_terms: FxHashSet::default(),
            bnb_used_reasons: FxHashSet::default(),
            cuts_in_split_scope: false,
            atom_rows: FxHashMap::default(),
            slack_forms: FxHashMap::default(),
        }
    }

    /// Create a new mixed-integer solver (`Int` and `Real` variables side by
    /// side, per-variable integrality – Z3's `theory_mi_arith`).
    #[must_use]
    pub fn mixed() -> Self {
        Self::with_mode(ArithMode::Mixed)
    }

    /// Create a new LRA solver
    #[must_use]
    pub fn lra() -> Self {
        Self::with_mode(ArithMode::Lra)
    }

    /// Create a new LIA solver
    #[must_use]
    pub fn lia() -> Self {
        Self::new(true)
    }

    /// Whether this solver performs *any* integer reasoning (LIA or mixed
    /// mode – i.e. branch-and-bound may run and integer-specific row
    /// reasoning is enabled).
    ///
    /// Callers that need "is THIS variable an integer" must consult the
    /// per-variable set instead: in mixed mode this is `true` while
    /// `Real`-sorted terms stay continuous.  [`ArithSolver::term_is_integer`]
    /// is the per-term query.
    #[must_use]
    pub fn is_integer(&self) -> bool {
        !matches!(self.mode, ArithMode::Lra)
    }

    /// Whether `term` is interned as an integer variable.  `false` for
    /// continuous (`Real`-sorted) terms and for terms never interned.
    #[must_use]
    pub fn term_is_integer(&self, term: TermId) -> bool {
        self.term_to_var
            .get(&term)
            .is_some_and(|&v| self.int_vars.contains(&v))
    }

    /// Diagnostic: reset the theory-combination probe counters.
    #[cfg(feature = "std")]
    pub fn diag_reset(&mut self) {
        super::simplex::diag::reset();
    }
    /// Diagnostic: print the theory-combination probe counters.
    #[cfg(feature = "std")]
    pub fn diag_print(&mut self) {
        super::simplex::diag::print();
    }
    /// Diagnostic: print timing shares against total solve wall-clock (ns).
    #[cfg(feature = "std")]
    pub fn diag_print_timing(&mut self, total_ns: u64) {
        super::simplex::diag::print_timing(total_ns);
    }

    /// Build the canonical [`RowKey`] for an assertion `Σ lhs·coef ~ rhs`.
    ///
    /// Canonical form: terms sorted by TermId with duplicate terms merged and
    /// zero coefficients dropped, constant `- rhs`, GCD-reduced (integer
    /// coefficients only), and – for equalities – sign-normalized so the
    /// first coefficient is positive (matching [`Self::normalize_expr`]).
    /// Comparison keys skip the sign step so the inequality direction is
    /// preserved (matching [`Self::normalize_ineq_expr`]).
    /// Negate every coefficient and the constant in place, returning
    /// `false` (with `terms` untouched) when any negation does not fit —
    /// the `i64::MIN`-numerator corner.  The un-flipped form is the SAME
    /// linear function, so skipping the flip loses only canonical-form
    /// sharing, never semantics; `row_key`'s sign normalization and
    /// `normalize_expr`'s use the same predicate so the key and the
    /// interned row stay consistent.
    fn try_flip_terms<T: Copy>(terms: &mut [(T, Rational64)], constant: &mut Rational64) -> bool {
        let mut flipped: Vec<Rational64> = Vec::with_capacity(terms.len());
        for (_, c) in terms.iter() {
            match checked_neg_r64(*c) {
                Some(n) => flipped.push(n),
                None => return false,
            }
        }
        let Some(nc) = checked_neg_r64(*constant) else {
            return false;
        };
        for ((_, c), n) in terms.iter_mut().zip(flipped) {
            *c = n;
        }
        *constant = nc;
        true
    }

    fn row_key(&self, lhs: &[(TermId, Rational64)], rhs: Rational64, equality: bool) -> RowKey {
        let mut terms: Vec<(TermId, Rational64)> = Vec::with_capacity(lhs.len());
        for &(term, coef) in lhs {
            if coef.is_zero() {
                continue;
            }
            match terms.binary_search_by_key(&term, |(t, _)| *t) {
                Ok(i) => terms[i].1 += coef,
                Err(i) => terms.insert(i, (term, coef)),
            }
        }
        terms.retain(|(_, c)| !c.is_zero());
        let mut constant = -rhs;

        // GCD reduction over integer TERM numerators (the constant is scaled
        // along), mirroring `normalize_expr`/`normalize_ineq_expr` so a key
        // hit implies the normalized LinExpr the row was built from is
        // identical.
        let all_integer = terms.iter().all(|(_, c)| c.denom() == &1);
        if self.is_integer() && all_integer && !terms.is_empty() {
            let g = terms
                .iter()
                .map(|(_, c)| c.numer().abs())
                .fold(0i64, |acc, n| if acc == 0 { n } else { gcd_i64(acc, n) });
            if g > 1 {
                let divisor = Rational64::from_integer(g);
                for (_, c) in &mut terms {
                    *c /= divisor;
                }
                constant /= divisor;
            }
        }

        // Sign normalization for equalities only (inequalities keep their
        // direction; see `normalize_ineq_expr`).  CHECKED: a coefficient or
        // constant at `i64::MIN` cannot be negated — skip the flip (the
        // key then matches the equally-unflipped row `normalize_expr`
        // builds; only canonical-form sharing is lost).
        if equality
            && let Some((_, c)) = terms.first()
            && c.is_negative()
        {
            Self::try_flip_terms(&mut terms, &mut constant);
        }

        RowKey { terms, constant }
    }

    /// Canonical key for a STRICT comparison's row: sorted/merged terms and
    /// constant with zero coefficients dropped – NO GCD division and NO sign
    /// flip, mirroring exactly what [`Self::cached_row_slack_strict`] interns
    /// (normalization would be value-preserving but a sign flip would reverse
    /// the strict inequality's direction, and the key must equal the row).
    fn row_key_strict(&self, lhs: &[(TermId, Rational64)], rhs: Rational64) -> RowKey {
        let mut terms: Vec<(TermId, Rational64)> = Vec::with_capacity(lhs.len());
        for &(term, coef) in lhs {
            if coef.is_zero() {
                continue;
            }
            match terms.binary_search_by_key(&term, |(t, _)| *t) {
                Ok(i) => terms[i].1 += coef,
                Err(i) => terms.insert(i, (term, coef)),
            }
        }
        terms.retain(|(_, c)| !c.is_zero());
        RowKey {
            terms,
            constant: -rhs,
        }
    }

    /// Return the slack variable whose tableau row defines the linear form
    /// keyed by `key`, interning the row on the first request.
    ///
    /// Every assertion of an atom over a linear form – either polarity, any
    /// decision level, any number of SAT re-sends – shares ONE row and
    /// differs only in the (trailed, pop-rewound) bound it sets on the slack.
    /// This is Z3's `lar_solver` row representation: the tableau is indexed
    /// by *distinct linear forms*, not by assertion events.  Sharing is
    /// content-addressed (the normalized `LinExpr` passed to
    /// [`Simplex::intern_row_cached`], whose `LinKey` is the canonical form
    /// with zero coefficients dropped), NOT keyed by TermId: two atoms over
    /// the same form really do constrain the same row, so a cache hit can
    /// never import a foreign constraint.
    ///
    /// (The historical TermId-keyed cache mentioned below was unsound for a
    /// different reason – it reused a slack *by atom identity* across scopes
    /// whose bounds had been popped, so the row carried stale side
    /// conditions.  Content addressing cannot do that: the row is a pure
    /// definition `slack = form`, and only the caller's own trailed bound
    /// ever constrains it.)
    fn cached_row_slack(
        &mut self,
        key: &RowKey,
        lhs: &[(TermId, Rational64)],
        rhs: Rational64,
        dir: SlackDir,
        reason: TermId,
    ) -> VarId {
        let _ = key;
        let equality = dir == SlackDir::Eq;
        let mut expr = LinExpr::new();
        for &(term, coef) in lhs {
            let var = self.intern(term);
            expr.add_term(var, coef);
        }
        expr.add_constant(-rhs);
        // Normalize exactly like the non-cached path did, so the interned
        // row is byte-for-byte what `add_le`/`add_eq` used to build.
        if equality {
            self.normalize_expr(&mut expr);
        } else {
            self.normalize_ineq_expr(&mut expr);
        }
        let integral = self.is_integral_form(&expr);
        let cache_key = (self.row_key(lhs, rhs, equality), reason);
        if let Some(&slack) = self.atom_rows.get(&cache_key)
            && self.simplex.row_defines_var(slack)
        {
            return slack;
        }
        let (slack, mode) = self.simplex.intern_row_reported(expr);
        if integral && self.intern_keeps_integrality(mode, slack) {
            self.int_vars.insert(slack);
        }
        self.slack_forms.insert(
            slack,
            SlackForm {
                lhs: lhs.to_vec(),
                rhs,
                dir,
                reason,
                exact: false,
            },
        );
        self.atom_rows.insert(cache_key, slack);
        slack
    }

    /// Re-establish a FEASIBLE, current assignment before model values are
    /// read after a `check()` that ended in `Sat`: the check's internal
    /// branch-and-bound unwinds its scopes AFTER accepting its leaf, and the
    /// persisted pivots can leave the raw LP point outside some bound
    /// windows — a stale or infeasible vector read by `value()` (for
    /// variables the accepted snapshot does not cover) publishes a model
    /// that violates asserted atoms.
    ///
    /// Returns `Some(conflict_terms)` when the live bound set is
    /// infeasible — the caller converts that into an honest conflict.
    pub fn ensure_feasible_or_conflict(&mut self) -> Option<Vec<TermId>> {
        if self.simplex.state_feasible() {
            return None;
        }
        match self.simplex.check() {
            Ok(()) => None,
            Err(reasons) => {
                let mut terms: Vec<TermId> = Vec::with_capacity(reasons.len());
                for r in reasons {
                    if let Some(&t) = self.reasons.get(r as usize) {
                        terms.push(t);
                    }
                }
                if terms.is_empty() {
                    terms.extend(self.full_unsat_core());
                }
                Some(terms)
            }
        }
    }

    /// Re-home stranded row bounds: a slack that once defined a row
    /// (`slack_forms`) but no longer does (`row_defines_var` false — a pivot
    /// consumed its defining row) while still carrying bounds leaves those
    /// bounds constraining a FREE-floating variable: the semantic constraint
    /// on the linear form is silently dropped from the live system, and a
    /// model accepted over that system violates the asserted atom (the
    /// QF_ANIA/sum10 invalid-model class, exposed once the per-final-check
    /// reset+replay — which re-homed every atom by re-assertion — was
    /// replaced by the restart rebuild).
    ///
    /// # Soundness gates (the item-69 false-`unsat` fix)
    ///
    /// The historical sweep re-interned the recorded form and copied the
    /// old slack's CURRENT bound values onto the fresh row (`copy_bounds`,
    /// since removed).  That copy was sound only under the assumption
    /// `fresh ≡ old`, which stranding breaks from BOTH ends:
    ///
    /// * **The fresh row is the form rendered through the CURRENT tableau,
    ///   not a copy of the old slack.**  After a pivot consumed the old
    ///   row, later rows may have been substituted through the old slack,
    ///   and the rendering can resolve the form as a MULTIPLE of the old
    ///   slack itself — the observed case rendered `form ≡ (20/7)·old`
    ///   while `old`'s live (propagated) pin said `old = 7/20`.  Copying
    ///   the pin value-for-value then asserted `(20/7)·old = 7/20` — a
    ///   constraint nobody ever derived — which crossed the sound
    ///   derivation `old = 7/20` and produced a SINGLETON conflict blaming
    ///   one Euclidean `div`/`mod` axiom, i.e. a learned unit `¬axiom` and
    ///   a false `unsat` (the seed-20261102 mixed-fuzz core,
    ///   `docs/studies/assets/2026-09-18/`; the completion of study
    ///   item 70's decode — the rescale factor item 70 fingered was
    ///   dropped by exactly this value copy).  The re-intern itself is
    ///   sound (the fresh row is substitution-derived from live rows); only
    ///   carrying bound VALUES across the stranding boundary was not.
    ///
    /// * **Only the atom's OWN bound may be re-asserted.**  A bound is only
    ///   translatable to the fresh row when its justification is the
    ///   recorded atom itself, because the fresh row is that atom's form:
    ///   the atom's assertion is exactly `slack ∘ 0` on it, a value-free
    ///   statement.  A TIGHTER bound on the old slack (a propagated pin,
    ///   justified through rows that expressed the form via the old slack)
    ///   has both a value and a justification tied to the OLD variable's
    ///   coordinates; moving either fabricates.  If the atom's own bound is
    ///   not live on the old slack, the atom is not currently asserted and
    ///   re-asserting it would constrain the search with a dead literal.
    ///
    /// So the sweep now: (1) re-interns the recorded form (unchanged — the
    /// restoration IS load-bearing; the `parity_infeasibility` and
    /// `bnb_dead_leaf` regressions pin that even a slack still referenced
    /// by narrow rows can have its constraint dropped from the live LP);
    /// (2) re-asserts ONLY the atom's own `∘ 0` bound — scale-invariant,
    /// so it carries soundly onto any rescaled rendering — and only when a
    /// live bound on the old slack carries the recorded atom's reason (a
    /// dead atom is never re-imposed).  Returns how many constraints were
    /// re-homed; the caller re-checks feasibility when it is non-zero.
    ///
    /// Scope note: the re-homed bounds live at the CURRENT scope, while the
    /// stranded originals stay trailed at their own (possibly shallower)
    /// scopes.  A backtrack past the re-homing scope re-strands the
    /// constraint until the next call — callers must run this before every
    /// feasibility decision that can accept a model, which `final_check`
    /// does.
    pub fn rehome_stranded_row_bounds(&mut self) -> usize {
        let stranded: Vec<VarId> = self
            .slack_forms
            .keys()
            .copied()
            .filter(|&slack| {
                self.simplex.has_any_bound(slack) && !self.simplex.row_defines_var(slack)
            })
            .collect();
        let n = stranded.len();
        #[cfg(feature = "std")]
        if std::env::var("NIXIE_REHOME_TRACE").is_ok() && n > 0 {
            eprintln!("[rehome] {n} stranded");
        }
        let mut rehomed = 0usize;
        for old in stranded {
            let Some(form) = self.slack_forms.get(&old).cloned() else {
                continue;
            };
            // Gate 1: still a column of a NARROW row — the bounds constrain
            // the system through that live equation; nothing to restore, and
            // a re-intern can fabricate (see the doc comment).  Wide-store
            // references do NOT count: the wide side table is invisible to
            // pivoting and LP feasibility, so a wide-referenced slack's
            // constraint is genuinely dropped and must be re-homed.
            // Gate: the atom's own bound must be live on the old slack.
            // A bound's reason ids stay mapped to their terms for as long
            // as the bound itself is live (bounds and reasons are undone by
            // the same pops), so a reason id resolving to the recorded
            // atom term is a live assertion of exactly that atom.
            let atom_live = |bounds: Option<&Bound>| -> Option<u32> {
                bounds?
                    .all_reasons()
                    .find(|&r| self.reasons.get(r as usize).copied() == Some(form.reason))
            };
            let lo_atom = atom_live(self.simplex.get_lower(old));
            let hi_atom = atom_live(self.simplex.get_upper(old));
            let (want_lower, want_upper) = match form.dir {
                SlackDir::Le | SlackDir::Lt => (false, hi_atom.is_some()),
                SlackDir::Ge | SlackDir::Gt => (lo_atom.is_some(), false),
                SlackDir::Eq => (lo_atom.is_some(), hi_atom.is_some()),
            };
            if !want_lower && !want_upper {
                continue; // the atom's own assertion is not live: restore nothing
            }
            // Re-intern through the SAME path that built the row: the
            // strict dirs must not run the equality/inequality normalizer's
            // sign flip (it would reverse a strict bound's direction), so
            // they rebuild exactly `lhs - rhs` like the delta paths did.
            let fresh = if form.exact {
                // The row was interned EXACTLY (`-rhs` beyond width): the
                // narrow re-intern below would build `-rhs` with the
                // UNCHECKED negation and wrap to a different row.  Route
                // through the same exact path that built it.
                self.intern_exact_row(&form.lhs, form.rhs, form.dir, form.reason)
            } else {
                match form.dir {
                    SlackDir::Lt | SlackDir::Gt => {
                        let key = self.row_key(&form.lhs, form.rhs, false);
                        self.cached_row_slack_strict(
                            &key,
                            &form.lhs,
                            form.rhs,
                            form.dir,
                            form.reason,
                        )
                    }
                    SlackDir::Le | SlackDir::Ge | SlackDir::Eq => {
                        let key = self.row_key(&form.lhs, form.rhs, form.dir == SlackDir::Eq);
                        self.cached_row_slack(&key, &form.lhs, form.rhs, form.dir, form.reason)
                    }
                }
            };
            if fresh == old {
                continue;
            }
            // The re-asserted bound VALUE is exactly the atom's own `∘ 0`:
            // the fresh slack is the recorded form, so this says precisely
            // what the atom said when it was first asserted.  The reason id
            // is one already live for this atom (never a recycled id).  The
            // `if let`s keep that invariant structural: no arm can fire
            // without the matching live atom reason in hand.
            let mut moved = false;
            // Strict atoms re-assert STRICT zero bounds (`slack < 0` /
            // `slack > 0`, the delta encoding) — matching the original
            // assertion exactly, never a weakened `<= 0` / `>= 0`.
            // The WEAK side is never written (the item-76 discipline): a
            // live tighter bound on the fresh row SUBSUMES the atom's own
            // zero bound (both constrain the same variable), so keeping it
            // is sound and writing under it would silently drop a
            // constraint the propagated bound carried.
            let zero = DeltaRational::from_rational(Rational64::zero());
            if want_lower
                && let Some(id) = lo_atom
                && self.simplex.get_lower(fresh).is_none_or(|b| {
                    BoundValue::Narrow(zero).cmp_value(&b.value) != core::cmp::Ordering::Less
                })
            {
                match form.dir {
                    SlackDir::Gt => self.simplex.set_strict_lower(fresh, Rational64::zero(), id),
                    _ => self.simplex.set_lower(fresh, Rational64::zero(), id),
                }
                moved = true;
            }
            if want_upper
                && let Some(id) = hi_atom
                && self.simplex.get_upper(fresh).is_none_or(|b| {
                    BoundValue::Narrow(zero).cmp_value(&b.value) != core::cmp::Ordering::Greater
                })
            {
                match form.dir {
                    SlackDir::Lt => self.simplex.set_strict_upper(fresh, Rational64::zero(), id),
                    _ => self.simplex.set_upper(fresh, Rational64::zero(), id),
                }
                moved = true;
            }
            if moved {
                rehomed += 1;
            }
        }
        rehomed
    }

    /// Like [`Self::cached_row_slack`] for strict comparisons: no
    /// normalization is applied when building the row (GCD division is
    /// value-preserving, but `normalize_expr`'s sign flip would reverse a
    /// strict inequality's direction), so the interned row is exactly
    /// `lhs - rhs` as given.
    fn cached_row_slack_strict(
        &mut self,
        key: &RowKey,
        lhs: &[(TermId, Rational64)],
        rhs: Rational64,
        dir: SlackDir,
        reason: TermId,
    ) -> VarId {
        let _ = key;
        let mut expr = LinExpr::new();
        for &(term, coef) in lhs {
            let var = self.intern(term);
            expr.add_term(var, coef);
        }
        expr.add_constant(-rhs);
        // Canonical integer rescaling, same as the non-strict path: the
        // factor is strictly positive, so neither the strict direction nor
        // the δ-encoding's satisfiability-equivalence is affected (a
        // positive rescaling of a row rescales its δ magnitudes, which the
        // ℚ[ε] framework admits – see `canonicalize_lin_form`).  Only the
        // SIGN-FLIP half of `normalize_expr` is forbidden here, and it is
        // not applied.
        super::simplex::canonicalize_lin_form(&mut expr.terms, &mut expr.constant);
        let integral = self.is_integral_form(&expr);
        let cache_key = (self.row_key_strict(lhs, rhs), reason);
        if let Some(&slack) = self.atom_rows.get(&cache_key)
            && self.simplex.row_defines_var(slack)
        {
            return slack;
        }
        let (slack, mode) = self.simplex.intern_row_reported(expr);
        if integral && self.intern_keeps_integrality(mode, slack) {
            self.int_vars.insert(slack);
        }
        // Recorded for the stranded-bound re-homing sweep like the
        // non-strict rows: a strict atom's row can be consumed by a pivot
        // exactly like any other, and its `slack < 0` bound then constrains
        // a free-floating variable — the constraint is dropped from the
        // live LP until the sweep re-asserts it.
        self.slack_forms.insert(
            slack,
            SlackForm {
                lhs: lhs.to_vec(),
                rhs,
                dir,
                reason,
                exact: false,
            },
        );
        self.atom_rows.insert(cache_key, slack);
        slack
    }

    /// Intern a term as a variable
    pub fn intern(&mut self, term: TermId) -> VarId {
        if let Some(&var) = self.term_to_var.get(&term) {
            return var;
        }

        let var = self.simplex.new_var();
        // In LIA mode every interned term is Int-sorted, so every term
        // variable is integer-valued in every model.  The Gomory-cut
        // generator's integrality test and the branch-variable scan rely on
        // this set containing them.  Mixed mode does NOT blanket-mark here:
        // the sort of the term is not visible at this call site.  It marks
        // explicitly through [`Self::intern_integer`], which ALSO records the
        // term in [`Self::int_terms`] so the mark survives `reset()` – the
        // theory layer rebuilds its tableau from scratch on restarts and
        // replays literals through the sort-blind `assert_*` paths, and a
        // mark that lived only in the per-variable set would be lost to that
        // replay (re-interning `x:Int` as continuous).  An unmarked variable
        // is treated as continuous – the sound default (a relaxation).
        if matches!(self.mode, ArithMode::Lia)
            || (!matches!(self.mode, ArithMode::Lra) && self.int_terms.contains(&term))
        {
            self.int_vars.insert(var);
        }
        self.term_to_var.insert(term, var);
        self.var_to_term.push(term);
        var
    }

    /// Intern `term` as an **integer** variable.
    ///
    /// The caller must know the term is `Int`-sorted (or, for the
    /// bit-vector-as-bounded-integer encoding, that its values are
    /// integral).  In LIA mode this is identical to [`Self::intern`]; in
    /// mixed mode it is what puts the variable into the integer-variable set so
    /// Gomory cuts and branch-and-bound close its integrality gap; in LRA
    /// mode it behaves as [`Self::intern`] (the mode is a contract that no
    /// integer term appears; if one does anyway, marking it would only make
    /// the solver *more* exact, so the mark is kept for safety).
    ///
    /// The term is remembered in the integer-term registry, so a later plain
    /// [`Self::intern`] of the same term (e.g. from the theory layer's
    /// reset/replay) re-marks the fresh variable integer.
    pub fn intern_integer(&mut self, term: TermId) -> VarId {
        let var = self.intern(term);
        self.int_terms.insert(term);
        if !matches!(self.mode, ArithMode::Lra) {
            self.int_vars.insert(var);
        }
        var
    }

    /// Pin an integer-constant COLUMN to its exact value: the big-const
    /// abstraction (encode synthesizes a fresh free column for a folded
    /// constant that leaves `Rational64` width in every orientation — no
    /// λ can shrink a numerator, so powers of two only ever fix
    /// denominator width) historically left that column FLOATING.  A
    /// floating constant column makes the abstracted system a relaxation
    /// of the original: refutations stayed sound (an abstract conflict
    /// holds for every column value, in particular the constant's true
    /// value) but every `sat` rested on certification, and a model whose
    /// column drifted answered `unknown` after the evaluator refuted it
    /// (the gap survey's floating-constant slice).  The wide bound store
    /// (any width, exact comparisons) can carry the TRUE value as a
    /// singleton bound, which turns the abstraction into an exact
    /// representation: the column is the constant, at every scope where
    /// an atom using it is asserted.
    ///
    /// The reason is the constant term ITSELF, registered by the caller as
    /// a theory tautology (`a constant equals itself in every model`), so a
    /// conflict explanation citing the pin drops it from the learned
    /// clause knowingly — the clause stays entailed by the asserted atoms.
    ///
    /// Idempotent by BOUND INSPECTION, not a memo: bounds pop with the
    /// scope that asserted them, and the next assert of an atom using the
    /// column re-pins — a memo would skip that re-pin after a pop and let
    /// the column float again (the exact hazard this pin retires).
    pub fn pin_int_const(&mut self, term: TermId, value: num_rational::BigRational) {
        use super::delta::BigDeltaRational;
        let var = self.intern(term);
        let exact = BigDeltaRational::real_only(value);
        let already_pinned = self
            .simplex
            .get_lower(var)
            .is_some_and(|b| b.value.cmp_big(&exact) == core::cmp::Ordering::Equal)
            && self
                .simplex
                .get_upper(var)
                .is_some_and(|b| b.value.cmp_big(&exact) == core::cmp::Ordering::Equal);
        if already_pinned {
            return;
        }
        let id = self.add_reason(term);
        self.simplex
            .set_lower_exact(var, exact.clone(), smallvec::smallvec![id]);
        self.simplex
            .set_upper_exact(var, exact, smallvec::smallvec![id]);
    }

    /// Whether every variable of `lhs` is a known-integer variable and every
    /// coefficient integral, so the linear form takes only integer values.
    /// Terms are interned first (idempotent) so the check never fails on a
    /// not-yet-interned term.
    fn lhs_is_integral(&mut self, lhs: &[(TermId, Rational64)]) -> bool {
        for (term, coef) in lhs {
            if coef.denom() != &1 {
                return false;
            }
            let var = self.intern(*term);
            if !self.int_vars.contains(&var) {
                return false;
            }
        }
        true
    }

    /// Whether `expr` is integer-valued in every model: integer constant,
    /// integer coefficients and every referenced variable known-integer.
    /// Used to decide whether a fresh row slack is an integer variable.
    fn is_integral_form(&self, expr: &LinExpr) -> bool {
        expr.constant.denom() == &1
            && expr
                .terms
                .iter()
                .all(|(v, c)| c.denom() == &1 && self.int_vars.contains(v))
    }

    /// Whether an interned row's slack may be integer-marked given HOW the
    /// intern produced it.  [`RowInternMode::Exact`] keeps the requested
    /// linear function (GCD canonicalization and basic-variable
    /// substitution are function-preserving, and the GCD division of an
    /// integral form stays integral), so an integral requested form makes
    /// the slack integer-valued.  [`RowInternMode::Rescaled`] defines the
    /// slack as `form / λ` for a positive width factor: the zero-bound
    /// constraints are unchanged, but integrality is NOT transferred —
    /// `3·2^62 + 1` rescaled by `1/52` takes value `1/52`.  The slack is
    /// integer-valued exactly when the RESCALED row is itself an integral
    /// form, which is checked directly here (the row is fresh: nothing
    /// pivots between the intern and this call).
    ///
    /// Why this matters: `gomory_cut` sources cuts from integer-marked
    /// tableau basics and `lia_branch_and_bound` splits
    /// `x ≤ ⌊x̄⌋ ∨ x ≥ ⌈x̄⌉` on them — both reason from `slack ∈ ℤ`, so a
    /// rescaled slack wrongly marked integer fabricates divisibility
    /// constraints (a Gomory cut over `(1 - s)/52` asserted `1 - s ≡ 0
    /// (mod 52)` with the axiom's own reason and refuted a `sat` goal:
    /// the arithmetic arc's item-54 false `unsat`).
    fn intern_keeps_integrality(&self, mode: RowInternMode, slack: VarId) -> bool {
        match mode {
            RowInternMode::Exact => true,
            RowInternMode::Rescaled => match self.simplex.defining_row(slack) {
                Some(row) => self.is_integral_form(row),
                None => false,
            },
        }
    }

    /// Add a reason and return its ID
    fn add_reason(&mut self, term: TermId) -> u32 {
        let id = self.reason_counter;
        self.reason_counter += 1;
        self.reasons.push(term);
        id
    }

    /// Normalize a linear expression
    ///
    /// Normalization performs:
    /// 1. Coefficient reduction: divide by GCD of all coefficients
    /// 2. Sorting: order terms by variable ID for canonical form
    /// 3. Sign normalization: ensure first coefficient (after sorting) is positive
    ///
    /// IMPORTANT: Step 3 is only safe for symmetric constraints (equalities).
    /// For inequalities (Le/Ge), sign normalization flips the direction and must
    /// NOT be applied.  Call `normalize_expr_no_sign` for those cases instead.
    fn normalize_expr(&self, expr: &mut LinExpr) {
        if expr.terms.is_empty() {
            return;
        }

        // Canonical integer rescaling (positive factor, both modes): keeps
        // large-constant assertions (e.g. every coefficient a multiple of
        // 10⁹) out of exact-rational pivot overflow.  Previously integer-mode
        // only, which left real-mode rows raw – the scaled `gap` LRA twins
        // overflowed `i64` pivots and bailed to `Unknown` (obligation fuzzer
        // finding 5; see `canonicalize_lin_form` for the soundness notes).
        super::simplex::canonicalize_lin_form(&mut expr.terms, &mut expr.constant);

        // Ensure first coefficient is positive — CHECKED: at an `i64::MIN`
        // coefficient or constant the negation does not fit; skipping the
        // flip keeps the same linear function (only the canonical form is
        // lost) and matches `row_key`'s identically-guarded flip.
        if let Some((_, c)) = expr.terms.first()
            && c.is_negative()
        {
            Self::try_flip_terms(&mut expr.terms, &mut expr.constant);
        }

        // Sort terms by variable ID for canonical form
        expr.terms.sort_by_key(|(v, _)| *v);
    }

    /// Normalize for inequalities: GCD reduction and sorting only.
    ///
    /// Sign normalization is deliberately omitted because negating an inequality
    /// expression reverses its direction (e.g., fa - fb <= 0 becomes fb - fa <= 0,
    /// which represents the opposite constraint fa >= fb).
    fn normalize_ineq_expr(&self, expr: &mut LinExpr) {
        if expr.terms.is_empty() {
            return;
        }

        // Canonical integer rescaling (positive factor, both modes) – same
        // rationale as `normalize_expr`, sign-preserving by construction.
        super::simplex::canonicalize_lin_form(&mut expr.terms, &mut expr.constant);

        // Sort terms by variable ID – safe because sorting doesn't change the sign
        // of the overall expression for inequalities (we don't negate afterwards).
        // NOTE: Sorting alone is also problematic because it reorders terms but the
        // sign is determined by all terms together.  We keep the sort for consistent
        // canonical form but do NOT apply the sign-flip step.
        expr.terms.sort_by_key(|(v, _)| *v);
    }

    /// Ensure the propagation-bound arrays cover `var`.
    fn prop_ensure(&mut self, var: VarId) {
        let idx = var as usize;
        if idx >= self.prop_lower.len() {
            self.prop_lower.resize(idx + 1, None);
            self.prop_upper.resize(idx + 1, None);
        }
    }

    /// Record a propagation lower bound `var ≥ value` (with `reason`), keeping
    /// the tightest (monotonic).  Sound: a valid consequence of one atom.
    fn prop_set_lower(&mut self, var: VarId, value: DeltaRational, reason: u32) {
        self.prop_ensure(var);
        let idx = var as usize;
        let tighten = match self.prop_lower[idx] {
            None => true,
            Some(cur) => value > cur.value,
        };
        if tighten {
            self.prop_undo
                .push(PropBoundUndo::Lower(var, self.prop_lower[idx]));
            self.prop_lower[idx] = Some(PropBoundEntry { value, reason });
        }
    }

    /// Record a propagation upper bound `var ≤ value` (with `reason`), keeping
    /// the tightest (monotonic).  Sound: a valid consequence of one atom.
    fn prop_set_upper(&mut self, var: VarId, value: DeltaRational, reason: u32) {
        self.prop_ensure(var);
        let idx = var as usize;
        let tighten = match self.prop_upper[idx] {
            None => true,
            Some(cur) => value < cur.value,
        };
        if tighten {
            self.prop_undo
                .push(PropBoundUndo::Upper(var, self.prop_upper[idx]));
            self.prop_upper[idx] = Some(PropBoundEntry { value, reason });
        }
    }

    /// Propagation lower bound for `var`, if any.
    fn prop_get_lower(&self, var: VarId) -> Option<PropBoundEntry> {
        self.prop_lower.get(var as usize).copied().flatten()
    }

    /// Propagation upper bound for `var`, if any.
    fn prop_get_upper(&self, var: VarId) -> Option<PropBoundEntry> {
        self.prop_upper.get(var as usize).copied().flatten()
    }

    /// Record the single-variable constant bound implied by a one-term LHS
    /// `coef·x ◦ rhs` on its variable `x`, where the comparison is given by
    /// `kind` and a δ gap encodes strict (`Lt`/`Gt`) bounds for LRA (LIA
    /// strict bounds are already folded to non-strict `±1` by the callers).
    ///
    /// No-op for `coef == 0`.  SOUND: a direct consequence of one atom.
    fn record_prop_bound(
        &mut self,
        var: VarId,
        coef: Rational64,
        rhs: Rational64,
        kind: PropCmp,
        reason: u32,
    ) {
        if coef.is_zero() {
            return;
        }
        // bound on x:  coef·x ◦ rhs  ⟺  x ◦' rhs/coef  (comparison flips when coef<0).
        // Checked: the division can leave `i64` width (fractional row
        // coefficients against near-`i64::MAX` bounds — the scaled pin
        // rows produce exactly that shape), and propagation is an
        // OPTIMIZATION: declining to record a bound that does not fit
        // costs completeness only, never soundness.  Unchecked, it wrapped
        // in release and propagated a fabricated bound.
        use num_traits::CheckedDiv;
        let Some(ratio) = rhs.checked_div(&coef) else {
            return;
        };
        let flip = coef.is_negative();
        match kind {
            PropCmp::Le => {
                // coef·x ≤ rhs
                if flip {
                    self.prop_set_lower(var, DeltaRational::from_rational(ratio), reason);
                } else {
                    self.prop_set_upper(var, DeltaRational::from_rational(ratio), reason);
                }
            }
            PropCmp::Ge => {
                // coef·x ≥ rhs
                if flip {
                    self.prop_set_upper(var, DeltaRational::from_rational(ratio), reason);
                } else {
                    self.prop_set_lower(var, DeltaRational::from_rational(ratio), reason);
                }
            }
            PropCmp::Lt => {
                // coef·x < rhs
                if flip {
                    // x > ratio  ⇒  lower (ratio, +δ)
                    self.prop_set_lower(var, DeltaRational::new(ratio, Rational64::one()), reason);
                } else {
                    // x < ratio  ⇒  upper (ratio, -δ)
                    self.prop_set_upper(var, DeltaRational::new(ratio, -Rational64::one()), reason);
                }
            }
            PropCmp::Gt => {
                // coef·x > rhs
                if flip {
                    // x < ratio  ⇒  upper (ratio, -δ)
                    self.prop_set_upper(var, DeltaRational::new(ratio, -Rational64::one()), reason);
                } else {
                    // x > ratio  ⇒  lower (ratio, +δ)
                    self.prop_set_lower(var, DeltaRational::new(ratio, Rational64::one()), reason);
                }
            }
        }
    }

    /// Debug-only (NIXIE_SCAN_VIOL): one-line description of a term's current
    /// arithmetic state – simplex var id, model value, lower/upper bounds,
    /// and whether the integral B&B snapshot supplies the value.
    #[cfg(debug_assertions)]
    pub fn debug_describe_term(&self, t: TermId) -> Option<String> {
        let &var = self.term_to_var.get(&t)?;
        let val = self.value(t);
        let lo = self
            .simplex
            .get_lower(var)
            .map(|b| format!("{:?}", b.value.narrow().map(|v| v.real)));
        let hi = self
            .simplex
            .get_upper(var)
            .map(|b| format!("{:?}", b.value.narrow().map(|v| v.real)));
        Some(format!(
            "{t:?}/v{var} val={val:?} lo={lo:?} hi={hi:?} lia_model={}",
            self.lia_model.contains_key(&var)
        ))
    }

    /// The EXACT-intern arm shared by every `assert_*` entry whose `-rhs`
    /// does not fit `Rational64` (`rhs = i64::MIN`): the row `lhs - rhs`
    /// is built exactly in `BigRational` and interned through the shared
    /// rescale-or-capture discipline (`Simplex::intern_row_big_reported`) —
    /// a positive rescale into width keeps the FULL narrow machinery, a
    /// row beyond any scaling is captured exactly in the wide store with
    /// its zero-bound constraint intact.  The slack's `SlackForm` records
    /// the exact path so the stranded-bound sweep re-interns through it
    /// (the narrow re-intern's `-rhs` would wrap to a DIFFERENT row — the
    /// pre-fix release hazard this replaces).  This retires the former
    /// sticky-decline guard: the constraint is now represented wherever
    /// width allows and captured exactly otherwise, so no verdict is owed
    /// to a silent drop.
    fn intern_exact_row(
        &mut self,
        lhs: &[(TermId, Rational64)],
        rhs: Rational64,
        dir: SlackDir,
        reason: TermId,
    ) -> VarId {
        let mut big = super::simplex::BigLinExpr {
            constant: num_rational::BigRational::new(
                -num_bigint::BigInt::from(*rhs.numer()),
                num_bigint::BigInt::from(*rhs.denom()),
            ),
            terms: Vec::new(),
        };
        // The integrality of the REQUESTED form (mirrors
        // `is_integral_form` over the exact row): every coefficient
        // integral, every referenced variable integer-valued, and the
        // constant (`-rhs`) integral.
        let mut integral_requested = big.constant.denom() == &num_bigint::BigInt::from(1);
        for &(term, coef) in lhs {
            if coef.is_zero() {
                continue;
            }
            let var = self.intern(term);
            if coef.denom() != &1 || !self.int_vars.contains(&var) {
                integral_requested = false;
            }
            let cb = num_rational::BigRational::new(
                num_bigint::BigInt::from(*coef.numer()),
                num_bigint::BigInt::from(*coef.denom()),
            );
            match big.terms.iter_mut().find(|(v, _)| *v == var) {
                Some(slot) => slot.1 += cb,
                None => big.terms.push((var, cb)),
            }
        }
        let reason_id = self.add_reason(reason);
        let (slack, mode) = self.simplex.intern_row_big_reported(big);
        if integral_requested && self.intern_keeps_integrality(mode, slack) {
            self.int_vars.insert(slack);
        }
        self.slack_forms.insert(
            slack,
            SlackForm {
                lhs: lhs.to_vec(),
                rhs,
                dir,
                reason,
                exact: true,
            },
        );
        let _ = reason_id;
        slack
    }

    /// Assert: lhs <= rhs
    pub fn assert_le(&mut self, lhs: &[(TermId, Rational64)], rhs: Rational64, reason: TermId) {
        // `-rhs` beyond `Rational64` (the `i64::MIN` corner): the row is
        // interned EXACTLY (rescaled into width or captured in the wide
        // store) instead of declined — the constraint is represented, not
        // dropped (the wide-LP build retiring the sticky decline).
        if checked_neg_r64(rhs).is_none() {
            let slack = self.intern_exact_row(lhs, rhs, SlackDir::Le, reason);
            let reason_id = self.add_reason(reason);
            self.simplex.set_upper(slack, Rational64::zero(), reason_id);
            return;
        }
        let mut expr = LinExpr::new();
        let mut single: Option<(VarId, Rational64)> = None;
        for (term, coef) in lhs {
            let var = self.intern(*term);
            expr.add_term(var, *coef);
            single = match single {
                None => Some((var, *coef)),
                Some(_) => None, // more than one term
            };
        }
        let _ = &mut expr;

        let reason_id = self.add_reason(reason);
        // One shared, interned row per linear form; the assertion itself is
        // just the bound `slack <= 0` on it.
        let key = self.row_key(lhs, rhs, false);
        let slack = self.cached_row_slack(&key, lhs, rhs, SlackDir::Le, reason);
        self.simplex.set_upper(slack, Rational64::zero(), reason_id);
        if let Some((var, coef)) = single {
            self.record_prop_bound(var, coef, rhs, PropCmp::Le, reason_id);
        }
    }

    /// Assert: lhs >= rhs
    pub fn assert_ge(&mut self, lhs: &[(TermId, Rational64)], rhs: Rational64, reason: TermId) {
        // `-rhs` beyond `Rational64`: exact intern (see `assert_le`).
        if checked_neg_r64(rhs).is_none() {
            let slack = self.intern_exact_row(lhs, rhs, SlackDir::Ge, reason);
            let reason_id = self.add_reason(reason);
            self.simplex.set_lower(slack, Rational64::zero(), reason_id);
            return;
        }
        let mut expr = LinExpr::new();
        let mut single: Option<(VarId, Rational64)> = None;
        for (term, coef) in lhs {
            let var = self.intern(*term);
            expr.add_term(var, *coef);
            single = match single {
                None => Some((var, *coef)),
                Some(_) => None,
            };
        }
        let _ = &mut expr;

        let reason_id = self.add_reason(reason);
        let key = self.row_key(lhs, rhs, false);
        let slack = self.cached_row_slack(&key, lhs, rhs, SlackDir::Ge, reason);
        self.simplex.set_lower(slack, Rational64::zero(), reason_id);
        if let Some((var, coef)) = single {
            self.record_prop_bound(var, coef, rhs, PropCmp::Ge, reason_id);
        }
    }

    /// Assert: lhs = rhs
    ///
    /// For integer arithmetic (LIA), checks GCD-based infeasibility:
    /// If all coefficients share a common GCD that doesn't divide the RHS,
    /// the constraint is infeasible over integers.
    ///
    /// Example: 2x + 2y = 7 is infeasible because gcd(2,2) = 2 doesn't divide 7.
    pub fn assert_eq(&mut self, lhs: &[(TermId, Rational64)], rhs: Rational64, reason: TermId) {
        // `-rhs` beyond `Rational64`: exact intern (see `assert_le`).  The
        // narrow-only GCD/Diophantine bookkeeping below is SKIPPED for the
        // exact row (its `i64` coefficient/constant reads would wrap);
        // those feeds are optimizations — the LP refutes the same
        // constraints through the interned row.
        if checked_neg_r64(rhs).is_none() {
            let slack = self.intern_exact_row(lhs, rhs, SlackDir::Eq, reason);
            let reason_id = self.add_reason(reason);
            self.simplex.set_lower(slack, Rational64::zero(), reason_id);
            self.simplex.set_upper(slack, Rational64::zero(), reason_id);
            return;
        }
        // Compute the row key up front: the LIA Diophantine bookkeeping below
        // is only performed for the FIRST assertion of this linear form at
        // the current scope (re-assertions set the same bounds again and
        // would otherwise duplicate `int_equalities` entries).
        let lia_key = self.row_key(lhs, rhs, true);
        // Diophantine bookkeeping: record on every assertion, exactly like
        // the pre-row-cache code (duplicate entries are harmless – the
        // feasibility check is memoized over the list).  Do NOT gate on
        // row-cache presence: with scoped rows, a pop removes the row (and
        // the ArithSolver cache entry goes stale) while `int_equalities` was
        // truncated by the same pop, so the next assertion must re-record.
        let lia_is_new = true;
        let mut expr = LinExpr::new();
        for (term, coef) in lhs {
            let var = self.intern(*term);
            expr.add_term(var, *coef);
        }
        expr.add_constant(-rhs);

        // For LIA, check GCD-based infeasibility BEFORE normalization
        // (normalization divides by GCD, which would lose the infeasibility signal).
        // Only for the first assertion of this form at this scope: a
        // re-assertion's contradictory bounds are already live.
        //
        // The guard is PER-ROW, not per-mode: the row's reasoning (GCD
        // divisibility, "integral lhs ≠ fractional rhs ⇒ infeasible") needs
        // every coefficient integral AND every variable known-integer.  In
        // mixed mode a row over `Real` variables satisfies neither, and
        // applying the integer argument to it would fabricate infeasibility
        // that does not exist (`0.5·y = 1.2` has the solution `y = 2.4`).
        let row_integer = self.is_integer()
            && expr
                .terms
                .iter()
                .all(|&(v, c)| c.denom() == &1 && self.int_vars.contains(&v));
        if row_integer && lia_is_new {
            // Extract integer coefficients
            let coeffs: Vec<i64> = expr
                .terms
                .iter()
                .filter_map(|(_, c)| {
                    if c.denom() == &1 {
                        Some(*c.numer())
                    } else {
                        None
                    }
                })
                .collect();

            // Extract the constant (which is -rhs in expr = 0 form)
            let const_term = if expr.constant.denom() == &1 {
                -*expr.constant.numer()
            } else {
                // Non-integer constant in equality - infeasible for integers.
                // Attribute the contradiction to the actual assertion that
                // caused it (not a hardcoded/arbitrary reason id), so the
                // resulting unsat core cites the real culprit.
                //
                // An EMPTY row (`0 = c`, `c` fractional — every coefficient
                // cancelled, e.g. `xr - xr` under a `/`-linearization) has
                // no variable to plant the crossed bounds on: it used to
                // plant NOTHING and silently DROP the equality, leaving the
                // atom a free Boolean and reporting `sat` for `0 = 5/3`.
                // A var-free infeasible row gets a fresh witness variable
                // instead — the crossed bounds `[1, 0]` refute regardless.
                let reason_id = self.add_reason(reason);
                let victim = expr
                    .terms
                    .first()
                    .map(|&(v, _)| v)
                    .unwrap_or_else(|| self.simplex.new_var());
                self.simplex
                    .set_lower(victim, Rational64::from_integer(1), reason_id);
                self.simplex
                    .set_upper(victim, Rational64::from_integer(0), reason_id);
                return;
            };

            // Check GCD infeasibility if all coefficients are integers
            if !coeffs.is_empty() && coeffs.len() == expr.terms.len() {
                // Compute GCD of all coefficients — on the RAW form, so the
                // divisibility test below sees the original magnitudes.
                let g = coeffs.iter().fold(0i64, |acc, &c| gcd_i64(acc, c.abs()));

                // Record the integer equality (sum a_i·x_i = const_term),
                // rescaled by gcd(coefficients ∪ {rhs}) so the Hermite view
                // gets minimal magnitudes: a scaled `gap` system (all
                // constants multiples of 10⁹) is recorded as its small-integer
                // core instead of tripping the 2⁴⁰ `i128` magnitude guard.
                // The division is exact and the factor is positive, so the
                // integer solution set — and the infeasibility lineage the
                // Hermite solve reports — is unchanged.
                let mut scale_g = g;
                if scale_g > 1 {
                    // `checked_abs`: `i64::MIN` has no magnitude; keep the raw
                    // form for that pathological case (recording is still
                    // exact, just not minimal).
                    if let Some(rhs_abs) = const_term.checked_abs() {
                        scale_g = gcd_i64(scale_g, rhs_abs);
                    }
                }
                let eq_terms: Vec<(VarId, i64)> = expr
                    .terms
                    .iter()
                    .map(|&(v, c)| {
                        let n = *c.numer();
                        if scale_g > 1 {
                            (v, n / scale_g)
                        } else {
                            (v, n)
                        }
                    })
                    .collect();
                let eq_rhs = if scale_g > 1 {
                    const_term / scale_g
                } else {
                    const_term
                };
                self.int_equalities.push(IntEquation {
                    terms: eq_terms,
                    rhs: eq_rhs,
                    reason,
                });
                // A new equality changes the Diophantine system → invalidate
                // the cached feasibility verdict.
                self.int_eq_verdict_cache = None;

                if g > 0 && const_term % g != 0 {
                    // GCD infeasibility detected!
                    // Add contradictory constraints: x >= 1 and x <= 0,
                    // attributed to the actual equality assertion that
                    // caused the contradiction (not a hardcoded reason id)
                    // so `check()`'s unsat core cites the real culprit
                    // instead of whatever the first reason ever added
                    // happened to be.
                    let reason_id = self.add_reason(reason);
                    // Empty-row GCD infeasibility needs a witness variable
                    // too (see the fractional-constant branch above).
                    let victim = expr
                        .terms
                        .first()
                        .map(|&(v, _)| v)
                        .unwrap_or_else(|| self.simplex.new_var());
                    self.simplex
                        .set_lower(victim, Rational64::from_integer(1), reason_id);
                    self.simplex
                        .set_upper(victim, Rational64::from_integer(0), reason_id);
                    return;
                }
            }
        }

        // One shared, interned row per linear form; the equality is the two
        // bounds `slack <= 0` and `slack >= 0` on it.
        let reason_id = self.add_reason(reason);
        let slack = self.cached_row_slack(&lia_key, lhs, rhs, SlackDir::Eq, reason);
        // A pin's WEAK side is never written (the item-76 discipline): a
        // live tighter bound on either side means the equality CONFLICTS
        // with it, and the tighter write of the pair has already recorded
        // that crossing.  Writing the weak side over the live tighter
        // bound would silently drop a constraint the old bound carried;
        // a skipped write leaves the crossed pair for the crossing scan.
        if self.simplex.get_lower(slack).is_none_or(|b| {
            BoundValue::Narrow(DeltaRational::from_rational(Rational64::zero())).cmp_value(&b.value)
                != core::cmp::Ordering::Less
        }) {
            self.simplex.set_lower(slack, Rational64::zero(), reason_id);
        }
        if self.simplex.get_upper(slack).is_none_or(|b| {
            BoundValue::Narrow(DeltaRational::from_rational(Rational64::zero())).cmp_value(&b.value)
                != core::cmp::Ordering::Greater
        }) {
            self.simplex.set_upper(slack, Rational64::zero(), reason_id);
        }
        // NOTE: no `record_prop_bound` here.  An equality's single-variable
        // constant bound is only sound for propagation when it is a GENUINE
        // `var = constant` (a plain variable directly equated to a numeric
        // constant).  Equalities reached through EUF congruence – or whose
        // linear parse dropped a non-constant operand – would record a bound
        // whose single-atom reason is insufficient (the real justification is
        // an equality chain the prop tracker does not see), yielding unsound
        // propagation.  Genuine `var = const` equalities are recorded by the
        // caller ([`Self::note_fixed_var`]) which can distinguish them.
    }

    /// Record the propagation bound implied by a GENUINE `term = value`
    /// equality (a plain variable directly equated to a numeric constant),
    /// for use by cheap bound propagation.  SOUND: the bound is a direct,
    /// unconditional consequence of the asserted equality whose `reason` term
    /// is supplied – no EUF chain is involved, so the single-atom reason is
    /// sufficient.  Callers MUST verify the equality is genuine
    /// (`Var = IntConst/RealConst`) before calling.
    pub fn note_fixed_var(&mut self, term: TermId, value: Rational64, reason: TermId) {
        let var = self.intern(term);
        let reason_id = self.add_reason(reason);
        let dr = DeltaRational::from_rational(value);
        self.prop_set_lower(var, dr, reason_id);
        self.prop_set_upper(var, dr, reason_id);
    }

    /// Tighten the simplex's tableau variable bounds to a fixpoint by running
    /// [`Simplex::propagate_bounds`] until it stops changing anything (bounded
    /// iterations).  This populates the simplex's `lower`/`upper` with the
    /// *transitive* bounds derived through tableau rows (e.g. a recurrence
    /// `x1 = f(x0)` derives `x1`'s bound once `x0` is pinned) – the bounds the
    /// cheap single-variable prop tracker cannot see.
    ///
    /// Call ONCE per assertion (not per atom) so the O(tableau) cost is paid
    /// once, then [`Self::derive_expr_bound_reasons`] reads the populated
    /// bounds cheaply.  SOUND: `propagate_bounds` only tightens (monotonic),
    /// with proper antecedent reasons, and is push/pop-scoped.
    pub fn tighten_tableau_bounds(&mut self) {
        // `propagate_bounds` derives basic-variable bounds from non-basic in
        // one pass; loop to a fixpoint so chains (x<-y<-z) fully propagate.
        // Cap iterations to avoid pathological non-termination on cyclic
        // tightenings.  The change signal is STORES (`applied`), not
        // derivations: a pass that derives plenty but stores nothing IS the
        // fixpoint (slice-6 only queues, the application loop stores), and
        // the old derived-count signal ran one vacuous full derivation pass
        // past it on every call.
        for _ in 0..16 {
            let applied = self.simplex.propagate_bounds_in(&self.int_vars);
            if applied == 0 {
                break;
            }
        }
    }

    /// Assert: lhs < rhs (strict inequality)
    /// For LRA, uses infinitesimals: lhs <= rhs - δ
    /// For LIA, transforms to: lhs <= rhs - 1 (since no integer exists between k and k+1)
    pub fn assert_lt(&mut self, lhs: &[(TermId, Rational64)], rhs: Rational64, reason: TermId) {
        // `-rhs` beyond `Rational64`: exact intern (see `assert_le`), with
        // the STRICT delta bound on the slack (the row-level `∘ 0`
        // encoding is what carries strictness at any width).
        if checked_neg_r64(rhs).is_none() {
            let slack = self.intern_exact_row(lhs, rhs, SlackDir::Lt, reason);
            let reason_id = self.add_reason(reason);
            self.simplex
                .set_strict_upper(slack, Rational64::zero(), reason_id);
            return;
        }
        // For an INTEGRAL row, x < k is equivalent to x <= k - 1
        // because there is no integer strictly between k-1 and k.
        //
        // Per-row, not per-mode: the tightening `k-1` is exact only when the
        // row takes integer values AND `k` itself is an integer.  A
        // fractional `k` would tighten too far (integral `x < 5/2` admits
        // `x = 2`, but `x <= 3/2` does not), and a row over `Real`
        // variables has no integer gap at all.  Both fall through to the
        // delta-rational path, which is exact for reals and integers alike.
        //
        // The shift itself is CHECKED: at `k = i64::MAX` the `k+1`/`k-1`
        // used to overflow — a debug panic, and in release a SILENT WRAP to
        // `i64::MIN`, turning `x < i64::MAX` into a different constraint
        // than the one asserted.  An unshiftable bound falls through to the
        // delta path, which represents the strict bound exactly.
        if rhs.denom() == &1
            && self.lhs_is_integral(lhs)
            && let Some(shifted) = rhs.checked_sub(&Rational64::one())
        {
            // Transform: lhs < rhs becomes lhs <= rhs - 1
            self.assert_le(lhs, shifted, reason);
            return;
        }

        // For reals, use delta-rationals: `lhs < rhs` is the strict upper
        // bound `slack < 0` on the interned row for `lhs - rhs`.
        //
        // Note: no `normalize_expr` here (it may negate the expression to
        // make the first coefficient positive, flipping the strict
        // inequality's direction); the row key therefore also uses the
        // direction-preserving comparison canonicalization.
        let mut single: Option<(VarId, Rational64)> = None;
        for (term, coef) in lhs {
            let var = self.intern(*term);
            single = match single {
                None => Some((var, *coef)),
                Some(_) => None,
            };
        }

        let reason_id = self.add_reason(reason);
        let key = self.row_key(lhs, rhs, false);
        let slack = self.cached_row_slack_strict(&key, lhs, rhs, SlackDir::Lt, reason);
        self.simplex
            .set_strict_upper(slack, Rational64::zero(), reason_id);
        if let Some((var, coef)) = single {
            self.record_prop_bound(var, coef, rhs, PropCmp::Lt, reason_id);
        }
    }

    /// Assert: lhs > rhs (strict inequality)
    /// For LRA, uses infinitesimals: lhs >= rhs + δ
    /// For LIA, transforms to: lhs >= rhs + 1 (since no integer exists between k and k+1)
    pub fn assert_gt(&mut self, lhs: &[(TermId, Rational64)], rhs: Rational64, reason: TermId) {
        // `-rhs` beyond `Rational64`: exact intern (see `assert_lt`).
        if checked_neg_r64(rhs).is_none() {
            let slack = self.intern_exact_row(lhs, rhs, SlackDir::Gt, reason);
            let reason_id = self.add_reason(reason);
            self.simplex
                .set_strict_lower(slack, Rational64::zero(), reason_id);
            return;
        }
        // For an INTEGRAL row, x > k is equivalent to x >= k + 1 (same
        // per-row conditions and CHECKED shift as `assert_lt`; see the
        // soundness note there — at `k = i64::MAX` the unchecked `k+1`
        // wrapped to `i64::MIN` in release).
        if rhs.denom() == &1
            && self.lhs_is_integral(lhs)
            && let Some(shifted) = rhs.checked_add(&Rational64::one())
        {
            // Transform: lhs > rhs becomes lhs >= rhs + 1
            self.assert_ge(lhs, shifted, reason);
            return;
        }

        // For reals, use delta-rationals: `lhs > rhs` is the strict lower
        // bound `slack > 0` on the interned row for `lhs - rhs` (the SAME
        // row `assert_le` interns, so both polarities share it).
        let mut single: Option<(VarId, Rational64)> = None;
        for (term, coef) in lhs {
            let var = self.intern(*term);
            single = match single {
                None => Some((var, *coef)),
                Some(_) => None,
            };
        }

        let reason_id = self.add_reason(reason);
        let key = self.row_key(lhs, rhs, false);
        let slack = self.cached_row_slack_strict(&key, lhs, rhs, SlackDir::Gt, reason);
        self.simplex
            .set_strict_lower(slack, Rational64::zero(), reason_id);
        if let Some((var, coef)) = single {
            self.record_prop_bound(var, coef, rhs, PropCmp::Gt, reason_id);
        }
    }

    /// Get the current value of a variable
    ///
    /// For integer arithmetic (LIA), this properly rounds values that have
    /// infinitesimal components from strict inequalities:
    /// - If value is `r + δ` (positive delta), return `ceil(r)` for integers
    /// - If value is `r - δ` (negative delta), return `floor(r)` for integers
    #[must_use]
    pub fn value(&self, term: TermId) -> Option<Rational64> {
        let &var = self.term_to_var.get(&term)?;
        // No fabricated values for wide basics whose exact value does not
        // narrow: the raw `assignment` entry is stale there, and returning
        // it would publish a witness that violates the variable's own
        // defining row (the Sat gates upstream make this unreachable in
        // practice; this read stays honest regardless — `None` is "no
        // value", never a guess).
        if self.simplex.is_wide_basic(var) && self.simplex.delta_value_exact(var).is_none() {
            return None;
        }
        // The leaf SNAPSHOT wins for BOTH sorts (integers rounded, reals
        // δ-instantiated at the leaf — see `snapshot_lia_model`'s real
        // pass): the branch scopes pop after the snapshot, restoring a
        // point that may re-violate strict bounds the leaf satisfied, and
        // the live reads then decline or report the pre-dive point.
        if let Some(v) = self.lia_model.get(&var) {
            use num_traits::ToPrimitive as _;
            return Some(Rational64::new_raw(
                v.numer().to_i64()?,
                v.denom().to_i64()?,
            ));
        }
        // The HONEST narrow read: BOTH wide channels leave the raw entry
        // stale by design — a wide basic's row (the guard above) AND a
        // wide POINT (a non-basic resting at a bound beyond `Rational64`,
        // typically a branch-and-bound bound at 2^63 scale).  Reading the
        // raw entry for a wide point published a fabricated `0` for an
        // integer resting at -9.2e18: the model carried it, the evaluator
        // refuted it (`Genuine`), and the blocking loop degraded a
        // decidable `sat` to `unknown`.  A point whose exact value does
        // not narrow declines to the exact channel (`value_exact`),
        // never a guess.
        let honest = if self.simplex.is_wide_point(var) {
            self.simplex.delta_value_exact(var)
        } else {
            Some(self.simplex.delta_value(var))
        };
        // Per-VARIABLE integrality, not per-mode: in mixed mode a
        // `Real`-sorted term sitting at a strict bound keeps its
        // delta-rational value, while an `Int`-sorted term rounds.
        if self.int_vars.contains(&var) {
            // Prefer the integral assignment found by branch-and-bound when
            // the last check() proved Sat – the raw LP optimum may be
            // fractional for Int variables.  The snapshot is EXACT
            // (`BigRational`, any width): the leaf's integral value
            // survives the branch scopes' pop, which restores the FRACTIONAL
            // pre-dive point the live reads would otherwise report (a
            // beyond-width leaf value used to be left to `value_exact` on
            // the assumption it would still be readable later — the popped
            // state declined it, the model builder defaulted the variable
            // to 0, and the evaluator refuted the candidate: the J5
            // 61-member class).  A value too wide for this channel hands
            // publication to the exact channel, never a guess.
            if let Some(v) = self.lia_model.get(&var) {
                use num_traits::ToPrimitive as _;
                return Some(Rational64::new_raw(
                    v.numer().to_i64()?,
                    v.denom().to_i64()?,
                ));
            }
            // Get the full delta-rational value (the HONEST read — a
            // wide point's raw entry is stale by design; see above)
            let dval = honest?;

            // For integer arithmetic, round based on delta:
            // - Positive delta means we have a strict lower bound (x > r)
            //   so round up to the next integer
            // - Negative delta means we have a strict upper bound (x < r)
            //   so round down to the previous integer
            // - Zero delta means exact value, round to nearest integer
            //
            // CHECKED: the ±1 shift at the walls (`r = i64::MAX` under a
            // positive delta, `i64::MIN` under a negative one) leaves
            // `i64` — the unchecked form wrapped (a fabricated witness at
            // the OPPOSITE end of the range).  `None` hands publication to
            // the exact channel (`value_exact`), which rounds in
            // `BigRational` and publishes the true integer.
            if dval.delta.is_positive() {
                // x > r implies x >= ceil(r) for integers
                // If r is already an integer, we need r + 1
                let real_val = dval.real;
                if real_val.is_integer() {
                    real_val
                        .to_integer()
                        .checked_add(1)
                        .map(Rational64::from_integer)
                } else {
                    Some(Rational64::from_integer(real_val.ceil().to_integer()))
                }
            } else if dval.delta.is_negative() {
                // x < r implies x <= floor(r) for integers
                // If r is already an integer, we need r - 1
                let real_val = dval.real;
                if real_val.is_integer() {
                    real_val
                        .to_integer()
                        .checked_sub(1)
                        .map(Rational64::from_integer)
                } else {
                    Some(Rational64::from_integer(real_val.floor().to_integer()))
                }
            } else {
                // No strict bound, just return the value
                // Round to nearest integer for consistency
                Some(dval.real)
            }
        } else {
            // For reals, the raw real part is NOT a model: a variable
            // sitting at a strict bound is stored as `r ± δ`, so returning
            // `r` alone reports a witness that violates the very constraint
            // that created it (e.g. `x > 0` would report `x = 0`).
            // Substitute a concrete positive δ₀ that keeps every bound
            // satisfied (see `Simplex::delta_instantiation`).
            //
            // CHECKED (the wide-LP build): the instantiation sum can leave
            // `i64` width — e.g. a variable resting on the strict bound
            // `-2^63 - δ` instantiates to `-2^63 - δ₀`, beyond `i64::MIN`.
            // The unchecked form PANICKED in debug and WRAPPED in release
            // (a dishonest witness at +2^63 that the model certifier then
            // rejected, degrading the verdict to `unknown`).  `None` hands
            // publication to the exact channel (`value_exact`), which
            // instantiates in `BigRational` and publishes the true value.
            let dval = honest?;
            if dval.delta.is_zero() {
                Some(dval.real)
            } else {
                let d0 = self.simplex.delta_instantiation()?;
                let dd = checked_mul_r64(dval.delta, d0)?;
                checked_add_r64(dval.real, dd)
            }
        }
    }

    /// The EXACT (`BigRational`) value of a term's variable — the
    /// publication channel for wide values.
    ///
    /// A wide basic whose exact value does not fit `Rational64` (and
    /// therefore `value`'s honest `None`) still has it exactly, from the
    /// wide store's own re-derivation.  Int-sorted terms publish only
    /// INTEGRAL exact values (a fractional one means the branch-and-bound
    /// has not resolved them — publishing would fabricate integrality).
    pub fn value_exact(&self, term: TermId) -> Option<num_rational::BigRational> {
        let &var = self.term_to_var.get(&term)?;
        // The branch-and-bound snapshot wins for integer variables: it is
        // the INTEGRAL leaf value, exact at any width, and it survives the
        // branch scopes' pop (the live exact read below would see the
        // fractional pre-dive point — see `value`'s snapshot note).
        if let Some(v) = self.lia_model.get(&var) {
            return Some(v.clone());
        }
        // The exact read covers BOTH wide channels: a wide basic's defining
        // row and a wide point value (a non-basic snapped to a wide
        // bound).  The δ-instantiation for a value carrying an
        // infinitesimal substitutes the EXACT `δ₀`
        // (`delta_instantiation_exact` — the narrow one declines on wide
        // states), so a published witness satisfies its strict bounds at
        // any width.
        let exact = self.simplex.point_value_exact(var)?;
        if self.int_vars.contains(&var) {
            // Integer rounding over the exact parts (the `value` rounding
            // applied in `BigRational` — the ±1 shift at the walls is
            // representable here), and only INTEGRAL results publish (a
            // fractional exact means branch-and-bound has not resolved
            // the variable — publishing would fabricate integrality).
            let rounded = if exact.delta.is_positive() {
                if exact.real.fract().is_zero() {
                    exact.real.clone()
                        + num_rational::BigRational::from(num_bigint::BigInt::from(1))
                } else {
                    exact.real.ceil()
                }
            } else if exact.delta.is_negative() {
                if exact.real.fract().is_zero() {
                    exact.real.clone()
                        - num_rational::BigRational::from(num_bigint::BigInt::from(1))
                } else {
                    exact.real.floor()
                }
            } else {
                exact.real.clone()
            };
            if rounded.fract().is_zero() {
                Some(rounded)
            } else {
                None
            }
        } else {
            if exact.delta.is_zero() {
                return Some(exact.real);
            }
            let d0 = self.simplex.delta_instantiation_exact()?;
            Some(exact.real + exact.delta * d0)
        }
    }

    /// LP-implied integer range `[lo, hi]` for `term` over the simplex's
    /// current feasible region, by minimizing then maximizing the term with the
    /// primal simplex (`optimize_linexpr`).  Returns `None` if `term` is not a
    /// TEMP DIAG (item 51 hunt).
    pub fn debug_peek_crossing_lit(&self) -> Option<&Vec<u32>> {
        self.simplex.debug_peek_crossing()
    }

    /// Cheap eager conflict probe for literal-assertion time: reports the
    /// bound-crossing conflicts only (see
    /// [`Simplex::bound_crossing_conflict`]).  O(variables), no pivoting, no
    /// branch-and-bound – the full LP/integer feasibility solve stays with
    /// [`Self::check`] at final-check time.  A `None` result proves nothing.
    pub fn check_bound_conflicts(&mut self) -> Result<TheoryResult> {
        match self.simplex.bound_crossing_conflict() {
            None => Ok(TheoryResult::Sat),
            Some(reasons) => {
                // Map reason ids to terms WITHOUT truncating the reason
                // table (`reasons_from_ids` would cut it to `base`, but the
                // tableau rows still reference these ids).  A missing id
                // falls back to the full core, mirroring `check`'s contract
                // that a conflict explanation must never lose a cause.
                let mut terms: Vec<TermId> = Vec::with_capacity(reasons.len());
                for &r in &reasons {
                    match self.reasons.get(r as usize).copied() {
                        Some(term) => terms.push(term),
                        None => {
                            debug_assert!(
                                false,
                                "simplex reported reason id {r} with no recorded term"
                            );
                            return Ok(TheoryResult::Unsat(self.full_unsat_core()));
                        }
                    }
                }
                Ok(TheoryResult::Unsat(terms))
            }
        }
    }

    /// simplex variable or either side is unbounded (no finite range).
    ///
    /// This is the difference-bound derivation that the per-variable interval
    /// fixpoint and simplex bound-propagation cannot do: a term like
    /// `D = fmt1 - fmt0 - 2`, bounded to `{0..4}` only through a bounded
    /// *difference* of free variables, gets its exact LP-implied range here.
    /// Mirrors z3's `opt_solver::maximize_objective` bound-inference path.
    ///
    /// **Sound** for integer case-splitting: the LP min ≤ every feasible value,
    /// so `ceil(min)` ≤ the least feasible integer; symmetrically `floor(max)`
    /// ≥ the greatest.  `[ceil(min), floor(max)]` is a superset of the true
    /// integer range, so the case-split `(or (= t lo) … (= t hi))` never
    /// excludes a value the term can take.
    #[must_use]
    pub fn lp_int_bounds(&mut self, term: TermId) -> Option<(i64, i64)> {
        let &var = self.term_to_var.get(&term)?;
        // Range over the ASSERTED (level-0) constraints only.  After a
        // satisfiable search the simplex still carries the model's
        // decision-level bounds (e.g. a decided `(= z -4)`); optimising over
        // that state returns the model's value as the range – a *subset* of
        // the true level-0 range – so the case-split `(t = lo ∨ … ∨ t = hi)`
        // would exclude reachable values and become an unsound permanent
        // clause (the `state_hygiene_audit` / `scope_rebase_adversarial`
        // inter-check `sat → unsat` regressions).  Popping to base leaves only
        // the asserted facts, which is the soundness criterion the case-split
        // needs.  Destructive, but `refine_int_case_split` is immediately
        // followed by a full `reset()`, so the discarded decision-level bounds
        // are re-derived by the re-solve.
        self.simplex.pop_to_base();
        let lo_real = match self.simplex.optimize_linexpr(&LinExpr::var(var)) {
            SimplexOptStatus::Optimal(v) => v,
            _ => return None,
        };
        let neg_max = match self.simplex.optimize_linexpr(&LinExpr {
            terms: smallvec::smallvec![(var, Rational64::from_integer(-1))],
            constant: Rational64::zero(),
        }) {
            SimplexOptStatus::Optimal(v) => v,
            _ => return None,
        };
        // `-neg_max` is CHECKED: at `neg_max = i64::MIN` the negation does
        // not fit, and a wrapped value would narrow the case-split range
        // (the false-`unsat` direction this helper's soundness note
        // exists for).
        let hi_real = checked_neg_r64(neg_max)?;
        Some((lo_real.ceil().to_integer(), hi_real.floor().to_integer()))
    }

    /// Status of the equality `a = b` from arithmetic's current bounds.
    /// Covers the `equalsConstant` / point-bounded case.  Individually
    /// classifies 0/14637 on pete2 (IDL terms are difference-linked, not
    /// point-fixed), but may compound on the chain as a cheap pre-filter
    /// for the care graph.
    pub fn equality_status(&self, a: TermId, b: TermId) -> ArithEqualityStatus {
        let (Some(va), Some(vb)) = (
            self.term_to_var.get(&a).copied(),
            self.term_to_var.get(&b).copied(),
        ) else {
            return ArithEqualityStatus::Unknown;
        };
        let fa = fixed_value(self.simplex.get_lower(va), self.simplex.get_upper(va));
        let fb = fixed_value(self.simplex.get_lower(vb), self.simplex.get_upper(vb));
        match (fa, fb) {
            (Some(x), Some(y)) if x == y => ArithEqualityStatus::EntailedEqual,
            (Some(_), Some(_)) => ArithEqualityStatus::EntailedDisequal,
            _ => ArithEqualityStatus::Unknown,
        }
    }
    /// Every term the arithmetic solver has internalised (interface / shared).
    pub fn interface_terms(&self) -> &[TermId] {
        &self.var_to_term
    }
    /// Soundly determine whether `term = const_value` is *entailed* by the
    /// current arithmetic assignment, and if so return an all-atom reason
    /// (the SAT atoms whose assertion forces the equality).
    ///
    /// Implemented as two infeasibility probes on a scratch simplex scope:
    /// `term >= const_value` holds iff `term < const_value` is infeasible, and
    /// `term <= const_value` holds iff `term > const_value` is infeasible.  The
    /// reason is the union of the two Farkas certificates, with the probe's own
    /// marker reason excluded.  When both hold with no collected reasons, the
    /// equality is entailed by the empty set (level-0 facts) and the full
    /// unsat-core is returned instead.
    ///
    /// Used by the z3-style `final_check` theory propagation to justify the
    /// triangle `le`/`ge` atoms deterministically.
    pub fn fixed_to_const_reason(&mut self, term: TermId, const_value: i64) -> Option<Vec<TermId>> {
        let &var = self.term_to_var.get(&term)?;
        let cv = Rational64::from_integer(const_value);
        // `x < cv` probe row needs `-cv`: at `cv = i64::MIN` the negation
        // does not fit — decline (None = no reason derived, always sound).
        checked_neg_r64(cv)?;
        let base = self.reasons.len();
        let mut collected: Vec<TermId> = Vec::new();
        // term < const_value infeasible  ⟺  term >= const_value entailed.
        let ge_entailed = {
            self.simplex.push();
            let marker = self.add_reason(term);
            let mut e = LinExpr::new();
            e.add_term(var, Rational64::one());
            e.add_constant(-cv);
            self.simplex.add_strict_lt(e, marker);
            let r = match self.simplex.check() {
                Ok(()) => false,
                Err(reasons) => {
                    for &rid in &reasons {
                        if rid != marker
                            && let Some(&t) = self.reasons.get(rid as usize)
                        {
                            collected.push(t);
                        }
                    }
                    true
                }
            };
            self.simplex.pop();
            r
        };
        if !ge_entailed {
            self.reasons.truncate(base);
            self.reason_counter = base as u32;
            return None;
        }
        // term > const_value infeasible  ⟺  term <= const_value entailed.
        let le_entailed = {
            self.simplex.push();
            let marker = self.add_reason(term);
            let mut e = LinExpr::new();
            e.add_term(var, -Rational64::one());
            e.add_constant(cv);
            self.simplex.add_strict_lt(e, marker);
            let r = match self.simplex.check() {
                Ok(()) => false,
                Err(reasons) => {
                    for &rid in &reasons {
                        if rid != marker
                            && let Some(&t) = self.reasons.get(rid as usize)
                        {
                            collected.push(t);
                        }
                    }
                    true
                }
            };
            self.simplex.pop();
            r
        };
        self.reasons.truncate(base);
        self.reason_counter = base as u32;
        if !le_entailed {
            return None;
        }
        collected.sort_unstable();
        collected.dedup();
        if collected.is_empty() {
            return Some(self.full_unsat_core());
        }
        Some(collected)
    }

    /// Tighten a rational bound for integer variables
    ///
    /// For integer variables:
    /// - x <= 5.7 becomes x <= 5
    /// - x >= 2.3 becomes x >= 3
    /// - x < 5.0 becomes x <= 4
    /// - x > 2.0 becomes x >= 3
    #[allow(dead_code)]
    fn tighten_bound(&self, bound: Rational64, is_upper: bool) -> Rational64 {
        if !self.is_integer() {
            return bound;
        }

        // For upper bounds (<=), floor the value
        // For lower bounds (>=), ceiling the value
        if bound.is_integer() {
            bound
        } else if is_upper {
            // x <= 5.7 becomes x <= 5
            Rational64::from_integer(bound.floor().to_integer())
        } else {
            // x >= 2.3 becomes x >= 3
            Rational64::from_integer(bound.ceil().to_integer())
        }
    }

    /// Maximum branch-and-bound tree depth for the LIA integrality search.
    const LIA_MAX_DEPTH: usize = 4096;
    /// Maximum number of branch-and-bound nodes explored before giving up
    /// (returning `Unknown`).  Bounds worst-case exponential search.
    const LIA_MAX_NODES: usize = 20_000;
    /// Gomory (GMI) cut rounds run at the root of the branch-and-bound
    /// search before branching starts.  Each round re-solves the LP and
    /// derives cuts from still-fractional integer basic rows (Z3's
    /// `theory_arith_int` interleaves `mk_gomory_cut` with the branch
    /// search the same way).
    const LIA_MAX_CUT_ROUNDS: usize = 24;
    /// Per-round cap on cuts: each cut adds a permanent row to the tableau
    /// for the rest of this B&B search, so a flood of weak cuts costs more
    /// pivot work than it saves.
    const LIA_MAX_CUTS_PER_ROUND: usize = 16;
    /// Coefficient magnitude guard for cuts: numerators/denominators beyond
    /// this would blow up every later pivot on the cut row, so the cut is
    /// skipped (branch-and-bound alone remains sound and complete).
    const LIA_CUT_MAX_DENOM: i64 = 1_000_000;

    /// Collect the simplex variable ids of all interned (Int) terms, sorted for
    /// deterministic branching order.  Slack variables are excluded – we only
    /// branch on the original integer-sorted variables.
    fn interned_int_vars(&self) -> Vec<VarId> {
        // ONLY the variables actually known integer.  The name-and-body used
        // to disagree in mixed mode (the body returned every interned term
        // variable): branching on a `Real`-sorted variable with the integer
        // split `v \le k ∨ v \ge k+1` deletes the fractional values and
        // refutes real solutions that exist – e.g. `y:Real \u2208 (0,1)` has
        // no integer point, so the search would return a spurious `unsat`.
        // In pure LIA the filter is a no-op (every interned term is marked at
        // `intern`), so the trajectory there is unchanged.
        let mut vars: Vec<VarId> = self
            .var_to_term
            .iter()
            .filter_map(|term| self.term_to_var.get(term).copied())
            .filter(|&v| self.int_vars.contains(&v))
            .collect();
        vars.sort_unstable();
        vars.dedup();
        vars
    }

    /// Find the interned Int variable to branch on: the fractional one with
    /// the smallest bound range (Z3's `find_bounded_infeasible_int_base_var`
    /// – the tightest box closes fastest, and on tool-generated bounded
    /// problems like `rings` it is the difference between closing the tree
    /// and never finishing), falling back to the first fractional variable
    /// when no fractional variable is bounded.
    fn find_fractional_int_var(&self, int_vars: &[VarId]) -> Option<FracVar> {
        let mut underivable: Option<VarId> = None;
        let mut best: Option<FracVar> = None;
        let mut best_range: Option<Rational64> = None;
        for &var in int_vars {
            // The value read must be WIDE-AWARE: a wide-basic integer
            // variable's raw `assignment` entry is exactly its exact value
            // only while that value narrows; otherwise it is stale and
            // reading it fabricates integrality (the false-`sat` class:
            // `(= (+ (* 27670116100584327436 v2) (* 9223372036854775808 v1))
            // -5)` with `v2 = 3` read `v1 = 0` and answered `sat` with an
            // invalid witness).  The exact un-narrowed value still yields
            // branch bounds when they fit `i64`.
            // The EXACT read (wide rows, wide points, narrow assignment
            // alike): a variable is RESOLVED exactly when its value is an
            // integer — integral real part AND no infinitesimal (an `Int`
            // variable resting at `r − δ` under a strict bound is NOT at
            // `r`; reading only the real part snapshot-published `r` as a
            // model value that violates the very bound — the wall cases
            // where the `k ± 1` tightening could not run).  Otherwise the
            // branch bounds are the exact floor/ceil at any width: the
            // `Underivable` class narrows to "no exact value at all".
            let branch = match self.simplex.point_value_exact(var) {
                Some(exact) => {
                    if exact.real.fract().is_zero() && exact.delta.is_zero() {
                        continue;
                    }
                    let (floor, ceil) =
                        super::simplex::Simplex::floor_ceil_big(&exact.real, &exact.delta);
                    FracVar::Branch { var, floor, ceil }
                }
                None => {
                    underivable = underivable.or(Some(var));
                    continue;
                }
            };
            let idx = var as usize;
            let lo = self.simplex.lower_real_at(idx);
            let hi = self.simplex.upper_real_at(idx);
            match (lo, hi) {
                (Some(lo), Some(hi)) => {
                    // CHECKED subtraction: on wide-literal instances the
                    // stored bounds straddle ±2^62, the difference leaves
                    // `i64` (num-rational's `sub` PANICS under
                    // debug-assertions and WRAPS in release — a wrapped
                    // range silently misranks the branch variable).  The
                    // range only RANKS candidates (any branch choice is
                    // sound), so a non-representable range ranks this
                    // candidate as worst-of-class instead of guessing: an
                    // unbounded-vars fallback ordering.  Found by the
                    // rehome canary's debug run after the derivation
                    // stamps changed which fractional variable the search
                    // visits first — the site is trajectory-independent
                    // (any B&B visit of a straddling pair hits it).
                    match num_traits::CheckedSub::checked_sub(&hi, &lo) {
                        Some(range) => {
                            if best_range.is_none_or(|r| range < r) {
                                best_range = Some(range);
                                best = Some(branch);
                            }
                        }
                        None => {
                            if best.is_none() {
                                best = Some(branch);
                            }
                        }
                    }
                }
                _ => {
                    if best.is_none() {
                        best = Some(branch);
                    }
                }
            }
        }
        best.or(if underivable.is_some() {
            Some(FracVar::Underivable)
        } else {
            None
        })
    }

    /// Record the real-atom reasons of one LP conflict from the search tree
    /// ([`BRANCH_REASON`] marks a case-split bound and carries no atom).
    fn note_bnb_conflict_reasons(&mut self, reasons: &[u32]) {
        for &r in reasons {
            if r != BRANCH_REASON {
                self.bnb_used_reasons.insert(r);
            }
        }
    }

    /// The branch-and-bound unsat core: the collected conflict atoms, falling
    /// back to the full reason set only when nothing was collected (defensive:
    /// an over-approximate core is sound, an empty one is not).
    fn bnb_unsat_core(&self) -> Vec<TermId> {
        if self.bnb_used_reasons.is_empty() {
            return self.full_unsat_core();
        }
        let mut terms: Vec<TermId> = self
            .bnb_used_reasons
            .iter()
            .filter_map(|&r| self.reasons.get(r as usize).copied())
            .collect();
        terms.sort_unstable();
        terms.dedup();
        if terms.is_empty() {
            self.full_unsat_core()
        } else {
            terms
        }
    }

    /// Build a sound (over-approximate) unsat core: every assertion reason known
    /// to the solver.  When branch-and-bound proves integer-infeasibility, the
    /// full conjunction of asserted constraints is genuinely inconsistent, so
    /// returning all of them is a valid (if imprecise) conflict explanation.
    fn full_unsat_core(&self) -> Vec<TermId> {
        // Index 0 is the reserved \"no external reason\" dummy (see
        // [`Self::new`]); it names no atom and must never enter a core.
        let mut terms: Vec<TermId> = self
            .reasons
            .iter()
            .enumerate()
            .filter_map(|(i, &t)| if i == 0 { None } else { Some(t) })
            .collect();
        terms.sort_unstable();
        terms.dedup();
        terms
    }

    /// Snapshot the current (integral) LP assignment of every interned Int
    /// variable into `lia_model`.  Called at an integer-feasible leaf so that
    /// `value()` reports the integral model after branch-and-bound unwinds.
    fn snapshot_lia_model(&mut self, int_vars: &[VarId]) {
        #[cfg(feature = "std")]
        if std::env::var("NIXIE_INV_TRACE").is_ok()
            && let Some(v) = self.simplex.debug_verify_invariant()
        {
            let bt = std::backtrace::Backtrace::force_capture();
            eprintln!("[inv-viol] at snapshot: {v}\n{bt}");
        }
        self.lia_model.clear();
        for &var in int_vars {
            // The honest NARROW integral value: the exact point value
            // rounded by the infinitesimal's sign (an `Int` variable at
            // `r ± δ` models at `r ± 1`), narrowed when representable.
            // The old body snapshotted the RAW real part — for a variable
            // resting on a strict bound that published `r` itself, a
            // witness violating the bound (the `i64::MIN`-corner class
            // where the `k ± 1` tightening cannot run).  A value beyond
            // width is left to the exact publication channel
            // (`value_exact`), never fabricated here.
            let Some(exact) = self.simplex.point_value_exact(var) else {
                continue;
            };
            let rounded = if exact.delta.is_positive() {
                if exact.real.fract().is_zero() {
                    exact.real.clone()
                        + num_rational::BigRational::from(num_bigint::BigInt::from(1))
                } else {
                    exact.real.ceil()
                }
            } else if exact.delta.is_negative() {
                if exact.real.fract().is_zero() {
                    exact.real.clone()
                        - num_rational::BigRational::from(num_bigint::BigInt::from(1))
                } else {
                    exact.real.floor()
                }
            } else {
                exact.real.clone()
            };
            if !rounded.fract().is_zero() {
                // Fractional exact value: unresolved — do not publish.
                continue;
            }
            // Store the integral leaf value EXACTLY (`BigRational`, any
            // width): the branch scopes pop right after this snapshot, and
            // the live reads would report the fractional pre-dive point.
            // The old narrow-only store left beyond-width leaf values to
            // `value_exact`'s live read — which declined on the popped
            // state, the model builder defaulted the variable to `0`, and
            // the evaluator refuted a genuine leaf model (the J5 class).
            self.lia_model.insert(var, rounded);
        }
        // The leaf's REAL values belong in the snapshot for the same
        // reason: the branch scopes pop right after, restoring a point
        // that may RE-VIOLATE strict bounds the leaf satisfied (a basic
        // resting at its strict bound's real part with no infinitesimal),
        // and the δ-instantiation computed over the popped state declines
        // — every real then published the sort default `0` and the
        // evaluator refuted the candidate (the J5 residual's real half).
        // Instantiating δ HERE, inside the leaf's scopes, yields the
        // concrete witness the leaf actually rests at.
        let d0 = self.simplex.delta_instantiation_exact();
        for var in 0..self.var_to_term.len() as VarId {
            if self.lia_model.contains_key(&var) || self.int_vars.contains(&var) {
                continue; // integers are snapshotted above (rounded)
            }
            let Some(exact) = self.simplex.point_value_exact(var) else {
                continue;
            };
            let value = if exact.delta.is_zero() {
                exact.real
            } else {
                match &d0 {
                    Some(d0) => exact.real + exact.delta * d0,
                    None => continue, // no positive instantiation at the leaf: leave unpublished
                }
            };
            self.lia_model.insert(var, value);
        }
    }

    /// Decide the recorded integer-equality subsystem *completely* via the
    /// Hermite (column-echelon) solve: `Infeasible` is a proof that the
    /// subsystem (and hence the whole problem) has no integer solution;
    /// `Incumbent` carries a concrete witness with free variables set to
    /// zero — lossless, because in column-echelon form the pivot variables
    /// are uniquely determined by their predecessors, so the witness exists
    /// iff any integer solution exists.
    ///
    /// This subsumes the historical GCD/fraction-free-Gaussian one-sided
    /// check: it resolves everything that check could (e.g.
    /// `y = 2x ∧ y = 2z + 1` ⇒ `2x − 2z = 1`) and additionally produces
    /// satisfying assignments for feasible systems — the class
    /// branch-and-bound cannot close (unbounded pure-equality systems such
    /// as the parity obligations; see
    /// `docs/studies/2026-09-06-mixed-parity-lia-equality-gap.md`).
    ///
    /// A pure function of `int_equalities`; callers memoize via
    /// [`ArithSolver::cached_int_eq_verdict`].  Guards (system size,
    /// intermediate magnitude) return `GiveUp` — never a wrapped verdict.
    fn compute_int_eq_verdict(&self) -> IntEqVerdict {
        if self.int_equalities.is_empty() {
            return IntEqVerdict::GiveUp;
        }

        // Assign a dense column index to every variable that appears.
        let mut col_of: FxHashMap<VarId, usize> = FxHashMap::default();
        for eq in &self.int_equalities {
            for &(v, _) in &eq.terms {
                let next = col_of.len();
                col_of.entry(v).or_insert(next);
            }
        }
        let cols = col_of.len();
        let rows = self.int_equalities.len();
        if cols == 0 || rows.saturating_mul(cols) > 200_000 {
            return IntEqVerdict::GiveUp;
        }

        let mut mat: Vec<Vec<i128>> = vec![vec![0i128; cols]; rows];
        let mut rhs: Vec<i128> = vec![0i128; rows];
        for (r, eq) in self.int_equalities.iter().enumerate() {
            for &(v, c) in &eq.terms {
                if let Some(&col) = col_of.get(&v) {
                    mat[r][col] += i128::from(c);
                }
            }
            rhs[r] = i128::from(eq.rhs);
        }

        match super::lia::solve_integer_eq_system(&mat, &rhs) {
            // Map the row-lineage core to its reason terms; an unmappable
            // row (stale index — cannot happen while rows and reasons are
            // pushed/truncated in lockstep) falls back to the full core.
            super::lia::EqSolution::Infeasible(core) => {
                let terms: Option<Vec<TermId>> = core
                    .iter()
                    .map(|&r| self.int_equalities.get(r).map(|eq| eq.reason))
                    .collect();
                match terms {
                    Some(mut t) => {
                        t.sort_unstable();
                        t.dedup();
                        IntEqVerdict::Infeasible(t)
                    }
                    None => IntEqVerdict::Infeasible(self.full_unsat_core()),
                }
            }
            super::lia::EqSolution::GiveUp => IntEqVerdict::GiveUp,
            super::lia::EqSolution::Feasible(x) => {
                let mut witness = Vec::with_capacity(cols);
                for (var, &col) in &col_of {
                    let v = x[col];
                    let Ok(small) = i64::try_from(v) else {
                        return IntEqVerdict::GiveUp;
                    };
                    witness.push((*var, Rational64::from_integer(small)));
                }
                IntEqVerdict::Incumbent(witness)
            }
        }
    }

    /// Memoized [`ArithSolver::compute_int_eq_verdict`]; invalidated exactly
    /// when an equality is asserted or retracted by `pop`.
    fn cached_int_eq_verdict(&mut self) -> IntEqVerdict {
        self.int_eq_cache().verdict
    }

    /// Verdict plus the incumbent-rejection marker, memoized together.
    fn int_eq_cache(&mut self) -> IntEqCache {
        if self.int_eq_verdict_cache.is_none() {
            self.int_eq_verdict_cache = Some(IntEqCache {
                verdict: self.compute_int_eq_verdict(),
                rejected: false,
            });
        }
        self.int_eq_verdict_cache.clone().unwrap_or(IntEqCache {
            verdict: IntEqVerdict::GiveUp,
            rejected: false,
        })
    }

    /// Attempt the incumbent once per equality-set state; record rejection.
    fn try_cached_eq_incumbent(&mut self) -> bool {
        let (verdict, rejected) = {
            let c = self.int_eq_cache();
            (c.verdict, c.rejected)
        };
        let IntEqVerdict::Incumbent(w) = verdict else {
            return false;
        };
        if rejected {
            return false;
        }
        let ok = self.try_eq_incumbent(&w);
        if !ok && let Some(c) = self.int_eq_verdict_cache.as_mut() {
            c.rejected = true;
        }
        ok
    }

    /// Re-solve under a scoped pinning of an equality witness (`var = x*`
    /// for every covered variable, inside its own simplex scope, exactly
    /// like a branch bound).  If the LP accepts the pins and every integer
    /// variable lands integral, `lia_cuts_then_bnb` snapshots the model and
    /// reports `Sat` — a genuine model of *all* active rows (the pins
    /// enforce the witness; the LP enforces everything else).  Any other
    /// outcome pops the scope and the caller falls back honestly: the
    /// witness is one lattice point, not a characterization, when rows
    /// beyond the equalities exist.
    fn try_eq_incumbent(&mut self, witness: &[(VarId, Rational64)]) -> bool {
        self.simplex.push();
        for &(var, value) in witness {
            self.simplex.set_lower(var, value, BRANCH_REASON);
            self.simplex.set_upper(var, value, BRANCH_REASON);
        }
        // Lean probe — one LP re-solve plus an integrality scan, no cut
        // rounds: this runs at theory-check frequency during search, and a
        // doomed pinning (rows beyond the equalities reject the witness)
        // must cost one simplex pass, not a full cuts+B&B pipeline
        // (measured: the pipeline turned mixed-parity UNSAT from a fast
        // honest `unknown` into a timeout).
        let int_vars = self.interned_int_vars();
        let accepted = self.simplex.check().is_ok()
            && !self.simplex.resource_limit_reached()
            && self.find_fractional_int_var(&int_vars).is_none();
        if accepted {
            self.snapshot_lia_model(&int_vars);
        }
        self.simplex.pop();
        accepted
    }

    /// Entry point for the LIA integrality search (cuts + branch-and-bound).
    ///
    /// Precondition: the LP relaxation is feasible and not resource-limited.
    /// All live bounds are asserted-atom bounds at entry (branch bounds exist
    /// only inside [`Self::bnb_recurse`]'s scopes), so Gomory cuts derived
    /// here are valid for the entire search and their reasons are real atoms.
    /// Everything the search adds – cut rows and branch bounds – lives inside
    /// ONE simplex scope popped before returning, so nothing leaks past this
    /// theory check into a different atom assignment (where a cut would be
    /// unsound).
    fn lia_branch_and_bound(&mut self) -> Result<TheoryResult> {
        // Eager Diophantine refutation: when the Hermite solve of the
        // recorded equalities (assertion rows plus search-propagated
        // equality atoms — the cache invalidates on every assert_eq/pop)
        // already proves integer-infeasibility, return the conflict NOW.
        // This is the leaf-firing mechanism: at a search leaf the
        // propagated link equalities make the system parity-inconsistent,
        // and without this check the refutation only surfaces AFTER
        // branch-and-bound burns LIA_MAX_NODES at that check — which
        // starves CDCL of the fast conflict loop it needs to learn the
        // parity clauses (the mixed-parity study's honest-timeout class).
        // Only the Infeasible direction is eager: an accepted incumbent
        // eagerly changes theory verdicts from Unknown to Sat under
        // partial assignments and measurably steers searches badly; the
        // incumbent stays post-hoc.
        if let IntEqVerdict::Infeasible(core) = self.cached_int_eq_verdict() {
            return Ok(TheoryResult::Unsat(core));
        }
        self.simplex.push();
        let result = self.lia_cuts_then_bnb()?;
        self.simplex.pop();
        match result {
            TheoryResult::Unknown => {}
            other => return Ok(other),
        }
        // The search gave up (unbounded variables, or its node/depth budget).
        // The complete Diophantine verdict upgrades the historical one-sided
        // check: `Infeasible` is a proof (converting a would-be `Unknown`
        // into a proven `Unsat` — everything the old GCD-elimination fallback
        // resolved, e.g. `y = 2x ∧ y = 2z + 1`), and `Incumbent` is re-pinned
        // through a scoped LP re-solve that respects every other active row;
        // acceptance yields a genuine integral model where branch-and-bound
        // could not construct one (the unbounded pure-equality class).
        match self.cached_int_eq_verdict() {
            IntEqVerdict::Infeasible(core) => Ok(TheoryResult::Unsat(core)),
            IntEqVerdict::Incumbent(_) => {
                if self.try_cached_eq_incumbent() {
                    Ok(TheoryResult::Sat)
                } else {
                    Ok(TheoryResult::Unknown)
                }
            }
            IntEqVerdict::GiveUp => Ok(TheoryResult::Unknown),
        }
    }

    /// Gomory-cut rounds, then branch-and-bound, inside the caller's scope.
    fn lia_cuts_then_bnb(&mut self) -> Result<TheoryResult> {
        self.bnb_used_reasons.clear();
        for _ in 0..Self::LIA_MAX_CUT_ROUNDS {
            // Re-solve after the previous round's cuts.
            match self.simplex.check() {
                Ok(()) => {
                    if self.simplex.resource_limit_reached() {
                        return Ok(TheoryResult::Unknown);
                    }
                }
                // The cuts alone refuted the current atom assignment.  The
                // conflict's reasons (which include the cut's own reason
                // sets) are the precise core.
                Err(reasons) => {
                    self.note_bnb_conflict_reasons(&reasons);
                    return Ok(TheoryResult::Unsat(self.bnb_unsat_core()));
                }
            }
            let int_vars = self.interned_int_vars();
            if self.find_fractional_int_var(&int_vars).is_none() {
                // Cuts closed the integrality gap outright — every integer
                // variable's value is derivably integral (the tri-state
                // read treats an underivable wide-basic value as NOT
                // integral, so this acceptance never rests on a fabricated
                // entry).
                self.snapshot_lia_model(&int_vars);
                return Ok(TheoryResult::Sat);
            }
            // Derive cuts from fractional integer basic rows.
            let mut candidates: Vec<VarId> = self
                .simplex
                .tableau_keys()
                .filter(|v| self.int_vars.contains(v) && !self.simplex.value(*v).is_integer())
                .collect();
            candidates.sort_unstable();
            let mut added = 0usize;
            for var in candidates {
                if added >= Self::LIA_MAX_CUTS_PER_ROUND {
                    break;
                }
                if let Some((cut, reasons)) = self.gomory_cut(var)
                    && self.simplex.add_le_with_reasons(cut, reasons).is_some()
                {
                    added += 1;
                }
            }
            if added == 0 {
                break; // no (more) derivable cuts: fall through to B&B
            }
        }
        // Branch-and-bound over the (cut-tightened) relaxation.  It is the
        // common exit on saturated integer inputs: the LP optimum is already
        // integral and B&B stops at its first node.
        let int_vars = self.interned_int_vars();
        let mut nodes: usize = 0;

        // Free-variable sign splits (Z3's `constrain_free_vars`,
        // theory_arith_int.h) – but only when the cut loop actually *failed
        // because of* free nonbasics: a fractional integer row that still
        // has unbounded variables keeps `gomory_cut` from firing, and plain
        // B&B then diverges on the unbounded ray while the integer conflict
        // is global (k7: `r = 2S - 2q`, `r in [0,1]`, `q < S`).  Z3
        // internalizes `v >= 0` case-split atoms so the DPLL layer bounds
        // them; here the split happens inside the theory: branch
        // `u >= 0` / `u <= -1` per free variable and re-run the whole
        // cuts-then-B&B inside each side, where the variable rests at its
        // new bound, the cut machinery applies (see
        // [`Self::cuts_in_split_scope`]), and the parity conflicts close.
        // Exhaustive (the two branches cover every integer of `u`), depth
        // bounded by the free-variable count, capped.
        let free_vars = self.uncuttable_free_vars();
        if !free_vars.is_empty() {
            return self.close_free_vars_then_bnb(&free_vars);
        }
        self.bnb_search(&int_vars, &mut nodes)
    }

    /// The free integer variables that keep the cut machinery from firing:
    /// nonbasics (bounded on neither side) of rows whose integer basic is
    /// fractional – exactly the rows `gomory_cut` had to refuse – plus free
    /// fractional integer basics, which plain B&B diverges on and which
    /// appear in no row (a basic is defined *by* its row, so the row walk
    /// alone misses them).  Z3's collection is the row-local part; the
    /// basics are the divergers this exists to stop.  Capped: more free
    /// variables than the cap falls back to the ordinary search
    /// (completeness only).
    fn uncuttable_free_vars(&self) -> Vec<VarId> {
        /// A handful of sign splits is plenty for the parity shapes this
        /// exists for; the cap bounds the 2^k recursion.
        const MAX_FREE_SPLITS: usize = 8;
        let mut out: Vec<VarId> = Vec::new();
        let is_free = |v: VarId| {
            let j = v as usize;
            self.simplex.bound_lower_at(j).is_none() && self.simplex.bound_upper_at(j).is_none()
        };
        for (var, row) in self.simplex.tableau_iter() {
            let var = *var;
            if !self.int_vars.contains(&var) || self.simplex.value(var).is_integer() {
                continue;
            }
            if self.simplex.is_basic(var as usize) {
                if is_free(var) && !out.contains(&var) {
                    out.push(var);
                }
                continue;
            }
            for (xj, a_j) in &row.terms {
                let xj = *xj;
                let j = xj as usize;
                if a_j.is_zero()
                    || !self.int_vars.contains(&xj)
                    || self.simplex.is_basic(j)
                    || !is_free(xj)
                    || out.contains(&xj)
                {
                    continue;
                }
                out.push(xj);
                if out.len() >= MAX_FREE_SPLITS {
                    return out;
                }
            }
        }
        out
    }

    /// Z3's `constrain_free_vars` analogue: sign-split each free integer
    /// variable (`u >= 0` / `u <= -1`) and re-run the full
    /// cuts-then-branch-and-bound inside each side, where `u` rests at its
    /// new bound and Gomory cuts apply ([`Self::cuts_in_split_scope`] is
    /// set for the recursion).  Both branches together cover every integer
    /// value of `u`, so an all-`Unsat` outcome is a proof; a `Sat` leaf is
    /// a found model; `Unknown` propagates honestly.
    fn close_free_vars_then_bnb(&mut self, free_vars: &[VarId]) -> Result<TheoryResult> {
        let Some((&u, _rest)) = free_vars.split_first() else {
            // Leaf: every previously-free variable is bounded on one side
            // now, so nonbasics rest at bounds and the Gomory cut machinery
            // applies – re-run the whole cuts-then-B&B.  Well-founded: the
            // free list inside this scope is a strict subset (every split
            // variable gained a bound), so the re-entry reaches the cut
            // loop, not another split of the same variables.
            let saved = self.cuts_in_split_scope;
            self.cuts_in_split_scope = true;
            let r = self.lia_cuts_then_bnb();
            self.cuts_in_split_scope = saved;
            return r;
        };
        let mut saw_unknown = false;
        for (bound, upper) in [
            (Rational64::zero(), false),
            (Rational64::from_integer(-1), true),
        ] {
            self.simplex.push();
            if upper {
                self.simplex.set_upper(u, bound, BRANCH_REASON);
            } else {
                self.simplex.set_lower(u, bound, BRANCH_REASON);
            }
            let saved = self.cuts_in_split_scope;
            self.cuts_in_split_scope = true;
            let child = match self.simplex.check() {
                Ok(()) if !self.simplex.resource_limit_reached() => {
                    let inner_free = self.uncuttable_free_vars();
                    if inner_free.is_empty() {
                        self.lia_cuts_then_bnb()
                    } else {
                        self.close_free_vars_then_bnb(&inner_free)
                    }
                }
                Ok(()) => {
                    // Pivot budget exhausted: Unknown, never a fabricated Sat.
                    Ok(TheoryResult::Unknown)
                }
                Err(reasons) => {
                    self.note_bnb_conflict_reasons(&reasons);
                    Ok(TheoryResult::Unsat(self.bnb_unsat_core()))
                }
            };
            self.cuts_in_split_scope = saved;
            self.simplex.pop();
            match child? {
                TheoryResult::Sat => return Ok(TheoryResult::Sat),
                TheoryResult::Unknown => saw_unknown = true,
                TheoryResult::Unsat(_) | TheoryResult::Propagate(_) => {}
            }
        }
        if saw_unknown {
            Ok(TheoryResult::Unknown)
        } else {
            Ok(TheoryResult::Unsat(self.bnb_unsat_core()))
        }
    }

    /// Generate a Gomory mixed-integer (GMI) cut from the tableau row of the
    /// fractional integer basic variable `var`.
    ///
    /// Port of Z3 `theory_arith_int::mk_gomory_cut` (and this crate's
    /// `lia::cuts::tableau_row_cut`, which documents the same derivation):
    /// rewrite the row
    ///
    /// ```text
    /// x_B = x̄_B + Σ_j â_j · y_j ,   y_j = x_j − l_j ≥ 0 (resting at a lower bound)
    ///                                  y_j = u_j − x_j ≥ 0 (resting at an upper bound)
    /// ```
    ///
    /// with `f0 = frac(x̄_B) ∈ (0,1)` and emit the valid inequality
    /// `Σ_j γ_j·y_j ≥ 1`: for integer `y_j` (integer variable resting at an
    /// integer bound) with `f_j = frac(−â_j)`, `γ_j = f_j/f0` if `f_j ≤ f0`
    /// else `γ_j = (1−f_j)/(1−f0)`; for continuous `y_j` with `ā_j = −â_j`,
    /// `γ_j = −ā_j/f0` if `ā_j ≥ 0` else `γ_j = ā_j/(1−f0)`.  The returned
    /// `LinExpr` encodes the cut in the `C ≤ 0` convention of
    /// [`Simplex::add_le_with_reasons`], together with the reason ids of
    /// every bound the derivation consumed – the cut is a consequence of
    /// exactly those asserted atoms (the row itself is a slack *definition*
    /// and carries no assertion).
    ///
    /// Returns `None` when no sound root-scoped cut is derivable: `var` not
    /// a fractional integer basic variable; a row variable resting at no
    /// finite bound; any involved bound being a branch bound (reason 0 –
    /// such a cut is only valid inside that branch); a coefficient exceeding
    /// [`Self::LIA_CUT_MAX_DENOM`]; or an empty polynomial.
    fn gomory_cut(&self, var: VarId) -> Option<(LinExpr, SmallVec<[u32; 4]>)> {
        if !self.int_vars.contains(&var) {
            return None;
        }
        if !self.simplex.is_basic(var as usize) {
            return None;
        }
        let bar = self.simplex.value(var);
        let f0 = bar - bar.floor();
        if f0.is_zero() {
            return None; // integral value: nothing to cut
        }

        let row = self
            .simplex
            .tableau_iter()
            .find(|(v, _)| **v == var)
            .map(|(_, e)| e.clone())?;
        if row.terms.is_empty() {
            return None;
        }

        let one = Rational64::one();
        let one_minus_f0 = one - f0;
        let mut reasons: SmallVec<[u32; 4]> = SmallVec::new();
        let mut cut = LinExpr::new();
        // `Σ γ_j y_j ≥ 1`  ⟺  `R − Σ c_j x_j ≤ 0` with `c_j = ±γ_j` (sign per
        // resting side) and `R = 1 + Σ γ_j·(± bound)`.
        let mut rhs = one;

        for (xj, a_j) in &row.terms {
            let xj = *xj;
            let a_j = *a_j;
            if a_j.is_zero() {
                continue;
            }
            let j = xj as usize;
            let vj = self.simplex.value(xj);
            let lo = self.simplex.bound_lower_at(j);
            let hi = self.simplex.bound_upper_at(j);
            // Which finite bound the non-basic rests at (needed to form the
            // non-negative slack y_j).  Resting at none ⇒ no sound cut.
            // A WIDE resting bound has no `i64` algebra for the GMI
            // formulas below — the cut is declined (an optimization;
            // branch-and-bound stays complete).
            let narrow_real = |b: &super::simplex::Bound| b.value.narrow().map(|v| v.real);
            let (at_lower, bound) = if lo.is_some_and(|b| narrow_real(b) == Some(vj)) {
                (true, lo)
            } else if hi.is_some_and(|b| narrow_real(b) == Some(vj)) {
                (false, hi)
            } else {
                return None;
            };
            let bound = bound?;
            // Branch bounds carry [`BRANCH_REASON`] (no external
            // justification): a cut using one is only valid inside that
            // branch, never at the root where cuts are asserted.  Inside a
            // free-variable split scope the cut *is* scoped to the branch
            // (the simplex scope pops with it), so the bound is usable; the
            // sentinel itself never enters the reason list either way –
            // `note_bnb_conflict_reasons` filters it before any core is
            // exported.
            if bound.reason == BRANCH_REASON && !self.cuts_in_split_scope {
                return None;
            }
            for r in bound.all_reasons() {
                if r == BRANCH_REASON {
                    if !self.cuts_in_split_scope {
                        return None;
                    }
                    continue;
                }
                if !reasons.contains(&r) {
                    reasons.push(r);
                }
            }

            // Stored row orientation: x_B = x̄_B + Σ â_j y_j with â_j = a_j at
            // a lower bound and â_j = −a_j at an upper bound; the canonical
            // GMI coefficient formulas use ā_j = −â_j.
            let hat_a = if at_lower { a_j } else { -a_j };
            let bar_a = -hat_a;

            let is_int_here = self.int_vars.contains(&xj)
                && bound.value.narrow().is_some_and(|b| b.real.is_integer());
            // CHECKED GMI coefficient arithmetic: `fj / f0` (and the
            // siblings below) PANICKED in debug and silently WRAPPED in
            // release on the dillig wide-bound family — and a wrapped
            // coefficient is not merely a bad cut, it is an UNSOUND LEMMA
            // asserted into the tableau. Declining the cut is always sound
            // (cuts are an optimization; branch-and-bound remains
            // complete).
            let gamma = if is_int_here {
                let fj = bar_a - bar_a.floor();
                if fj.is_zero() {
                    continue; // γ_j = 0: the term drops out of the cut
                }
                if fj <= f0 {
                    checked_div_r64(fj, f0)?
                } else {
                    checked_div_r64(one - fj, one_minus_f0)?
                }
            // GMI continuous-variable coefficient for `ā_j ≥ 0` (with the
            // `x_B = b̄ − Σ ā_j y_j` textbook orientation `bar_a` carries):
            // `γ_j = ā_j / f0 ≥ 0`.  The previous `-bar_a / f0` here flipped
            // the sign for every non-negative coefficient, emitting a
            // negative γ — the derived cut then excluded genuine integer
            // points (a satisfiable four-constraint QF_LIA system was
            // refuted `unsat` once a second cut round used the first round's
            // continuous cut slacks; caught by the arith incremental-vs-
            // replay differential fuzzer).
            } else if bar_a >= Rational64::zero() {
                checked_div_r64(bar_a, f0)?
            } else {
                checked_div_r64(hat_a, one_minus_f0)?
            };
            if gamma.is_zero() {
                continue;
            }
            // Coefficient guard: huge cut coefficients poison every later
            // pivot on the cut row.
            if gamma.denom().abs() > Self::LIA_CUT_MAX_DENOM
                || gamma.numer().abs() > Self::LIA_CUT_MAX_DENOM
            {
                return None;
            }

            // The `γ_j·bound` accumulation is checked for the same reason:
            // a wrapped `rhs` publishes a cut that is not implied by its
            // reasons.
            let contrib = checked_mul_r64(gamma, bound.value.narrow()?.real)?;
            if at_lower {
                cut.add_term(xj, -gamma);
                rhs = checked_add_r64(rhs, contrib)?;
            } else {
                cut.add_term(xj, gamma);
                rhs = checked_sub_r64(rhs, contrib)?;
            }
        }

        if cut.terms.is_empty() {
            return None;
        }
        cut.add_constant(rhs);
        Some((cut, reasons))
    }

    /// Recursive branch-and-bound over integer variables.
    ///
    /// Uses balanced simplex push/pop so no branch constraint leaks into the
    /// caller's decision level.  The satisfying integral assignment is captured
    /// into `lia_model` at the feasible leaf (before the pushes unwind), so
    /// `value()` can report it afterwards.
    ///
    /// Returns:
    /// - `Sat` if an integral assignment is found;
    /// - `Unsat(core)` if BOTH branches on the fractional variable are
    ///   infeasible (integer-infeasible);
    /// - `Unknown` if the depth/node budget is exhausted, or a sub-solve hit the
    ///   simplex pivot limit – never a fabricated Sat/Unsat.
    ///
    /// Branch-and-bound over integer variables, as an EXPLICIT heap stack.
    ///
    /// Two-child DFS: at each node pick a fractional integer variable, explore
    /// `x ≤ ⌊x̄⌋` then `x ≥ ⌈x̄⌉`, short-circuit on the first integral leaf
    /// (`Sat`), and conclude `Unsat` only when every branch is a *proven*
    /// dead end (any unresolved branch downgrades the verdict to `Unknown`).
    /// One simplex scope per live branch, pushed before descending and popped
    /// when the subtree under it finishes, so no branch bound leaks into a
    /// sibling; the satisfying assignment is snapshotted at the leaf, inside
    /// all open scopes.
    ///
    /// The recursion is a `Vec` of node frames rather than native calls: tree
    /// depth is bounded only by [`Self::LIA_MAX_DEPTH`] and the instance, and
    /// native recursion over user-controlled depth overflows the thread stack
    /// (observed as SIGABRT on WiSA inputs around depth 4k).  A frame
    /// `{var, up_done, saw_unknown}` is the node whose DOWN (or UP) branch
    /// scope is currently open on top of the simplex scope stack; the scope
    /// and the frame are pushed and popped together, so
    /// `simplex scopes open == stack.len()` holds at every node body.
    /// Depth-first integral dive for the B&B root (see the call site).
    ///
    /// At each level, pin the first fractional integer variable to its
    /// floor (then ceil) via scoped equal bounds and recurse; accept the
    /// first feasible fully-integral leaf as the model.  Equalities cannot
    /// drift, so recursion depth is bounded by `int_vars.len()`; the node
    /// cap bounds the worst case (2^depth) and merely falls back to the
    /// ordinary search.
    fn integral_dive(&mut self, int_vars: &[VarId], nodes: &mut usize) -> bool {
        /// Probe budget: beyond this the dive declines (the ordinary
        /// branch-and-bound takes over); the dive is a heuristic repair for
        /// the free-nonbasic divergence, not a decision procedure.
        const MAX_DIVE_NODES: usize = 512;
        if *nodes >= MAX_DIVE_NODES {
            return false;
        }
        *nodes += 1;

        let (var, floor, ceil) = match self.find_fractional_int_var(int_vars) {
            Some(FracVar::Branch { var, floor, ceil }) => (var, floor, ceil),
            // No honest value and no representable branch bounds: the dive
            // cannot proceed soundly — decline (the ordinary search will
            // surface the decline as `Unknown`).
            Some(FracVar::Underivable) => return false,
            None => {
                // Fully integral — and FEASIBLE: the dive's base case can run
                // right after a failed sibling's scope pop, whose persisted
                // pivots left basic values outside their (restored, wider)
                // windows.  Snapshotting that state publishes a model that
                // violates asserted atoms, so gate on a fresh feasibility
                // probe (re-derives the stale assignment first); an infeasible
                // state declines the dive and lets the ordinary branch-and-
                // bound — whose every node re-solves — handle it.
                if !self.simplex.state_feasible() {
                    return false;
                }
                // Re-scan at the post-`state_feasible` state: the probe's
                // `crash_basis` re-derivation may have replaced the very
                // entries the scan read (a stale integral-looking entry
                // whose row-true value is fractional).  The snapshot
                // publishes the re-derived values, so integrality must be
                // established for THOSE — the same
                // re-scan-after-the-feasibility-probe discipline the B&B
                // leaf and `try_eq_incumbent` apply.
                if self.find_fractional_int_var(int_vars).is_some() {
                    return false;
                }
                self.snapshot_lia_model(int_vars);
                return true;
            }
        };
        for k in [floor, ceil] {
            let k = super::delta::BigDeltaRational::real_only(k);
            self.simplex.push();
            self.simplex
                .set_lower_exact(var, k.clone(), smallvec::smallvec![BRANCH_REASON]);
            self.simplex
                .set_upper_exact(var, k, smallvec::smallvec![BRANCH_REASON]);
            let feasible =
                matches!(self.simplex.check(), Ok(())) && !self.simplex.resource_limit_reached();

            if feasible && self.integral_dive(int_vars, nodes) {
                self.simplex.pop();
                return true;
            }
            self.simplex.pop();
        }
        false
    }

    fn bnb_search(&mut self, int_vars: &[VarId], nodes: &mut usize) -> Result<TheoryResult> {
        struct Node {
            var: VarId,
            /// The node's exact up-branch bound (`ceil` of the exact
            /// fractional value, captured at node creation — see the
            /// unwind loop for why it is not re-read from the assignment).
            /// An integral `BigRational`: the exact channel at any width.
            ceil: num_rational::BigRational,
            up_done: bool,
            saw_unknown: bool,
        }
        /// Take one branch of `var`; on a feasible, unresolved LP return
        /// `true` with the branch scope left OPEN (the caller descends),
        /// otherwise pop the scope and return `false` (with `unknown` set
        /// when the failure was a resource limit rather than infeasibility).
        fn take_branch(
            s: &mut ArithSolver,
            var: VarId,
            bound: num_rational::BigRational,
            upper: bool,
            unknown: &mut bool,
        ) -> bool {
            // The EXACT branch bound (an integral `BigRational`): the
            // widened store takes it at any width — the `Underivable`
            // decline exists now only for a value with no exact read.
            let bound = super::delta::BigDeltaRational::real_only(bound);
            s.simplex.push();
            if upper {
                s.simplex
                    .set_upper_exact(var, bound, smallvec::smallvec![BRANCH_REASON]);
            } else {
                s.simplex
                    .set_lower_exact(var, bound, smallvec::smallvec![BRANCH_REASON]);
            }
            match s.simplex.check() {
                Ok(()) if !s.simplex.resource_limit_reached() => true,
                Ok(()) => {
                    // Pivot budget exhausted: Unknown, never a fabricated Sat.
                    s.simplex.pop();
                    *unknown = true;
                    false
                }
                Err(reasons) => {
                    // LP infeasible: a proven dead end; its atom reasons feed
                    // the tree-level unsat core.
                    s.note_bnb_conflict_reasons(&reasons);
                    s.simplex.pop();
                    false
                }
            }
        }

        let mut stack: Vec<Node> = Vec::new();
        loop {
            // ===== one node body =====
            if stack.is_empty() {
                // Integral dive (once per bnb_search, at the root).  The
                // LP's fractional vertex sits on rays whose endpoints are
                // integers of the fractional variables: free nonbasic
                // integer variables rest at arbitrary values (the crash
                // basis defaults them to zero), which makes Gomory cuts
                // inapplicable (their derivation assumes bound-resting
                // nonbasics) and plain inequality branching divergent – the
                // LP re-optimizes to the next half-integral point forever
                // (`y = 2a + 1` walked a := -1/2, -3/2, -5/2 … to the depth
                // cap; the jain/Ultimate `unknown`s).  Pinning each
                // fractional variable to `floor`/`ceil` *equalities* under
                // scoped bounds cannot drift, so the dive is at most
                // #int-vars deep; a leaf that is feasible and fully
                // integral is a *found model*, accepted only as such.
                let mut dive_nodes = 0usize;
                if self.integral_dive(int_vars, &mut dive_nodes) {
                    return Ok(TheoryResult::Sat);
                }
            }
            if stack.len() > Self::LIA_MAX_DEPTH || *nodes > Self::LIA_MAX_NODES {
                for _ in 0..stack.len() {
                    self.simplex.pop();
                }
                return Ok(TheoryResult::Unknown);
            }
            *nodes += 1;
            let mut dead_leaf = false;
            let (var, floor_v, ceil_v) = match self.find_fractional_int_var(int_vars) {
                Some(FracVar::Branch { var, floor, ceil }) => (var, floor, ceil),
                Some(FracVar::Underivable) => {
                    // An integer variable with no honest value AND no exact
                    // floor/ceil (a wide-basic whose row cannot even be
                    // evaluated exactly — a stale reference): no sound
                    // acceptance and no sound branch exist — the search
                    // declines honestly rather than snapshot a fabricated
                    // value.
                    for _ in 0..stack.len() {
                        self.simplex.pop();
                    }
                    return Ok(TheoryResult::Unknown);
                }
                None => {
                    // A fully integral candidate — see the dive's base case
                    // for why a fresh feasibility pass is required before a
                    // snapshot is trusted: sibling pops leave the flag down,
                    // and `state_feasible`'s re-derivation (a bound-snap
                    // `crash_basis`, a CRUDE point — not the search's
                    // feasible vertex) can land outside the windows even
                    // though the LP this node branched into was feasible.
                    // The old code read that crude point's violation as
                    // "infeasible leaf" and unwound the WHOLE search to
                    // `Unknown`; the honest reading is "the leaf needs a
                    // repair": re-solve (the repair from the crude point
                    // converges when the node's LP is feasible), and treat a
                    // refutation as a DEAD BRANCH — the backtrack loop then
                    // tries the siblings, and an all-dead tree is `Unsat`
                    // (the `11·xi = 7` gap class: three-disjunct div/mod
                    // unsat-side members answered `unknown` here).
                    match self.simplex.check() {
                        Ok(()) if !self.simplex.resource_limit_reached() => {
                            // RE-SCAN INTEGRality AT THE RE-SOLVED VERTEX.
                            // `check()` is a full `make_feasible` solve:
                            // repairing the crude point re-optimizes the LP
                            // onto a possibly DIFFERENT vertex than the one
                            // `find_fractional_int_var` scanned.  Accepting
                            // on feasibility alone certified the crude
                            // point's integrality, not the snapshot's —
                            // the wide-constant mod false-`sat` (2026-09-19,
                            // mixed fuzz 20262113 instance 41: with
                            // `mod(−2y + 2^62, 4) > 2` committed, the re-solve
                            // left `q = (2^62−1)/4` at the accepted vertex
                            // while the scan had seen it integral).  The
                            // same re-scan-after-check discipline
                            // `try_eq_incumbent` already applies.  A newly
                            // fractional vertex branches HERE (the loop
                            // continues with it); a newly underivable one
                            // declines; only a still-integral vertex is a
                            // model.
                            match self.find_fractional_int_var(int_vars) {
                                Some(FracVar::Branch { var, floor, ceil }) => (var, floor, ceil),
                                Some(FracVar::Underivable) => {
                                    for _ in 0..stack.len() {
                                        self.simplex.pop();
                                    }
                                    return Ok(TheoryResult::Unknown);
                                }
                                None => {
                                    self.snapshot_lia_model(int_vars);
                                    for _ in 0..stack.len() {
                                        self.simplex.pop();
                                    }
                                    return Ok(TheoryResult::Sat);
                                }
                            }
                        }
                        Ok(()) => {
                            // Pivot budget: honest Unknown, never a Sat.
                            for _ in 0..stack.len() {
                                self.simplex.pop();
                            }
                            return Ok(TheoryResult::Unknown);
                        }
                        Err(_) => {
                            // Genuinely dead leaf: fall into the unwind
                            // loop (it pops this node's scope and tries the
                            // ancestors' siblings; an exhausted tree
                            // answers Unsat).
                            dead_leaf = true;
                            (
                                0,
                                num_rational::BigRational::from_integer(num_bigint::BigInt::from(
                                    0,
                                )),
                                num_rational::BigRational::from_integer(num_bigint::BigInt::from(
                                    0,
                                )),
                            )
                        }
                    }
                }
            };
            if dead_leaf {
                // The leaf took no branches: deliver the all-dead outcome
                // for THIS subtree straight to the unwind loop (identical
                // to both branches having been tried and refuted).
                let mut outcome = TheoryResult::Unsat(self.bnb_unsat_core());
                loop {
                    let Some(mut frame) = stack.pop() else {
                        return Ok(outcome);
                    };
                    self.simplex.pop();
                    frame.saw_unknown |= matches!(outcome, TheoryResult::Unknown);
                    if !frame.up_done {
                        let ceil_v = frame.ceil.clone();
                        let mut saw = frame.saw_unknown;
                        if take_branch(self, frame.var, ceil_v, false, &mut saw) {
                            frame.up_done = true;
                            frame.saw_unknown = saw;
                            stack.push(frame);
                            break;
                        }
                        frame.saw_unknown = saw;
                    }
                    outcome = if frame.saw_unknown {
                        TheoryResult::Unknown
                    } else {
                        TheoryResult::Unsat(self.bnb_unsat_core())
                    };
                }
                continue;
            }
            let mut saw_unknown = false;

            // Branch down: var <= floor(value).
            if take_branch(self, var, floor_v, true, &mut saw_unknown) {
                stack.push(Node {
                    var,
                    ceil: ceil_v,
                    up_done: false,
                    saw_unknown,
                });
                continue; // descend into the down subtree
            }
            // Branch up: var >= ceil(value).
            if take_branch(self, var, ceil_v.clone(), false, &mut saw_unknown) {
                stack.push(Node {
                    var,
                    ceil: ceil_v,
                    up_done: true,
                    saw_unknown,
                });
                continue; // descend into the up subtree
            }
            // Both branches concluded at this node without descending.
            let mut outcome = if saw_unknown {
                TheoryResult::Unknown
            } else {
                TheoryResult::Unsat(self.bnb_unsat_core())
            };

            // ===== deliver `outcome` up through the ancestor frames =====
            loop {
                let Some(mut frame) = stack.pop() else {
                    return Ok(outcome); // root concluded
                };
                // The scope of the branch this subtree ran under.
                self.simplex.pop();
                frame.saw_unknown |= matches!(outcome, TheoryResult::Unknown);
                if !frame.up_done {
                    // Try this node's up branch.  Its down-branch scope was
                    // just popped, so the LP state is the node's own again.
                    // The branch bound is the EXACT ceil captured when the
                    // node was created (re-reading `value(var)` here would
                    // consult the raw assignment entry, which for a
                    // wide-basic variable is only its exact value while
                    // that value narrows — a fabricated re-read otherwise).
                    let ceil_v = frame.ceil.clone();
                    let mut saw = frame.saw_unknown;
                    if take_branch(self, frame.var, ceil_v, false, &mut saw) {
                        frame.up_done = true;
                        frame.saw_unknown = saw;
                        stack.push(frame);
                        break; // descend into the up subtree (node body next)
                    }
                    frame.saw_unknown = saw;
                }
                outcome = if frame.saw_unknown {
                    TheoryResult::Unknown
                } else {
                    TheoryResult::Unsat(self.bnb_unsat_core())
                };
                // Continue delivering this frame's outcome to ITS parent.
            }
        }
    }

    /// Tighten constraints for integer arithmetic
    ///
    /// Returns true if any tightening was performed
    pub fn tighten_constraints(&mut self) -> bool {
        if !self.is_integer() {
            return false;
        }

        // In a full implementation, we would:
        // 1. Iterate through all bounds
        // 2. Apply tightening rules
        // 3. Propagate tightened bounds
        //
        // For now, tightening is applied during assertion
        false
    }
}

impl Theory for ArithSolver {
    fn id(&self) -> TheoryId {
        // Mixed-integer arithmetic dispatches like LIA (integer reasoning is
        // armed); there is no separate `TheoryId` variant for it.  The only
        // consumer of this id (`combination.rs` politeness) treats LIA and
        // LRA identically anyway.
        if self.is_integer() {
            TheoryId::LIA
        } else {
            TheoryId::LRA
        }
    }

    fn name(&self) -> &str {
        match self.mode {
            ArithMode::Lra => "LRA",
            ArithMode::Lia => "LIA",
            ArithMode::Mixed => "LIRA",
        }
    }

    fn can_handle(&self, _term: TermId) -> bool {
        // In a full implementation, check if term is arithmetic
        true
    }

    fn assert_true(&mut self, term: TermId) -> Result<TheoryResult> {
        // In a full implementation, parse the term and add constraints
        let _ = self.intern(term);
        Ok(TheoryResult::Sat)
    }

    fn assert_false(&mut self, term: TermId) -> Result<TheoryResult> {
        let _ = self.intern(term);
        Ok(TheoryResult::Sat)
    }

    fn check(&mut self) -> Result<TheoryResult> {
        self.lia_model.clear();
        // Slice 6 cadence: the tighten runs at every final-check round (the
        // only place wide rows from earlier rounds exist). A pending
        // crossing planted by an EARLIER round is discarded first — reason
        // ids recycle across pops, so a stale id list can map to wrong
        // terms (an invalid clause, a false `unsat`); only a crossing
        // planted by THIS check's own tighten is consumed, and no pop
        // happens between the two.
        let _ = self.simplex.bound_crossing_conflict();
        self.tighten_tableau_bounds();
        if let Some(reasons) = self.simplex.bound_crossing_conflict() {
            let mut terms: Vec<TermId> = Vec::with_capacity(reasons.len());
            let mut all_mapped = true;
            for &r in &reasons {
                match self.reasons.get(r as usize).copied() {
                    Some(term) => terms.push(term),
                    None => {
                        all_mapped = false;
                        break;
                    }
                }
            }
            if all_mapped && !terms.is_empty() {
                return Ok(TheoryResult::Unsat(terms));
            }
        }

        // Debug canary (item 91): every interned atom row's slack must
        // still satisfy `slack = r · (key form)` AT THE CURRENT POINT for
        // some positive scalar r (the intern's rescale-into-width mode
        // mints r = 1/λ; Eq rows' sign normalization allows r < 0).  A
        // detached row — the pivot zoo's corruption, observed as an
        // equality's row reduced to a trivial variable while the
        // candidate violated the atom by 34 — yields r = 0 or an
        // inconsistent r, and fires loudly.
        #[cfg(all(debug_assertions, feature = "std"))]
        {
            use num_rational::BigRational as BR;
            use std::fmt::Write as _;
            let mut broken = String::new();
            // Freshness gate: a stale assignment vector makes every basic
            // entry unreliable — the canary's evidence must come from a
            // current state (the third false-positive class).
            if self.simplex.assignment_is_current() {
                for ((key, reason), &slack) in self.atom_rows.iter() {
                    // Only rows whose CONSTRAINT is live at this scope can
                    // detach: rows are search-global, but the bound on the
                    // slack comes and goes with the asserting polarity — a
                    // popped atom's row legitimately rests anywhere (the
                    // false-positive class of the canary's first version).
                    if !self.simplex.has_live_bound(slack) {
                        continue;
                    }
                    // A key over a CONSTANT COLUMN (the big-const abstraction)
                    // is only equivalent to its row while the column's PIN is
                    // live — a floating column's stale entry poisons the key
                    // form's evaluation (the second false-positive class).
                    let mut floating_column = false;
                    for &(term, _) in &key.terms {
                        if let Some(&v) = self.term_to_var.get(&term)
                            && self.simplex.is_wide_point(v)
                            && !self.simplex.has_live_bound(v)
                        {
                            floating_column = true;
                            break;
                        }
                    }
                    if floating_column {
                        continue;
                    }
                    let Some(slack_val) = self.simplex.point_value_exact(slack) else {
                        continue;
                    };
                    let mut want = BR::new(
                        num_bigint::BigInt::from(*key.constant.numer()),
                        num_bigint::BigInt::from(*key.constant.denom()),
                    );
                    let mut ok = true;
                    for &(term, coef) in &key.terms {
                        let Some(&var) = self.term_to_var.get(&term) else {
                            ok = false;
                            break;
                        };
                        let Some(v) = self.simplex.point_value_exact(var) else {
                            ok = false;
                            break;
                        };
                        want += v.real
                            * BR::new(
                                num_bigint::BigInt::from(*coef.numer()),
                                num_bigint::BigInt::from(*coef.denom()),
                            );
                    }
                    if !ok || want.is_zero() {
                        continue; // undecidable at this point; not evidence
                    }
                    let r = &slack_val.real / &want;
                    let is_eq = self
                        .slack_forms
                        .get(&slack)
                        .is_some_and(|f| f.dir == SlackDir::Eq);
                    let good = if is_eq { !r.is_zero() } else { r.is_positive() };
                    if !good {
                        let _ = writeln!(
                            broken,
                            "  atom row v{slack} reason={reason:?}: slack {:?} is not a positive multiple of its key form's {:?} (r = {r:?})",
                            slack_val.real, want
                        );
                    }
                }
                if !broken.is_empty() {
                    debug_assert!(
                        false,
                        "atom-row equivalence broken (detached constraints):\n{broken}"
                    );
                }
            }
        }

        // Step 1: solve the LP (real) relaxation.
        match self.simplex.check() {
            Ok(()) => {
                // The pivot budget may have been exhausted without a definitive
                // answer.  In that case the assignment is NOT a model – report
                // Unknown rather than a fabricated Sat.
                if self.simplex.resource_limit_reached() {
                    return Ok(TheoryResult::Unknown);
                }
            }
            Err(reasons) => {
                // `reasons` and the simplex constraints that carry these ids are
                // pushed and popped together, so every id must resolve.  A miss
                // would silently shrink the core – and a conflict explanation
                // that loses one of its causes is not weaker, it is wrong – so
                // assert it loudly and, in release, fall back to the full set of
                // known reasons rather than a truncated one.
                let mut terms: Vec<TermId> = Vec::with_capacity(reasons.len());
                for &r in &reasons {
                    match self.reasons.get(r as usize).copied() {
                        Some(term) => terms.push(term),
                        None => {
                            debug_assert!(
                                false,
                                "simplex reported reason id {r} with no recorded term \
                                 (only {} known): the conflict core would lose a cause",
                                self.reasons.len()
                            );
                            return Ok(TheoryResult::Unsat(self.full_unsat_core()));
                        }
                    }
                }
                return Ok(TheoryResult::Unsat(terms));
            }
        }

        // Step 2 (LRA): the LP relaxation is exact – feasible LP ⇒ Sat.
        // Mixed mode falls through to Step 3 as well: its integer variables
        // live in `int_vars`, and `lia_branch_and_bound` scans exactly that
        // set, so a formula with no integer variables pays one scan that
        // finds nothing and returns Sat.
        if !self.is_integer() {
            // Model-value availability gate: a TERM-BACKED variable whose
            // defining row is wide and whose exact value does not narrow
            // has NO honest witness value — the model layer would print the
            // stale `assignment` entry (a fabricated value violating the
            // very row that defines it).  Integer variables are covered by
            // the branch-and-bound path below (its value reads are
            // wide-aware); this gate closes the pure-real acceptance.
            if self.wide_underivable_blocks_sat() {
                return Ok(TheoryResult::Unknown);
            }
            return Ok(TheoryResult::Sat);
        }

        // Step 3 (LIA): the LP relaxation being feasible is NOT sufficient – a
        // fractional assignment over Int variables must be resolved by
        // branch-and-bound before we may answer Sat.  Otherwise integer-
        // infeasible-but-LP-feasible systems (e.g. y = 2x ∧ y = 2z+1) would be
        // wrongly reported Sat with fractional values for Int terms.
        let verdict = self.lia_branch_and_bound()?;
        if matches!(verdict, TheoryResult::Sat) && self.wide_underivable_blocks_sat() {
            // Same availability gate as Step 2, for the mixed-mode Real
            // variables the integer search does not scan.
            return Ok(TheoryResult::Unknown);
        }
        Ok(verdict)
    }

    fn push(&mut self) {
        self.context_stack.push(ContextState {
            num_reasons: self.reasons.len(),
            num_shared_equalities: self.shared_equalities.len(),
            num_int_equalities: self.int_equalities.len(),
        });
        self.simplex.push();
        // Propagation-bound scope marker: `pop` replays `prop_undo` back to
        // this index, undoing every bound recorded inside this scope.
        self.prop_undo.push(PropBoundUndo::Scope);
    }

    fn pop(&mut self) {
        if let Some(state) = self.context_stack.pop() {
            // Term interning is search-global: VarIds are never recycled
            // (see `Simplex::register_var`), so `term_to_var` entries never
            // go stale and draining them would only force re-interning
            // after every backtrack.
            self.reasons.truncate(state.num_reasons);
            self.reason_counter = state.num_reasons as u32;
            self.shared_equalities.truncate(state.num_shared_equalities);
            // Only invalidate the Diophantine-feasibility cache if `pop` actually
            // removed equalities asserted in this scope; a truncate that changes
            // nothing leaves the live equality set identical, so any cached
            // verdict over it is still valid.
            if self.int_equalities.len() > state.num_int_equalities {
                self.int_eq_verdict_cache = None;
            }
            self.int_equalities.truncate(state.num_int_equalities);
            // The LIA branch-and-bound model is a snapshot of the *last* check's
            // integral assignment, keyed by VarId. Because VarIds are recycled
            // across this pop, a leftover entry could be misread by `value()`
            // for a freshly interned term that reuses the index before the next
            // `check()` repopulates it. It is only valid immediately after a
            // successful `check()`, so drop it on backtrack.
            self.lia_model.clear();
            self.simplex.pop();
            // Replay the propagation-bound undo trail back to the scope marker.
            while let Some(entry) = self.prop_undo.pop() {
                match entry {
                    PropBoundUndo::Scope => break,
                    PropBoundUndo::Lower(var, prev) => {
                        let idx = var as usize;
                        if idx < self.prop_lower.len() {
                            self.prop_lower[idx] = prev;
                        }
                    }
                    PropBoundUndo::Upper(var, prev) => {
                        if (var as usize) < self.prop_upper.len() {
                            self.prop_upper[var as usize] = prev;
                        }
                    }
                }
            }
        }
    }

    fn reset(&mut self) {
        self.simplex.reset();
        self.term_to_var.clear();
        self.atom_rows.clear();
        self.slack_forms.clear();
        self.int_vars.clear();
        // `int_terms` is deliberately KEPT: a term's integer-valuedness is a
        // structural fact (its sort), not search state, and the replay that
        // follows this reset re-interns terms through the sort-blind
        // `assert_*` paths – `intern` consults this registry to re-mark.
        // (The former sticky `unrepresentable_row_assert` flag lived here
        // too; the wide-LP build retired it — every `assert_*` entry now
        // interns its row exactly, so there is no dropped atom to remember.)
        self.var_to_term.clear();
        self.reason_counter = 0;
        self.reasons.clear();
        self.context_stack.clear();
        self.shared_equalities.clear();
        self.lia_model.clear();
        self.int_equalities.clear();
        self.int_eq_verdict_cache = None;
        self.prop_lower.clear();
        self.prop_upper.clear();
        self.prop_undo.clear();
    }

    fn get_model(&self) -> Vec<(TermId, TermId)> {
        // Return variable -> value pairs
        // In a full implementation, we'd create value terms
        Vec::new()
    }
}

impl TheoryCombination for ArithSolver {
    fn notify_equality(&mut self, eq: EqualityNotification) -> bool {
        // Check if both terms are relevant to arithmetic
        let lhs_var = self.term_to_var.get(&eq.lhs).copied();
        let rhs_var = self.term_to_var.get(&eq.rhs).copied();

        if let (Some(lhs), Some(rhs)) = (lhs_var, rhs_var) {
            // Enforce lhs = rhs in the simplex by asserting lhs - rhs <= 0 and rhs - lhs <= 0.
            // This is equivalent to lhs - rhs = 0, i.e., add_eq(lhs - rhs, 0).
            let reason_id = if let Some(r) = eq.reason {
                self.add_reason(r)
            } else {
                self.add_reason(eq.lhs)
            };

            // Build expression: lhs - rhs
            let mut expr_le = LinExpr::new();
            expr_le.add_term(lhs, Rational64::one());
            expr_le.add_term(rhs, -Rational64::one());
            // lhs - rhs <= 0
            self.simplex.add_le(expr_le, reason_id);

            // Build expression: rhs - lhs
            let mut expr_ge = LinExpr::new();
            expr_ge.add_term(rhs, Rational64::one());
            expr_ge.add_term(lhs, -Rational64::one());
            // rhs - lhs <= 0  (i.e., lhs - rhs >= 0)
            self.simplex.add_le(expr_ge, reason_id);

            // Record so that get_shared_equalities can return it
            self.shared_equalities.push(eq);

            true
        } else {
            // Terms not relevant to this arithmetic solver
            false
        }
    }

    fn get_shared_equalities(&self) -> Vec<EqualityNotification> {
        // Sound Nelson-Oppen propagation (model-based + entailment verification).
        //
        // Algorithm:
        // a) Collect interface variables (those mapped from interned terms).
        // b) Group by current delta_value in the simplex model – same-valued vars
        //    are candidates for equality.
        // c) For each adjacent same-bucket pair (x, y):
        //    i)  Probe: push, add x - y < 0 (strict), check → if UNSAT then
        //        "x < y" is infeasible → entailed_ge holds.
        //    ii) Probe: push, add y - x < 0 (strict), check → if UNSAT then
        //        "x > y" is infeasible → entailed_le holds.
        //    iii) Emit equality only if BOTH probes are UNSAT.
        // d) Also include equalities accumulated via notify_equality.

        // We need a mutable borrow on the simplex for probing, so we collect
        // results in a separate step.  Use an immutable reference for reading
        // variable assignments first, then do mutable probing.

        // Need &mut self for probing; but the trait signature is &self.
        // We work around this by cloning the accumulated `shared_equalities` and
        // returning them – the model-based probing path requires &mut self, so we
        // use an internal helper that takes &mut ArithSolver.
        self.shared_equalities.clone()
    }

    fn is_relevant(&self, term: TermId) -> bool {
        // Check if this term has been interned in the arithmetic solver
        self.term_to_var.contains_key(&term)
    }
}

impl ArithSolver {
    /// Whether some TERM-BACKED variable's exact value is unavailable: its
    /// defining row lives in the wide store and its exact value does not
    /// narrow.  Such a variable has no honest witness value — the model
    /// layer would print the stale `assignment` entry (a fabricated value
    /// violating the row that defines the variable: the wide-coefficient
    /// false-`sat` class of 2026-09-15, where `v1` printed `0` against a row
    /// forcing `v1 = −9 − 41/2⁶³`).  Purely internal slacks are exempt
    /// (their values are never printed), which keeps otherwise-decidable
    /// wide formulas decidable.
    fn wide_underivable_blocks_sat(&self) -> bool {
        let mut any_wide = false;
        for (var, wexpr) in self.simplex.wide_rows_iter() {
            any_wide = true;
            let _ = wexpr;
            // Derivable values do not block: a NARROWING value publishes
            // through `value`, and an unrepresentable one still publishes
            // EXACTLY through the wide channel (`value_exact` synthesizes
            // the rational term on the model side).  Only a value not even
            // exactly derivable (stale reference) is a genuine block.
            if self.simplex.delta_value_exact(var).is_some()
                || self.simplex.wide_basic_value_exact(var).is_some()
            {
                continue;
            }
            if self.term_to_var.values().any(|&v| v == var) {
                return true;
            }
        }
        let _ = any_wide;
        false
    }
    /// Sound Nelson-Oppen equality propagation.
    ///
    /// Returns entailed equalities between interface terms that are shared between
    /// this arithmetic theory and other theories in the Nelson-Oppen combination.
    ///
    /// Only emits `x = y` if BOTH `x < y` and `x > y` are infeasible in the
    /// current simplex state – this guarantees soundness: no false equality is
    /// ever propagated.
    ///
    /// Uses probe-and-pop to avoid permanently modifying the simplex state.
    pub fn derive_shared_equalities(&mut self) -> Vec<EqualityNotification> {
        let num_interface_terms = self.var_to_term.len();
        if num_interface_terms < 2 {
            return self.shared_equalities.clone();
        }

        // Collect (delta_value, VarId, TermId) for all interned variables.
        let mut candidates: Vec<(super::delta::DeltaRational, VarId, TermId)> = self
            .var_to_term
            .iter()
            .enumerate()
            .filter_map(|(idx, &term)| {
                // term_to_var maps TermId → VarId; we stored in var_to_term in order
                let var = self.term_to_var.get(&term).copied()?;
                let _ = idx; // suppress warning
                // Wide-aware read: a variable whose honest value does not
                // narrow (wide basic / wide point) is SKIPPED, never read
                // from the stale narrow entry — a fabricated `0` would
                // merge two such variables into a phony equality.
                let dval = self.simplex.delta_value_exact(var)?;
                Some((dval, var, term))
            })
            .collect();

        if candidates.len() < 2 {
            return self.shared_equalities.clone();
        }

        // Sort by current assignment value so same-valued pairs are adjacent.
        candidates.sort_by_key(|a| a.0);

        let mut result = self.shared_equalities.clone();

        // Check adjacent same-bucket pairs.
        let mut i = 0;
        while i < candidates.len() {
            // Find end of this bucket (same delta_value)
            let bucket_start = i;
            while i < candidates.len() && candidates[i].0 == candidates[bucket_start].0 {
                i += 1;
            }
            let bucket = &candidates[bucket_start..i];

            // For each adjacent pair in the bucket, probe for entailment.
            for pair_idx in 0..bucket.len().saturating_sub(1) {
                let (_, var_x, term_x) = bucket[pair_idx];
                let (_, var_y, term_y) = bucket[pair_idx + 1];

                // Probe 1: Can x < y? (i.e., x - y < 0)
                // If UNSAT → x >= y is entailed (x cannot be strictly less than y).
                let entailed_ge = {
                    self.simplex.push();
                    // Add strict x - y < 0
                    let mut expr = LinExpr::new();
                    expr.add_term(var_x, Rational64::one());
                    expr.add_term(var_y, -Rational64::one());
                    self.simplex.add_strict_lt(expr, 0);
                    let infeasible = self.simplex.check().is_err();
                    self.simplex.pop();
                    infeasible
                };

                // Probe 2: Can x > y? (i.e., y - x < 0)
                // If UNSAT → x <= y is entailed (x cannot be strictly greater than y).
                let entailed_le = {
                    self.simplex.push();
                    // Add strict y - x < 0
                    let mut expr = LinExpr::new();
                    expr.add_term(var_y, Rational64::one());
                    expr.add_term(var_x, -Rational64::one());
                    self.simplex.add_strict_lt(expr, 0);
                    let infeasible = self.simplex.check().is_err();
                    self.simplex.pop();
                    infeasible
                };

                // Both strict directions infeasible → x = y is entailed.
                if entailed_ge && entailed_le {
                    // Avoid duplicates from shared_equalities.
                    let already_known = result.iter().any(|eq| {
                        (eq.lhs == term_x && eq.rhs == term_y)
                            || (eq.lhs == term_y && eq.rhs == term_x)
                    });
                    if !already_known {
                        result.push(EqualityNotification {
                            lhs: term_x,
                            rhs: term_y,
                            reason: None,
                        });
                    }
                }
            }
        }

        result
    }

    /// Group the interface (arith-interned) terms by their current simplex
    /// model value, returning every group of size >= 2 (terms the arithmetic
    /// model currently holds *equal*).  Cheap -- no feasibility probe, just a
    /// value read and a sort.  These groups are the candidate set for
    /// [`Self::entailed_equal_reason`]; the caller (which knows the EUF class
    /// structure) filters out pairs already equal in EUF before paying for a
    /// probe, which is what keeps theory combination affordable on large
    /// interfaces.
    pub fn interface_value_buckets(&self) -> Vec<Vec<TermId>> {
        if self.var_to_term.len() < 2 {
            return Vec::new();
        }
        let mut candidates: Vec<(super::delta::DeltaRational, TermId)> = self
            .var_to_term
            .iter()
            .filter_map(|&term| {
                let var = self.term_to_var.get(&term).copied()?;
                // Wide-aware read (see the shared-equality candidates).
                Some((self.simplex.delta_value_exact(var)?, term))
            })
            .collect();
        if candidates.len() < 2 {
            return Vec::new();
        }
        candidates.sort_by_key(|a| a.0);
        let mut buckets: Vec<Vec<TermId>> = Vec::new();
        let mut i = 0;
        while i < candidates.len() {
            let start = i;
            while i < candidates.len() && candidates[i].0 == candidates[start].0 {
                i += 1;
            }
            if i - start >= 2 {
                buckets.push(candidates[start..i].iter().map(|(_, t)| *t).collect());
            }
        }
        buckets
    }

    /// Sound comparison-entailment probe (bound propagation core).
    ///
    /// For a comparison atom `sum(coef_i·x_i) <op> constant`, returns
    /// `Some((truth, reason))` iff arithmetic *forces* the atom to `truth`
    /// (true or false) – implemented as two push/check/pop probes: assert the
    /// atom (if infeasible, FALSE is forced) and assert its negation (if
    /// infeasible, TRUE is forced).  `reason` is the Farkas certificate.
    /// Sound by construction: the probes are on a scratch simplex scope.
    ///
    /// `less`: `sum ≤/< c` (Le/Lt) vs `sum ≥/> c` (Ge/Gt).
    /// `strict`: strict inequality (Lt/Gt) vs non-strict (Le/Ge).
    #[allow(clippy::too_many_arguments)]
    pub fn comparison_entailed_reason(
        &mut self,
        terms: &[(TermId, Rational64)],
        constant: Rational64,
        less: bool,
        strict: bool,
    ) -> Option<(bool, Vec<TermId>)> {
        let mut e = LinExpr::constant(-constant);
        for &(term, coef) in terms {
            let &var = self.term_to_var.get(&term)?;
            e.add_term(var, coef);
        }
        let mut neg_e = LinExpr::constant(constant);
        for &(term, coef) in terms {
            if let Some(&var) = self.term_to_var.get(&term) {
                neg_e.add_term(var, -coef);
            }
        }
        let base = self.reasons.len();
        let probe = |simplex: &mut Simplex, expr: LinExpr, is_strict: bool| -> Option<Vec<u32>> {
            simplex.push();
            if is_strict {
                simplex.add_strict_lt(expr, 0);
            } else {
                simplex.add_le(expr, 0);
            }
            let r = simplex.check().err();
            simplex.pop();
            r
        };
        let (atom_expr, atom_strict, neg_expr, neg_strict) = match (less, strict) {
            (true, false) => (e.clone(), false, neg_e.clone(), true),
            (true, true) => (e.clone(), true, neg_e.clone(), false),
            (false, false) => (neg_e.clone(), false, e.clone(), true),
            (false, true) => (neg_e.clone(), true, e.clone(), false),
        };
        if let Some(reasons) = probe(&mut self.simplex, neg_expr, neg_strict) {
            return Some((true, self.reasons_from_ids(&reasons, base)));
        }
        if let Some(reasons) = probe(&mut self.simplex, atom_expr, atom_strict) {
            return Some((false, self.reasons_from_ids(&reasons, base)));
        }
        None
    }

    /// Collect reason terms from simplex Farkas IDs, truncate scratch buffer.
    fn reasons_from_ids(&mut self, ids: &[u32], base: usize) -> Vec<TermId> {
        let mut out: Vec<TermId> = Vec::new();
        for &rid in ids {
            if let Some(&t) = self.reasons.get(rid as usize) {
                out.push(t);
            }
        }
        self.reasons.truncate(base);
        self.reason_counter = base as u32;
        out.sort_unstable();
        out.dedup();
        if out.is_empty() {
            out = self.full_unsat_core();
        }
        out
    }

    /// Soundly derive lower/upper bounds on a linear expression `Σ coefᵢ·termᵢ
    /// + constant` from the simplex's current per-variable bounds, returning
    /// the reason `TermId`s (the atoms whose assertions produced the bounds).
    ///
    /// Each direction is `None` when some variable lacks the needed bound
    /// direction.  This is the cheap (`O(expr)`, no LP solve) Dutertre–de
    /// Oliveira bound derivation: a *relaxation* that is never tighter than
    /// the true bound, so any atom it forces is genuinely forced (sound).
    ///
    /// Optionally tighten the tableau's variable bounds first via
    /// [`Simplex::propagate_bounds`] (`tighten = true`) so derived (transitive)
    /// bounds feed the expression derivation – needed to catch propagation
    /// chains through tableau rows (e.g. finite-domain recurrences).
    #[must_use]
    pub fn derive_expr_bound_reasons(
        &mut self,
        terms: &[(TermId, Rational64)],
        constant: Rational64,
        tighten: bool,
    ) -> (ExplainedBound, ExplainedBound) {
        // NOTE: `tighten` is accepted for API stability but the tableau
        // tightening is now done ONCE per assertion by the caller
        // ([`Self::tighten_tableau_bounds`]) rather than per-atom here –
        // running `propagate_bounds` (O(tableau)) inside this per-atom method
        // made `=tight` O(tableau × atoms × assertions), far too slow.  The
        // populated simplex bounds are read below regardless.
        let _ = tighten;
        let mut var_terms: Vec<(VarId, Rational64)> = Vec::with_capacity(terms.len());
        for &(term, coef) in terms {
            let Some(&var) = self.term_to_var.get(&term) else {
                return (None, None);
            };
            var_terms.push((var, coef));
        }
        // Derive the expression bound from the propagation-only single-variable
        // tracker (`prop_lower`/`prop_upper`), falling back to the simplex's own
        // bounds (slack-derived, via `propagate_bounds`) so transitive bounds
        // also feed the derivation when `tighten` was requested.  Each bound's
        // antecedent is its `reason` id; collecting all of them yields a sound
        // explanation of the derived expression bound.
        let map_reasons = |rids: &SmallVec<[u32; 4]>| -> Vec<TermId> {
            let mut out: Vec<TermId> = Vec::with_capacity(rids.len());
            for &rid in rids {
                if let Some(&t) = self.reasons.get(rid as usize) {
                    out.push(t);
                }
            }
            out.sort_unstable();
            out.dedup();
            out
        };
        // Lower bound of e = Σ coefᵢ·varᵢ + constant.
        let mut lo_val = DeltaRational::from_rational(constant);
        let mut lo_reasons: SmallVec<[u32; 4]> = SmallVec::new();
        let mut lo_ok = true;
        for &(var, coef) in &var_terms {
            if coef.is_zero() {
                continue;
            }
            let bound = if coef.is_positive() {
                // needs lower(var): tracker first, then simplex
                self.prop_get_lower(var)
                    .map(|e| (e.value, e.reason))
                    .or_else(|| {
                        self.simplex
                            .get_lower(var)
                            .and_then(|b| b.value.narrow().map(|v| (v, b.reason)))
                    })
            } else {
                self.prop_get_upper(var)
                    .map(|e| (e.value, e.reason))
                    .or_else(|| {
                        self.simplex
                            .get_upper(var)
                            .and_then(|b| b.value.narrow().map(|v| (v, b.reason)))
                    })
            };
            let Some((bv, br)) = bound else {
                lo_ok = false;
                break;
            };
            lo_val += bv * coef;
            lo_reasons.push(br);
            if let Some(b) = self.simplex.get_lower(var) {
                lo_reasons.extend(b.aux_reasons.iter().copied());
            }
            if let Some(b) = self.simplex.get_upper(var) {
                lo_reasons.extend(b.aux_reasons.iter().copied());
            }
        }
        // Upper bound of e.
        let mut hi_val = DeltaRational::from_rational(constant);
        let mut hi_reasons: SmallVec<[u32; 4]> = SmallVec::new();
        let mut hi_ok = true;
        for &(var, coef) in &var_terms {
            if coef.is_zero() {
                continue;
            }
            let bound = if coef.is_positive() {
                self.prop_get_upper(var)
                    .map(|e| (e.value, e.reason))
                    .or_else(|| {
                        self.simplex
                            .get_upper(var)
                            .and_then(|b| b.value.narrow().map(|v| (v, b.reason)))
                    })
            } else {
                self.prop_get_lower(var)
                    .map(|e| (e.value, e.reason))
                    .or_else(|| {
                        self.simplex
                            .get_lower(var)
                            .and_then(|b| b.value.narrow().map(|v| (v, b.reason)))
                    })
            };
            let Some((bv, br)) = bound else {
                hi_ok = false;
                break;
            };
            hi_val += bv * coef;
            hi_reasons.push(br);
            if let Some(b) = self.simplex.get_lower(var) {
                hi_reasons.extend(b.aux_reasons.iter().copied());
            }
            if let Some(b) = self.simplex.get_upper(var) {
                hi_reasons.extend(b.aux_reasons.iter().copied());
            }
        }
        lo_reasons.sort_unstable();
        lo_reasons.dedup();
        hi_reasons.sort_unstable();
        hi_reasons.dedup();
        let lower = lo_ok.then_some((lo_val, map_reasons(&lo_reasons)));
        let upper = hi_ok.then_some((hi_val, map_reasons(&hi_reasons)));
        (lower, upper)
    }

    /// Sound disequality-entailment probe.  Returns `Some(reason)` iff
    /// arithmetic forces `x ≠ y` (i.e. `x = y` is infeasible).  cvc5's
    /// `watchedVariableCannotBeZero` analogue.
    pub fn entailed_disequal_reason(&mut self, x: TermId, y: TermId) -> Option<Vec<TermId>> {
        let (Some(var_x), Some(var_y)) = (
            self.term_to_var.get(&x).copied(),
            self.term_to_var.get(&y).copied(),
        ) else {
            return None;
        };
        let base = self.reasons.len();
        self.simplex.push();
        let mut e1 = LinExpr::new();
        e1.add_term(var_x, Rational64::one());
        e1.add_term(var_y, -Rational64::one());
        self.simplex.add_le(e1, 0);
        let mut e2 = LinExpr::new();
        e2.add_term(var_y, Rational64::one());
        e2.add_term(var_x, -Rational64::one());
        self.simplex.add_le(e2, 0);
        let conflict = self.simplex.check().err();
        self.simplex.pop();
        let reasons = conflict?;
        Some(self.reasons_from_ids(&reasons, base))
    }

    /// Sound single-pair equality-entailment probe with a Farkas reason.
    ///
    /// Returns `Some(reason)` exactly when both `x < y` and `x > y` are
    /// infeasible in the current simplex state. The two scratch scopes are
    /// always popped, so probing does not alter incremental solver state.
    pub fn entailed_equal_reason(&mut self, x: TermId, y: TermId) -> Option<Vec<TermId>> {
        let (Some(var_x), Some(var_y)) = (
            self.term_to_var.get(&x).copied(),
            self.term_to_var.get(&y).copied(),
        ) else {
            return None;
        };
        let base = self.reasons.len();
        // x < y infeasible  <=>  x >= y entailed.
        let ge_reasons = {
            self.simplex.push();
            let mut e = LinExpr::new();
            e.add_term(var_x, Rational64::one());
            e.add_term(var_y, -Rational64::one());
            self.simplex.add_strict_lt(e, 0);
            let r = self.simplex.check().err();
            self.simplex.pop();
            r
        };
        let ge_reasons = ge_reasons?;
        // x > y infeasible  <=>  x <= y entailed.
        let le_reasons = {
            self.simplex.push();
            let mut e = LinExpr::new();
            e.add_term(var_y, Rational64::one());
            e.add_term(var_x, -Rational64::one());
            self.simplex.add_strict_lt(e, 0);
            let r = self.simplex.check().err();
            self.simplex.pop();
            r
        };
        let le_reasons = le_reasons?;
        let mut reason_terms: Vec<TermId> = Vec::new();
        for &rid in ge_reasons.iter().chain(le_reasons.iter()) {
            if let Some(&t) = self.reasons.get(rid as usize) {
                reason_terms.push(t);
            }
        }
        self.reasons.truncate(base);
        self.reason_counter = base as u32;
        reason_terms.sort_unstable();
        reason_terms.dedup();
        if reason_terms.is_empty() {
            // Entailed at decision level 0 (no atom reason): justify with the
            // full unsat-core so a conflict citing this merge is explainable.
            reason_terms = self.full_unsat_core();
        }
        Some(reason_terms)
    }
}

#[cfg(test)]
mod fuzz_incremental;

#[cfg(test)]
mod tests {
    use super::*;
    use num_traits::{One, Zero};

    /// Regression (2026-09-10): the Gomory mixed-integer cut's
    /// continuous-variable branch had a sign error for `bar_a >= 0`
    /// (`-bar_a / f0`, a negative γ where the GMI formula requires
    /// `bar_a / f0`).  The invalid cut excluded genuine integer points and,
    /// once a second cut round used the first round's continuous cut slacks,
    /// refuted this satisfiable four-constraint system as `unsat` (found by
    /// the `arith_incremental_matches_replay_fuzz` differential; witness
    /// t1=0, t2=4, t3=7, t4=0, z3-certified `sat`).
    #[test]
    fn gomory_continuous_branch_sign_does_not_refute_satisfiable_system() {
        use crate::theory::Theory as _;
        let mut s = ArithSolver::lia();
        let t = |i: u32| TermId::new(i);
        let r = Rational64::from_integer;
        // >: t3 + 2*t1 - 3*t4 > -3
        s.assert_gt(&[(t(3), r(1)), (t(1), r(2)), (t(4), r(-3))], r(-3), t(100));
        // >: t2 - 2*t1 > 3
        s.assert_gt(&[(t(2), r(1)), (t(1), r(-2))], r(3), t(101));
        // =: -2*t3 + t3 - t4 = -7  (duplicate-term spelling of t3 + t4 = 7)
        s.assert_eq(&[(t(3), r(-2)), (t(3), r(1)), (t(4), r(-1))], r(-7), t(102));
        // >=: 2*t2 + 3*t4 >= 4
        s.assert_ge(&[(t(2), r(2)), (t(4), r(3))], r(4), t(103));
        assert!(
            matches!(s.check(), Ok(TheoryResult::Sat)),
            "satisfiable system refuted (GMI continuous-branch cut): {}",
            "witness t1=0 t2=4 t3=7 t4=0"
        );
    }

    /// The parity-shaped pure-equality class that stall(ed) branch-and-bound:
    /// unbounded vertex equations with slack, even total charge.  The
    /// Hermite fast path must decide it (see
    /// `docs/studies/2026-09-06-mixed-parity-lia-equality-gap.md`).
    #[test]
    fn pure_equality_parity_system_even_charge_is_sat() {
        let mut solver = ArithSolver::lia();
        let mut reason = 10_000u32;
        let term_id = |v: u32| TermId::new(v);
        // 12 vertices, spanning-star + ring edges (deterministic).
        let verts = 12usize;
        let mut edges: Vec<(usize, usize)> = Vec::new();
        for v in 1..verts {
            edges.push((0, v));
        }
        for v in 0..verts {
            edges.push((v, (v + 1) % verts));
        }
        let charge = [1u8, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]; // total 2: even
        // Columns: i_e (edges) then k_v (slack), moved to the left side:
        // sum_{e incident} i_e - 2*k_v = c_v.
        for (v, &ch) in charge.iter().enumerate() {
            let mut terms: Vec<(TermId, Rational64)> = Vec::new();
            for (e, &(a, b)) in edges.iter().enumerate() {
                if a == v || b == v {
                    terms.push((term_id(e as u32), Rational64::from_integer(1)));
                }
            }
            terms.push((
                term_id((edges.len() + v) as u32),
                Rational64::from_integer(-2),
            ));
            reason += 1;
            solver.assert_eq(
                &terms,
                Rational64::from_integer(i64::from(ch)),
                TermId::new(reason),
            );
        }
        assert!(
            matches!(solver.check(), Ok(TheoryResult::Sat)),
            "even-charge parity system must be decided Sat by the Hermite fast path"
        );
    }

    #[test]
    fn pure_equality_parity_system_odd_charge_is_unsat() {
        let mut solver = ArithSolver::lia();
        let mut reason = 20_000u32;
        let verts = 8usize;
        let mut edges: Vec<(usize, usize)> = Vec::new();
        for v in 1..verts {
            edges.push((0, v));
        }
        for v in 0..verts {
            edges.push((v, (v + 1) % verts));
        }
        let charge = [1u8, 0, 0, 0, 0, 0, 0, 0]; // total 1: odd
        for (v, &ch) in charge.iter().enumerate() {
            let mut terms: Vec<(TermId, Rational64)> = Vec::new();
            for (e, &(a, b)) in edges.iter().enumerate() {
                if a == v || b == v {
                    terms.push((TermId::new(e as u32), Rational64::from_integer(1)));
                }
            }
            terms.push((
                TermId::new((edges.len() + v) as u32),
                Rational64::from_integer(-2),
            ));
            reason += 1;
            solver.assert_eq(
                &terms,
                Rational64::from_integer(i64::from(ch)),
                TermId::new(reason),
            );
        }
        assert!(
            matches!(solver.check(), Ok(TheoryResult::Unsat(_))),
            "odd-charge parity system must be refuted"
        );
    }

    #[test]
    fn test_arith_basic() {
        let mut solver = ArithSolver::lra();

        let x = TermId::new(1);
        let y = TermId::new(2);
        let reason = TermId::new(100);

        // x >= 0
        solver.assert_ge(
            &[(x, Rational64::one())],
            Rational64::from_integer(0),
            reason,
        );

        // y >= 0
        solver.assert_ge(
            &[(y, Rational64::one())],
            Rational64::from_integer(0),
            reason,
        );

        // x + y <= 10
        solver.assert_le(
            &[(x, Rational64::one()), (y, Rational64::one())],
            Rational64::from_integer(10),
            reason,
        );

        let result = solver.check().expect("test operation should succeed");
        assert!(matches!(result, TheoryResult::Sat));
    }

    #[test]
    fn test_arith_unsat() {
        let mut solver = ArithSolver::lra();

        let x = TermId::new(1);
        let reason = TermId::new(100);

        // x >= 10
        solver.assert_ge(
            &[(x, Rational64::one())],
            Rational64::from_integer(10),
            reason,
        );

        // x <= 5
        solver.assert_le(
            &[(x, Rational64::one())],
            Rational64::from_integer(5),
            reason,
        );

        let result = solver.check().expect("test operation should succeed");
        assert!(matches!(result, TheoryResult::Unsat(_)));
    }

    #[test]
    fn test_arith_strict_inequality() {
        let mut solver = ArithSolver::lra();

        let x = TermId::new(1);
        let reason = TermId::new(100);

        // x > 0 (strict)
        solver.assert_gt(
            &[(x, Rational64::one())],
            Rational64::from_integer(0),
            reason,
        );

        // x < 10 (strict)
        solver.assert_lt(
            &[(x, Rational64::one())],
            Rational64::from_integer(10),
            reason,
        );

        let result = solver.check().expect("test operation should succeed");
        assert!(matches!(result, TheoryResult::Sat));
    }

    #[test]
    fn test_arith_strict_unsat() {
        let mut solver = ArithSolver::lra();

        let x = TermId::new(1);
        let reason = TermId::new(100);

        // x >= 5
        solver.assert_ge(
            &[(x, Rational64::one())],
            Rational64::from_integer(5),
            reason,
        );

        // x < 5 (strict) - should be unsatisfiable with x >= 5
        solver.assert_lt(
            &[(x, Rational64::one())],
            Rational64::from_integer(5),
            reason,
        );

        let result = solver.check().expect("test operation should succeed");
        assert!(matches!(result, TheoryResult::Unsat(_)));
    }

    #[test]
    fn test_coefficient_normalization_lia() {
        let mut solver = ArithSolver::lia();

        let x = TermId::new(1);
        let y = TermId::new(2);
        let reason = TermId::new(100);

        // 2x + 4y <= 10 should be normalized to x + 2y <= 5 (GCD = 2)
        solver.assert_le(
            &[
                (x, Rational64::from_integer(2)),
                (y, Rational64::from_integer(4)),
            ],
            Rational64::from_integer(10),
            reason,
        );

        // The solver should handle this correctly
        let result = solver.check().expect("test operation should succeed");
        assert!(matches!(result, TheoryResult::Sat));
    }

    #[test]
    fn test_coefficient_normalization_sign() {
        let solver = ArithSolver::lra();

        let _x = TermId::new(1);
        let _y = TermId::new(2);

        // Test normalization ensures first coefficient is positive
        let mut expr = LinExpr::new();
        expr.add_term(0, Rational64::from_integer(-3));
        expr.add_term(1, Rational64::from_integer(2));

        solver.normalize_expr(&mut expr);

        // After normalization, first coefficient should be positive
        if let Some((_, c)) = expr.terms.first() {
            assert!(c > &Rational64::zero());
        }
    }

    #[test]
    fn test_gcd_computation() {
        assert_eq!(gcd_i64(12, 8), 4);
        assert_eq!(gcd_i64(15, 25), 5);
        assert_eq!(gcd_i64(7, 13), 1);
        assert_eq!(gcd_i64(0, 5), 5);
        assert_eq!(gcd_i64(5, 0), 5);
        assert_eq!(gcd_i64(-12, 8), 4);
        assert_eq!(gcd_i64(12, -8), 4);
    }

    // Audit regression (theories-arith): the GCD-infeasibility path in
    // `assert_eq` used to fabricate its contradictory bounds with a
    // hardcoded `reason` id of `0`, so the resulting UNSAT conflict always
    // cited whatever the FIRST reason ever added happened to be, instead of
    // the actual assertion that caused the contradiction. Assert an
    // unrelated, satisfiable constraint first (populating reason id `0`
    // with an unrelated term), then a GCD-infeasible equality with a
    // DIFFERENT reason term, and confirm the conflict cites the real
    // culprit.
    #[test]
    fn audit_gcd_infeasibility_conflict_cites_real_reason() {
        let mut solver = ArithSolver::lia();

        let x = TermId::new(10);
        let y = TermId::new(20);
        let unrelated_reason = TermId::new(1);
        let real_reason = TermId::new(2);

        // x >= 0: satisfiable, unrelated to the GCD conflict. If the old
        // hardcoded-reason-0 bug were still present, this becomes
        // `self.reasons[0]`, and the GCD conflict below would wrongly cite
        // it instead of `real_reason`.
        solver.assert_ge(
            &[(x, Rational64::one())],
            Rational64::zero(),
            unrelated_reason,
        );

        // 2y = 7 has no integer solution: gcd(2) = 2 does not divide 7.
        solver.assert_eq(
            &[(y, Rational64::from_integer(2))],
            Rational64::from_integer(7),
            real_reason,
        );

        let result = solver.check().expect("check should succeed");
        match result {
            TheoryResult::Unsat(conflict) => {
                assert!(
                    conflict.contains(&real_reason),
                    "GCD-infeasibility conflict must cite the actual violating \
                     assertion {real_reason:?}, got {conflict:?}"
                );
            }
            other => panic!("expected Unsat (2y=7 is GCD-infeasible over integers), got {other:?}"),
        }
    }

    #[test]
    fn test_bound_tightening_lia() {
        let solver = ArithSolver::lia();

        // Upper bound tightening: x <= 5.7 -> x <= 5
        let tightened = solver.tighten_bound(Rational64::new(57, 10), true);
        assert_eq!(tightened, Rational64::from_integer(5));

        // Lower bound tightening: x >= 2.3 -> x >= 3
        let tightened = solver.tighten_bound(Rational64::new(23, 10), false);
        assert_eq!(tightened, Rational64::from_integer(3));

        // Integer bounds don't change
        let tightened = solver.tighten_bound(Rational64::from_integer(5), true);
        assert_eq!(tightened, Rational64::from_integer(5));
    }

    #[test]
    fn test_bound_tightening_lra() {
        let solver = ArithSolver::lra();

        // No tightening for real arithmetic
        let bound = Rational64::new(57, 10);
        let tightened = solver.tighten_bound(bound, true);
        assert_eq!(tightened, bound);
    }

    #[test]
    fn test_tighten_constraints() {
        let mut solver_lia = ArithSolver::lia();
        let mut solver_lra = ArithSolver::lra();

        // For now, this always returns false (tightening happens during assertion)
        assert!(!solver_lia.tighten_constraints());
        assert!(!solver_lra.tighten_constraints());
    }

    /// Test that x > 5 AND x < 6 is UNSAT for integers (no integer in open interval (5,6))
    /// This is the bug report test case: strict inequalities must be transformed for LIA
    #[test]
    fn test_lia_strict_inequality_empty_interval() {
        let mut solver = ArithSolver::lia();

        let x = TermId::new(1);
        let reason = TermId::new(100);

        // x > 5 (for integers, this becomes x >= 6)
        solver.assert_gt(
            &[(x, Rational64::one())],
            Rational64::from_integer(5),
            reason,
        );

        // x < 6 (for integers, this becomes x <= 5)
        solver.assert_lt(
            &[(x, Rational64::one())],
            Rational64::from_integer(6),
            reason,
        );

        // Should be UNSAT: x >= 6 AND x <= 5 is impossible
        let result = solver.check().expect("test operation should succeed");
        assert!(
            matches!(result, TheoryResult::Unsat(_)),
            "Expected UNSAT for x > 5 AND x < 6 in LIA, got {:?}",
            result
        );
    }

    /// Test that x > 5 AND x < 6 is SAT for reals (5.5 is a valid solution)
    #[test]
    fn test_lra_strict_inequality_has_solution() {
        let mut solver = ArithSolver::lra();

        let x = TermId::new(1);
        let reason = TermId::new(100);

        // x > 5
        solver.assert_gt(
            &[(x, Rational64::one())],
            Rational64::from_integer(5),
            reason,
        );

        // x < 6
        solver.assert_lt(
            &[(x, Rational64::one())],
            Rational64::from_integer(6),
            reason,
        );

        // Should be SAT for reals: x = 5.5 is a valid solution
        let result = solver.check().expect("test operation should succeed");
        assert!(
            matches!(result, TheoryResult::Sat),
            "Expected SAT for x > 5 AND x < 6 in LRA, got {:?}",
            result
        );
    }

    /// Test x >= 5 AND x <= 5 with strict bounds in LIA
    #[test]
    fn test_lia_strict_at_boundary() {
        let mut solver = ArithSolver::lia();

        let x = TermId::new(1);
        let reason = TermId::new(100);

        // x >= 5
        solver.assert_ge(
            &[(x, Rational64::one())],
            Rational64::from_integer(5),
            reason,
        );

        // x < 6 (becomes x <= 5)
        solver.assert_lt(
            &[(x, Rational64::one())],
            Rational64::from_integer(6),
            reason,
        );

        // Should be SAT: x = 5 is the only solution
        let result = solver.check().expect("test operation should succeed");
        assert!(
            matches!(result, TheoryResult::Sat),
            "Expected SAT for x >= 5 AND x < 6 in LIA, got {:?}",
            result
        );
    }

    // ======== Nelson-Oppen tests ========

    /// x <= y AND y <= x should yield an entailed equality.
    #[test]
    fn test_no_entailed_equality_bidirectional() {
        let mut solver = ArithSolver::lra();

        let x = TermId::new(1);
        let y = TermId::new(2);
        let reason = TermId::new(100);

        // Intern both so they appear in var_to_term.
        solver.intern(x);
        solver.intern(y);

        // x <= y
        solver.assert_le(
            &[(x, Rational64::one()), (y, -Rational64::one())],
            Rational64::from_integer(0),
            reason,
        );
        // y <= x
        solver.assert_le(
            &[(y, Rational64::one()), (x, -Rational64::one())],
            Rational64::from_integer(0),
            reason,
        );

        let sat = solver.check().expect("check should succeed");
        assert!(matches!(sat, TheoryResult::Sat), "Expected SAT");

        // Both x < y and x > y should be infeasible – equality is entailed.
        let eqs = solver.derive_shared_equalities();
        let has_xy = eqs
            .iter()
            .any(|e| (e.lhs == x && e.rhs == y) || (e.lhs == y && e.rhs == x));
        assert!(
            has_xy,
            "Expected entailed equality between x and y, got: {:?}",
            eqs
        );
    }

    /// x <= y alone should NOT yield an entailed equality (y could be > x).
    #[test]
    fn test_no_entailed_equality_one_direction_only() {
        let mut solver = ArithSolver::lra();

        let x = TermId::new(1);
        let y = TermId::new(2);
        let reason = TermId::new(100);

        solver.intern(x);
        solver.intern(y);

        // x <= y only (one direction)
        solver.assert_le(
            &[(x, Rational64::one()), (y, -Rational64::one())],
            Rational64::from_integer(0),
            reason,
        );

        solver.check().expect("check should succeed");

        let eqs = solver.derive_shared_equalities();
        let has_xy = eqs
            .iter()
            .any(|e| (e.lhs == x && e.rhs == y) || (e.lhs == y && e.rhs == x));
        assert!(
            !has_xy,
            "Should NOT derive x=y from x<=y alone; got: {:?}",
            eqs
        );
    }

    /// notify_equality(x, y) followed by check should enforce x = y:
    /// asserting x < y should then be UNSAT.
    #[test]
    fn test_notify_equality_enforces_equality() {
        use crate::theory::{EqualityNotification, TheoryCombination};

        let mut solver = ArithSolver::lra();

        let x = TermId::new(1);
        let y = TermId::new(2);
        let reason = TermId::new(100);

        solver.intern(x);
        solver.intern(y);

        // Notify x = y
        let eq = EqualityNotification {
            lhs: x,
            rhs: y,
            reason: Some(reason),
        };
        let accepted = solver.notify_equality(eq);
        assert!(accepted, "notify_equality should accept x=y");

        // After asserting x=y, adding x < y should yield UNSAT.
        solver.push();
        solver.assert_lt(
            &[(x, Rational64::one()), (y, -Rational64::one())],
            Rational64::from_integer(0),
            reason,
        );
        let result = solver.check().expect("check should not error");
        assert!(
            matches!(result, TheoryResult::Unsat(_)),
            "Expected UNSAT when x=y is enforced and x<y is added; got {:?}",
            result
        );
        solver.pop();
    }

    // ======== push/pop state-rollback regression (term_to_var / var_to_term) ========

    /// `pop()` must roll back `term_to_var` in lockstep with `var_to_term`.
    ///
    /// Before the fix, `pop()` truncated `var_to_term` but left stale
    /// `term_to_var` entries behind. Because the simplex recycles VarIds across
    /// a pop, those stale entries made `intern()` replay indices that now belong
    /// to a different (or not-yet-created) variable. This test inspects the
    /// internal maps directly to prove the two stay consistent.
    #[test]
    fn regression_pop_rolls_back_term_to_var() {
        let mut solver = ArithSolver::lra();
        let a = TermId::new(1);
        let b = TermId::new(2);
        let c = TermId::new(3);

        // Intern `a` at the base level.
        let va = solver.intern(a);
        assert_eq!(va, 0);

        solver.push();
        // Intern two more terms inside the scope.
        let vb = solver.intern(b);
        let vc = solver.intern(c);
        assert_eq!(vb, 1);
        assert_eq!(vc, 2);
        assert_eq!(solver.var_to_term.len(), 3);
        assert_eq!(solver.term_to_var.len(), 3);

        solver.pop();

        // Term interning is search-global (VarIds are never recycled, see
        // `Simplex::register_var`): the scoped interning SURVIVES the pop and
        // re-interning returns the SAME VarIds.  This replaces the old
        // pop-truncates-interning contract, whose point was to stop
        // `term_to_var` from pointing at recycled VarIds – with permanent
        // VarIds that hazard no longer exists, and keeping the interning is
        // what lets interned rows serve every scope that asserts them.
        assert_eq!(solver.var_to_term.len(), 3);
        assert_eq!(solver.term_to_var.len(), 3);
        assert_eq!(solver.intern(b), vb);
        assert_eq!(solver.intern(c), vc);

        // The core invariant: NO surviving mapping points at a truncated
        // (out-of-range) variable index.
        let live = solver.var_to_term.len() as VarId;
        for (&term, &var) in &solver.term_to_var {
            assert!(
                var < live,
                "term {term:?} maps to stale var {var} >= live var count {live}"
            );
        }

        // Re-interning the truncated terms yields FRESH valid indices.
        let vb2 = solver.intern(b);
        assert_eq!(vb2, 1, "re-interned `b` should take the next fresh index");
        assert!((vb2 as usize) < solver.var_to_term.len());
        let vc2 = solver.intern(c);
        assert_eq!(vc2, 2, "re-interned `c` should take the next fresh index");
        assert_ne!(vb2, vc2);
    }

    /// A fresh term interned after a pop must NOT collide with a stale-but-since-
    /// re-interned term that used to hold the recycled index.
    ///
    /// This is the recycled-index hazard the fix removes, observable purely
    /// through the public `intern()` API: intern `a`, push, intern `b`, pop –
    /// then intern a brand-new `c` (which the simplex hands the index `b` used
    /// to occupy) and finally re-intern `b`. With the stale mapping still
    /// present, `intern(b)` would return the same index as `c`.
    #[test]
    fn regression_pop_no_recycled_index_collision() {
        let mut solver = ArithSolver::lra();
        let a = TermId::new(11);
        let b = TermId::new(22);
        let c = TermId::new(33);

        let _va = solver.intern(a);
        solver.push();
        let _vb = solver.intern(b);
        solver.pop();

        // `c` is new: the simplex hands it the index `b` used to occupy.
        let vc = solver.intern(c);
        // `b` was truncated: re-interning must allocate a *different* fresh index.
        let vb2 = solver.intern(b);
        assert_ne!(
            vc, vb2,
            "recycled var index {vc} collided with re-interned truncated term"
        );
    }

    /// Regression (GitHub issue #12): in LRA the assignment for a variable
    /// pinned at a *strict* bound is a delta-rational `r ± δ`.  `value()` must
    /// instantiate `δ` with a concrete positive rational, otherwise it reports
    /// `x = 0` for `x > 0` – a witness that violates the asserted constraint.
    #[test]
    fn regression_lra_strict_bound_model_instantiates_delta() {
        let mut solver = ArithSolver::lra();
        let x = TermId::new(1);
        let reason = TermId::new(100);

        // x > 0
        solver.assert_gt(&[(x, Rational64::one())], Rational64::zero(), reason);
        assert!(matches!(solver.check(), Ok(TheoryResult::Sat)));

        let value = solver.value(x).expect("x must have a model value");
        assert!(
            value > Rational64::zero(),
            "model x = {value} violates x > 0"
        );
    }

    /// Both ends of a strict range must be respected simultaneously: the
    /// instantiated delta has to keep `0 < x < 1/2` genuinely inside the range.
    #[test]
    fn regression_lra_strict_range_model_inside_bounds() {
        let mut solver = ArithSolver::lra();
        let x = TermId::new(1);
        let lo = TermId::new(100);
        let hi = TermId::new(101);
        let half = Rational64::new(1, 2);

        solver.assert_gt(&[(x, Rational64::one())], Rational64::zero(), lo);
        solver.assert_lt(&[(x, Rational64::one())], half, hi);
        assert!(matches!(solver.check(), Ok(TheoryResult::Sat)));

        let value = solver.value(x).expect("x must have a model value");
        assert!(
            value > Rational64::zero() && value < half,
            "model x = {value} is outside the strict range (0, 1/2)"
        );
    }

    #[test]
    fn test_pr30_entailed_disequal_reason_declines_unknown_terms() {
        let x = TermId::new(1);
        let stranger = TermId::new(9_999);
        let bound = TermId::new(101);

        let mut solver = ArithSolver::lra();
        solver.intern(x);
        solver.assert_ge(
            &[(x, Rational64::one())],
            Rational64::from_integer(3),
            bound,
        );
        solver.assert_le(
            &[(x, Rational64::one())],
            Rational64::from_integer(3),
            bound,
        );
        solver.check().expect("check should succeed");

        assert!(
            solver.entailed_disequal_reason(x, stranger).is_none(),
            "an uninterned term must never yield an entailed disequality"
        );
    }

    #[test]
    fn test_pr30_entailed_disequal_reason_fires_only_on_disjoint_bounds() {
        let x = TermId::new(1);
        let y = TermId::new(2);
        let x_lo = TermId::new(101);
        let x_hi = TermId::new(102);
        let y_lo = TermId::new(103);
        let y_hi = TermId::new(104);

        let mut solver = ArithSolver::lra();
        solver.intern(x);
        solver.intern(y);
        solver.assert_ge(&[(x, Rational64::one())], Rational64::from_integer(3), x_lo);
        solver.assert_le(&[(x, Rational64::one())], Rational64::from_integer(3), x_hi);
        solver.assert_ge(&[(y, Rational64::one())], Rational64::from_integer(5), y_lo);
        solver.assert_le(&[(y, Rational64::one())], Rational64::from_integer(5), y_hi);

        assert!(
            matches!(
                solver.check().expect("check should succeed"),
                TheoryResult::Sat
            ),
            "the bounds themselves are consistent; only x = y is not"
        );

        let reason = solver
            .entailed_disequal_reason(x, y)
            .expect("x in [3,3] and y in [5,5] entails x != y");
        assert!(
            !reason.is_empty(),
            "an entailed disequality must be justified by the bound atoms"
        );
        assert!(
            reason.iter().all(|t| [x_lo, x_hi, y_lo, y_hi].contains(t)),
            "the reason must name only the asserted bound atoms, got: {reason:?}"
        );
        assert!(
            reason.contains(&x_hi) || reason.contains(&x_lo),
            "the reason must cite a bound on x, got: {reason:?}"
        );
        assert!(
            reason.contains(&y_hi) || reason.contains(&y_lo),
            "the reason must cite a bound on y, got: {reason:?}"
        );

        // Overlapping ranges: y in [2, 5] admits y = 3 = x.
        let mut solver = ArithSolver::lra();
        solver.intern(x);
        solver.intern(y);
        solver.assert_ge(&[(x, Rational64::one())], Rational64::from_integer(3), x_lo);
        solver.assert_le(&[(x, Rational64::one())], Rational64::from_integer(3), x_hi);
        solver.assert_ge(&[(y, Rational64::one())], Rational64::from_integer(2), y_lo);
        solver.assert_le(&[(y, Rational64::one())], Rational64::from_integer(5), y_hi);
        assert!(matches!(
            solver.check().expect("check should succeed"),
            TheoryResult::Sat
        ));

        assert!(
            solver.entailed_disequal_reason(x, y).is_none(),
            "x = 3 lies inside y's range [2, 5], so x != y is NOT entailed"
        );
    }
}
