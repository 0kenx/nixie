//! Arithmetic Theory Solver

use super::delta::DeltaRational;
use super::simplex::{LinExpr, Simplex, SimplexOptStatus, VarId};
#[allow(unused_imports)]
use crate::prelude::*;
use crate::theory::{EqualityNotification, Theory, TheoryCombination, TheoryId, TheoryResult};
use nixie_core::ast::TermId;
use nixie_core::error::Result;
use num_rational::Rational64;
use num_traits::{One, Signed, Zero};
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
fn fixed_value<'a>(
    lo: Option<&'a super::simplex::Bound>,
    hi: Option<&'a super::simplex::Bound>,
) -> Option<&'a super::delta::DeltaRational> {
    match (lo, hi) {
        (Some(l), Some(u)) if l.value == u.value => Some(&l.value),
        _ => None,
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

/// Compute GCD of two i128 values (used by the Diophantine consistency check).
fn gcd_i128(mut a: i128, mut b: i128) -> i128 {
    a = a.abs();
    b = b.abs();
    while b != 0 {
        let temp = b;
        b = a % b;
        a = temp;
    }
    a
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
    /// Is this LIA (integers) or LRA (reals)?
    is_integer: bool,
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
    lia_model: FxHashMap<VarId, Rational64>,
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
    /// points and recomputed lazily.  `None` ⇒ dirty.
    int_eq_infeasible_cache: Option<bool>,
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
}

/// A linear equality over the integers: `sum(coeff_i · var_i) = rhs`.
#[derive(Debug, Clone)]
struct IntEquation {
    terms: Vec<(VarId, i64)>,
    rhs: i64,
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
const BRANCH_REASON: u32 = u32::MAX;

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

impl Default for ArithSolver {
    fn default() -> Self {
        Self::new(false)
    }
}

impl ArithSolver {
    /// Create a new arithmetic solver
    #[must_use]
    pub fn new(is_integer: bool) -> Self {
        Self {
            simplex: Simplex::new(),
            term_to_var: FxHashMap::default(),
            var_to_term: Vec::new(),
            reason_counter: 0,
            reasons: Vec::new(),
            is_integer,
            context_stack: Vec::new(),
            shared_equalities: Vec::new(),
            lia_model: FxHashMap::default(),
            int_equalities: Vec::new(),
            int_eq_infeasible_cache: None,
            prop_lower: Vec::new(),
            prop_upper: Vec::new(),
            prop_undo: Vec::new(),
            int_vars: FxHashSet::default(),
            bnb_used_reasons: FxHashSet::default(),
            atom_rows: FxHashMap::default(),
        }
    }

    /// Create a new LRA solver
    #[must_use]
    pub fn lra() -> Self {
        Self::new(false)
    }

    /// Create a new LIA solver
    #[must_use]
    pub fn lia() -> Self {
        Self::new(true)
    }

    /// Whether this solver operates in integer (LIA) mode
    #[must_use]
    pub fn is_integer(&self) -> bool {
        self.is_integer
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
        if self.is_integer && all_integer && !terms.is_empty() {
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
        // direction; see `normalize_ineq_expr`).
        if equality
            && let Some((_, c)) = terms.first()
            && c.is_negative()
        {
            for (_, c) in &mut terms {
                *c = -*c;
            }
            constant = -constant;
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
        equality: bool,
        reason: TermId,
    ) -> VarId {
        let _ = key;
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
        let integral = self.is_integer && self.is_integral_form(&expr);
        let cache_key = (self.row_key(lhs, rhs, equality), reason);
        if let Some(&slack) = self.atom_rows.get(&cache_key)
            && self.simplex.row_defines_var(slack)
        {
            return slack;
        }
        let slack = self.simplex.intern_row(expr);
        if integral {
            self.int_vars.insert(slack);
        }
        self.atom_rows.insert(cache_key, slack);
        slack
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
        reason: TermId,
    ) -> VarId {
        let _ = key;
        let mut expr = LinExpr::new();
        for &(term, coef) in lhs {
            let var = self.intern(term);
            expr.add_term(var, coef);
        }
        expr.add_constant(-rhs);
        let integral = self.is_integer && self.is_integral_form(&expr);
        let cache_key = (self.row_key_strict(lhs, rhs), reason);
        if let Some(&slack) = self.atom_rows.get(&cache_key)
            && self.simplex.row_defines_var(slack)
        {
            return slack;
        }
        let slack = self.simplex.intern_row(expr);
        if integral {
            self.int_vars.insert(slack);
        }
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
        // this set containing them.
        if self.is_integer {
            self.int_vars.insert(var);
        }
        self.term_to_var.insert(term, var);
        self.var_to_term.push(term);
        var
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

        // For integer arithmetic, reduce by GCD
        if self.is_integer {
            // Find GCD of all coefficients
            let gcd = expr
                .terms
                .iter()
                .map(|(_, c)| c.numer().abs())
                .fold(0i64, |acc, n| if acc == 0 { n } else { gcd_i64(acc, n) });

            if gcd > 1 {
                let divisor = Rational64::from_integer(gcd);
                expr.scale(Rational64::one() / divisor);
            }
        }

        // Ensure first coefficient is positive
        if let Some((_, c)) = expr.terms.first()
            && c.is_negative()
        {
            expr.negate();
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

        // For integer arithmetic, reduce by GCD only (preserves sign)
        if self.is_integer {
            let gcd = expr
                .terms
                .iter()
                .map(|(_, c)| c.numer().abs())
                .fold(0i64, |acc, n| if acc == 0 { n } else { gcd_i64(acc, n) });

            if gcd > 1 {
                let divisor = Rational64::from_integer(gcd);
                expr.scale(Rational64::one() / divisor);
            }
        }

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
        let ratio = rhs / coef;
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
            .map(|b| format!("{:?}", b.value.real));
        let hi = self
            .simplex
            .get_upper(var)
            .map(|b| format!("{:?}", b.value.real));
        Some(format!(
            "{t:?}/v{var} val={val:?} lo={lo:?} hi={hi:?} lia_model={}",
            self.lia_model.contains_key(&var)
        ))
    }

    /// Assert: lhs <= rhs
    pub fn assert_le(&mut self, lhs: &[(TermId, Rational64)], rhs: Rational64, reason: TermId) {
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
        let slack = self.cached_row_slack(&key, lhs, rhs, false, reason);
        self.simplex.set_upper(slack, Rational64::zero(), reason_id);
        if let Some((var, coef)) = single {
            self.record_prop_bound(var, coef, rhs, PropCmp::Le, reason_id);
        }
    }

    /// Assert: lhs >= rhs
    pub fn assert_ge(&mut self, lhs: &[(TermId, Rational64)], rhs: Rational64, reason: TermId) {
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
        let slack = self.cached_row_slack(&key, lhs, rhs, false, reason);
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
        if self.is_integer && lia_is_new {
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
                let reason_id = self.add_reason(reason);
                if let Some(&(var, _)) = expr.terms.first() {
                    self.simplex
                        .set_lower(var, Rational64::from_integer(1), reason_id);
                    self.simplex
                        .set_upper(var, Rational64::from_integer(0), reason_id);
                }
                return;
            };

            // Check GCD infeasibility if all coefficients are integers
            if !coeffs.is_empty() && coeffs.len() == expr.terms.len() {
                // Record the integer equality (sum a_i·x_i = const_term) so the
                // cross-constraint Diophantine consistency check can see it.
                let eq_terms: Vec<(VarId, i64)> =
                    expr.terms.iter().map(|(v, c)| (*v, *c.numer())).collect();
                self.int_equalities.push(IntEquation {
                    terms: eq_terms,
                    rhs: const_term,
                });
                // A new equality changes the Diophantine system → invalidate
                // the cached feasibility verdict.
                self.int_eq_infeasible_cache = None;

                // Compute GCD of all coefficients
                let g = coeffs.iter().fold(0i64, |acc, &c| gcd_i64(acc, c.abs()));

                if g > 0 && const_term % g != 0 {
                    // GCD infeasibility detected!
                    // Add contradictory constraints: x >= 1 and x <= 0,
                    // attributed to the actual equality assertion that
                    // caused the contradiction (not a hardcoded reason id)
                    // so `check()`'s unsat core cites the real culprit
                    // instead of whatever the first reason ever added
                    // happened to be.
                    let reason_id = self.add_reason(reason);
                    if let Some(&(var, _)) = expr.terms.first() {
                        self.simplex
                            .set_lower(var, Rational64::from_integer(1), reason_id);
                        self.simplex
                            .set_upper(var, Rational64::from_integer(0), reason_id);
                    }
                    return;
                }
            }
        }

        // One shared, interned row per linear form; the equality is the two
        // bounds `slack <= 0` and `slack >= 0` on it.
        let reason_id = self.add_reason(reason);
        let slack = self.cached_row_slack(&lia_key, lhs, rhs, true, reason);
        self.simplex.set_lower(slack, Rational64::zero(), reason_id);
        self.simplex.set_upper(slack, Rational64::zero(), reason_id);
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
        // `propagate_bounds` derives basic-variable bounds from non-basic in one
        // pass; loop to a fixpoint so chains (x<-y<-z) fully propagate.  Cap
        // iterations to avoid pathological non-termination on cyclic tightenings.
        for _ in 0..16 {
            let before = self.simplex.num_original_vars();
            self.simplex.propagate_bounds();
            // propagate_bounds does not report whether it changed anything;
            // use the propagated-vector length as a cheap change signal.  It
            // clears+repopulates `propagated` each call, so a non-empty result
            // means at least one derivation fired this pass.
            if self.simplex.get_propagated().is_empty() {
                break;
            }
            let _ = before;
        }
    }

    /// Assert: lhs < rhs (strict inequality)
    /// For LRA, uses infinitesimals: lhs <= rhs - δ
    /// For LIA, transforms to: lhs <= rhs - 1 (since no integer exists between k and k+1)
    pub fn assert_lt(&mut self, lhs: &[(TermId, Rational64)], rhs: Rational64, reason: TermId) {
        // For integer arithmetic, x < k is equivalent to x <= k - 1
        // because there's no integer strictly between k-1 and k
        if self.is_integer {
            // Transform: lhs < rhs becomes lhs <= rhs - 1
            self.assert_le(lhs, rhs - Rational64::one(), reason);
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
        let slack = self.cached_row_slack_strict(&key, lhs, rhs, reason);
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
        // For integer arithmetic, x > k is equivalent to x >= k + 1
        // because there's no integer strictly between k and k+1
        if self.is_integer {
            // Transform: lhs > rhs becomes lhs >= rhs + 1
            self.assert_ge(lhs, rhs + Rational64::one(), reason);
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
        let slack = self.cached_row_slack_strict(&key, lhs, rhs, reason);
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
        self.term_to_var.get(&term).map(|&var| {
            if self.is_integer {
                // Prefer the integral assignment found by branch-and-bound when
                // the last check() proved Sat – the raw LP optimum may be
                // fractional for Int variables.
                if let Some(v) = self.lia_model.get(&var) {
                    return *v;
                }
                // Get the full delta-rational value
                let dval = self.simplex.delta_value(var);

                // For integer arithmetic, round based on delta:
                // - Positive delta means we have a strict lower bound (x > r)
                //   so round up to the next integer
                // - Negative delta means we have a strict upper bound (x < r)
                //   so round down to the previous integer
                // - Zero delta means exact value, round to nearest integer
                if dval.delta.is_positive() {
                    // x > r implies x >= ceil(r) for integers
                    // If r is already an integer, we need r + 1
                    let real_val = dval.real;
                    if real_val.is_integer() {
                        Rational64::from_integer(real_val.to_integer() + 1)
                    } else {
                        Rational64::from_integer(real_val.ceil().to_integer())
                    }
                } else if dval.delta.is_negative() {
                    // x < r implies x <= floor(r) for integers
                    // If r is already an integer, we need r - 1
                    let real_val = dval.real;
                    if real_val.is_integer() {
                        Rational64::from_integer(real_val.to_integer() - 1)
                    } else {
                        Rational64::from_integer(real_val.floor().to_integer())
                    }
                } else {
                    // No strict bound, just return the value
                    // Round to nearest integer for consistency
                    dval.real
                }
            } else {
                // For reals, the raw real part is NOT a model: a variable
                // sitting at a strict bound is stored as `r ± δ`, so returning
                // `r` alone reports a witness that violates the very constraint
                // that created it (e.g. `x > 0` would report `x = 0`).
                // Substitute a concrete positive δ₀ that keeps every bound
                // satisfied (see `Simplex::delta_instantiation`).
                let dval = self.simplex.delta_value(var);
                if dval.delta.is_zero() {
                    dval.real
                } else {
                    dval.real + dval.delta * self.simplex.delta_instantiation()
                }
            }
        })
    }

    /// LP-implied integer range `[lo, hi]` for `term` over the simplex's
    /// current feasible region, by minimizing then maximizing the term with the
    /// primal simplex (`optimize_linexpr`).  Returns `None` if `term` is not a
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
        let hi_real = -neg_max;
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
        if !self.is_integer {
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
        let mut vars: Vec<VarId> = self
            .var_to_term
            .iter()
            .filter_map(|term| self.term_to_var.get(term).copied())
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
    fn find_fractional_int_var(&self, int_vars: &[VarId]) -> Option<(VarId, Rational64)> {
        let mut best: Option<(VarId, Rational64)> = None;
        let mut best_range: Option<Rational64> = None;
        for &var in int_vars {
            let val = self.simplex.value(var);
            if val.is_integer() {
                continue;
            }
            let idx = var as usize;
            let lo = self.simplex.lower_real_at(idx);
            let hi = self.simplex.upper_real_at(idx);
            match (lo, hi) {
                (Some(lo), Some(hi)) => {
                    let range = hi - lo;
                    if best_range.is_none_or(|r| range < r) {
                        best_range = Some(range);
                        best = Some((var, val));
                    }
                }
                _ => {
                    if best.is_none() {
                        best = Some((var, val));
                    }
                }
            }
        }
        best
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
        self.lia_model.clear();
        for &var in int_vars {
            self.lia_model.insert(var, self.simplex.value(var));
        }
    }

    /// Decide whether the accumulated system of integer equalities has NO
    /// integer solution (a sound, one-sided UNSAT detector).
    ///
    /// Every equality `sum a_i·x_i = b` is an exact integer row.  We run integer
    /// (fraction-free) Gaussian elimination: reducing rows with the identity
    /// `row := (a/g)·row − (b/g)·pivot` (g = gcd of the two pivot-column
    /// entries) produces rows that are integer linear combinations of the
    /// originals, hence consequences that every integer solution must satisfy.
    /// For any resulting row `sum c_j·x_j = d`, an integer solution requires
    /// `gcd(c_j) | d`; if that fails – or a row reduces to `0 = d` with `d ≠ 0` –
    /// the whole system is integer-infeasible.
    ///
    /// This catches cross-constraint parity infeasibility such as
    /// `y = 2x ∧ y = 2z + 1` (⇒ `2x − 2z = 1`, and `gcd(2,2) = 2 ∤ 1`), which
    /// per-equation GCD reasoning and unbounded branch-and-bound cannot.
    ///
    /// The check is *sound but incomplete*: it only ever concludes UNSAT.  If an
    /// intermediate value would overflow `i128`, or the system is too large, it
    /// conservatively returns `false` (defer to branch-and-bound).
    fn int_equalities_infeasible(&self) -> bool {
        if self.int_equalities.is_empty() {
            return false;
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

        // Bound the work: skip very large systems (defer to branch-and-bound).
        if cols == 0 || rows.saturating_mul(cols) > 200_000 {
            return false;
        }

        // Dense augmented matrix: last entry of each row is the RHS.
        let mut mat: Vec<Vec<i128>> = vec![vec![0i128; cols + 1]; rows];
        for (r, eq) in self.int_equalities.iter().enumerate() {
            for &(v, c) in &eq.terms {
                if let Some(&col) = col_of.get(&v) {
                    mat[r][col] += c as i128;
                }
            }
            mat[r][cols] = eq.rhs as i128;
        }

        // Fraction-free Gaussian elimination.
        let mut pivot_row = 0usize;
        for col in 0..cols {
            // Find a pivot at or below `pivot_row` with a nonzero entry.
            let Some(sel) = (pivot_row..rows).find(|&r| mat[r][col] != 0) else {
                continue;
            };
            mat.swap(pivot_row, sel);

            // Snapshot the pivot row to avoid aliasing two rows of `mat`.
            let pivot = mat[pivot_row].clone();
            let a = pivot[col];

            // Eliminate this column from every other row.
            for (r, row) in mat.iter_mut().enumerate() {
                if r == pivot_row || row[col] == 0 {
                    continue;
                }
                let b = row[col];
                let g = gcd_i128(a, b);
                let fa = a / g; // scale for row r
                let fb = b / g; // scale for pivot
                for (k, &pv) in pivot.iter().enumerate().skip(col) {
                    let lhs = match row[k].checked_mul(fa) {
                        Some(v) => v,
                        None => return false, // overflow → cannot decide
                    };
                    let rhs = match pv.checked_mul(fb) {
                        Some(v) => v,
                        None => return false,
                    };
                    row[k] = match lhs.checked_sub(rhs) {
                        Some(v) => v,
                        None => return false,
                    };
                }
            }

            pivot_row += 1;
            if pivot_row == rows {
                break;
            }
        }

        // Consequence check: each row must be integer-satisfiable on its own.
        for row in &mat {
            let mut g = 0i128;
            for &c in &row[..cols] {
                g = gcd_i128(g, c);
            }
            let d = row[cols];
            if g == 0 {
                // 0 = d with d ≠ 0 is inconsistent (even over the rationals).
                if d != 0 {
                    return true;
                }
            } else if d % g != 0 {
                // gcd of coefficients does not divide the constant ⇒ no integer
                // solution to this consequence ⇒ system integer-infeasible.
                return true;
            }
        }

        false
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
        self.simplex.push();
        let result = self.lia_cuts_then_bnb()?;
        self.simplex.pop();
        match result {
            TheoryResult::Unknown => {}
            other => return Ok(other),
        }
        // The search gave up (unbounded variables, or its node/depth budget).
        // Try the sound Diophantine parity check as a fallback: it resolves
        // the cross-constraint integer-infeasibility that branch-and-bound
        // over unbounded variables cannot (e.g. `y = 2x ∧ y = 2z + 1`),
        // converting a would-be `Unknown` into a proven `Unsat`.  It only
        // ever strengthens (never weakens) the verdict.  The check is a pure
        // function of `int_equalities`, so its result is memoised in
        // `int_eq_infeasible_cache` (invalidated only when an equality is
        // asserted or retracted by `pop`).
        let infeasible = match self.int_eq_infeasible_cache {
            Some(v) => v,
            None => {
                let v = self.int_equalities_infeasible();
                self.int_eq_infeasible_cache = Some(v);
                v
            }
        };
        if infeasible {
            return Ok(TheoryResult::Unsat(self.full_unsat_core()));
        }
        Ok(TheoryResult::Unknown)
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
                // Cuts closed the integrality gap outright.
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
        self.bnb_search(&int_vars, &mut nodes)
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
            let (at_lower, bound) = if lo.is_some_and(|b| b.value.real == vj) {
                (true, lo)
            } else if hi.is_some_and(|b| b.value.real == vj) {
                (false, hi)
            } else {
                return None;
            };
            let bound = bound?;
            // Branch bounds carry [`BRANCH_REASON`] (no external
            // justification): a cut using one is only valid inside that
            // branch, never at the root where cuts are asserted.
            if bound.reason == BRANCH_REASON {
                return None;
            }
            for r in bound.all_reasons() {
                if r == BRANCH_REASON {
                    return None;
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

            let is_int_here = self.int_vars.contains(&xj) && bound.value.real.is_integer();
            let gamma = if is_int_here {
                let fj = bar_a - bar_a.floor();
                if fj.is_zero() {
                    continue; // γ_j = 0: the term drops out of the cut
                }
                if fj <= f0 {
                    fj / f0
                } else {
                    (one - fj) / one_minus_f0
                }
            } else if bar_a >= Rational64::zero() {
                -bar_a / f0
            } else {
                hat_a / one_minus_f0
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

            if at_lower {
                cut.add_term(xj, -gamma);
                rhs += gamma * bound.value.real;
            } else {
                cut.add_term(xj, gamma);
                rhs -= gamma * bound.value.real;
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
    fn bnb_search(&mut self, int_vars: &[VarId], nodes: &mut usize) -> Result<TheoryResult> {
        struct Node {
            var: VarId,
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
            bound: Rational64,
            upper: bool,
            unknown: &mut bool,
        ) -> bool {
            s.simplex.push();
            if upper {
                s.simplex.set_upper(var, bound, BRANCH_REASON);
            } else {
                s.simplex.set_lower(var, bound, BRANCH_REASON);
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
            if stack.len() > Self::LIA_MAX_DEPTH || *nodes > Self::LIA_MAX_NODES {
                for _ in 0..stack.len() {
                    self.simplex.pop();
                }
                return Ok(TheoryResult::Unknown);
            }
            *nodes += 1;
            let Some((var, value)) = self.find_fractional_int_var(int_vars) else {
                // Fully integral leaf: record the model, unwind, report Sat.
                self.snapshot_lia_model(int_vars);
                for _ in 0..stack.len() {
                    self.simplex.pop();
                }
                return Ok(TheoryResult::Sat);
            };
            let floor_v = value.floor();
            let ceil_v = value.ceil();
            let mut saw_unknown = false;

            // Branch down: var <= floor(value).
            if take_branch(self, var, floor_v, true, &mut saw_unknown) {
                stack.push(Node {
                    var,
                    up_done: false,
                    saw_unknown,
                });
                continue; // descend into the down subtree
            }
            // Branch up: var >= ceil(value).
            if take_branch(self, var, ceil_v, false, &mut saw_unknown) {
                stack.push(Node {
                    var,
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
                    // just popped, so the LP state is the node's own again
                    // and `value(var)` re-reads the original fractional
                    // optimum.
                    let ceil_v = self.simplex.value(frame.var).ceil();
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
        if !self.is_integer {
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
        if self.is_integer {
            TheoryId::LIA
        } else {
            TheoryId::LRA
        }
    }

    fn name(&self) -> &str {
        if self.is_integer { "LIA" } else { "LRA" }
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
        if !self.is_integer {
            return Ok(TheoryResult::Sat);
        }

        // Step 3 (LIA): the LP relaxation being feasible is NOT sufficient – a
        // fractional assignment over Int variables must be resolved by
        // branch-and-bound before we may answer Sat.  Otherwise integer-
        // infeasible-but-LP-feasible systems (e.g. y = 2x ∧ y = 2z+1) would be
        // wrongly reported Sat with fractional values for Int terms.
        self.lia_branch_and_bound()
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
                self.int_eq_infeasible_cache = None;
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
        self.int_vars.clear();
        self.var_to_term.clear();
        self.reason_counter = 0;
        self.reasons.clear();
        self.context_stack.clear();
        self.shared_equalities.clear();
        self.lia_model.clear();
        self.int_equalities.clear();
        self.int_eq_infeasible_cache = None;
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
                let dval = self.simplex.delta_value(var);
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
                Some((self.simplex.delta_value(var), term))
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
                    .or_else(|| self.simplex.get_lower(var).map(|b| (b.value, b.reason)))
            } else {
                self.prop_get_upper(var)
                    .map(|e| (e.value, e.reason))
                    .or_else(|| self.simplex.get_upper(var).map(|b| (b.value, b.reason)))
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
                    .or_else(|| self.simplex.get_upper(var).map(|b| (b.value, b.reason)))
            } else {
                self.prop_get_lower(var)
                    .map(|e| (e.value, e.reason))
                    .or_else(|| self.simplex.get_lower(var).map(|b| (b.value, b.reason)))
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
mod tests {
    use super::*;
    use num_traits::{One, Zero};

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
