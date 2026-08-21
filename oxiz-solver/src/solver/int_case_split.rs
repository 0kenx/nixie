//! Non-convex LIA integer case-splitting refinement.
//!
//! ## The problem
//!
//! A QF_UFLIA formula is *non-convex* in the arithmetic sense when an integer
//! term `t` is pinned to a small finite domain by arithmetic bounds (e.g.
//! `(>= t 0)` ∧ `(<= t 1)` ⟹ `t ∈ {0, 1}`) and that same `t` is used as an
//! argument to an uninterpreted function.  Whether the formula is satisfiable
//! can then depend on *which* concrete value `t` takes, because each value
//! triggers a different congruence in EUF (`f(0)` vs `f(1)`).
//!
//! Nelson–Oppen equality sharing between the arithmetic and EUF solvers can
//! only propagate *entailed* equalities.  `t = 0` is **not** entailed while
//! `t = 1` is still possible, so the disjunction `t ∈ {0,1}` is never resolved
//! and the CDCL core has no Boolean atom to branch on `t`'s value.  The
//! result is a spurious `sat` on an `unsat` instance – a classic false-SAT of
//! non-convex theory combination.
//!
//! ## The fix
//!
//! After the CDCL(T) core reports a candidate `sat`, we look for integer
//! terms that (a) appear as uninterpreted-function arguments and (b) are
//! tightly bounded to a small finite domain by *decision-level-0* arithmetic
//! atoms, then assert an explicit disjunction `(or (= t lo) … (= t hi))` as a
//! lemma and re-solve.  Each disjunct is a fresh equality atom shared by both
//! theories, so once CDCL picks a value the EUF congruence `f(t) = f(k)`
//! fires and the arithmetic solver detects the conflict – exactly reproducing
//! what a hand-written `(assert (or (= d 0) (= d 1)))` achieves.
//!
//! This closes the gap for both simple UF arguments (`f(d)`) and compound ones
//! (`f(fmt1 - 2)`, abstracted to a fresh proxy during preprocessing): splitting
//! the proxy directly is sound because
//! [`TheoryManager::propagate_euf_equalities_to_arith`] expands theory-derived
//! equalities through the EUF proof forest, giving conflict clauses complete
//! decision-level reasons.
//!
//! ## Soundness
//!
//! The disjunction is a *theorem* of the formula (it only restates that `t`
//! lies in `[lo, hi]`), so adding it can never change satisfiability.  Bounds
//! come only from **direct single-variable** arithmetic atoms
//! (`(>= d 0)`, `(< d 5)`, `(= d 3)`) that are unit-propagated to true at
//! decision level 0 – i.e. they are theorems of the formula and hold in every
//! model.  A model-consistency guard backstops any derivation bug.
//!
//! Multi-variable equalities are deliberately *not* used to transfer bounds
//! between linked terms: an interval fixpoint over them can converge to a
//! (candidate-model-consistent but not formula-entailed) point bound, which
//! produces a false `unsat` on some WiSA variants.  Closing that gap safely is
//! left to future work; the direct-bound refinement here is sound and captures
//! the common case where a UF argument is itself directly bounded.
//!
//! ## Cost control
//!
//! Each refinement round re-solves the whole problem from scratch, so the
//! refinement is capped at one round (`MAX_CASE_SPLIT_ROUNDS`) and at
//! [`PER_ROUND_CAP`] new split terms.  There is deliberately NO wall-clock
//! affordability gate: see the note at [`PER_ROUND_CAP`] — a time-gated
//! closing round made verdicts load-dependent (`sat` on a busy machine,
//! `unsat` on a quiet one, same binary, same input).
//!
//! Reference: the standard "integer case splitting" used by Z3 / cvc5 for
//! non-convex LIA theory combination (Barrett et al., "Decision Procedures",
//! ch. 10).

use num_rational::Rational64;
use num_traits::ToPrimitive;
use oxiz_core::ast::{TermId, TermKind, TermManager, collect_subterms};
use oxiz_sat::Lit;
use rustc_hash::{FxHashMap, FxHashSet};
use smallvec::SmallVec;

use super::Solver;
use super::types::{ArithConstraintType, Constraint};

/// Maximum integer range `hi - lo` for which we emit an explicit case split.
/// Kept modest: a wider disjunction both enlarges the CDCL search and (for the
/// WiSA family) tends to coincide with the harder, larger instances where the
/// extra solve is not affordable.  Small ranges cover the common non-convex
/// cases.
const MAX_INT_CASE_RANGE: i64 = 8;

/// Hard cap on the number of reset-and-re-solve refinement rounds.  Kept at 1:
/// every eligible UF argument is split in that single round (see
/// [`PER_ROUND_CAP`]), so one extra solve either closes the gap or reports the
/// (still valid) `sat`.  Bounding rounds bounds the worst-case cost.
const MAX_CASE_SPLIT_ROUNDS: u32 = 1;

/// Maximum number of *new* terms split in a single refinement round.  Set high
/// so every eligible UF argument is split in the one allowed round: the term
/// whose enumeration resolves the formula is not necessarily the smallest-range
/// one, so restricting the count would risk leaving it unsplit.
const PER_ROUND_CAP: usize = 32;

// NOTE: the refinement used to carry a wall-clock affordability gate
// (`CASE_SPLIT_REFINE_BUDGET_MS`, first solve < 5 s).  Removed 2026-08-21:
// it made the *verdict* load-dependent — on QF_UFLIA/wisas/xs_8_13.smt2 the
// same binary answered `sat` 7/8 identical runs (gate expired → closing
// round skipped → non-convex hole reported as `sat`) and `unsat` when the
// first solve happened to be fast; forcing the arms gave 5×`sat` (budget 0)
// vs 5×`unsat` (budget ∞).  "Preserving the original fast answer" is not a
// legitimate goal when that answer is uncertifiable: skipping the closing
// round must yield `unknown`, never `sat` — and with the gate gone the
// round always runs, so the case never arises.  Cost stays bounded by the
// deterministic caps above; an overall unaffordable search is the user's
// `timeout_ms`'s business.

/// Whether a constraint's effect on a variable is to pin a lower bound, an
/// upper bound, or both (equality).  Strict `<` / `>` are normalised to `<=` /
/// `>=` with an off-by-one constant (valid over the integers) at collection
/// time, so the propagation core only handles these three cases.
#[derive(Clone, Copy)]
enum Dir {
    Le,
    Ge,
    Eq,
}

/// One normalized arithmetic fact for the interval fixpoint:
/// `sum(coef_i * x_i) <dir-op> constant`.
struct Fact {
    terms: SmallVec<[(TermId, Rational64); 4]>,
    constant: Rational64,
    dir: Dir,
}

impl Solver {
    /// Lazy integer case-split refinement entry point.
    ///
    /// **Eager** half of the integer case-split architecture (z3
    /// `arith_eq_adapter` / cvc5 `ensureLiteral` parity): assert the
    /// `(or (= t lo) .. (= t hi))` enumeration lemmas for every int-sorted UF
    /// argument whose finite range is derivable *before* the search starts,
    /// from the level-0 interval fixpoint alone ([`Self::compute_int_bounds`]
    /// over the SAT trail's level-0 prefix and the single-variable atoms –
    /// the exact same soundness basis the reactive round uses).
    ///
    /// The literals are phase-guided toward `true` (`set_preferred_phase`,
    /// the port of z3's `try_true_first` / cvc5 B&B's `preferPhase(literal,
    /// true)`): CDCL pins `t` to one of its finitely many values first, so
    /// the congruence closure sees a concrete arrangement early instead of
    /// reaching an unchecked candidate and paying the reactive round's
    /// reset-and-re-solve.
    ///
    /// Runs once per `check_core`, right after `pre_encode_care_graph_atoms`.
    /// Deliberately does **not** touch `case_split_rounds`: it performs no
    /// re-solve, and the reactive round ([`Self::refine_int_case_split`])
    /// must stay available for ranges that only the LP fallback can see
    /// (the simplex is empty pre-search) – e.g. a bounded *difference* of
    /// free variables, the wisas shape.  Terms already eagerly split land in
    /// `case_split_terms`, so the reactive round skips them.
    pub(super) fn assert_eager_int_case_splits(&mut self, manager: &mut TermManager) {
        // Quantified goals route through MBQI; enumeration lemmas over its
        // search would churn without bound.
        if self.has_quantifiers {
            return;
        }
        let uf_args = self.collect_int_uf_args(manager);
        if uf_args.is_empty() {
            return;
        }
        let bounds = self.compute_int_bounds();
        if bounds.is_empty() {
            return;
        }
        // Same deterministic eligibility as the reactive round: finite range,
        // width within the enumeration cap, deduped, tightest-first, capped
        // per search.  No model-consistency guard here: there is no candidate
        // model yet, and soundness rests on the level-0 derivation itself
        // (bounds are theorems of the formula, so the enumeration clause is
        // logically valid over the reachable values).
        let mut candidates: Vec<(TermId, i64, i64)> = Vec::new();
        for t in &uf_args {
            if self.case_split_terms.contains(t) {
                continue;
            }
            let Some(&(Some(lo), Some(hi))) = bounds.get(t) else {
                continue;
            };
            if hi < lo || hi - lo > MAX_INT_CASE_RANGE {
                continue;
            }
            candidates.push((*t, lo, hi));
        }
        if candidates.is_empty() {
            return;
        }
        candidates.sort_by_key(|&(_, lo, hi)| (hi - lo, lo));
        candidates.truncate(PER_ROUND_CAP);
        for &(term, lo, hi) in &candidates {
            let mut lits: Vec<Lit> = Vec::new();
            for k in lo..=hi {
                let int_k = manager.mk_int(k);
                let eq = manager.mk_eq(term, int_k);
                let lit = self.encode_depth(eq, manager, 0);
                self.sat.set_preferred_phase(lit.var(), true);
                lits.push(lit);
            }
            self.sat.add_clause(lits);
            self.case_split_terms.insert(term);
        }
    }

    /// **Reactive** half: at a theory-consistent candidate model, derive
    /// finite ranges the eager pass could not see (the LP fallback needs the
    /// base-scoped simplex, which only exists once the search has propagated
    /// the level-0 constraints) and assert their enumeration lemmas.
    ///
    /// The trigger is deductive, never temporal: a candidate `Sat` plus a
    /// finite range derived from the *asserted* facts.  This mirrors the
    /// trigger class of cvc5's branch-and-bound (`BranchAndBound::
    /// branchIntegerVariable` fires at the fractional LP value, a property
    /// of the current tableau state) – deterministic and load-independent.
    /// The reset-and-re-solve that follows is inherent to enumeration
    /// lemmas: unlike a B&B split at a fractional point (violated at the
    /// trigger), an enumeration clause over `[lo, hi]` is *satisfied* by the
    /// candidate (the model's value is one of the disjuncts), so asserting
    /// it mid-search cannot invalidate that candidate; only a fresh search
    /// in which the branching dimension exists explores the arrangements.
    ///
    pub(super) fn refine_int_case_split(&mut self, manager: &mut TermManager) -> bool {
        // Not gated on `self.arith.is_integer()`: the Solver always constructs
        // `ArithSolver::lra()` (is_integer == false), so that guard disabled
        // this non-convexity refinement entirely -- dead code, and the source
        // of the QF_UFLIA/QF_UFIDL false-SAT (an integer UF argument pinned to
        // a small finite domain never gets its `(or (= t lo) ... (= t hi))`
        // lemma, so CDCL cannot branch on its value and a genuine `unsat` is
        // reported `sat`).  Int-sorted UF arguments are selected by
        // `collect_int_uf_args` (int_sort only); Real arguments are never
        // enumerated, so dropping the global flag is sound.
        if self.case_split_rounds >= MAX_CASE_SPLIT_ROUNDS {
            return false;
        }

        let uf_args = self.collect_int_uf_args(manager);
        // Snapshot each candidate's value in the model the theory just built
        // BEFORE `lp_int_bounds` runs: that call pops the simplex to the
        // base scope (to range over asserted facts only), which discards the
        // decision-level assignment `ArithSolver::value` would otherwise read.
        // The guard below compares the derived range against this model value.
        let model_vals: FxHashMap<TermId, Option<i64>> = uf_args
            .iter()
            .map(|&t| (t, self.arith.value(t).and_then(|r| r.to_i64())))
            .collect();
        let mut bounds = self.compute_int_bounds();
        // LP-optimization fallback for UF-arguments whose finite range comes
        // from a bounded *difference* of free variables – invisible to both the
        // per-variable interval fixpoint above and to simplex bound propagation
        // (e.g. `D = fmt1 - fmt0 - 2 ∈ {0..4}`).  Minimize then maximize each
        // such term over the simplex feasible region (`ArithSolver::lp_int_bounds`,
        // mirroring z3's `opt_solver::maximize_objective`) to get its exact
        // LP-implied integer range.  Sound: `[ceil(min), floor(max)]` is a
        // superset of the true integer range, so the case-split never excludes
        // a reachable value (this is the QF_UFLIA false-SAT fix).
        for &t in &uf_args {
            if let std::collections::hash_map::Entry::Vacant(entry) = bounds.entry(t) {
                if let Some((lo, hi)) = self.arith.lp_int_bounds(t) {
                    // A single-value LP range `[v, v]` would make the case-split
                    // a permanent unit `(t = v)`.  That is only sound when `t` is
                    // genuinely pinned to `v` by the *asserted* constraints; the
                    // level-0 simplex state can still spuriously pin a free term
                    // (a purification proxy whose only bound is a search-decided
                    // equality recorded at the base scope), and the resulting
                    // unit leaks across checks as a spurious `unsat`
                    // (`state_hygiene_audit`, `scope_rebase_adversarial`).  A
                    // term truly pinned to one value is derived by CDCL + the
                    // arithmetic solver directly, so dropping the degenerate
                    // single-value LP split costs no completeness.
                    if lo != hi {
                        entry.insert((Some(lo), Some(hi)));
                    }
                }
            }
        }

        let mut candidates: Vec<(TermId, i64, i64)> = Vec::new();
        for t in &uf_args {
            if self.case_split_terms.contains(t) {
                continue;
            }
            let Some(&(Some(lo), Some(hi))) = bounds.get(t) else {
                continue;
            };
            if hi < lo || hi - lo > MAX_INT_CASE_RANGE {
                continue;
            }
            if let Some(val) = model_vals.get(t).and_then(|v| *v) {
                if val < lo || val > hi {
                    // Derived range excludes the model the theory just built –
                    // our bounds are wrong for this term; do not prune.
                    continue;
                }
            }
            candidates.push((*t, lo, hi));
        }
        if candidates.is_empty() {
            return false;
        }

        // Prefer the tightest ranges first (a range-1 split enumerates only
        // two cases), minimising the per-clause disjunction cost.
        candidates.sort_by_key(|&(_, lo, hi)| (hi - lo, lo));
        candidates.truncate(PER_ROUND_CAP);

        for &(term, lo, hi) in &candidates {
            let mut lits: Vec<Lit> = Vec::new();
            for k in lo..=hi {
                let int_k = manager.mk_int(k);
                let eq = manager.mk_eq(term, int_k);
                let lit = self.encode_depth(eq, manager, 0);
                // cvc5 B&B `preferPhase(literal, true)` parity: try the
                // pinning polarity first so the re-solve walks arrangements
                // immediately instead of skipping every enumeration atom.
                self.sat.set_preferred_phase(lit.var(), true);
                lits.push(lit);
            }
            self.sat.add_clause(lits);
            self.case_split_terms.insert(term);
        }

        self.case_split_rounds += 1;
        true
    }

    /// Collect every integer/real-sorted term that appears directly as an
    /// argument of an uninterpreted function application.
    ///
    /// The assertions are scanned *after* preprocessing (purification +
    /// compound-argument abstraction), so a compound UF argument like
    /// `f(fmt1 + 1)` is already represented by its fresh abstraction proxy,
    /// which is exactly the plain variable EUF/Arith share – the right thing
    /// to split.
    fn collect_int_uf_args(&self, manager: &TermManager) -> Vec<TermId> {
        let int_sort = manager.sorts.int_sort;
        let mut seen: FxHashSet<TermId> = FxHashSet::default();
        let mut out: Vec<TermId> = Vec::new();
        for &assertion in &self.assertions {
            for st in collect_subterms(assertion, manager) {
                let Some(t) = manager.get(st) else {
                    continue;
                };
                let TermKind::Apply { args, .. } = &t.kind else {
                    continue;
                };
                for &arg in args {
                    let Some(at) = manager.get(arg) else {
                        continue;
                    };
                    if at.sort != int_sort {
                        continue;
                    }
                    if seen.insert(arg) {
                        out.push(arg);
                    }
                }
            }
        }
        out
    }

    /// Compute sound inclusive integer bounds `[lo, hi]` for arithmetic terms
    /// from **direct single-variable** arithmetic atoms that are
    /// unit-propagated to true at decision level 0.
    ///
    /// Only single-variable atoms (`(>= d 0)`, `(< d 5)`, `(= d 3)`) are used:
    /// they are theorems of the formula (level 0), so any bound derived from
    /// them holds in all models.  Multi-variable equalities are excluded – see
    /// the module-level soundness note.
    fn compute_int_bounds(&self) -> FxHashMap<TermId, (Option<i64>, Option<i64>)> {
        let mut facts: Vec<Fact> = Vec::new();
        for (&var, parsed) in &self.var_to_parsed_arith {
            if !self.atom_is_level0_true(var) {
                continue;
            }
            // SOUNDNESS: only direct single-variable bounds (e.g. `(>= d 0)`,
            // `(<= d 1)`) are used.  Multi-variable equalities can pin a term
            // to the candidate model's value via a fixpoint that is not
            // actually entailed by the formula (a false-UNSAT on some WiSA
            // variants), so they are excluded.
            if parsed.terms.len() != 1 {
                continue;
            }
            // Coefficients must be integer for our i64 interval arithmetic.
            if parsed.constant.denom() != &1 {
                continue;
            }
            if parsed.terms.iter().any(|(_, c)| c.denom() != &1) {
                continue;
            }
            let dir = match self.var_to_constraint.get(&var) {
                Some(Constraint::Eq(_, _)) => Dir::Eq,
                _ => match parsed.constraint_type {
                    ArithConstraintType::Lt => Dir::Le,
                    ArithConstraintType::Le => Dir::Le,
                    ArithConstraintType::Gt => Dir::Ge,
                    ArithConstraintType::Ge => Dir::Ge,
                },
            };
            // Strict inequalities tighten by one over the integers.
            let constant = match parsed.constraint_type {
                ArithConstraintType::Lt => parsed.constant - Rational64::from_integer(1),
                ArithConstraintType::Gt => parsed.constant + Rational64::from_integer(1),
                _ => parsed.constant,
            };
            facts.push(Fact {
                terms: parsed.terms.clone(),
                constant,
                dir,
            });
        }
        if facts.is_empty() {
            return FxHashMap::default();
        }

        let mut bounds: FxHashMap<TermId, (Option<i64>, Option<i64>)> = FxHashMap::default();
        let mut changed = true;
        while changed {
            changed = false;
            for fact in &facts {
                propagate_fact(fact, &mut bounds, &mut changed);
            }
        }
        bounds
    }

    /// `true` iff the SAT atom `var` is forced to its positive polarity at
    /// decision level 0 – i.e. it is unit-propagated from the formula alone and
    /// therefore holds in every model.  This is the soundness criterion for
    /// using the atom's constraint in bound derivation.
    fn atom_is_level0_true(&self, var: oxiz_sat::Var) -> bool {
        let trail = self.sat.trail();
        trail.level(var) == 0 && trail.value(var).is_true()
    }
}

/// Apply one normalized fact `sum(coef_i·x_i) <dir> constant` to tighten the
/// bounds map.  For every variable, derive the bound implied by the *other*
/// variables' current intervals and intersect.
fn propagate_fact(
    fact: &Fact,
    bounds: &mut FxHashMap<TermId, (Option<i64>, Option<i64>)>,
    changed: &mut bool,
) {
    let Some(c) = fact.constant.to_i64() else {
        return;
    };
    for k in 0..fact.terms.len() {
        let (xk, ak_rat) = &fact.terms[k];
        let Some(ak) = ak_rat.to_i64() else {
            return;
        };
        if ak == 0 {
            continue;
        }
        let (tlo, thi) = sum_excluding(&fact.terms, k, bounds);
        match fact.dir {
            Dir::Eq => {
                // a_k·x_k = c - T  ∈ [c - thi, c - tlo]  (needs T fully bounded)
                let (Some(thi), Some(tlo)) = (thi, tlo) else {
                    continue;
                };
                let Some(klo) = c.checked_sub(thi) else {
                    continue;
                };
                let Some(khi) = c.checked_sub(tlo) else {
                    continue;
                };
                let (lo_b, hi_b) = div_interval(ak, klo, khi);
                tighten(*xk, lo_b, hi_b, bounds, changed);
            }
            Dir::Le => {
                // a_k·x_k <= c - T   (needs T bounded below)
                let Some(tlo) = tlo else {
                    continue;
                };
                let Some(uhi) = c.checked_sub(tlo) else {
                    continue;
                };
                let (lo_b, hi_b) = div_le_ge(ak, uhi, true);
                tighten(*xk, lo_b, hi_b, bounds, changed);
            }
            Dir::Ge => {
                // a_k·x_k >= c - T   (needs T bounded above)
                let Some(thi) = thi else {
                    continue;
                };
                let Some(llo) = c.checked_sub(thi) else {
                    continue;
                };
                let (lo_b, hi_b) = div_le_ge(ak, llo, false);
                tighten(*xk, lo_b, hi_b, bounds, changed);
            }
        }
    }
}

/// Interval of `sum_{i != k} a_i · x_i` from the current bounds.
///
/// Returns `(lo, hi)` as `Option<i64>` where `None` denotes an unbounded side.
/// Any arithmetic overflow is treated as unbounded (forgoes a derivation
/// rather than risk an unsound bound).
fn sum_excluding(
    terms: &[(TermId, Rational64)],
    k: usize,
    bounds: &FxHashMap<TermId, (Option<i64>, Option<i64>)>,
) -> (Option<i64>, Option<i64>) {
    let mut lo: Option<i64> = Some(0);
    let mut hi: Option<i64> = Some(0);
    for (j, (x, a_rat)) in terms.iter().enumerate() {
        if j == k {
            continue;
        }
        let Some(a) = a_rat.to_i64() else {
            return (None, None);
        };
        if a == 0 {
            continue;
        }
        let (xlo, xhi) = bounds.get(x).copied().unwrap_or((None, None));
        // Lower contribution: a>0 ⇒ a·xlo ; a<0 ⇒ a·xhi.
        // Upper contribution: a>0 ⇒ a·xhi ; a<0 ⇒ a·xlo.
        let lo_src = if a > 0 { xlo } else { xhi };
        let hi_src = if a > 0 { xhi } else { xlo };
        lo = match (lo, lo_src.and_then(|v| a.checked_mul(v))) {
            (Some(s), Some(t)) => s.checked_add(t),
            _ => None,
        };
        hi = match (hi, hi_src.and_then(|v| a.checked_mul(v))) {
            (Some(s), Some(t)) => s.checked_add(t),
            _ => None,
        };
    }
    (lo, hi)
}

/// Given `a·x ∈ [klo, khi]`, return the implied inclusive integer `[lo, hi]`
/// of `x` (ceiling on the lower edge, floor on the upper).
fn div_interval(a: i64, klo: i64, khi: i64) -> (Option<i64>, Option<i64>) {
    if a > 0 {
        (ceil_div(klo, a), floor_div(khi, a))
    } else if a < 0 {
        (ceil_div(khi, a), floor_div(klo, a))
    } else {
        (None, None)
    }
}

/// Given a one-sided relation `a·x <= rhs` (`upper = true`) or `a·x >= rhs`,
/// return the implied inclusive integer bound on `x`.
fn div_le_ge(a: i64, rhs: i64, upper: bool) -> (Option<i64>, Option<i64>) {
    if a > 0 {
        if upper {
            (None, floor_div(rhs, a))
        } else {
            (ceil_div(rhs, a), None)
        }
    } else if a < 0 {
        if upper {
            (ceil_div(rhs, a), None)
        } else {
            (None, floor_div(rhs, a))
        }
    } else {
        (None, None)
    }
}

/// Tighten the stored `[lo, hi]` for `x` by intersecting with the new bounds.
fn tighten(
    x: TermId,
    new_lo: Option<i64>,
    new_hi: Option<i64>,
    bounds: &mut FxHashMap<TermId, (Option<i64>, Option<i64>)>,
    changed: &mut bool,
) {
    if new_lo.is_none() && new_hi.is_none() {
        return;
    }
    let entry = bounds.entry(x).or_insert((None, None));
    if let Some(nl) = new_lo {
        let updated = match entry.0 {
            Some(cur) => Some(cur.max(nl)),
            None => Some(nl),
        };
        if updated != entry.0 {
            entry.0 = updated;
            *changed = true;
        }
    }
    if let Some(nh) = new_hi {
        let updated = match entry.1 {
            Some(cur) => Some(cur.min(nh)),
            None => Some(nh),
        };
        if updated != entry.1 {
            entry.1 = updated;
            *changed = true;
        }
    }
}

/// Floor division `num / den` (rounds toward −∞).  `den` must be non-zero.
fn floor_div(num: i64, den: i64) -> Option<i64> {
    if den == 0 {
        return None;
    }
    if den < 0 {
        floor_div(-num, -den)
    } else {
        Some(num.div_euclid(den))
    }
}

/// Ceiling division `num / den` (rounds toward +∞).  `den` must be non-zero.
fn ceil_div(num: i64, den: i64) -> Option<i64> {
    if den == 0 {
        return None;
    }
    if den < 0 {
        ceil_div(-num, -den)
    } else {
        Some(-((-num).div_euclid(den)))
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn floor_and_ceil_div_signs() {
        assert_eq!(floor_div(7, 2), Some(3));
        assert_eq!(floor_div(-7, 2), Some(-4));
        assert_eq!(floor_div(7, -2), Some(-4));
        assert_eq!(floor_div(-7, -2), Some(3));
        assert_eq!(ceil_div(7, 2), Some(4));
        assert_eq!(ceil_div(-7, 2), Some(-3));
        assert_eq!(ceil_div(7, -2), Some(-3));
        assert_eq!(ceil_div(-7, -2), Some(4));
        assert_eq!(floor_div(6, 2), Some(3));
        assert_eq!(ceil_div(6, 2), Some(3));
    }

    #[test]
    fn div_interval_positive_coef() {
        // 2·x ∈ [3, 7] ⇒ x ∈ [ceil(3/2), floor(7/2)] = [2, 3]
        assert_eq!(div_interval(2, 3, 7), (Some(2), Some(3)));
    }

    #[test]
    fn div_interval_negative_coef() {
        // -2·x ∈ [3, 7] ⇒ x ∈ [-3.5, -1.5] ⇒ integer [-3, -2]
        assert_eq!(div_interval(-2, 3, 7), (Some(-3), Some(-2)));
    }

    #[test]
    fn div_le_ge_positive_coef() {
        assert_eq!(div_le_ge(2, 7, true), (None, Some(3)));
        assert_eq!(div_le_ge(2, 3, false), (Some(2), None));
    }

    #[test]
    fn div_le_ge_negative_coef() {
        // -2·x <= 7 ⇒ x >= -3.5 ⇒ integer x >= -3
        assert_eq!(div_le_ge(-2, 7, true), (Some(-3), None));
        // -2·x >= 3 ⇒ x <= -1.5 ⇒ integer x <= -2
        assert_eq!(div_le_ge(-2, 3, false), (None, Some(-2)));
    }

    #[test]
    fn tighten_intersects() {
        let mut bounds: FxHashMap<TermId, (Option<i64>, Option<i64>)> = FxHashMap::default();
        let mut changed = false;
        tighten(TermId(0), Some(2), None, &mut bounds, &mut changed);
        assert!(changed);
        assert_eq!(bounds.get(&TermId(0)), Some(&(Some(2), None)));
        changed = false;
        // A less-restrictive lower bound (1 < 2) must NOT relax the stored one.
        tighten(TermId(0), Some(1), None, &mut bounds, &mut changed);
        assert!(!changed);
        // A more-restrictive lower bound (5 > 2) tightens it.
        tighten(TermId(0), Some(5), None, &mut bounds, &mut changed);
        assert!(changed);
        assert_eq!(bounds.get(&TermId(0)), Some(&(Some(5), None)));
        changed = false;
        tighten(TermId(0), None, Some(4), &mut bounds, &mut changed);
        assert!(changed);
        assert_eq!(bounds.get(&TermId(0)), Some(&(Some(5), Some(4))));
    }
}
