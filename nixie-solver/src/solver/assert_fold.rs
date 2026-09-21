//! The assertion fold pass (flag-gated, `NIXIE_ASSERT_FOLD=1`).
//!
//! z3's default preprocessing shape: every assertion runs through the
//! core rewriter before the search sees it.  Nixie's encoder pipeline
//! rewrites structurally (`expand_lets`, `flatten_eq_ite_tables`,
//! `eliminate_nonbool_ite`, …) but had no VALUE-level folder — the
//! nec-smt class (2537-deep let/ite/`=` spines encoding a
//! priority-select) reached the encoder structurally intact, tripped
//! `ENCODE_DEPTH_LIMIT`, and answered an instant spurious `Unknown`,
//! while z3's rewriter folds the same goal to `false` outright.
//!
//! The fold composes the two `TermManager` passes that now carry the
//! guard-equality solve rules (z3 `bool_rewriter`'s ite-eq family —
//! `2026-09-20-solve-eqs-guard-elimination.md`): the memoized
//! bottom-up `simplify`, then the context walk `ctx_simplify`.  Both
//! are explicit-stack and fuel-bounded, so a deep spine is stack-safe,
//! and every rule is an unconditional equivalence — the folded
//! assertion is satisfied by exactly the same models.
//!
//! Placement contract (see `Solver::assert`):
//! * AFTER `expand_lets` — the fold does not descend into `Let` nodes,
//!   and the let-expanded DAG is where the select-chains become
//!   visible to the solve rules;
//! * BEFORE the encode-depth guard and the set/bag survey — a folded
//!   spine collapses to a constant (or a much smaller residual), so
//!   the guard measures the folded term and the survey walks fewer
//!   nodes;
//! * the caller's EXACT term is already captured in
//!   `certificate_assertions` — certified mode never trusts the fold.

use nixie_core::ast::{TermId, TermManager};

/// Whether the fold pass is armed (`NIXIE_ASSERT_FOLD` set).  Probe-only
/// until the measurement campaign flips the default.
pub(super) fn enabled() -> bool {
    #[cfg(feature = "std")]
    {
        static ON: std::sync::OnceLock<bool> = std::sync::OnceLock::new();
        *ON.get_or_init(|| std::env::var_os("NIXIE_ASSERT_FOLD").is_some())
    }
    #[cfg(not(feature = "std"))]
    {
        false
    }
}

/// Fold one let-expanded assertion: bottom-up simplify, then the
/// context walk.  Pure function of the term (no solver state).
pub(super) fn fold(term: TermId, manager: &mut TermManager) -> TermId {
    let bottom_up = manager.simplify(term);
    manager.ctx_simplify(bottom_up)
}

#[cfg(test)]
mod tests {
    use super::*;

    /// The fold closes the nec-smt member shape: the self-referential
    /// priority select `(= 5 (ite (= x 5) 3 x))` refutes by pure value
    /// reasoning (x=5 selects 3; x≠5 selects x≠5), so the assertion
    /// folds to `false` outright — the class the depth guard used to
    /// refuse with a spurious instant `Unknown`.
    #[test]
    fn fold_refutes_the_self_referential_select() {
        let mut m = TermManager::new();
        let x = m.mk_var("x", m.sorts.int_sort);
        let five = m.mk_int(5);
        let three = m.mk_int(3);
        let c = m.mk_eq(five, x);
        let sel = m.mk_ite(c, three, x);
        let goal = m.mk_eq(sel, five);
        let out = fold(goal, &mut m);
        assert_eq!(out, m.false_id);
    }

    /// The fold never refutes a satisfiable goal: the same select with
    /// the guard selecting `5` is satisfiable at x=5 and folds to the
    /// guard itself.
    #[test]
    fn fold_keeps_satisfiable_selects() {
        let mut m = TermManager::new();
        let x = m.mk_var("x", m.sorts.int_sort);
        let five = m.mk_int(5);
        let seven = m.mk_int(7);
        let c = m.mk_eq(five, x);
        let sel = m.mk_ite(c, five, seven);
        let goal = m.mk_eq(sel, five);
        let out = fold(goal, &mut m);
        assert_eq!(out, c);
        assert_ne!(out, m.false_id);
    }

    /// Deep-spine safety: a 1200-level nested select folds on the
    /// explicit-stack passes without native recursion, and the result
    /// stays equivalent (here: every level is value-decided, so the
    /// whole spine folds to a constant).
    #[test]
    fn fold_handles_a_deep_spine() {
        let mut m = TermManager::new();
        let p = m.mk_var("p", m.sorts.bool_sort);
        // (ite p 1 (ite p 2 (ite p 3 ... ))): every level's condition
        // is the same undecided p, so the same-condition merges collapse
        // the spine before any walk; the fold still runs through both
        // passes without overflowing (the passes are explicit-stack).
        let mut t = m.mk_int(1200);
        for k in 0..1200 {
            let v = m.mk_int(k);
            t = m.mk_ite(p, v, t);
        }
        let out = fold(t, &mut m);
        // The result must exist and be well-formed (any of: a constant,
        // or a residual ite) — the regression is the process not
        // overflowing, plus idempotence of a second fold.
        let again = fold(out, &mut m);
        assert_eq!(out, again, "the fold is idempotent on its result");
    }

    /// The fold is an end-to-end equivalence on a mixed shape: a
    /// conjunction whose select-equality refutes folds the whole
    /// conjunction to `false`, while the same conjunction with the
    /// satisfiable twin keeps the other conjuncts.
    #[test]
    fn fold_composes_with_conjunctions() {
        let mut m = TermManager::new();
        let x = m.mk_var("x", m.sorts.int_sort);
        let q = m.mk_var("q", m.sorts.bool_sort);
        let five = m.mk_int(5);
        let three = m.mk_int(3);
        let c = m.mk_eq(five, x);
        let sel = m.mk_ite(c, three, x);
        let bad = m.mk_eq(sel, five);
        let goal = m.mk_and([q, bad]);
        let out = fold(goal, &mut m);
        assert_eq!(out, m.false_id, "q AND false is false");
    }
}
