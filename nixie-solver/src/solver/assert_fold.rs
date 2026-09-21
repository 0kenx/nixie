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
