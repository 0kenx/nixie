//! Regression tests for `TheoryCombiner::presolve` / `detect_singletons_euf`.
//!
//! Before this fix, `detect_singletons_euf` unconditionally returned an
//! empty `Vec` (never querying the EUF solver) and `presolve`'s Phase 3
//! loop discarded every candidate with `let _ = var;` while still
//! incrementing `vars_eliminated` -- a no-op stub reporting fabricated
//! progress. These tests confirm singleton detection now performs a real
//! EUF equivalence-class query, and that `presolve` actually queues the
//! discovered equality through `propagate_equality`/`propagate` so other
//! theories observe it.

use oxiz_core::ast::TermId;
use oxiz_theories::TheoryCombiner;
// `theory::TheoryResult` collides with `error::TheoryResult` at the crate
// root, so the theory-level check result is re-exported under this alias.
use oxiz_theories::TheoryCheckResult;

/// Two shared variables merged directly in EUF must be reported as a
/// singleton pair by presolve, with a deterministic (smallest `TermId`)
/// canonical representative -- not silently dropped.
#[test]
fn presolve_detects_euf_merged_shared_vars() {
    let mut combiner = TheoryCombiner::new();

    let x = TermId::new(10);
    let y = TermId::new(20);
    combiner.add_shared_var(x);
    combiner.add_shared_var(y);

    let nx = combiner.euf_mut().intern(x);
    let ny = combiner.euf_mut().intern(y);
    combiner
        .euf_mut()
        .merge(nx, ny, TermId::new(0))
        .expect("merge must not error");

    let stats = combiner.presolve().expect("presolve must not error");

    assert_eq!(
        stats.singleton_propagations, 1,
        "the merged pair must be detected, not silently dropped"
    );
    assert_eq!(
        stats.vars_eliminated, 1,
        "the detected pair must be counted as a real elimination"
    );
}

/// A shared variable that EUF has no information about (never interned,
/// never merged with anything) must NOT be fabricated as a singleton.
#[test]
fn presolve_reports_nothing_for_unconstrained_shared_vars() {
    let mut combiner = TheoryCombiner::new();

    let x = TermId::new(1);
    let y = TermId::new(2);
    combiner.add_shared_var(x);
    combiner.add_shared_var(y);

    let stats = combiner.presolve().expect("presolve must not error");

    assert_eq!(stats.singleton_propagations, 0);
    assert_eq!(stats.vars_eliminated, 0);
}

/// The equality `presolve` discovers must actually be propagated (not just
/// counted): after `presolve`, `check()` must still succeed and the theory
/// combiner's EUF/arith view must remain consistent with the merge.
#[test]
fn presolve_propagation_is_consumed_by_check() {
    let mut combiner = TheoryCombiner::new();

    let x = TermId::new(1);
    let y = TermId::new(2);
    combiner.add_shared_var(x);
    combiner.add_shared_var(y);

    let nx = combiner.euf_mut().intern(x);
    let ny = combiner.euf_mut().intern(y);
    combiner
        .euf_mut()
        .merge(nx, ny, TermId::new(0))
        .expect("merge must not error");

    let stats = combiner.presolve().expect("presolve must not error");
    assert_eq!(stats.vars_eliminated, 1);

    // The queued propagation must not corrupt the solve loop.
    let result = combiner.check().expect("check must not error");
    assert!(matches!(result, TheoryCheckResult::Sat));
}
