//! Regression tests for the arithmetic solver's push/pop state rollback.
//!
//! Diagnosed bug: `ArithSolver::pop()` truncated `var_to_term` but did NOT roll
//! back `term_to_var`. Because the underlying simplex recycles variable indices
//! across a pop (its per-variable arrays shrink), the stale `term_to_var`
//! entries made `intern()` replay indices that now belong to a different – or
//! not-yet-created – variable. Downstream constraints could then attach to a
//! recycled index, a correctness/performance hazard.
//!
//! These tests exercise the behaviour purely through the public API:
//! `intern()` (variable identity) and `push`/`pop`/`check` (solve verdicts).

use num_rational::Rational64;
use num_traits::One;
use oxiz_core::ast::TermId;
use oxiz_theories::Theory;
use oxiz_theories::TheoryCheckResult;
use oxiz_theories::arithmetic::ArithSolver;

/// After a pop, a fresh term must not be handed an index that a stale (but
/// still re-internable) term also claims.
///
/// intern `a`, push, intern `b`, pop. Then intern a brand-new `c` (the simplex
/// hands it the slot `b` vacated) and re-intern `b`. If `pop()` failed to drop
/// `b`'s stale mapping, `intern(b)` would return the same index as `c`.
#[test]
fn pop_recycled_index_no_collision() {
    let mut solver = ArithSolver::lra();
    let a = TermId::new(1);
    let b = TermId::new(2);
    let c = TermId::new(3);

    let _va = solver.intern(a);
    solver.push();
    let _vb = solver.intern(b);
    solver.pop();

    let vc = solver.intern(c);
    let vb2 = solver.intern(b);
    assert_ne!(
        vc, vb2,
        "recycled var index {vc} collided with re-interned truncated term (vb2={vb2})"
    );
}

/// Re-interning a term that was truncated by a pop yields a stable, valid index
/// and interning the *same* term again is idempotent (returns the same index).
#[test]
fn pop_reintern_truncated_term_is_stable() {
    let mut solver = ArithSolver::lra();
    let base = TermId::new(1);
    let scoped = TermId::new(2);

    let vbase = solver.intern(base);
    solver.push();
    let _vscoped = solver.intern(scoped);
    solver.pop();

    // `base` predates the push, so its identity is unchanged by the pop.
    assert_eq!(
        solver.intern(base),
        vbase,
        "base term identity must survive pop"
    );

    // `scoped` was truncated; re-interning gives a fresh index, and interning it
    // once more is idempotent.
    let vscoped2 = solver.intern(scoped);
    let vscoped3 = solver.intern(scoped);
    assert_eq!(vscoped2, vscoped3, "re-intern must be idempotent");
    assert_ne!(vscoped2, vbase, "distinct terms must map to distinct vars");
}

/// A repeated push / assert / check / pop loop over a term interned at the base
/// level must return consistent verdicts every iteration. If the stale mapping
/// leaked, the recycled-index constraints could perturb later solves.
#[test]
fn push_pop_solve_loop_consistent_verdicts() {
    let mut solver = ArithSolver::lra();
    let x = TermId::new(1);
    let reason = TermId::new(100);

    // Base constraint: x >= 0.
    solver.assert_ge(
        &[(x, Rational64::one())],
        Rational64::from_integer(0),
        reason,
    );

    for iter in 0..8 {
        // Base state alone is satisfiable (x >= 0).
        let base = solver.check().expect("base check should succeed");
        assert!(
            matches!(base, TheoryCheckResult::Sat),
            "iter {iter}: base (x>=0) must be Sat, got {base:?}"
        );

        // Under a scope, add x <= -1 → contradicts x >= 0 → Unsat.
        solver.push();
        solver.assert_le(
            &[(x, Rational64::one())],
            Rational64::from_integer(-1),
            reason,
        );
        let scoped = solver.check().expect("scoped check should succeed");
        assert!(
            matches!(scoped, TheoryCheckResult::Unsat(_)),
            "iter {iter}: x>=0 AND x<=-1 must be Unsat, got {scoped:?}"
        );
        solver.pop();

        // After the pop the contradiction is gone: base is Sat again.
        let after = solver.check().expect("post-pop check should succeed");
        assert!(
            matches!(after, TheoryCheckResult::Sat),
            "iter {iter}: base must be Sat again after pop, got {after:?}"
        );
    }
}

/// Interleave scopes that each intern a *fresh* term (exercising VarId
/// recycling), then reuse an earlier term outside the scopes. Verdicts must be
/// stable and reflect the base constraints only.
#[test]
fn push_pop_fresh_terms_recycled_vars_consistent() {
    let mut solver = ArithSolver::lia();
    let reason = TermId::new(100);
    let anchor = TermId::new(1);

    // anchor in [2, 4]: satisfiable, established at the base level.
    solver.assert_ge(
        &[(anchor, Rational64::one())],
        Rational64::from_integer(2),
        reason,
    );
    solver.assert_le(
        &[(anchor, Rational64::one())],
        Rational64::from_integer(4),
        reason,
    );

    for i in 0..6 {
        solver.push();
        // Each scope interns a brand-new term whose simplex var index is
        // recycled from a prior popped scope.
        let scoped = TermId::new(1000 + i);
        // scoped in [5, 3]: empty interval → Unsat within this scope.
        solver.assert_ge(
            &[(scoped, Rational64::one())],
            Rational64::from_integer(5),
            reason,
        );
        solver.assert_le(
            &[(scoped, Rational64::one())],
            Rational64::from_integer(3),
            reason,
        );
        let scoped_res = solver.check().expect("scoped check should succeed");
        assert!(
            matches!(scoped_res, TheoryCheckResult::Unsat(_)),
            "iter {i}: scoped [5,3] must be Unsat, got {scoped_res:?}"
        );
        solver.pop();

        // Base (anchor in [2,4]) remains satisfiable after the pop.
        let base = solver.check().expect("base check should succeed");
        assert!(
            matches!(base, TheoryCheckResult::Sat),
            "iter {i}: base (anchor in [2,4]) must stay Sat, got {base:?}"
        );
    }
}
