//! Regression tests for audited EUF soundness defects.
//!
//! Covers two confirmed critical findings:
//!  1. `union_find.rs`: path compression inside `find()` must be undone on
//!     `pop()` so a pointer compressed to a deep root at a deeper scope cannot
//!     survive a backtrack and corrupt equivalence classes.
//!  2. `euf/solver.rs`: `pop()` must remove proof-forest edges appended to
//!     *pre-existing* nodes during the popped scope, so conflict explanations
//!     never cite retracted assertions.

use oxiz_core::ast::TermId;
use oxiz_theories::Theory;
use oxiz_theories::euf::EufSolver;

/// Finding 1 — direct reproduction at the solver level.
///
/// Base: b = a (so root(b) walks through a). Push. In the scope, merge a = c and
/// force a `find(b)` (via `are_equal`) that would path-compress b straight to the
/// c-root. After `pop`, b must be back with a and NOT equal to c.
#[test]
fn find_path_compression_is_undone_on_pop() {
    let mut solver = EufSolver::new();
    let a = solver.intern(TermId::new(1));
    let b = solver.intern(TermId::new(2));
    let c = solver.intern(TermId::new(3));

    // Base level: b = a.
    solver.merge(b, a, TermId::new(10)).expect("merge b=a");
    assert!(solver.are_equal(a, b));

    solver.push();
    // Scope: a = c. Now root of {a,b} is unified with c.
    solver.merge(a, c, TermId::new(11)).expect("merge a=c");
    // Force path compression on b: are_equal walks find(b), which may rewrite
    // parent[b] to point directly at the c-root.
    assert!(solver.are_equal(b, c), "b, a, c all equal inside the scope");
    assert!(solver.are_equal(a, c));

    // Pop: the a=c union is retracted. If compression on b survived, b would
    // still be wrongly equal to c.
    solver.pop();

    assert!(
        solver.are_equal(a, b),
        "b=a from the base level must persist after pop"
    );
    assert!(
        !solver.are_equal(b, c),
        "b must NOT be equal to c after the a=c scope is popped \
         (path compression must be trail-undone)"
    );
    assert!(
        !solver.are_equal(a, c),
        "a must NOT be equal to c after pop"
    );
}

/// Finding 1 — deeper stress: multiple compressions across nested scopes must all
/// unwind exactly, leaving only the base-level equalities.
#[test]
fn nested_scope_compression_unwinds_exactly() {
    let mut solver = EufSolver::new();
    let a = solver.intern(TermId::new(1));
    let b = solver.intern(TermId::new(2));
    let c = solver.intern(TermId::new(3));
    let d = solver.intern(TermId::new(4));

    // Base: chain b = a.
    solver.merge(b, a, TermId::new(10)).expect("merge b=a");

    solver.push(); // level 1
    solver.merge(a, c, TermId::new(11)).expect("merge a=c");
    assert!(solver.are_equal(b, c)); // compress b -> c-root

    solver.push(); // level 2
    solver.merge(c, d, TermId::new(12)).expect("merge c=d");
    assert!(solver.are_equal(b, d)); // compress b -> d-root

    solver.pop(); // undo c=d
    assert!(solver.are_equal(b, c), "b=c should hold at level 1");
    assert!(!solver.are_equal(b, d), "b=d must be undone");

    solver.pop(); // undo a=c
    assert!(solver.are_equal(a, b), "base b=a persists");
    assert!(!solver.are_equal(b, c), "b=c must be undone");
    assert!(!solver.are_equal(a, c));
    assert!(!solver.are_equal(a, d));
}

/// Finding 2 — proof-forest edges on pre-existing nodes must not leak past a pop
/// and let a later conflict be "explained" by a retracted assertion.
///
/// a, b pre-exist the scope. Inside the scope we assert a = b (reason 21). We pop.
/// Now, at the base level, we assert a != b and then a = b with a DIFFERENT reason
/// (31). The conflict explanation must cite reason 31 (the live assertion) and
/// must NOT cite the retracted reason 21.
#[test]
fn popped_proof_edges_do_not_pollute_explanations() {
    let mut solver = EufSolver::new();
    let a = solver.intern(TermId::new(1));
    let b = solver.intern(TermId::new(2));

    solver.push();
    // Merge inside the scope, appending proof-forest edges onto pre-existing
    // nodes a and b with reason 21.
    solver
        .merge(a, b, TermId::new(21))
        .expect("merge a=b in scope");
    assert!(solver.are_equal(a, b));
    solver.pop();

    // After pop the merge is retracted.
    assert!(
        !solver.are_equal(a, b),
        "a=b asserted inside the scope must be retracted by pop"
    );

    // Fresh, live conflict at the base level with a different reason.
    solver.assert_diseq(a, b, TermId::new(30));
    solver.merge(a, b, TermId::new(31)).expect("merge a=b live");

    let conflict = solver
        .check_conflicts()
        .expect("a=b together with a!=b is a conflict");

    assert!(
        conflict.contains(&TermId::new(31)),
        "explanation must cite the live equality reason 31, got {conflict:?}"
    );
    assert!(
        !conflict.contains(&TermId::new(21)),
        "explanation must NOT cite the retracted reason 21 from the popped scope, \
         got {conflict:?}"
    );
}

/// Finding 2 — congruence edges appended to pre-existing nodes during a scope must
/// also be removed on pop.
#[test]
fn popped_congruence_edges_do_not_pollute_explanations() {
    let mut solver = EufSolver::new();
    let a = solver.intern(TermId::new(1));
    let b = solver.intern(TermId::new(2));
    let f_sym = 7u32;
    let fa = solver.intern_app(TermId::new(10), f_sym, [a]);
    let fb = solver.intern_app(TermId::new(11), f_sym, [b]);

    solver.push();
    // a=b inside the scope forces congruence f(a)=f(b), appending congruence
    // proof edges onto the pre-existing fa/fb nodes.
    solver
        .merge(a, b, TermId::new(50))
        .expect("merge a=b in scope");
    assert!(solver.are_equal(fa, fb));
    solver.pop();

    assert!(
        !solver.are_equal(fa, fb),
        "congruence f(a)=f(b) must be retracted after pop"
    );
    assert!(!solver.are_equal(a, b), "a=b must be retracted after pop");

    // Re-establish congruence with a fresh reason and check the explanation is
    // built only from live edges.
    solver.assert_diseq(fa, fb, TermId::new(60));
    solver.merge(a, b, TermId::new(61)).expect("merge a=b live");
    let conflict = solver
        .check_conflicts()
        .expect("f(a)=f(b) with f(a)!=f(b) is a conflict");
    assert!(
        conflict.contains(&TermId::new(60)),
        "explanation must cite live diseq reason 60, got {conflict:?}"
    );
    assert!(
        !conflict.contains(&TermId::new(50)),
        "explanation must NOT cite the retracted scope reason 50, got {conflict:?}"
    );
}

/// Sanity: repeated push/pop cycles keep state consistent (no drift in either the
/// union-find trail or the proof-forest trail).
#[test]
fn repeated_push_pop_cycles_are_stable() {
    let mut solver = EufSolver::new();
    let a = solver.intern(TermId::new(1));
    let b = solver.intern(TermId::new(2));
    let c = solver.intern(TermId::new(3));
    solver.merge(a, b, TermId::new(5)).expect("base a=b");

    for round in 0..8u32 {
        solver.push();
        solver
            .merge(b, c, TermId::new(100 + round))
            .expect("scope b=c");
        assert!(solver.are_equal(a, c));
        solver.pop();
        assert!(
            solver.are_equal(a, b),
            "base equality survives round {round}"
        );
        assert!(
            !solver.are_equal(b, c),
            "scope equality retracted round {round}"
        );
    }
}
