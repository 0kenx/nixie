//! The finite-set decision procedure.
//!
//! Every membership atom gets its defining axioms when the assertion is
//! encoded (`solver::set_theory`), so the SAT layer and EUF decide sets
//! together. These tests are the evidence that it *decides* — each asserts a
//! formula whose status is known independently.

use nixie_core::{TermId, TermManager};
use nixie_solver::{Solver, SolverResult};

/// Assert `build`'s formulas and report the verdict.
fn solve(build: impl FnOnce(&mut TermManager) -> Vec<TermId>) -> SolverResult {
    let mut tm = TermManager::new();
    let asserts = build(&mut tm);
    let mut solver = Solver::new();
    for a in asserts {
        solver.assert(a, &mut tm);
    }
    solver.check(&mut tm)
}

/// `1 \in {1}` is true, so asserting its negation is unsatisfiable.
#[test]
fn membership_in_a_singleton_is_decided() {
    let got = solve(|tm| {
        let one = tm.mk_int(1);
        let s = tm.mk_set_singleton(one);
        let m = tm.mk_set_member(one, s);
        vec![tm.mk_not(m)]
    });
    assert_eq!(got, SolverResult::Unsat);
}

/// ...and `2 \in {1}` is false, so asserting it is unsatisfiable.
#[test]
fn non_membership_in_a_singleton_is_decided() {
    let got = solve(|tm| {
        let one = tm.mk_int(1);
        let two = tm.mk_int(2);
        let s = tm.mk_set_singleton(one);
        vec![tm.mk_set_member(two, s)]
    });
    assert_eq!(got, SolverResult::Unsat);
}

/// Nothing is in the empty set.
#[test]
fn nothing_is_in_the_empty_set() {
    let got = solve(|tm| {
        let int = tm.sorts.int_sort;
        let x = tm.mk_var("x", int);
        let e = tm.mk_set_empty(int);
        vec![tm.mk_set_member(x, e)]
    });
    assert_eq!(got, SolverResult::Unsat);
}

/// Membership propagates through union: `x \in a` forces `x \in a \cup b`.
#[test]
fn union_absorbs_its_operands() {
    let got = solve(|tm| {
        let int = tm.sorts.int_sort;
        let x = tm.mk_var("x", int);
        let si = tm.sorts.set(int);
        let a = tm.mk_var("a", si);
        let b = tm.mk_var("b", si);
        let u = tm.mk_set_union(a, b);
        let in_a = tm.mk_set_member(x, a);
        let in_u = tm.mk_set_member(x, u);
        let not_in_u = tm.mk_not(in_u);
        vec![in_a, not_in_u]
    });
    assert_eq!(got, SolverResult::Unsat);
}

/// Intersection needs *both*: being in `a` alone does not put you in `a \cap b`.
#[test]
fn intersection_requires_both_sides() {
    let mut tm = TermManager::new();
    let int = tm.sorts.int_sort;
    let x = tm.mk_var("x", int);
    let si = tm.sorts.set(int);
    let a = tm.mk_var("a", si);
    let b = tm.mk_var("b", si);
    let i = tm.mk_set_inter(a, b);
    let in_a = tm.mk_set_member(x, a);
    let in_i = tm.mk_set_member(x, i);
    let not_in_i = tm.mk_not(in_i);

    // Satisfiable: x is in a but not in b.
    let mut s1 = Solver::new();
    s1.assert(in_a, &mut tm);
    s1.assert(not_in_i, &mut tm);
    assert_eq!(s1.check(&mut tm), SolverResult::Sat);

    // Unsatisfiable: in both, yet not in the intersection.
    let in_b = tm.mk_set_member(x, b);
    let mut s2 = Solver::new();
    s2.assert(in_a, &mut tm);
    s2.assert(in_b, &mut tm);
    s2.assert(not_in_i, &mut tm);
    assert_eq!(s2.check(&mut tm), SolverResult::Unsat);
}

/// Difference needs the *negative* side, which is the rule easiest to get
/// backwards: `x \in a \ b` requires `x \in a` and `x \notin b`.
#[test]
fn difference_requires_the_negative_side() {
    let got = solve(|tm| {
        let int = tm.sorts.int_sort;
        let x = tm.mk_var("x", int);
        let si = tm.sorts.set(int);
        let a = tm.mk_var("a", si);
        let b = tm.mk_var("b", si);
        let d = tm.mk_set_minus(a, b);
        let in_d = tm.mk_set_member(x, d);
        let in_b = tm.mk_set_member(x, b);
        // In `a \ b` and also in `b` — impossible.
        vec![in_d, in_b]
    });
    assert_eq!(got, SolverResult::Unsat);
}

/// Set equality is **extensional**: equal sets have the same members.
#[test]
fn equal_sets_share_their_members() {
    let got = solve(|tm| {
        let int = tm.sorts.int_sort;
        let x = tm.mk_var("x", int);
        let si = tm.sorts.set(int);
        let a = tm.mk_var("a", si);
        let b = tm.mk_var("b", si);
        let eq = tm.mk_eq(a, b);
        let in_a = tm.mk_set_member(x, a);
        let in_b = tm.mk_set_member(x, b);
        let not_in_b = tm.mk_not(in_b);
        vec![eq, in_a, not_in_b]
    });
    assert_eq!(got, SolverResult::Unsat);
}

/// The converse, which needs the **disequality witness**: two sets with
/// exactly the same members must be equal. Without a witness the solver could
/// keep `a != b` while every membership agrees.
#[test]
fn sets_with_the_same_members_are_equal() {
    let got = solve(|tm| {
        let int = tm.sorts.int_sort;
        let one = tm.mk_int(1);
        let s1 = tm.mk_set_singleton(one);
        let s2 = tm.mk_set_singleton(one);
        let _ = int;
        // `{1}` and `{1}` are the same term, so use union with empty to make
        // two syntactically different but equal sets.
        let e = tm.mk_set_empty(int);
        let u = tm.mk_set_union(s2, e);
        let eq = tm.mk_eq(s1, u);
        vec![tm.mk_not(eq)]
    });
    assert_eq!(
        got,
        SolverResult::Unsat,
        "`{{1}}` and `{{1}} \\cup {{}}` have the same members, so they are equal"
    );
}

/// Subset is decided by membership, in both directions.
#[test]
fn subset_is_decided() {
    let mut tm = TermManager::new();
    let int = tm.sorts.int_sort;
    let si = tm.sorts.set(int);
    let a = tm.mk_var("a", si);
    let b = tm.mk_var("b", si);
    let u = tm.mk_set_union(a, b);

    // `a \subseteq a \cup b` is valid, so its negation is unsatisfiable.
    let sub = tm.mk_set_subset(a, u);
    let not_sub = tm.mk_not(sub);
    let mut s = Solver::new();
    s.assert(not_sub, &mut tm);
    assert_eq!(s.check(&mut tm), SolverResult::Unsat);
}

/// ...and a subset claim that does not hold is satisfiable, so the rule is not
/// just answering `Unsat` to everything.
#[test]
fn a_false_subset_claim_is_satisfiable() {
    let got = solve(|tm| {
        let int = tm.sorts.int_sort;
        let si = tm.sorts.set(int);
        let a = tm.mk_var("a", si);
        let b = tm.mk_var("b", si);
        let sub = tm.mk_set_subset(a, b);
        vec![tm.mk_not(sub)]
    });
    assert_eq!(got, SolverResult::Sat);
}

/// A plainly satisfiable set problem must come back `Sat`, not `Unknown`:
/// the honesty gate must no longer fire for membership.
#[test]
fn a_satisfiable_set_problem_is_sat_not_unknown() {
    let got = solve(|tm| {
        let int = tm.sorts.int_sort;
        let x = tm.mk_var("x", int);
        let si = tm.sorts.set(int);
        let a = tm.mk_var("a", si);
        vec![tm.mk_set_member(x, a)]
    });
    assert_eq!(got, SolverResult::Sat);
}

/// `set.card` is *not* covered by the reduction, so it must still degrade to
/// `Unknown` rather than resting on an unconstrained integer.
#[test]
fn cardinality_still_degrades_to_unknown() {
    let got = solve(|tm| {
        let one = tm.mk_int(1);
        let s = tm.mk_set_singleton(one);
        let card = tm.mk_set_card(s);
        let two = tm.mk_int(2);
        // `Cardinality({1}) = 2` is false, but nothing here knows that.
        vec![tm.mk_eq(card, two)]
    });
    assert_eq!(got, SolverResult::Unknown);
}
