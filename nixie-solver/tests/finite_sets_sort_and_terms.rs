//! The finite-set sort and term language, and the honesty gate that keeps it
//! sound until the theory solver exists.
//!
//! The SMT-LIB theory of finite sets, as CVC5 implements it in
//! `src/theory/sets`. This slice adds the *language*: a `Set` sort, the eight
//! operators, sort rules, printing and substitution. It does **not** add a
//! decision procedure, and the tests below are mostly about making sure that
//! absence cannot be mistaken for an answer.

use nixie_core::{SortKind, TermManager};
use nixie_solver::{Solver, SolverResult};

fn int_set(tm: &mut TermManager) -> nixie_core::SortId {
    let int = tm.sorts.int_sort;
    tm.sorts.set(int)
}

#[test]
fn the_set_sort_is_parameterised_and_interned() {
    let mut tm = TermManager::new();
    let int = tm.sorts.int_sort;
    let bool_ = tm.sorts.bool_sort;
    let si = tm.sorts.set(int);
    let sb = tm.sorts.set(bool_);
    assert_ne!(si, sb, "sets of different elements are different sorts");
    assert_eq!(si, tm.sorts.set(int), "the same set sort interns once");

    let s = tm.sorts.get(si).expect("interned");
    assert!(s.is_set());
    assert_eq!(s.set_element(), Some(int));
}

/// A set of sets is an ordinary sort, which an `Array(elem, Bool)` encoding
/// would have made awkward and a flat representation would have made
/// impossible.
#[test]
fn sets_nest() {
    let mut tm = TermManager::new();
    let si = int_set(&mut tm);
    let ssi = tm.sorts.set(si);
    assert_eq!(
        tm.sorts.get(ssi).and_then(nixie_core::Sort::set_element),
        Some(si)
    );
}

#[test]
fn operators_get_the_right_sorts() {
    let mut tm = TermManager::new();
    let int = tm.sorts.int_sort;
    let si = int_set(&mut tm);

    let empty = tm.mk_set_empty(int);
    assert_eq!(tm.get(empty).expect("built").sort, si);

    let one = tm.mk_int(1);
    let singleton = tm.mk_set_singleton(one);
    assert_eq!(tm.get(singleton).expect("built").sort, si);

    for built in [
        tm.mk_set_union(empty, singleton),
        tm.mk_set_inter(empty, singleton),
        tm.mk_set_minus(empty, singleton),
    ] {
        assert_eq!(tm.get(built).expect("built").sort, si);
    }

    // The predicates are Bool, and cardinality is where sets meet arithmetic.
    let bool_ = tm.sorts.bool_sort;
    let member = tm.mk_set_member(one, singleton);
    assert_eq!(tm.get(member).expect("built").sort, bool_);
    let subset = tm.mk_set_subset(empty, singleton);
    assert_eq!(tm.get(subset).expect("built").sort, bool_);
    let card = tm.mk_set_card(singleton);
    assert_eq!(tm.get(card).expect("built").sort, tm.sorts.int_sort);
}

/// Terms are hash-consed, so the same set expression is the same node — which
/// is what makes congruence over set operators meaningful.
#[test]
fn set_terms_are_interned() {
    let mut tm = TermManager::new();
    let one = tm.mk_int(1);
    let a = tm.mk_set_singleton(one);
    let b = tm.mk_set_singleton(one);
    assert_eq!(a, b);

    let int = tm.sorts.int_sort;
    assert_eq!(tm.mk_set_empty(int), tm.mk_set_empty(int));
    let bool_ = tm.sorts.bool_sort;
    assert_ne!(
        tm.mk_set_empty(int),
        tm.mk_set_empty(bool_),
        "the empty set's identity includes its element sort"
    );
}

/// Membership is **decided**, not gated.
///
/// This test began life asserting `Unknown`: when only the set *language*
/// existed, `set.member` was an opaque Boolean nothing constrained, and the
/// honesty gate had to stop a wrong `sat`. `solver::set_theory` now supplies
/// the defining axioms, so the right answer is available and the gate no
/// longer fires for membership. The gate itself is still load-bearing — see
/// `cardinality_still_degrades_to_unknown` in `finite_sets_decision.rs`, which
/// covers the one construct the reduction does not.
#[test]
fn membership_is_decided_rather_than_gated() {
    let mut tm = TermManager::new();
    let one = tm.mk_int(1);
    let singleton = tm.mk_set_singleton(one);
    // `1 \in {1}` is true, so its negation is unsatisfiable.
    let member = tm.mk_set_member(one, singleton);
    let claim = tm.mk_not(member);

    let mut solver = Solver::new();
    solver.assert(claim, &mut tm);
    assert_eq!(
        solver.check(&mut tm),
        SolverResult::Unsat,
        "the reduction decides membership in a singleton"
    );
}

/// A problem with no set terms is unaffected by any of this.
#[test]
fn the_gate_does_not_fire_without_set_terms() {
    let mut tm = TermManager::new();
    let x = tm.mk_var("x", tm.sorts.int_sort);
    let one = tm.mk_int(1);
    let eq = tm.mk_eq(x, one);
    let mut solver = Solver::new();
    solver.assert(eq, &mut tm);
    assert_eq!(solver.check(&mut tm), SolverResult::Sat);
}

/// An `Unsat` that does not depend on the set atoms stays `Unsat`.
#[test]
fn an_unsat_independent_of_sets_still_holds() {
    let mut tm = TermManager::new();
    let one = tm.mk_int(1);
    let singleton = tm.mk_set_singleton(one);
    let member = tm.mk_set_member(one, singleton);

    let x = tm.mk_var("x", tm.sorts.int_sort);
    let two = tm.mk_int(2);
    let a = tm.mk_eq(x, one);
    let b = tm.mk_eq(x, two);
    let contradiction = tm.mk_and([a, b, member]);

    let mut solver = Solver::new();
    solver.assert(contradiction, &mut tm);
    assert_eq!(
        solver.check(&mut tm),
        SolverResult::Unsat,
        "a refutation that does not rest on set semantics is still valid"
    );
}

/// Substitution rebuilds set terms through the builder, so the result is
/// interned and sorted exactly as a freshly built term would be.
#[test]
fn substitution_rebuilds_set_terms() {
    let mut tm = TermManager::new();
    let int = tm.sorts.int_sort;
    let x = tm.mk_var("x", int);
    let s = tm.mk_set_singleton(x);
    let card = tm.mk_set_card(s);

    let one = tm.mk_int(1);
    let subst = [(x, one)].into_iter().collect();
    let out = tm.substitute(card, &subst);

    let expected_set = tm.mk_set_singleton(one);
    let expected = tm.mk_set_card(expected_set);
    assert_eq!(out, expected);
}

/// Sorts print in SMT-LIB syntax, so a `(Set Int)` round-trips as text.
#[test]
fn the_set_sort_prints_as_smtlib() {
    let mut tm = TermManager::new();
    let si = int_set(&mut tm);
    let name = tm.sorts.sort_name(si);
    assert_eq!(name.as_deref(), Some("Set"));
    assert!(matches!(
        tm.sorts.get(si).map(|s| &s.kind),
        Some(SortKind::Set(_))
    ));
}
