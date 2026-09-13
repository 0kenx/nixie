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

/// `set.card` over a set with known members is **decided**.
///
/// This pinned `Unknown` when the reduction did not cover cardinality at all.
/// It now pins the right answer; the gate it used to guard still applies to a
/// set whose members are *not* statically known, which is
/// `cardinality_of_an_opaque_set_is_declined`.
#[test]
fn cardinality_of_a_known_set_is_decided() {
    let got = solve(|tm| {
        let one = tm.mk_int(1);
        let s = tm.mk_set_singleton(one);
        let card = tm.mk_set_card(s);
        let two = tm.mk_int(2);
        // `Cardinality({1}) = 2` is false.
        vec![tm.mk_eq(card, two)]
    });
    assert_eq!(got, SolverResult::Unsat);
}

// ---------------------------------------------------------------------------
// String-literal distinctness — regressions for a false `sat`
// ---------------------------------------------------------------------------
//
// Found through the TLA+ arena's `Cardinality` encoding, which guards each
// indicator with an element equality. Two independent gaps made a string
// equality undecidable whenever it reached the solver as anything other than
// a top-level assertion (which preprocessing folds):
//
//   1. `mk_eq` folded `IntConst`, `Bool` and `BitVecConst` but not `StringLit`;
//   2. EUF never marked string literals as distinguished values, so merging
//      classes holding `"a"` and `"b"` raised no conflict.
//
// Both directions matter: the fix must decide the unsatisfiable cases *without*
// simply assuming equalities false, so a genuinely satisfiable case is checked
// too.

/// Gap 1: two distinct string literals forced equal through a clause.
#[test]
fn distinct_string_literals_cannot_be_equal() {
    let got = solve(|tm| {
        let bs = tm.sorts.bool_sort;
        let p = tm.mk_var("p", bs);
        let a = tm.mk_string_lit("a");
        let b = tm.mk_string_lit("b");
        let eq = tm.mk_eq(a, b);
        let clause = tm.mk_or([eq, p]);
        let np = tm.mk_not(p);
        vec![clause, np]
    });
    assert_eq!(got, SolverResult::Unsat);
}

/// Gap 2: one variable forced equal to two distinct literals, both through
/// clauses so that preprocessing cannot fold either.
#[test]
fn a_variable_cannot_equal_two_string_literals() {
    let got = solve(|tm| {
        let ss = tm.sorts.string_sort();
        let bs = tm.sorts.bool_sort;
        let x = tm.mk_var("x", ss);
        let p = tm.mk_var("p", bs);
        let q = tm.mk_var("q", bs);
        let a = tm.mk_string_lit("a");
        let b = tm.mk_string_lit("b");
        let ea = tm.mk_eq(x, a);
        let eb = tm.mk_eq(x, b);
        let c1 = tm.mk_or([ea, p]);
        let c2 = tm.mk_or([eb, q]);
        let np = tm.mk_not(p);
        let nq = tm.mk_not(q);
        vec![c1, np, c2, nq]
    });
    assert_eq!(got, SolverResult::Unsat);
}

/// Two variables pinned to different literals cannot be equal — the shape the
/// `Cardinality` de-duplication actually builds.
#[test]
fn variables_at_distinct_literals_are_distinct() {
    let got = solve(|tm| {
        let ss = tm.sorts.string_sort();
        let (x, y) = (tm.mk_var("x", ss), tm.mk_var("y", ss));
        let a = tm.mk_string_lit("a");
        let b = tm.mk_string_lit("b");
        let ea = tm.mk_eq(x, a);
        let eb = tm.mk_eq(y, b);
        let xy = tm.mk_eq(x, y);
        let one = tm.mk_int(1);
        let zero = tm.mk_int(0);
        let ite = tm.mk_ite(xy, one, zero);
        let is_zero = tm.mk_eq(ite, zero);
        let n = tm.mk_not(is_zero);
        vec![ea, eb, n]
    });
    assert_eq!(got, SolverResult::Unsat);
}

/// The same spellings of one literal *must* still merge freely, so the marks
/// do not make equal strings look different.
#[test]
fn equal_string_literals_still_merge() {
    let got = solve(|tm| {
        let ss = tm.sorts.string_sort();
        let (x, y) = (tm.mk_var("x", ss), tm.mk_var("y", ss));
        let a1 = tm.mk_string_lit("a");
        let a2 = tm.mk_string_lit("a");
        let e1 = tm.mk_eq(x, a1);
        let e2 = tm.mk_eq(y, a2);
        let xy = tm.mk_eq(x, y);
        // `x = "a"`, `y = "a"`, and `x != y` is a contradiction.
        let nxy = tm.mk_not(xy);
        vec![e1, e2, nxy]
    });
    assert_eq!(got, SolverResult::Unsat);
}

/// ...and a genuinely satisfiable string problem is still `Sat`, so the fix is
/// not "assume every equality false".
#[test]
fn an_open_string_equality_is_still_satisfiable() {
    let got = solve(|tm| {
        let ss = tm.sorts.string_sort();
        let (x, y) = (tm.mk_var("x", ss), tm.mk_var("y", ss));
        vec![tm.mk_eq(x, y)]
    });
    assert_eq!(got, SolverResult::Sat);
}

// ---------------------------------------------------------------------------
// Cardinality
// ---------------------------------------------------------------------------
//
// Exact where a set's members are confined to a statically known list, and
// declined (degrading `Sat` to `Unknown`) where they are not. The candidates
// in that list are NOT distinct, so the count de-duplicates: a plain sum of
// indicators reports `|{x} \cup {y}| = 2` even when `x = y`.

#[test]
fn cardinality_of_literal_sets() {
    let mut tm = TermManager::new();
    let int = tm.sorts.int_sort;
    let empty = tm.mk_set_empty(int);
    let (one, two) = (tm.mk_int(1), tm.mk_int(2));
    let s1 = tm.mk_set_singleton(one);
    let s2 = tm.mk_set_singleton(two);
    let pair = tm.mk_set_union(s1, s2);

    for (set, expected) in [(empty, 0i64), (s1, 1), (pair, 2)] {
        let card = tm.mk_set_card(set);
        let lit = tm.mk_int(expected);
        let claim = tm.mk_eq(card, lit);
        let negated = tm.mk_not(claim);
        let mut solver = Solver::new();
        solver.assert(negated, &mut tm);
        assert_eq!(
            solver.check(&mut tm),
            SolverResult::Unsat,
            "cardinality should be exactly {expected}"
        );
    }
}

/// **The de-duplication.** `{x} \cup {y}` has two candidates denoting one
/// value when `x = y`, so its cardinality is 1. A plain sum of indicators gets
/// this wrong in every model that equates them.
#[test]
fn cardinality_does_not_double_count_equal_members() {
    let mut tm = TermManager::new();
    let int = tm.sorts.int_sort;
    let (x, y) = (tm.mk_var("x", int), tm.mk_var("y", int));
    let (sx, sy) = (tm.mk_set_singleton(x), tm.mk_set_singleton(y));
    let u = tm.mk_set_union(sx, sy);
    let card = tm.mk_set_card(u);
    let eq = tm.mk_eq(x, y);
    let one = tm.mk_int(1);
    let is_one = tm.mk_eq(card, one);
    let not_one = tm.mk_not(is_one);

    let mut s = Solver::new();
    s.assert(eq, &mut tm);
    s.assert(not_one, &mut tm);
    assert_eq!(
        s.check(&mut tm),
        SolverResult::Unsat,
        "two equal members are one element"
    );
}

/// ...and when they differ, the cardinality really is 2, so the rule is not
/// simply collapsing everything.
#[test]
fn cardinality_counts_distinct_members_separately() {
    let mut tm = TermManager::new();
    let int = tm.sorts.int_sort;
    let (x, y) = (tm.mk_var("x", int), tm.mk_var("y", int));
    let (sx, sy) = (tm.mk_set_singleton(x), tm.mk_set_singleton(y));
    let u = tm.mk_set_union(sx, sy);
    let card = tm.mk_set_card(u);
    let eq = tm.mk_eq(x, y);
    let neq = tm.mk_not(eq);
    let two = tm.mk_int(2);
    let is_two = tm.mk_eq(card, two);
    let not_two = tm.mk_not(is_two);

    let mut s = Solver::new();
    s.assert(neq, &mut tm);
    s.assert(not_two, &mut tm);
    assert_eq!(s.check(&mut tm), SolverResult::Unsat);
}

/// Over **string** elements — the exact shape that exposed the string-literal
/// false `sat`, since the de-duplication guards are element equalities.
#[test]
fn cardinality_over_string_elements() {
    let mut tm = TermManager::new();
    let a = tm.mk_string_lit("a");
    let b = tm.mk_string_lit("b");
    let (sa, sb) = (tm.mk_set_singleton(a), tm.mk_set_singleton(b));
    let u = tm.mk_set_union(sa, sb);
    let card = tm.mk_set_card(u);
    let two = tm.mk_int(2);
    let claim = tm.mk_eq(card, two);
    let negated = tm.mk_not(claim);

    let mut s = Solver::new();
    s.assert(negated, &mut tm);
    assert_eq!(
        s.check(&mut tm),
        SolverResult::Unsat,
        "two distinct string literals are two elements"
    );
}

/// Intersection and difference only shrink their left operand, so cardinality
/// is exact even when the *other* operand is opaque. A coarser "every leaf
/// must be a literal" rule would decline this, and it is the common shape.
#[test]
fn cardinality_is_exact_through_intersection_and_difference() {
    let mut tm = TermManager::new();
    let int = tm.sorts.int_sort;
    let si = tm.sorts.set(int);
    let v = tm.mk_var("v", si);
    let one = tm.mk_int(1);
    let s1 = tm.mk_set_singleton(one);

    // `|{1} \ v| <= 1` however `v` is chosen.
    let d = tm.mk_set_minus(s1, v);
    let card = tm.mk_set_card(d);
    let lit1 = tm.mk_int(1);
    let le = tm.mk_le(card, lit1);
    let not_le = tm.mk_not(le);
    let mut s = Solver::new();
    s.assert(not_le, &mut tm);
    assert_eq!(s.check(&mut tm), SolverResult::Unsat);
}

/// A cardinality whose set has no known support is **declined**, not guessed.
#[test]
fn cardinality_of_an_opaque_set_is_declined() {
    let mut tm = TermManager::new();
    let int = tm.sorts.int_sort;
    let si = tm.sorts.set(int);
    let v = tm.mk_var("v", si);
    let card = tm.mk_set_card(v);
    let huge = tm.mk_int(999);
    let claim = tm.mk_eq(card, huge);

    let mut s = Solver::new();
    s.assert(claim, &mut tm);
    assert_eq!(
        s.check(&mut tm),
        SolverResult::Unknown,
        "an opaque set's cardinality is not determined here"
    );
}
