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

// ---- conditional sets -------------------------------------------------
//
// `ite` at a set sort is *structured*, and the reduction has to treat it so.
// The generic mux pass (`eliminate_nonbool_ite`) does own this sort, but it
// runs after the reduction, so the conditional equalities it creates are never
// surveyed. Leaving the `ite` opaque made the three cases below answer `Sat`.

/// `(ite c {1} {2})` is never empty, whichever way `c` goes.
#[test]
fn a_conditional_set_is_not_opaque() {
    let got = solve(|tm| {
        let b = tm.sorts.bool_sort;
        let c = tm.mk_var("c", b);
        let one = tm.mk_int(1);
        let two = tm.mk_int(2);
        let s1 = tm.mk_set_singleton(one);
        let s2 = tm.mk_set_singleton(two);
        let ite = tm.mk_ite(c, s1, s2);
        let int = tm.sorts.int_sort;
        let set_int = tm.sorts.set(int);
        let empty = tm.mk_set_empty_at(set_int);
        vec![tm.mk_eq(ite, empty)]
    });
    assert_eq!(got, SolverResult::Unsat);
}

/// The condition decides which branch the membership follows.
#[test]
fn membership_in_a_conditional_set_follows_the_condition() {
    let got = solve(|tm| {
        let b = tm.sorts.bool_sort;
        let c = tm.mk_var("c", b);
        let one = tm.mk_int(1);
        let two = tm.mk_int(2);
        let s1 = tm.mk_set_singleton(one);
        let s2 = tm.mk_set_singleton(two);
        let ite = tm.mk_ite(c, s1, s2);
        // `c /\ 1 \notin (ite c {1} {2})` is unsatisfiable.
        let m = tm.mk_set_member(one, ite);
        let no = tm.mk_not(m);
        vec![c, no]
    });
    assert_eq!(got, SolverResult::Unsat);
}

/// Cardinality is exact through a conditional: both branches are known, so
/// the support is their union and the count de-duplicates as usual.
#[test]
fn cardinality_of_a_conditional_set_is_exact() {
    let got = solve(|tm| {
        let b = tm.sorts.bool_sort;
        let c = tm.mk_var("c", b);
        let one = tm.mk_int(1);
        let two = tm.mk_int(2);
        let s1 = tm.mk_set_singleton(one);
        let s2 = tm.mk_set_singleton(two);
        let ite = tm.mk_ite(c, s1, s2);
        let card = tm.mk_set_card(ite);
        // Either branch is a singleton, so the cardinality is 1 either way.
        let n = tm.mk_int(1);
        let eq = tm.mk_eq(card, n);
        vec![tm.mk_not(eq)]
    });
    assert_eq!(got, SolverResult::Unsat);
}

// ---- set terms under a binder ----------------------------------------
//
// `survey` walks into quantifier bodies, and a bound variable in this AST is
// an ordinary named `Var` — so a set-sorted bound name is indistinguishable
// from a free one, and the axioms land at the top level where that name reads
// free. That is sound, and these pin it: every axiom the reduction emits is a
// *tautology of the theory of finite sets in all its variables*, so reading a
// bound name as a free one just instantiates the tautology at a fresh
// variable. What it is not is complete, which costs `Unknown`, never a wrong
// answer.

/// `1 \in t /\ (\E t : t = {})` is satisfiable — the inner `t` is a different
/// variable, and the extensionality axioms must not force the outer one empty.
#[test]
fn a_shadowed_set_binder_does_not_constrain_the_free_name() {
    let mut tm = TermManager::new();
    let int = tm.sorts.int_sort;
    let set_int = tm.sorts.set(int);
    let t = tm.mk_var("t", set_int);
    let one = tm.mk_int(1);
    let outer = tm.mk_set_member(one, t);
    let empty = tm.mk_set_empty_at(set_int);
    let inner = tm.mk_eq(t, empty);
    let ex = tm.mk_exists([("t", set_int)], inner);
    let mut solver = Solver::new();
    solver.assert(outer, &mut tm);
    solver.assert(ex, &mut tm);
    assert_eq!(solver.check(&mut tm), SolverResult::Sat);
}

/// `(\A x : x \in s) /\ s = {}` has no model, and must not be claimed to.
#[test]
fn a_quantified_membership_is_never_answered_sat() {
    let mut tm = TermManager::new();
    let int = tm.sorts.int_sort;
    let set_int = tm.sorts.set(int);
    let s = tm.mk_var("s", set_int);
    let x = tm.mk_var("x", int);
    let mem = tm.mk_set_member(x, s);
    let all = tm.mk_forall([("x", int)], mem);
    let empty = tm.mk_set_empty_at(set_int);
    let is_empty = tm.mk_eq(s, empty);
    let mut solver = Solver::new();
    solver.assert(all, &mut tm);
    solver.assert(is_empty, &mut tm);
    assert_ne!(solver.check(&mut tm), SolverResult::Sat);
}

// ---- the honesty gate is scoped ----

/// `set.card` of an opaque set is not reduced, so the gate goes up and a `Sat`
/// resting on it degrades to `Unknown`. Retracting that assertion must bring
/// the gate back down: a `push`/`pop` pair that leaves it raised poisons every
/// later answer in the outer scope.
#[test]
fn popping_lowers_the_set_honesty_gate() {
    let mut tm = TermManager::new();
    let int = tm.sorts.int_sort;
    let set_int = tm.sorts.set(int);
    let s = tm.mk_var("s", set_int);
    let mut solver = Solver::new();

    solver.push();
    let card = tm.mk_set_card(s);
    let three = tm.mk_int(3);
    let claim = tm.mk_eq(card, three);
    solver.assert(claim, &mut tm);
    assert_eq!(
        solver.check(&mut tm),
        SolverResult::Unknown,
        "an unreduced cardinality must not be answered"
    );
    solver.pop();

    // Nothing about sets is left asserted, so this is an ordinary `Sat`.
    let x = tm.mk_var("x", int);
    let one = tm.mk_int(1);
    let plain = tm.mk_eq(x, one);
    solver.assert(plain, &mut tm);
    assert_eq!(solver.check(&mut tm), SolverResult::Sat);
}

// ---- membership under a *derived* equality --------------------------------
//
// There is no set theory *solver*: `TermTheory::Set` is classified and nothing
// consumes it, so `set.member` is not a congruence-closed symbol and two
// membership atoms over sets the solver merges at solve time are unrelated SAT
// variables. Every equality the reduction did not *read* was therefore
// invisible, and each of the first three below answered `sat`.
//
// The reduction now relates every pair of same-sorted set terms, which is what
// congruence would have given. The fourth is the case that always worked — the
// equality is written down — and is here so a regression cannot quietly narrow
// the fix back to it.

/// `5 \in (store a 1 {})[1]` — the select reduces to the empty set, so no
/// element is in it.
#[test]
fn membership_in_a_set_read_out_of_an_array() {
    let mut tm = TermManager::new();
    let int = tm.sorts.int_sort;
    let set_int = tm.sorts.set(int);
    let arr = tm.sorts.array(int, set_int);
    let a = tm.mk_var("a", arr);
    let one = tm.mk_int(1);
    let empty = tm.mk_set_empty_at(set_int);
    let b = tm.mk_store(a, one, empty);
    let five = tm.mk_int(5);
    let sel = tm.mk_select(b, one);
    let m = tm.mk_set_member(five, sel);
    let mut s = Solver::new();
    s.assert(m, &mut tm);
    assert_eq!(s.check(&mut tm), SolverResult::Unsat);
}

/// The same through an array *equality*, which is the shape a state variable
/// pinned by `Init` produces.
#[test]
fn membership_through_an_array_equality() {
    let mut tm = TermManager::new();
    let int = tm.sorts.int_sort;
    let set_int = tm.sorts.set(int);
    let arr = tm.sorts.array(int, set_int);
    let a = tm.mk_var("a", arr);
    let base = tm.mk_var("base", arr);
    let one = tm.mk_int(1);
    let empty = tm.mk_set_empty_at(set_int);
    let b = tm.mk_store(base, one, empty);
    let eq = tm.mk_eq(a, b);
    let five = tm.mk_int(5);
    let sel = tm.mk_select(a, one);
    let m = tm.mk_set_member(five, sel);
    let mut s = Solver::new();
    s.assert(eq, &mut tm);
    s.assert(m, &mut tm);
    assert_eq!(s.check(&mut tm), SolverResult::Unsat);
}

/// Two set *variables* the solver derives equal through EUF, with no
/// syntactic `(= a b)` anywhere.
#[test]
fn derived_equality_between_set_variables() {
    let mut tm = TermManager::new();
    let int = tm.sorts.int_sort;
    let set_int = tm.sorts.set(int);
    let x = tm.mk_var("x", int);
    let y = tm.mk_var("y", int);
    let fx = tm.mk_apply("f", [x], set_int);
    let fy = tm.mk_apply("f", [y], set_int);
    let xy = tm.mk_eq(x, y);
    let five = tm.mk_int(5);
    let in_fx = tm.mk_set_member(five, fx);
    let in_fy = tm.mk_set_member(five, fy);
    let not_fy = tm.mk_not(in_fy);
    let mut s = Solver::new();
    s.assert(xy, &mut tm);
    s.assert(in_fx, &mut tm);
    s.assert(not_fy, &mut tm);
    assert_eq!(s.check(&mut tm), SolverResult::Unsat);
}

/// The syntactic case, which the reduction's own axioms cover.
#[test]
fn syntactic_equality_between_set_variables() {
    let mut tm = TermManager::new();
    let int = tm.sorts.int_sort;
    let set_int = tm.sorts.set(int);
    let a = tm.mk_var("a", set_int);
    let b = tm.mk_var("b", set_int);
    let ab = tm.mk_eq(a, b);
    let five = tm.mk_int(5);
    let in_a = tm.mk_set_member(five, a);
    let in_b = tm.mk_set_member(five, b);
    let not_b = tm.mk_not(in_b);
    let mut s = Solver::new();
    s.assert(ab, &mut tm);
    s.assert(in_a, &mut tm);
    s.assert(not_b, &mut tm);
    assert_eq!(s.check(&mut tm), SolverResult::Unsat);
}

/// Two disequalities, each needing a *different* element to witness it.
///
/// `a = {1}`, `b = {}`, `c = {}`, `d = {2}` with `a # b` and `c # d` is
/// satisfiable: 1 witnesses the first, 2 the second. The extensionality
/// witness used to be named from a counter that restarts on every `reduce`
/// call — and `reduce` runs once per `assert`, over the whole stack — so the
/// same name, and therefore the same hash-consed variable, could be handed to
/// a different pair on a later call. One element then had to witness both
/// disequalities, which no theory says, and a satisfiable problem could come
/// back `unsat`. Witnesses are keyed on their pair now.
#[test]
fn two_disequalities_need_two_witnesses() {
    let mut tm = TermManager::new();
    let int = tm.sorts.int_sort;
    let set_int = tm.sorts.set(int);
    let (one, two) = (tm.mk_int(1), tm.mk_int(2));
    let empty = tm.mk_set_empty_at(set_int);
    let s1 = tm.mk_set_singleton(one);
    let s2 = tm.mk_set_singleton(two);
    let mut solver = Solver::new();
    for (x, want) in [("a", s1), ("b", empty), ("c", empty), ("d", s2)] {
        let v = tm.mk_var(x, set_int);
        let eq = tm.mk_eq(v, want);
        solver.assert(eq, &mut tm);
    }
    // Asserted separately, which is what makes the stack re-surveyed.
    for (x, y) in [("a", "b"), ("c", "d")] {
        let (p, q) = (tm.mk_var(x, set_int), tm.mk_var(y, set_int));
        let eq = tm.mk_eq(p, q);
        let ne = tm.mk_not(eq);
        solver.assert(ne, &mut tm);
    }
    assert_eq!(solver.check(&mut tm), SolverResult::Sat);
}

/// Membership is a **function of the element**: two elements the solver makes
/// equal are in exactly the same sets.
///
/// A theory solver gets this from congruence closure and never states it. The
/// ground reduction has to, and it did not: an opaque set's membership atoms
/// were independent Booleans, so
///
/// ```smt
/// (set.member x S)  (= y x)  (not (set.member y S))
/// ```
///
/// were three unrelated variables and this answered `sat`. It is `unsat` —
/// `y` *is* `x`, and `x` is in `S`.
///
/// It was found from the most ordinary specification there is:
/// `Init == x \in Nodes`, `Next == UNCHANGED x`, `Inv == x \in Nodes`, which
/// has no counterexample and was reported as violated at step 1.
#[test]
fn equal_elements_are_in_the_same_sets() {
    let mut tm = TermManager::new();
    let int = tm.sorts.int_sort;
    let set_int = tm.sorts.set(int);
    let s = tm.mk_var("S", set_int);
    let x = tm.mk_var("x", int);
    let y = tm.mk_var("y", int);
    let mx = tm.mk_set_member(x, s);
    let same = tm.mk_eq(y, x);
    let my = tm.mk_set_member(y, s);
    let not_my = tm.mk_not(my);
    let mut solver = Solver::new();
    solver.assert(mx, &mut tm);
    solver.assert(same, &mut tm);
    solver.assert(not_my, &mut tm);
    assert_eq!(solver.check(&mut tm), SolverResult::Unsat);
}

/// And it does not over-constrain: two elements that are *not* asserted equal
/// may still differ in their membership.
#[test]
fn unequal_elements_may_differ_in_membership() {
    let mut tm = TermManager::new();
    let int = tm.sorts.int_sort;
    let set_int = tm.sorts.set(int);
    let s = tm.mk_var("S", set_int);
    let x = tm.mk_var("x", int);
    let y = tm.mk_var("y", int);
    let mx = tm.mk_set_member(x, s);
    let my = tm.mk_set_member(y, s);
    let not_my = tm.mk_not(my);
    let mut solver = Solver::new();
    solver.assert(mx, &mut tm);
    solver.assert(not_my, &mut tm);
    assert_eq!(solver.check(&mut tm), SolverResult::Sat);
}

/// The congruence has to reach through a *structured* set too, since its
/// membership is defined from atoms that bottom out in opaque ones.
#[test]
fn equal_elements_agree_through_a_union() {
    let mut tm = TermManager::new();
    let int = tm.sorts.int_sort;
    let set_int = tm.sorts.set(int);
    let a = tm.mk_var("A", set_int);
    let b = tm.mk_var("B", set_int);
    let u = tm.mk_set_union(a, b);
    let x = tm.mk_var("x", int);
    let y = tm.mk_var("y", int);
    let mx = tm.mk_set_member(x, u);
    let same = tm.mk_eq(y, x);
    let my = tm.mk_set_member(y, u);
    let not_my = tm.mk_not(my);
    let mut solver = Solver::new();
    solver.assert(mx, &mut tm);
    solver.assert(same, &mut tm);
    solver.assert(not_my, &mut tm);
    assert_eq!(solver.check(&mut tm), SolverResult::Unsat);
}
