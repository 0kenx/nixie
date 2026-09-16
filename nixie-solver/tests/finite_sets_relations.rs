//! Relations: the `rel.*` operators over tuple sorts, end to end.
//!
//! Tuples are single-constructor datatypes (`(_ Tuple A B)` — structural,
//! declared once per field-sort list), and the operators reduce through
//! the same eager membership scheme as the rest of the finite-set theory
//! (CVC5's `theory_sets_rels.cpp` is the reference):
//!
//! ```text
//! t ∈ transpose(r)  ⇔  rev(t) ∈ r                (rev = components reversed)
//! (t,u) ∈ a × b     ⇔  t ∈ a ∧ u ∈ b             (projections)
//! (a,b) ∈ iden(s)   ⇔  a ∈ s ∧ a = b             (the diagonal)
//! (a,c) ∈ r ⨝ s     ⇒  ∃x. (a,x) ∈ r ∧ (x,c) ∈ s   (split, skolemized)
//! u ∈ r ∧ v ∈ s ∧ last(u) = first(v) ⇒ glue(u,v) ∈ r ⨝ s  (compose)
//! ```
//!
//! The join keeps CVC5's column arithmetic: `(A,B) ⨝ (B,C) : (A,C)` — the
//! shared middle column is dropped. Cardinality rules: `|transpose r| =
//! |r|`, `|iden s| = |s|`, `|a×b| = |a|·|b|` and `|r⨝s| ≤ |r|·|s|` (the
//! bound is what keeps a join's slack from being unconstrained above — a
//! false-`sat` class caught while landing this).
//!
//! Each case's status was cross-checked against CVC5's semantics while
//! writing.

use nixie_core::{TermId, TermManager};
use nixie_solver::{Solver, SolverResult};

/// Assert `build`'s formulas one by one and report the verdict.
fn solve(build: impl FnOnce(&mut TermManager) -> Vec<TermId>) -> SolverResult {
    let mut tm = TermManager::new();
    let asserts = build(&mut tm);
    let mut solver = Solver::new();
    for a in asserts {
        solver.assert(a, &mut tm);
    }
    solver.check(&mut tm)
}

/// Solve an SMT-LIB snippet through the parser, end to end.
fn solve_smt(script: &str) -> SolverResult {
    let mut context = nixie_solver::Context::new();
    match context.execute_script(script) {
        Ok(lines) => lines
            .first()
            .and_then(|l| match l.as_str() {
                "sat" => Some(SolverResult::Sat),
                "unsat" => Some(SolverResult::Unsat),
                "unknown" => Some(SolverResult::Unknown),
                _ => None,
            })
            .unwrap_or(SolverResult::Unknown),
        Err(_) => SolverResult::Unknown,
    }
}

// ===== the tuple surface =====

/// `(_ tuple.select i)` reads components, `(_ tuple.update i)` writes them,
/// and `tuple.unit` is the empty tuple.
#[test]
fn tuple_select_and_update() {
    let got = solve_smt(
        "(set-logic ALL)\n\
         (declare-const t (Tuple Int Bool))\n\
         (assert (= t (tuple 7 true)))\n\
         (assert (= ((_ tuple.select 0) t) 7))\n\
         (assert (= ((_ tuple.select 1) t) true))\n\
         (check-sat)\n\
         (get-value (((_ tuple.update 0) t 9)))\n",
    );
    assert_eq!(got, SolverResult::Sat);
}

/// A tuple's constructor is injective: equal tuples have equal components
/// and vice versa.
#[test]
fn tuple_equality_is_componentwise() {
    let unsat = solve_smt(
        "(set-logic ALL)\n\
         (declare-const x Int)\n\
         (assert (= (tuple 1 x) (tuple 1 2)))\n\
         (assert (distinct x 2))\n\
         (check-sat)\n",
    );
    assert_eq!(unsat, SolverResult::Unsat);
    let sat = solve_smt(
        "(set-logic ALL)\n\
         (declare-const x Int)\n\
         (declare-const y Int)\n\
         (assert (= x 3))\n\
         (assert (= y 4))\n\
         (assert (= (tuple x y) (tuple 3 4)))\n\
         (check-sat)\n",
    );
    assert_eq!(sat, SolverResult::Sat);
}

// ===== transpose =====

/// `(1,2) ∈ transpose(r)` forces `(2,1) ∈ r`.
#[test]
fn transpose_swaps_components() {
    let got = solve(|tm| {
        let tuple = tm.tuple_sort(&[tm.sorts.int_sort, tm.sorts.int_sort]);
        let rel = tm.sorts.set(tuple);
        let r = tm.mk_var("r", rel);
        let one = tm.mk_int(1);
        let two = tm.mk_int(2);
        let t12 = tm.mk_tuple(&[one, two]);
        let t21 = tm.mk_tuple(&[two, one]);
        let tr = tm.mk_rel_transpose(r);
        let in_tr = tm.mk_set_member(t12, tr);
        let in_r = tm.mk_set_member(t21, r);
        vec![in_tr, tm.mk_not(in_r)]
    });
    assert_eq!(got, SolverResult::Unsat);
}

/// Double transpose is the identity on members.
#[test]
fn double_transpose_round_trips() {
    let got = solve_smt(
        "(set-logic ALL)\n\
         (declare-const r (Relation Int Int))\n\
         (assert (set.member (tuple 1 2) r))\n\
         (assert (set.member (tuple 2 1) (rel.transpose (rel.transpose r))))\n\
         (assert (not (set.member (tuple 1 2) r)))\n\
         (check-sat)\n",
    );
    assert_eq!(got, SolverResult::Unsat);
}

// ===== product =====

/// `t ∈ a ∧ u ∈ b` puts `(t, u)` in the product; denying it is unsat.
#[test]
fn product_pairs_members() {
    let got = solve_smt(
        "(set-logic ALL)\n\
         (declare-const a (Set Int))\n\
         (declare-const b (Set Int))\n\
         (assert (set.member 1 a))\n\
         (assert (set.member 2 b))\n\
         (assert (not (set.member (tuple 1 2) (rel.product a b))))\n\
         (check-sat)\n",
    );
    assert_eq!(got, SolverResult::Unsat);
}

/// `|a×b| = |a|·|b|` with exact ground counts: `5` is unsat, and the
/// model-side count over the six pairs refutes it.
#[test]
fn product_cardinality_is_the_product() {
    let unsat = solve_smt(
        "(set-logic ALL)\n\
         (declare-const a (Set Int))\n\
         (declare-const b (Set Int))\n\
         (assert (set.member 1 a))\n\
         (assert (set.member 2 a))\n\
         (assert (= (set.card a) 2))\n\
         (assert (set.member 5 b))\n\
         (assert (set.member 6 b))\n\
         (assert (set.member 7 b))\n\
         (assert (= (set.card b) 3))\n\
         (assert (= (set.card (rel.product a b)) 5))\n\
         (check-sat)\n",
    );
    assert_eq!(unsat, SolverResult::Unsat);
}

/// Pure product cardinality over unconfined operands routes through the
/// nonlinear rule and answers honestly `unknown` (never a guess).
#[test]
fn unconfined_product_cardinality_declines_honestly() {
    let got = solve_smt(
        "(set-logic ALL)\n\
         (declare-const a (Set Int))\n\
         (declare-const b (Set Int))\n\
         (assert (= (set.card a) 2))\n\
         (assert (= (set.card b) 3))\n\
         (assert (= (set.card (rel.product a b)) 6))\n\
         (check-sat)\n",
    );
    assert_eq!(got, SolverResult::Unknown);
}

// ===== iden =====

/// The diagonal is over equal components: `(3,4) ∈ iden(a)` is unsat.
#[test]
fn iden_requires_equal_components() {
    let got = solve_smt(
        "(set-logic ALL)\n\
         (declare-const a (Set Int))\n\
         (assert (set.member (tuple 3 4) (rel.iden a)))\n\
         (check-sat)\n",
    );
    assert_eq!(got, SolverResult::Unsat);
}

/// `x ∈ a` puts `(x,x)` on the diagonal; denying it is unsat.
#[test]
fn iden_carries_membership() {
    let got = solve_smt(
        "(set-logic ALL)\n\
         (declare-const a (Set Int))\n\
         (assert (set.member 3 a))\n\
         (assert (not (set.member (tuple 3 3) (rel.iden a))))\n\
         (check-sat)\n",
    );
    assert_eq!(got, SolverResult::Unsat);
}

/// `|iden a| = |a|`: three is unsat when `|a| = 2`.
#[test]
fn iden_cardinality_is_the_operands() {
    let got = solve_smt(
        "(set-logic ALL)\n\
         (declare-const a (Set Int))\n\
         (assert (= (set.card a) 2))\n\
         (assert (= (set.card (rel.iden a)) 3))\n\
         (check-sat)\n",
    );
    assert_eq!(got, SolverResult::Unsat);
}

// ===== join =====

/// The compose rule: connecting members force the joined member.
/// `(1,2) ∈ r ∧ (2,3) ∈ s` puts `(1,3)` in `r ⨝ s` (the middle column is
/// dropped).
#[test]
fn join_composes_members() {
    let got = solve_smt(
        "(set-logic ALL)\n\
         (declare-const r (Relation Int Int))\n\
         (declare-const s (Relation Int Int))\n\
         (assert (set.member (tuple 1 2) r))\n\
         (assert (set.member (tuple 2 3) s))\n\
         (assert (not (set.member (tuple 1 3) (rel.join r s))))\n\
         (check-sat)\n",
    );
    assert_eq!(got, SolverResult::Unsat);
}

/// The split rule: a joined member needs a witness in both operands, so
/// an empty left operand refutes it.
#[test]
fn join_splits_through_a_witness() {
    let got = solve_smt(
        "(set-logic ALL)\n\
         (declare-const r (Relation Int Int))\n\
         (declare-const s (Relation Int Int))\n\
         (assert (set.member (tuple 1 3) (rel.join r s)))\n\
         (assert (= (set.card r) 0))\n\
         (check-sat)\n",
    );
    assert_eq!(got, SolverResult::Unsat);
}

/// `|r ⨝ s| ≤ |r|·|s|`: a join of two singletons cannot have two members.
/// (The bound is what keeps the join's slack from being unconstrained
/// above — without it this answered `sat`.)
#[test]
fn join_cardinality_is_bounded() {
    let got = solve_smt(
        "(set-logic ALL)\n\
         (declare-const r (Relation Int Int))\n\
         (declare-const s (Relation Int Int))\n\
         (assert (set.member (tuple 1 2) r))\n\
         (assert (set.member (tuple 2 3) s))\n\
         (assert (= (set.card r) 1))\n\
         (assert (= (set.card s) 1))\n\
         (assert (= (set.card (rel.join r s)) 2))\n\
         (check-sat)\n",
    );
    assert_eq!(got, SolverResult::Unsat);
}

/// The satisfiable side: connecting members witness the join, and a free
/// left relation can always supply the split's front.
#[test]
fn join_witnesses_freely() {
    let sat = solve_smt(
        "(set-logic ALL)\n\
         (declare-const r (Relation Int Int))\n\
         (declare-const s (Relation Int Int))\n\
         (assert (set.member (tuple 1 2) r))\n\
         (assert (set.member (tuple 2 3) s))\n\
         (assert (set.member (tuple 1 3) (rel.join r s)))\n\
         (check-sat)\n",
    );
    assert_eq!(sat, SolverResult::Sat);
    // s pinned to its one non-connecting member: the join needs (1,x) ∈ r
    // with (x,3) ∈ s — only (5,3) ∈ s, so r must hold (1,5), which a free
    // r can.
    let sat2 = solve_smt(
        "(set-logic ALL)\n\
         (declare-const r (Relation Int Int))\n\
         (declare-const s (Relation Int Int))\n\
         (assert (set.member (tuple 1 2) r))\n\
         (assert (set.member (tuple 5 3) s))\n\
         (assert (= (set.card s) 1))\n\
         (assert (set.member (tuple 1 3) (rel.join r s)))\n\
         (check-sat)\n",
    );
    assert_eq!(sat2, SolverResult::Sat);
}

// ===== the model side =====

/// A relation variable's members print as tuples, and the queries fold.
#[test]
fn relation_models_print_tuples() {
    let mut context = nixie_solver::Context::new();
    let out = context
        .execute_script(
            "(set-logic ALL)\n\
             (declare-const r (Relation Int Int))\n\
             (assert (set.member (tuple 1 2) r))\n\
             (assert (set.member (tuple 3 4) r))\n\
             (check-sat)\n\
             (get-model)\n\
             (get-value ((set.member (tuple 1 2) r) (set.member (tuple 9 9) r)\n\
                           (set.card r)))\n",
        )
        .expect("script executes");
    let joined = out.join("\n");
    assert!(joined.contains("sat"), "{joined}");
    assert!(
        joined.contains("(set.singleton (tuple 1 2))")
            && joined.contains("(set.singleton (tuple 3 4))"),
        "the members must print as tuples: {joined}"
    );
    assert!(
        joined.contains("((set.member (tuple 1 2) r) true)")
            && joined.contains("((set.member (tuple 9 9) r) false)")
            && joined.contains("((set.card r) 2)"),
        "the queries must fold: {joined}"
    );
}

// ===== the surface's error side =====

/// Non-joinable relations are a parse error, as in CVC5.
#[test]
fn non_joinable_relations_are_rejected() {
    let mut context = nixie_solver::Context::new();
    let out = context.execute_script(
        "(set-logic ALL)\n\
         (declare-const r (Relation Int Int))\n\
         (declare-const s (Relation Bool Int))\n\
         (assert (= (set.card (rel.join r s)) 0))\n\
         (check-sat)\n",
    );
    assert!(out.is_err(), "boundary mismatch must be rejected");
}

// ===== rel compounds in the model =====

/// A transpose's value prints (reversed tuples) and its queries fold.
#[test]
fn transpose_value_prints_reversed() {
    let mut context = nixie_solver::Context::new();
    let out = context
        .execute_script(
            "(set-logic ALL)\n\
             (declare-const r (Relation Int Int))\n\
             (assert (set.member (tuple 1 2) r))\n\
             (assert (set.member (tuple 3 4) r))\n\
             (assert (set.member (tuple 2 1) (rel.transpose r)))\n\
             (check-sat)\n\
             (get-value ((rel.transpose r) (set.card (rel.transpose r))\n\
                           (set.member (tuple 4 3) (rel.transpose r))))\n",
        )
        .expect("script executes");
    let joined = out.join("\n");
    assert!(joined.contains("sat"), "{joined}");
    assert!(
        joined.contains("((rel.transpose r) (set.union")
            && joined.contains("(set.singleton (tuple 4 3))"),
        "the converse must print the reversed members: {joined}"
    );
    assert!(
        joined.contains("((set.card (rel.transpose r)) 3)"),
        "the converse's cardinality must fold to |r|: {joined}"
    );
    assert!(
        joined.contains("((set.member (tuple 4 3) (rel.transpose r)) true)"),
        "membership over the converse must fold: {joined}"
    );
}

/// A product's value prints the pairs and its cardinality folds to the
/// product of the operand sizes.
#[test]
fn product_value_prints_pairs() {
    let mut context = nixie_solver::Context::new();
    let out = context
        .execute_script(
            "(set-logic ALL)\n\
             (declare-const a (Set Int))\n\
             (declare-const b (Set Int))\n\
             (assert (set.member 1 a))\n\
             (assert (set.member 2 b))\n\
             (assert (set.member (tuple 1 2) (rel.product a b)))\n\
             (check-sat)\n\
             (get-value ((rel.product a b) (set.card (rel.product a b))))\n",
        )
        .expect("script executes");
    let joined = out.join("\n");
    assert!(joined.contains("sat"), "{joined}");
    assert!(
        joined.contains("((rel.product a b) (set.union")
            && joined.contains("(set.singleton (tuple 1 2))"),
        "the product must print its pairs: {joined}"
    );
    assert!(
        joined.contains("((set.card (rel.product a b)) "),
        "the product's cardinality must fold: {joined}"
    );
}

/// An iden's value prints the diagonal.
#[test]
fn iden_value_prints_the_diagonal() {
    let mut context = nixie_solver::Context::new();
    let out = context
        .execute_script(
            "(set-logic ALL)\n\
             (declare-const a (Set Int))\n\
             (assert (set.member 3 a))\n\
             (assert (set.member (tuple 3 3) (rel.iden a)))\n\
             (check-sat)\n\
             (get-value ((rel.iden a) (set.member (tuple 3 3) (rel.iden a))))\n",
        )
        .expect("script executes");
    let joined = out.join("\n");
    assert!(joined.contains("sat"), "{joined}");
    assert!(
        joined.contains("((rel.iden a) (set.singleton (tuple 3 3)))"),
        "the diagonal must print: {joined}"
    );
}

/// A cardinality target on a rel compound no longer rolls the operand's
/// model back: `|transpose r| = 1` with `(1,2) ∈ r` keeps `r` printed.
#[test]
fn rel_card_target_keeps_the_operand_model() {
    let mut context = nixie_solver::Context::new();
    let out = context
        .execute_script(
            "(set-logic ALL)\n\
             (declare-const r (Relation Int Int))\n\
             (assert (set.member (tuple 1 2) r))\n\
             (assert (= (set.card (rel.transpose r)) 1))\n\
             (check-sat)\n\
             (get-model)\n",
        )
        .expect("script executes");
    let joined = out.join("\n");
    assert!(joined.contains("sat"), "{joined}");
    assert!(
        joined.contains("(define-fun r ()") && joined.contains("(set.singleton (tuple 1 2))"),
        "the operand's model must survive the rel card target: {joined}"
    );
}

/// A join's value prints (it used to echo honestly): the split-collision
/// repair's witness minting is pre-empted by pre-minting every unpinned
/// join skolem against a component-level used set, so no fresh witness
/// collides with a genuine constant, the collision repair no longer
/// declines the sort, and the rel synthesis folds the join from its
/// operands' values.
#[test]
fn join_value_prints() {
    let mut context = nixie_solver::Context::new();
    let out = context
        .execute_script(
            "(set-logic ALL)\n\
             (declare-const r (Relation Int Int))\n\
             (declare-const s (Relation Int Int))\n\
             (assert (set.member (tuple 1 2) r))\n\
             (assert (set.member (tuple 2 3) s))\n\
             (assert (set.member (tuple 1 3) (rel.join r s)))\n\
             (check-sat)\n\
             (get-value ((rel.join r s)))\n",
        )
        .expect("script executes");
    let joined = out.join("\n");
    assert!(
        joined.contains("sat"),
        "the verdict must stay sat: {joined}"
    );
    assert!(
        joined.contains("((rel.join r s) (set.union")
            && joined.contains("(set.singleton (tuple 1 3))"),
        "the join value must fold to its composed members: {joined}"
    );
    // The composed value is verified before it is published: the
    // asserted member (1,3) is present (the connectable pair), and the
    // echo must be gone.
    assert!(
        !joined.contains("((rel.join r s) (rel.join r s))"),
        "the echo decline must be gone: {joined}"
    );
}

// ===== the join split's counting (a closed false-`sat` class) =====

/// `(a,c) ∈ r ⨝ s` with both operands pinned exactly to a non-connecting
/// pair is unsatisfiable: the split's witness `(a,k) ∈ r` forces a second
/// member past `r`'s exact size. This was a **false `sat`** — the split
/// terms were pushed into the element lists under a key read as a *set's*
/// element sort (`None` for a tuple), so the push silently never happened
/// and the counting equations never saw them.
#[test]
fn join_split_is_counted() {
    let got = solve_smt(
        "(set-logic ALL)\n\
         (declare-const r (Relation Int Int))\n\
         (declare-const s (Relation Int Int))\n\
         (assert (set.member (tuple 5 9) r))\n\
         (assert (= (set.card r) 1))\n\
         (assert (set.member (tuple 9 3) s))\n\
         (assert (= (set.card s) 1))\n\
         (assert (set.member (tuple 1 3) (rel.join r s)))\n\
         (check-sat)\n",
    );
    assert_eq!(got, SolverResult::Unsat);
}

/// The mirror: the one connectable pair makes the joined member hold, and
/// a non-connecting exact left operand does not.
#[test]
fn join_split_counting_is_not_overconstrained() {
    let sat = solve_smt(
        "(set-logic ALL)\n\
         (declare-const r (Relation Int Int))\n\
         (declare-const s (Relation Int Int))\n\
         (assert (set.member (tuple 1 2) r))\n\
         (assert (set.member (tuple 2 3) s))\n\
         (assert (set.member (tuple 1 3) (rel.join r s)))\n\
         (check-sat)\n",
    );
    assert_eq!(sat, SolverResult::Sat);
    // The bound side: an exact one-member left operand with an exact
    // one-member right bounds the join by one member. (The *slack* of a
    // join is only bounded by |r|·|s|, so richer shapes answer honestly
    // `unknown` rather than guess; this shape stays inside the bound.)
    let unsat = solve_smt(
        "(set-logic ALL)\n\
         (declare-const r (Relation Int Int))\n\
         (declare-const s (Relation Int Int))\n\
         (assert (set.member (tuple 1 2) r))\n\
         (assert (= (set.card r) 1))\n\
         (assert (set.member (tuple 2 3) s))\n\
         (assert (= (set.card s) 1))\n\
         (assert (= (set.card (rel.join r s)) 2))\n\
         (check-sat)\n",
    );
    assert_eq!(unsat, SolverResult::Unsat);
}

/// Tuple constructor equality unfolds componentwise (the datatype
/// injectivity axiom, as a builder rewrite): distinct components refute
/// the equality, and the reduction's counting guards see it.
#[test]
fn tuple_constructor_equality_unfolds() {
    // Distinct tuples are distinct (and the disequality holds trivially).
    let sat = solve_smt(
        "(set-logic ALL)\n\
         (assert (not (= (tuple 1 2) (tuple 5 2))))\n\
         (check-sat)\n",
    );
    assert_eq!(sat, SolverResult::Sat);
    // Two distinct-constant tuples in a one-member relation: the count
    // cannot be one.
    let unsat = solve_smt(
        "(set-logic ALL)\n\
         (declare-const r (Relation Int Int))\n\
         (assert (set.member (tuple 1 2) r))\n\
         (assert (set.member (tuple 5 2) r))\n\
         (assert (= (set.card r) 1))\n\
         (check-sat)\n",
    );
    assert_eq!(unsat, SolverResult::Unsat);
    // Equal components make equal tuples.
    let sat2 = solve_smt(
        "(set-logic ALL)\n\
         (declare-const x Int)\n\
         (assert (= x 5))\n\
         (assert (= (tuple x 2) (tuple 5 2)))\n\
         (check-sat)\n",
    );
    assert_eq!(sat2, SolverResult::Sat);
}

/// A join of relations joined with *unary* operands is a parse error, as
/// in CVC5; unary with wider is fine.
#[test]
fn unary_join_typing_follows_cvc5() {
    let mut context = nixie_solver::Context::new();
    let out = context.execute_script(
        "(set-logic ALL)\n\
         (declare-const a (Relation Int))\n\
         (declare-const b (Relation Int))\n\
         (assert (= (set.card (rel.join a b)) 0))\n\
         (check-sat)\n",
    );
    assert!(out.is_err(), "two unary operands must be rejected");
    // Unary with a wider relation is fine (the front contributes no
    // columns): a unary joined with a binary is binary.
    let mut context = nixie_solver::Context::new();
    let out = context.execute_script(
        "(set-logic ALL)\n\
         (declare-const a (Relation Int))\n\
         (declare-const b (Relation Int Int))\n\
         (assert (set.member (tuple 7) a))\n\
         (assert (set.member (tuple 7 9) b))\n\
         (assert (set.member (tuple 9) (rel.join a b)))\n\
         (check-sat)\n",
    );
    assert!(out.is_ok(), "unary with wider must parse: {out:?}");
    assert_eq!(
        out.unwrap().first().map(String::as_str),
        Some("sat"),
        "the connectable pair witnesses the joined member"
    );
}

// ===== membership congruence under element equality (a closed false-`sat`
// class, four doors) =====
//
// `mk_eq` unfolds a tuple-constructor equality componentwise (datatype
// injectivity as a builder rewrite), so two ctor-spelled tuple elements
// never carry a syntactic `Eq` between them: their equality is decided at
// the *component* level. Before the congruence pass stated the dual —
// `C(xs) = C(ys) → (C(xs) ∈ S ↔ C(ys) ∈ S)`, with the component
// conjunction as antecedent — SAT could commit the component equalities
// beside disagreeing membership atoms, an arrangement no set family
// realizes, and each of the four shapes below answered `sat` (CVC5
// 1.3.4: `unsat` on every one).

/// Door 1 — the join's own skolem middle: `r = {(1,2)}` exactly, so
/// `(1,3) ∈ r ⨝ s` forces the witness `k = 2` through the extensional
/// singleton, and `(k,3) ∈ s` is then `(2,3) ∈ s` — contradicting the
/// asserted non-membership.
#[test]
fn join_split_skolem_pinned_by_singleton_is_congruent() {
    let got = solve_smt(
        "(set-logic ALL)\n\
         (declare-const r (Relation Int Int))\n\
         (declare-const s (Relation Int Int))\n\
         (assert (= r (set.singleton (tuple 1 2))))\n\
         (assert (not (set.member (tuple 2 3) s)))\n\
         (assert (set.member (tuple 1 3) (rel.join r s)))\n\
         (check-sat)\n",
    );
    assert_eq!(got, SolverResult::Unsat);
}

/// Door 2 — a user's component equality: `x = 3` makes `(1,x)` and the
/// compose-derived `(1,3)` the same element, so their memberships in the
/// join must agree; the compose rule forces `(1,3) ∈ J`, the assertion
/// negates `(1,x) ∈ J`.
#[test]
fn join_component_equality_is_congruent() {
    let got = solve_smt(
        "(set-logic ALL)\n\
         (declare-const x Int)\n\
         (declare-const r (Relation Int Int))\n\
         (declare-const s (Relation Int Int))\n\
         (assert (= r (set.singleton (tuple 1 2))))\n\
         (assert (= s (set.singleton (tuple 2 3))))\n\
         (assert (= x 3))\n\
         (assert (not (set.member (tuple 1 x) (rel.join r s))))\n\
         (check-sat)\n",
    );
    assert_eq!(got, SolverResult::Unsat);
}

/// Door 3 — a syntactic tuple-level equality (`t = (1,x)`) at the join:
// congruence used to be stated at opaque sets only, and a join is the one
// shape whose membership is not per-element defined from its bases.
#[test]
fn join_syntactic_tuple_equality_is_congruent() {
    let got = solve_smt(
        "(set-logic ALL)\n\
         (declare-const x Int)\n\
         (declare-const t (Tuple Int Int))\n\
         (declare-const r (Relation Int Int))\n\
         (declare-const s (Relation Int Int))\n\
         (assert (= r (set.singleton (tuple 1 2))))\n\
         (assert (= s (set.singleton (tuple 2 3))))\n\
         (assert (= x 3))\n\
         (assert (= t (tuple 1 x)))\n\
         (assert (not (set.member t (rel.join r s))))\n\
         (check-sat)\n",
    );
    assert_eq!(got, SolverResult::Unsat);
}

/// Door 4 — no opaque set at all: the join of two literal singletons
/// still needs congruence, and the `any_opaque` gate used to skip the
/// whole pass for formulas whose sets are all literal leaves.
#[test]
fn join_of_literals_needs_congruence_too() {
    let got = solve_smt(
        "(set-logic ALL)\n\
         (declare-const x Int)\n\
         (assert (= x 3))\n\
         (assert (not (set.member (tuple 1 x)\n\
                       (rel.join (set.singleton (tuple 1 2))\n\
                                 (set.singleton (tuple 2 3))))))\n\
         (check-sat)\n",
    );
    assert_eq!(got, SolverResult::Unsat);
}

/// The compose rule keeps its backward half for the syntactic glued
/// spelling: pinning both operands and negating the join's own member
/// (no congruence needed) was `unsat` before this arc and must stay so.
#[test]
fn join_compose_syntactic_glue_still_refutes() {
    let got = solve_smt(
        "(set-logic ALL)\n\
         (declare-const x Int)\n\
         (declare-const r (Relation Int Int))\n\
         (declare-const s (Relation Int Int))\n\
         (assert (= r (set.singleton (tuple 1 2))))\n\
         (assert (= s (set.singleton (tuple 2 3))))\n\
         (assert (= x 3))\n\
         (assert (not (set.member (tuple 1 3) (rel.join r s))))\n\
         (check-sat)\n",
    );
    assert_eq!(got, SolverResult::Unsat);
}

/// The mirror of door 2: without the negation the join is satisfiable —
/// congruence must not overconstrain the ordinary connectable shape.
/// The shape crosses the congruence pair budget (the compose feedback
/// fills the element lists), so the honest verdict may degrade to
/// `Unknown`; the one forbidden answer is `Unsat` — that would mean the
/// congruence axioms overconstrained a satisfiable formula.
#[test]
fn join_component_equality_congruence_is_not_overconstrained() {
    let got = solve_smt(
        "(set-logic ALL)\n\
         (declare-const x Int)\n\
         (declare-const r (Relation Int Int))\n\
         (declare-const s (Relation Int Int))\n\
         (assert (= r (set.singleton (tuple 1 2))))\n\
         (assert (= s (set.singleton (tuple 2 3))))\n\
         (assert (= x 3))\n\
         (assert (set.member (tuple 1 x) (rel.join r s)))\n\
         (check-sat)\n",
    );
    assert_ne!(got, SolverResult::Unsat);
}

/// The operand models print after the congruence fix: the skolem
/// witnesses are pre-minted against a component-level used set, so no
/// fresh value collides with a genuine constant and the collision repair
/// no longer declines the whole sort (the join's own value may still
/// echo honestly — see `join_value_declines_honestly_today`).
#[test]
fn join_operand_models_print_after_congruence() {
    let mut context = nixie_solver::Context::new();
    let out = context
        .execute_script(
            "(set-logic ALL)\n\
             (declare-const r (Relation Int Int))\n\
             (declare-const s (Relation Int Int))\n\
             (assert (set.member (tuple 1 2) r))\n\
             (assert (set.member (tuple 2 3) s))\n\
             (assert (set.member (tuple 1 3) (rel.join r s)))\n\
             (check-sat)\n\
             (get-model)\n",
        )
        .expect("script executes");
    let joined = out.join("\n");
    assert!(joined.contains("sat"), "{joined}");
    assert!(
        joined.contains("(define-fun r ()")
            && joined.contains("(set.singleton (tuple 1 2))")
            && joined.contains("(set.singleton (tuple 2 3))"),
        "the operands' committed members must print: {joined}"
    );
}
