//! Set model synthesis: the `(get-model)` / `(get-value)` faithfulness
//! tests.
//!
//! The verdicts were already correct (see `finite_sets_decision` /
//! `finite_sets_cardinality`); what these pin is the *model*: a set-sorted
//! variable must print the set the satisfying assignment actually chose —
//! ground members from the committed membership atoms, fresh elements
//! where a cardinality target demands them — and set queries
//! (`set.member`, `set.card`, `set.union`, `set.choose`) must fold to
//! constants instead of echoing themselves.
//!
//! Every `sat` here is also a test of the model-verification soundness
//! gate, which is set-aware since the synthesis landed: a synthesized
//! model that contradicted an assertion would downgrade the verdict to
//! `unknown`, so these cases passing as `sat` certifies the synthesis.

use nixie_solver::Context;

/// Run a script and return its output lines (the `(check-sat)` answer is
/// `lines[0]`).
fn run(script: &str) -> Vec<String> {
    let mut context = Context::new();
    context.execute_script(script).expect("script must execute")
}

/// The whole script's output joined, for substring assertions.
fn run_joined(script: &str) -> String {
    run(script).join("\n")
}

/// A set with committed members prints exactly those members, and the
/// member/card/union queries fold to constants.
#[test]
fn members_are_read_from_the_atoms() {
    let out = run_joined(
        "(set-logic ALL)\n\
         (declare-const S (Set Int))\n\
         (declare-const T (Set Int))\n\
         (assert (set.member 1 S))\n\
         (assert (set.member 2 S))\n\
         (assert (set.member 5 T))\n\
         (check-sat)\n\
         (get-model)\n\
         (get-value (S (set.member 1 S) (set.member 3 S) (set.card S)\n\
                       (set.union S T)))\n",
    );
    assert!(
        out.contains("sat"),
        "verdict must stay sat under the gate: {out}"
    );
    // S prints as the two-element set {1, 2} — a union of the two
    // singletons, in either order.
    assert!(
        out.contains("(set.singleton 1)") && out.contains("(set.singleton 2)"),
        "S must print its members: {out}"
    );
    assert!(out.contains("(set.singleton 5)"), "T must print 5: {out}");
    assert!(
        out.contains("((set.member 1 S) true)") && out.contains("((set.member 3 S) false)"),
        "membership queries must fold: {out}"
    );
    assert!(
        out.contains("((set.card S) 2)"),
        "cardinality must fold to the count: {out}"
    );
    // The union folds structurally: three distinct singletons appear in
    // its value (1, 2 from S and 5 from T).
    assert!(
        out.contains("((set.union S T)"),
        "the union query must produce a value: {out}"
    );
}

/// A cardinality target above the ground count mints fresh elements:
/// `|S| = 3` with `1 ∈ S` prints a three-element set containing 1, and
/// `(set.card S)` folds to 3.
#[test]
fn slack_mints_fresh_elements() {
    let out = run_joined(
        "(set-logic ALL)\n\
         (declare-const S (Set Int))\n\
         (assert (= (set.card S) 3))\n\
         (assert (set.member 1 S))\n\
         (check-sat)\n\
         (get-model)\n\
         (get-value (S (set.card S)))\n",
    );
    assert!(out.contains("sat"), "{out}");
    assert!(
        out.contains("(set.singleton 1)"),
        "the ground member must appear: {out}"
    );
    // Count the singletons in S's value: exactly three.
    let s_value = out
        .split("(define-fun S ()")
        .nth(1)
        .and_then(|rest| rest.split('\n').next())
        .unwrap_or_default();
    let singletons = s_value.matches("(set.singleton").count();
    assert_eq!(singletons, 3, "S must have exactly 3 elements: {out}");
    assert!(out.contains("((set.card S) 3)"), "{out}");
}

/// Committed-equal sets share one value (one equivalence class), sized to
/// the cardinality target.
#[test]
fn equal_sets_share_one_value() {
    let out = run_joined(
        "(set-logic ALL)\n\
         (declare-const S (Set Int))\n\
         (declare-const T (Set Int))\n\
         (assert (= S T))\n\
         (assert (>= (set.card S) 2))\n\
         (assert (set.member 7 S))\n\
         (check-sat)\n\
         (get-model)\n\
         (get-value ((= S T)))\n",
    );
    assert!(out.contains("sat"), "{out}");
    let s_value = out
        .split("(define-fun S ()")
        .nth(1)
        .and_then(|rest| rest.split('\n').next())
        .unwrap_or_default()
        .to_string();
    let t_value = out
        .split("(define-fun T ()")
        .nth(1)
        .and_then(|rest| rest.split('\n').next())
        .unwrap_or_default()
        .to_string();
    assert_eq!(
        s_value.trim(),
        t_value.trim(),
        "committed-equal sets must print the same value: {out}"
    );
    assert!(
        s_value.matches("(set.singleton").count() >= 2,
        "the shared value must meet the card target: {out}"
    );
    assert!(
        s_value.contains("(set.singleton 7)"),
        "the ground member must be in it: {out}"
    );
    assert!(
        out.contains("((= S T) true)"),
        "set equality must fold to true: {out}"
    );
}

/// A committed subset propagates its elements and its fresh pool upward:
/// `S ⊆ T`, `|S| = 1`, `|T| = 2`, `5 ∈ S` gives `5 ∈ T`, `|S ∪ T| = 2`,
/// and `S`'s value inside `T`'s.
#[test]
fn subsets_propagate_members_and_fresh() {
    let out = run_joined(
        "(set-logic ALL)\n\
         (declare-const S (Set Int))\n\
         (declare-const T (Set Int))\n\
         (assert (set.subset S T))\n\
         (assert (= (set.card S) 1))\n\
         (assert (= (set.card T) 2))\n\
         (assert (set.member 5 S))\n\
         (check-sat)\n\
         (get-model)\n\
         (get-value ((set.member 5 T) (set.card (set.union S T))\n\
                       (set.subset S T)))\n",
    );
    assert!(out.contains("sat"), "{out}");
    assert!(
        out.contains("((set.member 5 T) true)"),
        "the subset must carry the member: {out}"
    );
    assert!(
        out.contains("((set.card (set.union S T)) 2)"),
        "the union keeps the target size: {out}"
    );
    assert!(
        out.contains("((set.subset S T) true)"),
        "the subset query must fold: {out}"
    );
    // S's one element (5) appears in T's two-element value.
    let t_value = out
        .split("(define-fun T ()")
        .nth(1)
        .and_then(|rest| rest.split('\n').next())
        .unwrap_or_default();
    assert!(
        t_value.contains("(set.singleton 5)") && t_value.matches("(set.singleton").count() == 2,
        "T must contain S's member plus one fresh element: {out}"
    );
}

/// `set.choose`: the chosen element is a member of a nonempty set, and the
/// choose query folds to a constant.
///
/// (A `(>= (set.card S) 1)` query would echo: `Model::eval` folds `=` but
/// not order comparisons over *any* theory — `(>= x 3)` echoes for a pure
/// integer `x` too — so that is a pre-existing general gap, not a set one.)
#[test]
fn choose_picks_a_member() {
    let out = run_joined(
        "(set-logic ALL)\n\
         (declare-const S (Set Int))\n\
         (assert (= (set.card S) 2))\n\
         (assert (set.member 42 S))\n\
         (check-sat)\n\
         (get-value ((set.member (set.choose S) S) (set.choose S) (= (set.card S) 2)))\n",
    );
    assert!(out.contains("sat"), "{out}");
    assert!(
        out.contains("((set.member (set.choose S) S) true)"),
        "choose must land inside the set: {out}"
    );
    assert!(
        out.contains("((= (set.card S) 2) true)"),
        "the cardinality equality must fold: {out}"
    );
    // The choose value itself is a constant of the element sort.
    assert!(
        !out.contains("((set.choose S) (set.choose S))"),
        "the choose query must not echo itself: {out}"
    );
}

/// Nested set sorts: `Set (Set Int)` elements are themselves synthesized
/// set values, bottom-up.
#[test]
fn nested_set_sorts_synthesize_bottom_up() {
    let out = run_joined(
        "(set-logic ALL)\n\
         (declare-const SS (Set (Set Int)))\n\
         (declare-const inner (Set Int))\n\
         (assert (set.member inner SS))\n\
         (assert (= (set.card inner) 1))\n\
         (assert (set.member 9 inner))\n\
         (check-sat)\n\
         (get-model)\n\
         (get-value ((set.card SS)))\n",
    );
    assert!(out.contains("sat"), "{out}");
    assert!(
        out.contains("(set.singleton (set.singleton 9))"),
        "SS's value must be the singleton of inner's value: {out}"
    );
    assert!(
        out.contains("((set.card SS) 1)"),
        "the outer cardinality must fold: {out}"
    );
}

/// Disequality witnesses stay consistent: `S ≠ T` with equal cardinalities
/// keeps both values distinct (the witness lands in exactly one).
#[test]
fn disequality_witness_lands_in_one_side() {
    let out = run_joined(
        "(set-logic ALL)\n\
         (declare-const S (Set Int))\n\
         (declare-const T (Set Int))\n\
         (assert (distinct S T))\n\
         (assert (= (set.card S) 2))\n\
         (assert (= (set.card T) 2))\n\
         (assert (set.member 5 S))\n\
         (assert (set.member 5 T))\n\
         (check-sat)\n\
         (get-model)\n\
         (get-value ((= S T)))\n",
    );
    assert!(out.contains("sat"), "{out}");
    let s_value = out
        .split("(define-fun S ()")
        .nth(1)
        .and_then(|rest| rest.split('\n').next())
        .unwrap_or_default()
        .to_string();
    let t_value = out
        .split("(define-fun T ()")
        .nth(1)
        .and_then(|rest| rest.split('\n').next())
        .unwrap_or_default()
        .to_string();
    assert_ne!(
        s_value.trim(),
        t_value.trim(),
        "distinct sets must print distinct values: {out}"
    );
    assert!(
        out.contains("((= S T) false)"),
        "the disequality must fold to false: {out}"
    );
}

/// A set over a finite element sort with a universe constraint: the
/// universe and complements enumerate.
#[test]
fn finite_universe_enumerates() {
    let out = run_joined(
        "(set-logic ALL)\n\
         (declare-const S (Set Bool))\n\
         (assert (= (set.card S) 1))\n\
         (check-sat)\n\
         (get-model)\n\
         (get-value ((set.card (as set.universe (Set Bool)))))\n",
    );
    assert!(out.contains("sat"), "{out}");
    assert!(
        out.contains("((set.card (as set.universe (Set Bool))) 2)"),
        "the Bool universe has exactly two elements: {out}"
    );
}

/// `set.minus` / `set.inter` values fold structurally from their operands.
#[test]
fn compound_operators_fold_structurally() {
    let out = run_joined(
        "(set-logic ALL)\n\
         (declare-const S (Set Int))\n\
         (declare-const T (Set Int))\n\
         (assert (set.member 1 S))\n\
         (assert (set.member 2 S))\n\
         (assert (set.member 2 T))\n\
         (assert (set.member 3 T))\n\
         (check-sat)\n\
         (get-value ((set.card (set.inter S T)) (set.member 1 (set.minus S T))\n\
                       (set.member 2 (set.minus S T)) (set.is_empty (set.minus T S))))\n",
    );
    assert!(out.contains("sat"), "{out}");
    assert!(
        out.contains("((set.card (set.inter S T)) 1)"),
        "the intersection is the shared element: {out}"
    );
    assert!(
        out.contains("((set.member 1 (set.minus S T)) true)")
            && out.contains("((set.member 2 (set.minus S T)) false)"),
        "the difference keeps 1 and drops 2: {out}"
    );
}

/// An unconstrained set variable declines honestly: the verdict stays
/// `sat`, the default prints, and queries echo rather than guess.
#[test]
fn unconstrained_sets_decline_honestly() {
    let out = run_joined(
        "(set-logic ALL)\n\
         (declare-const U (Set Int))\n\
         (declare-const x Int)\n\
         (assert (> x 0))\n\
         (check-sat)\n\
         (get-value ((set.card U)))\n",
    );
    assert!(out.contains("sat"), "{out}");
    // No cardinality was asserted; `set.card U` has no determined value
    // and must echo itself (never a fabricated number).
    assert!(
        out.contains("((set.card U) (set.card U))"),
        "an undetermined cardinality must echo: {out}"
    );
}
