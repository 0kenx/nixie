//! Evaluating lowered terms.
//!
//! These pin the semantics unit by unit; `bench/tla_eval` checks the same
//! evaluator against TLC over the corpora.

use nixie_tla::{EvalErrorKind, Evaluator, Lowerer, Value};
use nixie_tla_syntax::parse_file;
use std::collections::HashMap;

fn eval(body: &str) -> String {
    let src = format!("---- MODULE M ----\nEXTENDS Integers\n{body}\n====\n");
    let parsed = match parse_file(&src) {
        Ok(p) => p,
        Err(e) => panic!("parse failed: {e}"),
    };
    let m = parsed.module;
    let mut low = Lowerer::new();
    low.add_module(&m);
    let k = match low.lower_named(&m, "A") {
        Ok(k) => k,
        Err(e) => panic!("lowering failed: {e}"),
    };
    match Evaluator::new().eval(&k) {
        Ok(v) => v.to_string(),
        Err(e) => panic!("evaluation failed: {e}"),
    }
}

/// Lower `A` in a module that declares `x` and `y`, for the action tests.
fn lower_action(body: &str) -> nixie_tla::KeraRef {
    let src = format!("---- MODULE M ----\nEXTENDS Integers\nVARIABLES x, y\n{body}\n====\n");
    let parsed = parse_file(&src).expect("parses");
    let m = parsed.module;
    let mut low = Lowerer::new();
    low.add_module(&m);
    low.lower_named(&m, "A").expect("lowers")
}

fn state(pairs: &[(&str, Value)]) -> HashMap<String, Value> {
    pairs
        .iter()
        .map(|(k, v)| ((*k).to_string(), v.clone()))
        .collect()
}

/// Evaluate `A` as an action between two states.
fn act(body: &str, now: &[(&str, Value)], then: &[(&str, Value)]) -> String {
    let k = lower_action(body);
    match Evaluator::new().eval_action(&k, &state(now), &state(then)) {
        Ok(v) => v.to_string(),
        Err(e) => panic!("evaluation failed: {e}"),
    }
}

fn act_err(body: &str, now: &[(&str, Value)], then: &[(&str, Value)]) -> EvalErrorKind {
    let k = lower_action(body);
    match Evaluator::new().eval_action(&k, &state(now), &state(then)) {
        Ok(v) => panic!("expected an error, got {v}"),
        Err(e) => e,
    }
}

fn eval_err(body: &str) -> EvalErrorKind {
    let src = format!("---- MODULE M ----\nEXTENDS Integers\n{body}\n====\n");
    let parsed = parse_file(&src).expect("parses");
    let m = parsed.module;
    let mut low = Lowerer::new();
    low.add_module(&m);
    let k = low.lower_named(&m, "A").expect("lowers");
    match Evaluator::new().eval(&k) {
        Ok(v) => panic!("expected an error, got {v}"),
        Err(e) => e,
    }
}

#[test]
fn arithmetic_and_comparison() {
    assert_eq!(eval("A == 2 + 3 * 4"), "14");
    assert_eq!(eval("A == 7 < 8"), "TRUE");
    assert_eq!(eval("A == -(3) + 1"), "-2");
}

#[test]
fn division_and_modulus_follow_tla_not_rust() {
    // TLA+ requires `a % b \in 0..b-1`, so `\div` rounds towards minus
    // infinity. Rust's `/` and `%` truncate towards zero and would give
    // `-3` and `-1` here — quietly wrong.
    assert_eq!(eval("A == (-7) \\div 2"), "-4");
    assert_eq!(eval("A == (-7) % 2"), "1");
    // The defining identity, which is what makes those the right answers.
    assert_eq!(eval("A == 2 * ((-7) \\div 2) + ((-7) % 2)"), "-7");

    // TLA+ says nothing about a non-positive divisor, so neither do we.
    let e = eval_err("A == 7 \\div (-2)");
    assert!(matches!(e, EvalErrorKind::Unsupported(_)), "got {e:?}");
}

#[test]
fn overflow_is_an_error_not_a_wrap() {
    // Wrapping here is the silent truncation this codebase has shipped
    // soundness bugs from.
    let e = eval_err("A == 170141183460469231731687303715884105727 + 1");
    assert!(matches!(e, EvalErrorKind::Overflow(_)), "got {e:?}");
}

#[test]
fn sets_and_their_operations() {
    assert_eq!(eval("A == {3, 1, 2, 1}"), "{1, 2, 3}");
    assert_eq!(eval("A == {1, 2} \\cup {2, 3}"), "{1, 2, 3}");
    assert_eq!(eval("A == {1, 2, 3} \\cap {2, 3, 4}"), "{2, 3}");
    assert_eq!(eval("A == {1, 2, 3} \\ {2}"), "{1, 3}");
    assert_eq!(eval("A == 1..4"), "{1, 2, 3, 4}");
    assert_eq!(eval("A == SUBSET {1, 2}"), "{{}, {1}, {1, 2}, {2}}");
    assert_eq!(eval("A == UNION {{1}, {2, 3}}"), "{1, 2, 3}");
    assert_eq!(eval("A == {x \\in 1..5 : x % 2 = 0}"), "{2, 4}");
    assert_eq!(eval("A == {x * x : x \\in 1..3}"), "{1, 4, 9}");
}

#[test]
fn quantifiers() {
    assert_eq!(eval("A == \\A x \\in 1..3 : x > 0"), "TRUE");
    assert_eq!(eval("A == \\A x \\in 1..3 : x > 1"), "FALSE");
    assert_eq!(eval("A == \\E x \\in 1..3 : x = 2"), "TRUE");
    assert_eq!(eval("A == \\A x, y \\in 1..2 : x + y <= 4"), "TRUE");
}

#[test]
fn functions_records_and_tuples() {
    assert_eq!(eval("A == [i \\in 1..3 |-> i * 2][2]"), "4");
    assert_eq!(eval("A == DOMAIN [i \\in 1..2 |-> 0]"), "{1, 2}");
    // A function on `{1}` *is* the 1-tuple: TLA+ has no separate sequence
    // type, so this prints as a tuple. It used to print `(1 :> 0)`, which is
    // the same value spelled as a function and a spelling TLC does not use.
    assert_eq!(eval("A == [f \\in {1} |-> 0] "), "<<0>>");
    assert_eq!(eval("A == [a |-> 1, b |-> 2].b"), "2");
    assert_eq!(eval("A == <<10, 20, 30>>[2]"), "20");
    assert_eq!(eval("A == [[i \\in 1..2 |-> 0] EXCEPT ![1] = 9][1]"), "9");
    // `@` is the old value.
    assert_eq!(
        eval("A == [[i \\in 1..2 |-> 5] EXCEPT ![1] = @ + 1][1]"),
        "6"
    );
}

#[test]
fn cartesian_product_and_function_sets() {
    assert_eq!(eval("A == {1, 2} \\X {3}"), "{<<1, 3>>, <<2, 3>>}");
    // `[S -> T]` enumerates the function space.
    assert_eq!(eval("A == [{1} -> {7, 8}]"), "{(1 :> 7), (1 :> 8)}");
}

#[test]
fn definitions_are_inlined_before_evaluation() {
    assert_eq!(eval("N == 3\nA == N * N"), "9");
    assert_eq!(eval("Sq(x) == x * x\nA == Sq(4)"), "16");
    assert_eq!(eval("A == LET y == 5 IN y + 1"), "6");
}

#[test]
fn choose_is_deliberately_not_evaluated() {
    // TLA+ says only that `CHOOSE` picks *some* satisfying element. Any answer
    // here could differ from TLC's without either being wrong, so evaluating
    // it would turn a differential into noise.
    let e = eval_err("A == CHOOSE x \\in 1..3 : x > 1");
    assert!(matches!(e, EvalErrorKind::Unsupported(_)), "got {e:?}");
}

#[test]
fn a_non_ground_term_is_an_error_not_a_guess() {
    let src = "---- MODULE M ----\nVARIABLE v\nA == v + 1\n====\n";
    let parsed = parse_file(src).expect("parses");
    let m = parsed.module;
    let mut low = Lowerer::new();
    low.add_module(&m);
    let k = low.lower_named(&m, "A").expect("lowers");
    let e = Evaluator::new().eval(&k).map(|_| ()).unwrap_err();
    assert!(matches!(e, EvalErrorKind::FreeName(_)), "got {e:?}");
}

#[test]
fn an_unimplemented_primitive_is_named_not_guessed() {
    // `ToString` has no kernel node and no implementation here; lowering
    // carries it through as an opaque application, and evaluation must decline
    // rather than invent a value.
    let e = eval_err("A == ToString(1)");
    let EvalErrorKind::Unsupported(what) = &e else {
        panic!("got {e:?}");
    };
    assert!(what.contains("ToString"), "the diagnostic names it: {what}");
}

#[test]
fn runaway_sets_are_bounded() {
    let src = "---- MODULE M ----\nEXTENDS Integers\nA == 1..1000000\n====\n";
    let parsed = parse_file(src).expect("parses");
    let m = parsed.module;
    let mut low = Lowerer::new();
    low.add_module(&m);
    let k = low.lower_named(&m, "A").expect("lowers");
    let e = Evaluator::new().eval(&k).map(|_| ()).unwrap_err();
    assert!(matches!(e, EvalErrorKind::SetTooLarge { .. }), "got {e:?}");
}

// ---- regressions found by the TLC differential ----------------------------

#[test]
fn cartesian_product_is_n_ary() {
    // `A \X B \X C` is a set of *3-tuples* in TLA+, not a set of pairs whose
    // first component is a pair. Nesting it gave `{<<<<1, 2>>, 3>>}` where TLC
    // gives `{<<1, 2, 3>>}`.
    assert_eq!(eval("A == {1} \\X {2} \\X {3}"), "{<<1, 2, 3>>}");
    assert_eq!(
        eval("A == {1, 2} \\X {3} \\X {4}"),
        "{<<1, 3, 4>>, <<2, 3, 4>>}"
    );
    // Explicit parentheses mean the nested reading, and TLA+ distinguishes
    // the two, so this must NOT be flattened.
    assert_eq!(eval("A == ({1} \\X {2}) \\X {3}"), "{<<<<1, 2>>, 3>>}");
}

#[test]
fn a_multi_bound_set_map_is_flat() {
    // `{e : x \in S, y \in T}` collects `e` over every combination, giving one
    // flat set. Nesting the binders produced a set of sets.
    assert_eq!(
        eval("A == {<<x, y>> : x \\in {1}, y \\in {2}}"),
        "{<<1, 2>>}"
    );
    assert_eq!(
        eval("A == {x + y : x \\in {1, 2}, y \\in {10}}"),
        "{11, 12}"
    );
    // The single-bound form is unaffected.
    assert_eq!(eval("A == {x * 2 : x \\in {1, 2}}"), "{2, 4}");
}

#[test]
fn a_multi_variable_function_has_a_product_domain() {
    assert_eq!(
        eval("A == DOMAIN [x \\in {1}, y \\in {2} |-> 0]"),
        "{<<1, 2>>}"
    );
    assert_eq!(
        eval("A == [x \\in {1}, y \\in {2} |-> x + y][<<1, 2>>]"),
        "3"
    );
}

#[test]
fn standard_module_primitives() {
    // Sequences.
    assert_eq!(eval("A == Len(<<1, 2, 3>>)"), "3");
    assert_eq!(eval("A == Head(<<7, 8>>)"), "7");
    assert_eq!(eval("A == Tail(<<7, 8, 9>>)"), "<<8, 9>>");
    assert_eq!(eval("A == Append(<<1>>, 2)"), "<<1, 2>>");
    assert_eq!(eval("A == <<1, 2>> \\o <<3>>"), "<<1, 2, 3>>");
    assert_eq!(eval("A == SubSeq(<<1, 2, 3, 4>>, 2, 3)"), "<<2, 3>>");
    // A function on 1..n *is* a sequence, so the constructed form works too.
    assert_eq!(eval("A == Len([i \\in 1..4 |-> i])"), "4");

    // FiniteSets.
    assert_eq!(eval("A == Cardinality({1, 2, 2, 3})"), "3");
    assert_eq!(eval("A == IsFiniteSet({1})"), "TRUE");

    // TLC.
    // `1 :> 5` builds the function `{1} -> {5}`, which is the 1-tuple.
    assert_eq!(eval("A == 1 :> 5"), "<<5>>");
    // ...and `@@` of `1 :> 5` and `2 :> 6` has domain `{1, 2}`, so it is the
    // 2-tuple. A function whose domain is *not* `1..n` still prints as one.
    assert_eq!(eval("A == (1 :> 5) @@ (2 :> 6)"), "<<5, 6>>");
    assert_eq!(
        eval("A == (1 :> 5) @@ (3 :> 6)"),
        "(1 :> 5, 3 :> 6)".replace(", ", " @@ ")
    );
    // `@@` keeps the left operand on a shared key.
    assert_eq!(eval("A == (1 :> 5) @@ (1 :> 9)"), "<<5>>");
}

#[test]
fn head_and_tail_of_the_empty_sequence_are_errors() {
    // TLA+ leaves them undefined; returning a plausible value would be
    // fabrication.
    assert!(matches!(
        eval_err("A == Head(<<>>)"),
        EvalErrorKind::OutOfDomain(_)
    ));
    assert!(matches!(
        eval_err("A == Tail(<<>>)"),
        EvalErrorKind::OutOfDomain(_)
    ));
}

#[test]
fn boolean_literals_are_built_in_not_free_names() {
    // `TRUE`, `FALSE` and `BOOLEAN` are part of the language. Lowering them to
    // `Var("TRUE")` made them free names: unevaluable here, and an undeclared
    // symbol to any encoder.
    assert_eq!(eval("A == TRUE"), "TRUE");
    assert_eq!(eval("A == FALSE /\\ TRUE"), "FALSE");
    assert_eq!(eval("A == BOOLEAN"), "{FALSE, TRUE}");
    assert_eq!(eval("A == TRUE \\in BOOLEAN"), "TRUE");
}

// ---- `@` in a multi-update EXCEPT ----
//
// `[f EXCEPT !p1 = v1, !p2 = v2]` abbreviates `[[f EXCEPT !p1 = v1] EXCEPT
// !p2 = v2]`, so the `@` in `v2` denotes the **partially updated** function at
// `p2` — not the original `f`, and certainly not `v1`.
//
// The expected values below are TLC's, on `tlaplus 1.7.4`. They are the
// oracle: the two readings of `@` differ only when two updates touch the same
// index, which is exactly the case a from-first-principles reading gets wrong.

/// Different fields: both readings agree, and this is the common shape.
#[test]
fn at_in_a_later_update_reads_the_function_not_the_previous_value() {
    assert_eq!(
        eval("A == [[a |-> 1, b |-> 10] EXCEPT !.a = 5, !.b = @ + 100].b"),
        "110"
    );
}

/// The same field twice, where the readings disagree. TLC says 105: the `@`
/// sees the 5 written by the first update.
#[test]
fn at_sees_what_an_earlier_update_wrote() {
    assert_eq!(
        eval("A == [[a |-> 1] EXCEPT !.a = 5, !.a = @ + 100].a"),
        "105"
    );
}

/// The regression proper. The `@` used to be lowered against the *previous
/// update's value* — `1[\"b\"]` here — because the function was assumed to sit
/// a fixed distance below the top of the value stack, which holds only for the
/// first update. Silent, and a wrong value rather than a refusal.
#[test]
fn the_first_update_does_not_become_the_function() {
    assert_eq!(
        eval("A == [[a |-> 1, b |-> 10] EXCEPT !.a = 7, !.b = @].b"),
        "10"
    );
    // Three updates, so the third has two to skip over.
    assert_eq!(
        eval("A == [[a |-> 1, b |-> 2, c |-> 3] EXCEPT !.a = 9, !.b = 9, !.c = @].c"),
        "3"
    );
}

/// An untouched field keeps its value, and the earlier updates are all applied.
#[test]
fn every_update_in_a_multi_update_lands() {
    assert_eq!(
        eval("A == [[a |-> 1, b |-> 2] EXCEPT !.a = 5, !.b = 6]"),
        "[a |-> 5, b |-> 6]"
    );
}

/// Indexed rather than field paths, which take the same code path.
#[test]
fn at_in_a_multi_update_over_a_function() {
    assert_eq!(
        eval("A == [[i \\in 1..3 |-> i] EXCEPT ![1] = 10, ![2] = @ + 100][2]"),
        "102"
    );
    assert_eq!(
        eval("A == [[i \\in 1..3 |-> i] EXCEPT ![1] = 10, ![1] = @ + 100][1]"),
        "110"
    );
}

// ---- a tuple IS a function on `1..n` ----
//
// TLA+ has no separate sequence type: `<<3, 4, 5>>` *is* the function with
// domain `1..3`, so the two spellings denote one value and must compare equal.
// Found by the TLC differential (`Apalache!MkSeq`, which is defined as
// `[i \in 1..N |-> F(i)]` and is tested against a tuple literal).

#[test]
fn a_function_on_a_range_equals_the_tuple_of_its_values() {
    assert_eq!(
        eval("A == [i \\in 1..4 |-> 2 * i] = <<2, 4, 6, 8>>"),
        "TRUE"
    );
    assert_eq!(
        eval("A == <<2, 4, 6, 8>> = [i \\in 1..4 |-> 2 * i]"),
        "TRUE"
    );
}

#[test]
fn the_empty_function_equals_the_empty_tuple() {
    assert_eq!(eval("A == [i \\in 1..0 |-> i] = << >>"), "TRUE");
}

#[test]
fn a_different_value_is_still_different() {
    assert_eq!(eval("A == [i \\in 1..3 |-> i] = <<1, 2, 4>>"), "FALSE");
    assert_eq!(eval("A == [i \\in 1..3 |-> i] = <<1, 2>>"), "FALSE");
}

/// A function whose domain is not `1..n` is not a tuple, however its values
/// line up.
#[test]
fn a_function_on_another_domain_is_not_a_tuple() {
    assert_eq!(eval("A == [i \\in 2..4 |-> i] = <<2, 3, 4>>"), "FALSE");
    assert_eq!(eval("A == [i \\in {\"a\"} |-> 1] = <<1>>"), "FALSE");
}

// ---- folds ----
//
// `ApaFoldSet` and `ApaFoldSeqLeft` are the only standard operators that take
// an *operator* as an argument. The kernel stays first-order: lowering keeps
// the operator's body with its two parameters free and `Kera::Fold` names
// them, which is a binder of the same shape as `\A x \in S : …`.

#[test]
fn fold_set_sums() {
    assert_eq!(
        eval("Add(a, b) == a + b\nA == ApaFoldSet(Add, 0, {1, 2, 3, 4})"),
        "10"
    );
}

#[test]
fn fold_set_over_the_empty_set_is_the_base() {
    assert_eq!(eval("Add(a, b) == a + b\nA == ApaFoldSet(Add, 7, {})"), "7");
}

/// A set has no duplicates, so a member written twice is folded once. This is
/// the property the encoder has to work for, and it is free here.
#[test]
fn fold_set_counts_each_member_once() {
    assert_eq!(
        eval("Inc(a, b) == a + 1\nA == ApaFoldSet(Inc, 0, {1, 1, 2, 2, 2})"),
        "2"
    );
}

#[test]
fn fold_set_takes_a_lambda() {
    assert_eq!(
        eval("A == ApaFoldSet(LAMBDA a, b: a + b, 100, {1, 2})"),
        "103"
    );
}

/// A `LET`-bound operator, which is how Apalache's own regression specs write
/// it (`Sum(S) == LET Add(i, j) == i + j IN ApaFoldSet(Add, 0, S)`).
#[test]
fn fold_set_takes_a_let_bound_operator() {
    assert_eq!(
        eval("A == LET Add(i, j) == i + j IN ApaFoldSet(Add, 0, {1, 2, 3})"),
        "6"
    );
}

#[test]
fn fold_seq_left_is_left_to_right() {
    // Subtraction is not commutative, so this pins the direction:
    // ((100 - 1) - 2) - 3.
    assert_eq!(
        eval("Sub(a, b) == a - b\nA == ApaFoldSeqLeft(Sub, 100, <<1, 2, 3>>)"),
        "94"
    );
}

#[test]
fn fold_seq_left_over_the_empty_sequence_is_the_base() {
    assert_eq!(
        eval("Sub(a, b) == a - b\nA == ApaFoldSeqLeft(Sub, 5, <<>>)"),
        "5"
    );
}

/// Unlike a set, a sequence keeps its repeats.
#[test]
fn fold_seq_left_counts_repeats() {
    assert_eq!(
        eval("Inc(a, b) == a + 1\nA == ApaFoldSeqLeft(Inc, 0, <<1, 1, 1>>)"),
        "3"
    );
}

/// A fold's parameters are renamed on the way in, so an enclosing binder that
/// happens to use the same name cannot be captured.
#[test]
fn a_folds_parameters_do_not_capture_an_enclosing_binder() {
    assert_eq!(
        eval("Add(a, b) == a + b\nA == {a + ApaFoldSet(Add, 0, {1, 2}) : a \\in {10, 20}}"),
        "{13, 23}"
    );
}

/// Nested folds, where the inner one is applied to the outer one's element.
#[test]
fn folds_nest() {
    assert_eq!(
        eval(
            "Add(a, b) == a + b\n\
             A == ApaFoldSet(LAMBDA x, S: x + ApaFoldSet(Add, 0, S), 0, {{1, 2}, {3}})"
        ),
        "6"
    );
}

/// A specification that defines its own `ApaFoldSet` keeps it: the intercept
/// only fires for a name nothing local has bound.
#[test]
fn a_local_definition_of_a_fold_name_wins() {
    assert_eq!(
        eval("A == LET ApaFoldSet(x, y, z) == 42 IN ApaFoldSet(1, 2, 3)"),
        "42"
    );
}

// ---- multi-variable function definitions ----
//
// `f[x \in S, y \in T] == e` is a function of *one* variable ranging over
// `S \X T`, exactly as `[x \in S, y \in T |-> e]` is. The two differ only in
// where they are written; lowering them differently was the defect.

#[test]
fn a_two_variable_function_definition() {
    assert_eq!(
        eval("f[x \\in {1, 2}, y \\in {10, 20}] == x + y\nA == f[<<2, 20>>]"),
        "22"
    );
}

/// Its domain is the product, not the first bound.
#[test]
fn a_two_variable_function_definition_has_a_product_domain() {
    assert_eq!(
        eval("f[x \\in {1, 2}, y \\in {10}] == x + y\nA == DOMAIN f"),
        "{<<1, 10>>, <<2, 10>>}"
    );
}

/// Two names in one bound range over the same set, and each is its own
/// component.
#[test]
fn two_names_in_one_bound() {
    assert_eq!(eval("f[x, y \\in {1, 2}] == x - y\nA == f[<<1, 2>>]"), "-1");
}

/// The definition form and the expression form must agree.
#[test]
fn the_definition_and_expression_forms_agree() {
    assert_eq!(
        eval(
            "f[x \\in {1, 2}, y \\in {3, 4}] == x * y\n\
             g == [x \\in {1, 2}, y \\in {3, 4} |-> x * y]\n\
             A == f = g"
        ),
        "TRUE"
    );
}

/// Three variables, so the product is not merely a pair.
#[test]
fn a_three_variable_function_definition() {
    assert_eq!(
        eval("f[x \\in {1}, y \\in {2}, z \\in {3}] == x + y + z\nA == f[<<1, 2, 3>>]"),
        "6"
    );
}

/// A tuple pattern inside a multi-variable definition projects again.
#[test]
fn a_tuple_pattern_in_a_multi_variable_definition() {
    assert_eq!(
        eval("f[<<x, y>> \\in {<<1, 2>>}, z \\in {10}] == x + y + z\nA == f[<<<<1, 2>>, 10>>]"),
        "13"
    );
}

// ---- a multi-argument EXCEPT selector ----
//
// `[f EXCEPT ![i, j] = v]` is **one** application of a function of two
// arguments, which in TLA+ is a function of the pair — so it updates `f` at
// `<<i, j>>`. Flattening the selector into two path steps reads it as
// `f[i][j]`: a different function and a different value. TLC settles it.
//
//     f == [i \in 1..2, j \in 1..2 |-> 10*i + j]
//     [f EXCEPT ![1,2] = 99][<<1,2>>]   = 99
//     [f EXCEPT ![1,2] = 99]            = (<<1,1>> :> 11 @@ <<1,2>> :> 99
//                                          @@ <<2,1>> :> 21 @@ <<2,2>> :> 22)

const GRID: &str = "f == [i \\in 1..2, j \\in 1..2 |-> 10*i + j]\n";

#[test]
fn a_multi_argument_except_selector_updates_one_point() {
    assert_eq!(
        eval(&format!("{GRID}A == [f EXCEPT ![1, 2] = 99][<<1, 2>>]")),
        "99"
    );
}

/// And leaves every other point alone — in particular `<<2, 1>>`, which a
/// reading of `![1,2]` as `f[1][2]` would have had no way to touch either, and
/// `<<1, 1>>`, which such a reading would have destroyed.
#[test]
fn a_multi_argument_except_selector_leaves_the_rest_alone() {
    assert_eq!(
        eval(&format!(
            "{GRID}A == LET g == [f EXCEPT ![1, 2] = 99] \
             IN <<g[<<1, 1>>], g[<<2, 1>>], g[<<2, 2>>]>>"
        )),
        "<<11, 21, 22>>"
    );
}

/// The domain does not change: an update is not an extension.
#[test]
fn a_multi_argument_except_selector_keeps_the_domain() {
    assert_eq!(
        eval(&format!(
            "{GRID}A == DOMAIN [f EXCEPT ![1, 2] = 99] = DOMAIN f"
        )),
        "TRUE"
    );
}

/// Nested brackets are the *other* form and still nest: `![i][j]` updates the
/// function that `f[i]` returns.
#[test]
fn nested_except_selectors_still_nest() {
    assert_eq!(
        eval(
            "g == [i \\in 1..2 |-> [j \\in 1..2 |-> 10*i + j]]\n\
             A == [g EXCEPT ![1][2] = 99]"
        ),
        "<<<<11, 99>>, <<21, 22>>>>"
    );
}

/// `@` in a multi-argument selector is the old value at that one point.
#[test]
fn at_in_a_multi_argument_selector() {
    assert_eq!(
        eval(&format!(
            "{GRID}A == [f EXCEPT ![1, 2] = @ + 100][<<1, 2>>]"
        )),
        "112"
    );
}

/// A multi-argument selector followed by a field, which is the shape that
/// found this: `![1,2].a`.
#[test]
fn a_multi_argument_selector_then_a_field() {
    assert_eq!(
        eval(
            "r == [i \\in 1..2, j \\in 1..2 |-> [a |-> i, b |-> j]]\n\
             A == [r EXCEPT ![1, 2].a = 22][<<1, 2>>]"
        ),
        "[a |-> 22, b |-> 2]"
    );
}

// ---- actions: `x'` ----
//
// `'` is not a different variable. `e'` is the *same* expression evaluated in
// the successor state, so priming distributes through everything inside it —
// which is why the evaluator carries a mode rather than looking up a name
// spelled `x'`.

#[test]
fn a_primed_variable_reads_the_next_state() {
    assert_eq!(
        act(
            "A == x' = x + 1",
            &[("x", Value::Int(1))],
            &[("x", Value::Int(2))]
        ),
        "TRUE"
    );
    assert_eq!(
        act(
            "A == x' = x + 1",
            &[("x", Value::Int(1))],
            &[("x", Value::Int(3))]
        ),
        "FALSE"
    );
}

#[test]
fn unchanged_compares_the_two_states() {
    assert_eq!(
        act(
            "A == UNCHANGED x",
            &[("x", Value::Int(7))],
            &[("x", Value::Int(7))]
        ),
        "TRUE"
    );
    assert_eq!(
        act(
            "A == UNCHANGED x",
            &[("x", Value::Int(7))],
            &[("x", Value::Int(8))]
        ),
        "FALSE"
    );
}

/// Priming distributes: `(x + y)'` is `x' + y'`, not `x' + y`.
#[test]
fn priming_distributes_over_an_expression() {
    assert_eq!(
        act(
            "A == (x + y)' = 30",
            &[("x", Value::Int(1)), ("y", Value::Int(2))],
            &[("x", Value::Int(10)), ("y", Value::Int(20))],
        ),
        "TRUE"
    );
}

/// A binder's variable is not a state variable, so it is not re-read from the
/// successor state even under a prime.
#[test]
fn a_binder_under_a_prime_is_not_a_state_variable() {
    let f_now = Value::Tuple(vec![Value::Int(1), Value::Int(2)]);
    let f_next = Value::Tuple(vec![Value::Int(2), Value::Int(3)]);
    assert_eq!(
        act(
            "A == \\A i \\in {1, 2} : (x[i])' = x[i] + 1",
            &[("x", f_now)],
            &[("x", f_next)],
        ),
        "TRUE"
    );
}

/// A constant is unchanged by the step, so it falls through to the ordinary
/// environment even under a prime — which is what a constant is.
#[test]
fn an_unprimed_name_in_an_action_reads_the_current_state() {
    assert_eq!(
        act(
            "A == <<x, x'>> = <<1, 2>>",
            &[("x", Value::Int(1))],
            &[("x", Value::Int(2))],
        ),
        "TRUE"
    );
}

/// TLA+ has no `x''`: priming selects the successor state, and there is only
/// one. Reported rather than flattened to a single prime.
#[test]
fn a_double_prime_is_an_error() {
    let e = act_err(
        "A == x'' = 1",
        &[("x", Value::Int(1))],
        &[("x", Value::Int(2))],
    );
    assert!(
        matches!(&e, EvalErrorKind::Unsupported(m) if m.contains("double prime")),
        "got {e}"
    );
}

/// And outside an action there is no next state to read, so `'` stays the
/// honest refusal it was — a ground definition that mentions it has no value.
#[test]
fn a_prime_outside_an_action_is_still_refused() {
    let k = lower_action("A == x' = 1");
    let e = Evaluator::new()
        .eval_state(&k, &state(&[("x", Value::Int(1))]))
        .expect_err("a state predicate has no next state");
    assert!(
        matches!(&e, EvalErrorKind::Unsupported(m) if m.contains("outside an action")),
        "got {e}"
    );
}

// ---- the standard infinite sets ----
//
// `Nat`, `Int`, `Real` and `STRING` have no finite extension, so they are not
// values this evaluator can build. Membership in one is still decidable — by
// the *kind* of the value — and that is the only thing a state predicate ever
// asks of them.

#[test]
fn membership_in_nat() {
    assert_eq!(eval("A == 3 \\in Nat"), "TRUE");
    assert_eq!(eval("A == 0 \\in Nat"), "TRUE");
    assert_eq!(eval("A == -1 \\in Nat"), "FALSE");
    assert_eq!(eval("A == \"x\" \\in Nat"), "FALSE");
}

#[test]
fn membership_in_int() {
    assert_eq!(eval("A == -1 \\in Int"), "TRUE");
    assert_eq!(eval("A == 0 \\in Int"), "TRUE");
    assert_eq!(eval("A == TRUE \\in Int"), "FALSE");
}

/// TLA+'s `Real` contains every integer, and a genuine real is not a value
/// this evaluator has — so the answer is exact for everything it can be asked.
#[test]
fn membership_in_real() {
    assert_eq!(eval("A == 3 \\in Real"), "TRUE");
    assert_eq!(eval("A == \"x\" \\in Real"), "FALSE");
}

#[test]
fn membership_in_string() {
    assert_eq!(eval("A == \"x\" \\in STRING"), "TRUE");
    assert_eq!(eval("A == 1 \\in STRING"), "FALSE");
}

/// `BOOLEAN` needs no special case: lowering expands it to `{FALSE, TRUE}`,
/// which is an ordinary finite set.
#[test]
fn boolean_is_a_finite_set() {
    assert_eq!(eval("A == TRUE \\in BOOLEAN"), "TRUE");
    assert_eq!(eval("A == BOOLEAN"), "{FALSE, TRUE}");
}

/// And they stay unavailable everywhere else. An infinite set is not
/// approximated by a finite prefix.
#[test]
fn an_infinite_set_is_not_a_value() {
    assert!(matches!(eval_err("A == Nat"), EvalErrorKind::FreeName(n) if n == "Nat"));
    assert!(matches!(
        eval_err("A == \\A i \\in Nat : i >= 0"),
        EvalErrorKind::FreeName(n) if n == "Nat"
    ));
}

/// Negated membership is the ordinary `~`, so it follows for free.
#[test]
fn non_membership_in_nat() {
    assert_eq!(eval("A == -1 \\notin Nat"), "TRUE");
    assert_eq!(eval("A == 2 \\notin Nat"), "FALSE");
}
