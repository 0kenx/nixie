//! Evaluating lowered terms.
//!
//! These pin the semantics unit by unit; `bench/tla_eval` checks the same
//! evaluator against TLC over the corpora.

use nixie_tla::{EvalErrorKind, Evaluator, Lowerer};
use nixie_tla_syntax::parse_file;

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
    assert_eq!(eval("A == [f \\in {1} |-> 0] "), "(1 :> 0)");
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
    assert_eq!(eval("A == 1 :> 5"), "(1 :> 5)");
    assert_eq!(
        eval("A == (1 :> 5) @@ (2 :> 6)"),
        "(1 :> 5, 2 :> 6)".replace(", ", " @@ ")
    );
    // `@@` keeps the left operand on a shared key.
    assert_eq!(eval("A == (1 :> 5) @@ (1 :> 9)"), "(1 :> 5)");
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
