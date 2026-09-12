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
    // `\o` has no kernel node; lowering carries it through as an opaque
    // application, and evaluation must decline rather than invent a value.
    let e = eval_err("A == <<1>> \\o <<2>>");
    let EvalErrorKind::Unsupported(what) = &e else {
        panic!("got {e:?}");
    };
    assert!(what.contains("\\o"), "the diagnostic names it: {what}");
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
