//! Regression tests for audited SMT-LIB Div/Mod semantics defects.
//!
//! The shared `TermKind::Div` / `TermKind::Mod` nodes must follow SMT-LIB
//! semantics dispatched by operand sort:
//!
//! * Int operands: `(div a b)` is Euclidean integer division — the unique `q`
//!   with `a = b*q + r` and `0 <= r < |b|` — and `(mod a b)` is the matching
//!   non-negative remainder. In particular `(div 7 2) = 3`, `(div -7 2) = -4`,
//!   `(mod -7 2) = 1`. Previously constant folding used Rust truncated `/`/`%`,
//!   which gave wrong results for negative operands, and integer division of
//!   non-exact operands was fabricated as a `Real`.
//! * Real operands: `/` is exact rational division and must NOT truncate even
//!   when both operands happen to be integer-valued.
//! * Division / modulo by zero is left uninterpreted (never folded), and a
//!   symbolic divisor must not be folded either (it could be zero).

use num_rational::Rational64;
use oxiz_core::ast::{TermKind, TermManager};
use oxiz_core::model::{EvalResult, Model, ModelEvaluator, Value};
use oxiz_core::rewrite::arith::ArithRewriter;
use oxiz_core::rewrite::{RewriteContext, Rewriter};

// ---------------------------------------------------------------------------
// Rewriter: Euclidean integer div/mod constant folding.
// ---------------------------------------------------------------------------

fn fold_div(a: i64, b: i64) -> (TermManager, oxiz_core::ast::TermId) {
    let mut m = TermManager::new();
    let mut ctx = RewriteContext::new();
    let mut rw = ArithRewriter::new();
    let la = m.mk_int(a);
    let lb = m.mk_int(b);
    let div = m.mk_div(la, lb);
    let r = rw.rewrite(div, &mut ctx, &mut m);
    (m, r.term())
}

fn fold_mod(a: i64, b: i64) -> (TermManager, oxiz_core::ast::TermId) {
    let mut m = TermManager::new();
    let mut ctx = RewriteContext::new();
    let mut rw = ArithRewriter::new();
    let la = m.mk_int(a);
    let lb = m.mk_int(b);
    let md = m.mk_mod(la, lb);
    let r = rw.rewrite(md, &mut ctx, &mut m);
    (m, r.term())
}

fn expect_int(m: &TermManager, t: oxiz_core::ast::TermId, expected: i64) {
    match &m.get(t).expect("term should exist").kind {
        TermKind::IntConst(n) => {
            assert_eq!(*n, num_bigint::BigInt::from(expected), "wrong folded value");
        }
        other => panic!("expected IntConst({expected}), got {other:?}"),
    }
}

#[test]
fn rewrite_div_positive() {
    let (m, t) = fold_div(7, 2);
    expect_int(&m, t, 3); // (div 7 2) = 3
}

#[test]
fn rewrite_div_negative_dividend() {
    let (m, t) = fold_div(-7, 2);
    expect_int(&m, t, -4); // (div -7 2) = -4, NOT -3 (truncation)
}

#[test]
fn rewrite_div_negative_divisor() {
    let (m, t) = fold_div(7, -2);
    expect_int(&m, t, -3); // 7 = -2*-3 + 1, 0 <= 1 < 2
}

#[test]
fn rewrite_div_both_negative() {
    let (m, t) = fold_div(-7, -2);
    expect_int(&m, t, 4); // -7 = -2*4 + 1
}

#[test]
fn rewrite_mod_negative_dividend() {
    let (m, t) = fold_mod(-7, 2);
    expect_int(&m, t, 1); // (mod -7 2) = 1, NOT -1 (Rust %)
}

#[test]
fn rewrite_mod_positive() {
    let (m, t) = fold_mod(7, 2);
    expect_int(&m, t, 1);
}

#[test]
fn rewrite_mod_negative_divisor_is_non_negative() {
    let (m, t) = fold_mod(7, -2);
    expect_int(&m, t, 1); // remainder is always in [0, |b|)
}

#[test]
fn rewrite_int_div_exact_check() {
    // (div 6 2) = 3 exactly.
    let (m, t) = fold_div(6, 2);
    expect_int(&m, t, 3);
}

#[test]
fn rewrite_div_by_zero_is_not_folded() {
    // (div 7 0) is uninterpreted; the rewriter must leave a Div node intact.
    let (m, t) = fold_div(7, 0);
    assert!(
        matches!(&m.get(t).expect("term").kind, TermKind::Div(_, _)),
        "division by zero must not be folded"
    );
}

#[test]
fn rewrite_mod_by_zero_is_not_folded() {
    let (m, t) = fold_mod(7, 0);
    assert!(
        matches!(&m.get(t).expect("term").kind, TermKind::Mod(_, _)),
        "modulo by zero must not be folded"
    );
}

#[test]
fn rewrite_div_symbolic_divisor_not_folded_from_zero_numerator() {
    // (div 0 x) must NOT fold to 0 for a symbolic x, since x may be 0.
    let mut m = TermManager::new();
    let mut ctx = RewriteContext::new();
    let mut rw = ArithRewriter::new();
    let zero = m.mk_int(0);
    let x = m.mk_var("x", m.sorts.int_sort);
    let div = m.mk_div(zero, x);
    let r = rw.rewrite(div, &mut ctx, &mut m);
    assert!(
        matches!(&m.get(r.term()).expect("term").kind, TermKind::Div(_, _)),
        "(div 0 x) with symbolic x must stay a Div node (x could be 0)"
    );
}

#[test]
fn rewrite_real_division_stays_exact() {
    // Real-sorted (/ 7.0 2.0) must fold to 3.5, not truncate to 3.
    let mut m = TermManager::new();
    let mut ctx = RewriteContext::new();
    let mut rw = ArithRewriter::new();
    let a = m.mk_real(Rational64::new(7, 1));
    let b = m.mk_real(Rational64::new(2, 1));
    let div = m.mk_div(a, b);
    let r = rw.rewrite(div, &mut ctx, &mut m);
    match &m.get(r.term()).expect("term").kind {
        TermKind::RealConst(v) => assert_eq!(*v, Rational64::new(7, 2)),
        other => panic!("expected RealConst(7/2), got {other:?}"),
    }
}

/// Issue #22: the exact Int `div`/`mod` constants appearing in the reported
/// QF_AUFLIA read-over-write reproducer, over every operand-sign combination.
///
/// SMT-LIB Ints fixes `m = n * (div m n) + (mod m n)` with `0 <= (mod m n) <
/// |n|`, so the remainder is *never* negative — unlike Rust's truncating `%`,
/// where `-3 % -5 == -3` and `-3 % 5 == -3`.  Folding `div`/`mod` with `/`/`%`
/// instead of `div_euclid`/`rem_euclid` would be a soundness bug across every
/// Int logic, so pin the Euclidean answers directly.
#[test]
fn test_issue_22_euclidean_div_mod_folding() {
    // (div 7 7) = 1 and (mod 7 7) = 0.
    let (m, t) = fold_div(7, 7);
    expect_int(&m, t, 1);
    let (m, t) = fold_mod(7, 7);
    expect_int(&m, t, 0);

    // Both operands negative: -3 = -5*1 + 2.
    let (m, t) = fold_div(-3, -5);
    expect_int(&m, t, 1);
    let (m, t) = fold_mod(-3, -5);
    expect_int(&m, t, 2); // NOT Rust's -3 % -5 == -3

    // Negative dividend, positive divisor: -3 = 5*(-1) + 2.
    let (m, t) = fold_div(-3, 5);
    expect_int(&m, t, -1);
    let (m, t) = fold_mod(-3, 5);
    expect_int(&m, t, 2); // NOT Rust's -3 % 5 == -3

    // Positive dividend, negative divisor: 3 = -5*0 + 3.
    let (m, t) = fold_div(3, -5);
    expect_int(&m, t, 0);
    let (m, t) = fold_mod(3, -5);
    expect_int(&m, t, 3);
}

// ---------------------------------------------------------------------------
// Model evaluator: Euclidean div/mod and exact real division.
// ---------------------------------------------------------------------------

fn eval(term: oxiz_core::ast::TermId, m: &TermManager) -> EvalResult {
    let model = Model::new();
    let mut ev = ModelEvaluator::new(&model);
    ev.eval(term, m)
}

#[test]
fn eval_int_div_euclidean() {
    let mut m = TermManager::new();
    let a = m.mk_int(-7);
    let b = m.mk_int(2);
    let div = m.mk_div(a, b);
    match eval(div, &m) {
        EvalResult::Ok(Value::Int(v)) => assert_eq!(v, -4),
        other => panic!("expected Int(-4), got {other:?}"),
    }
}

#[test]
fn eval_int_mod_euclidean() {
    let mut m = TermManager::new();
    let a = m.mk_int(-7);
    let b = m.mk_int(2);
    let md = m.mk_mod(a, b);
    match eval(md, &m) {
        EvalResult::Ok(Value::Int(v)) => assert_eq!(v, 1),
        other => panic!("expected Int(1), got {other:?}"),
    }
}

#[test]
fn eval_int_div_positive() {
    let mut m = TermManager::new();
    let a = m.mk_int(7);
    let b = m.mk_int(2);
    let div = m.mk_div(a, b);
    match eval(div, &m) {
        EvalResult::Ok(Value::Int(v)) => assert_eq!(v, 3),
        other => panic!("expected Int(3), got {other:?}"),
    }
}

#[test]
fn eval_real_division_is_exact() {
    // Real (/ 7.0 2.0) evaluates to the rational 7/2, never truncated.
    let mut m = TermManager::new();
    let a = m.mk_real(Rational64::new(7, 1));
    let b = m.mk_real(Rational64::new(2, 1));
    let div = m.mk_div(a, b);
    match eval(div, &m) {
        EvalResult::Ok(Value::Rational(v)) => assert_eq!(v, Rational64::new(7, 2)),
        other => panic!("expected Rational(7/2), got {other:?}"),
    }
}

#[test]
fn eval_real_division_integer_valued_operands_not_truncated() {
    // Real (/ 3.0 2.0): both operands integer-valued yet the quotient is 3/2.
    let mut m = TermManager::new();
    let a = m.mk_real(Rational64::new(3, 1));
    let b = m.mk_real(Rational64::new(2, 1));
    let div = m.mk_div(a, b);
    match eval(div, &m) {
        EvalResult::Ok(Value::Rational(v)) => assert_eq!(v, Rational64::new(3, 2)),
        other => panic!("expected Rational(3/2), got {other:?}"),
    }
}

#[test]
fn eval_div_by_zero_is_error_not_fabricated() {
    let mut m = TermManager::new();
    let a = m.mk_int(7);
    let b = m.mk_int(0);
    let div = m.mk_div(a, b);
    assert!(matches!(eval(div, &m), EvalResult::Error(_)));
}

#[test]
fn eval_mod_by_zero_is_error_not_fabricated() {
    let mut m = TermManager::new();
    let a = m.mk_int(7);
    let b = m.mk_int(0);
    let md = m.mk_mod(a, b);
    assert!(matches!(eval(md, &m), EvalResult::Error(_)));
}

// ---------------------------------------------------------------------------
// Parser: to_int / is_int constant folding, and honest error on symbolic.
// ---------------------------------------------------------------------------

use oxiz_core::smtlib::{Command, parse_script};

fn assert_term(script: &str) -> (TermManager, oxiz_core::ast::TermId) {
    let mut m = TermManager::new();
    let cmds = parse_script(script, &mut m).expect("script should parse");
    let t = cmds
        .into_iter()
        .find_map(|c| match c {
            Command::Assert(t) => Some(t),
            _ => None,
        })
        .expect("expected an assert");
    (m, t)
}

#[test]
fn to_int_of_constant_folds_to_floor() {
    // (= (to_int 7.5) 7): to_int on a constant real folds to its floor.
    let (m, t) = assert_term("(assert (= (to_int 3.5) 3))");
    match &m.get(t).expect("term").kind {
        // Both sides are Int constants 3, so mk_eq canonicalizes to `true`.
        TermKind::True => {}
        TermKind::Eq(a, b) => {
            // If not folded to true, at least the to_int side must be Int 3.
            let ka = &m.get(*a).expect("a").kind;
            let kb = &m.get(*b).expect("b").kind;
            assert!(
                matches!(ka, TermKind::IntConst(n) if *n == num_bigint::BigInt::from(3))
                    || matches!(kb, TermKind::IntConst(n) if *n == num_bigint::BigInt::from(3)),
                "to_int(3.5) should fold to 3"
            );
        }
        other => panic!("unexpected term: {other:?}"),
    }
}

#[test]
fn to_int_of_negative_constant_floors_toward_neg_inf() {
    // to_int(-3.5) = floor(-3.5) = -4.
    let mut m = TermManager::new();
    let cmds = parse_script("(assert (< (to_int -3.5) 0))", &mut m).expect("parse");
    // Reach into the term: (< to_int(-3.5) 0). to_int side must be Int(-4).
    let assert_t = cmds
        .into_iter()
        .find_map(|c| match c {
            Command::Assert(t) => Some(t),
            _ => None,
        })
        .expect("assert");
    let TermKind::Lt(lhs, _) = &m.get(assert_t).expect("term").kind else {
        panic!("expected Lt");
    };
    match &m.get(*lhs).expect("lhs").kind {
        TermKind::IntConst(n) => {
            assert_eq!(*n, num_bigint::BigInt::from(-4), "floor(-3.5) must be -4")
        }
        other => panic!("expected IntConst(-4), got {other:?}"),
    }
}

#[test]
fn is_int_of_constant_folds() {
    // (is_int 4.0) is true; (is_int 4.5) is false.
    let (m, t) = assert_term("(assert (is_int 4.0))");
    assert!(matches!(&m.get(t).expect("term").kind, TermKind::True));

    let mut m2 = TermManager::new();
    let cmds = parse_script("(assert (is_int 4.5))", &mut m2).expect("parse");
    let t2 = cmds
        .into_iter()
        .find_map(|c| match c {
            Command::Assert(t) => Some(t),
            _ => None,
        })
        .expect("assert");
    assert!(matches!(&m2.get(t2).expect("term").kind, TermKind::False));
}

#[test]
fn to_int_of_symbolic_is_honest_error() {
    let mut m = TermManager::new();
    let script = "(declare-const x Real)(assert (= (to_int x) 3))";
    assert!(
        parse_script(script, &mut m).is_err(),
        "to_int on a symbolic real must stay an honest error"
    );
}

#[test]
fn is_int_of_symbolic_is_honest_error() {
    let mut m = TermManager::new();
    let script = "(declare-const x Real)(assert (is_int x))";
    assert!(parse_script(script, &mut m).is_err());
}

// ---------------------------------------------------------------------------
// Parser: script-mode strictness no longer depends on a non-empty decl table.
// ---------------------------------------------------------------------------

#[test]
fn undeclared_symbol_rejected_even_with_no_declarations() {
    // A script that declares nothing but references an undeclared symbol must
    // still be rejected — the old "any declaration table non-empty" heuristic
    // wrongly stayed lenient here.
    let mut m = TermManager::new();
    let script = "(assert (< undeclared_a undeclared_b))";
    assert!(
        parse_script(script, &mut m).is_err(),
        "undeclared symbols in a script must be rejected even with zero declarations"
    );
}

#[test]
fn bare_term_parse_stays_lenient() {
    // The bare `parse_term` convenience path (not a script) must remain lenient
    // so ad-hoc free variables can still be built.
    let mut m = TermManager::new();
    let t = oxiz_core::smtlib::parse_term("(< x y)", &mut m);
    assert!(
        t.is_ok(),
        "bare-term parsing should stay lenient for free vars"
    );
}
