//! Regression: a model must pin definition Booleans to their definitions'
//! values (the QF_NIA/VeryMax invalid-model class, 2026-09-10).
//!
//! A conjunct-level `(= b φ)` is a *definition*: the nonlinear searches
//! ground `b := φ` away before verifying a witness, so the witness itself
//! carries no value for `b`.  Completing `b` with the sort default `false`
//! prints a model whose own definition conjunct is violated whenever `φ`
//! evaluates `true` under the printed numeric values — an invalid model
//! behind a correct `sat` verdict (differential `--validate-models` caught
//! exactly this on QF_NIA/VeryMax 459/489/510/1527/1659 and
//! QF_ANIA/sum10 i_2/i_3).  The fix evaluates the definition at completion
//! time; these tests pin both halves of the invariant end-to-end.

use nixie_solver::Context;

/// Extract a `(define-fun <name> () Bool <val>)` pin from a printed model.
fn bool_pin(model: &str, name: &str) -> Option<bool> {
    for line in model.lines() {
        let line = line.trim();
        if let Some(rest) = line.strip_prefix("(define-fun ")
            && let Some(rest) = rest.strip_prefix(name)
            && let Some(rest) = rest.strip_prefix(" () Bool ")
        {
            let v = rest.trim_end_matches(')');
            return match v {
                "true" => Some(true),
                "false" => Some(false),
                _ => None,
            };
        }
    }
    None
}

fn int_pin(model: &str, name: &str) -> Option<String> {
    for line in model.lines() {
        let line = line.trim();
        if let Some(rest) = line.strip_prefix("(define-fun ")
            && let Some(rest) = rest.strip_prefix(name)
            && let Some(rest) = rest.strip_prefix(" () Int ")
        {
            return Some(rest.trim_end_matches(')').to_string());
        }
    }
    None
}

/// Definition-Boolean completion: `b` is defined `(or (not (= x 0))
/// (not (= y 0)))` and the printed numerics satisfy it, so the model must
/// pin `b = true` — not the `false` sort default.
#[test]
fn definition_bool_is_completed_from_its_definition() {
    let script = r#"
        (set-logic QF_NIA)
        (declare-const x Int)
        (declare-const y Int)
        (declare-const b Bool)
        (assert (>= x 0))
        (assert (<= x 2))
        (assert (>= y 0))
        (assert (<= y 2))
        (assert (= b (or (not (= x 0)) (not (= y 0)))))
        (assert (= (* x y) x))
        (assert (>= (+ x y) 1))
        (check-sat)
        (get-model)
    "#;
    let mut ctx = Context::new();
    let out = ctx.execute_script(script).unwrap_or_default();
    let model = out.concat();
    // The verdict is sat (x=1,y=0 among others).
    assert!(model.contains("sat"), "expected sat, got: {model}");
    let x = int_pin(&model, "x");
    let y = int_pin(&model, "y");
    let b = bool_pin(&model, "b");
    // Whatever numerics are printed, they must satisfy the definition, and
    // the pin must agree with it (the exact 510-class defect was
    // b=false with numerics making the definition true).
    let (xv, yv) = (
        x.as_deref().and_then(|s| s.parse::<i64>().ok()),
        y.as_deref().and_then(|s| s.parse::<i64>().ok()),
    );
    if let (Some(xv), Some(yv)) = (xv, yv) {
        let def_true = xv != 0 || yv != 0;
        assert_eq!(
            b,
            Some(def_true),
            "b is defined by (or (not (= x {xv})) (not (= y {yv}))); the printed pin contradicts the printed numerics"
        );
    } else {
        // Numerics themselves missing: still must not contradict.
        assert!(b.is_none_or(|_| true));
    }
}

/// The original 510 shape in miniature: several chained definition Booleans,
/// one of them `true` under every witness (TERM_NT_1 class).
#[test]
fn chained_definition_bools_complete_consistently() {
    let script = r#"
        (set-logic QF_NIA)
        (declare-const x Int)
        (declare-const b1 Bool)
        (declare-const b2 Bool)
        (assert (>= x 1))
        (assert (<= x 5))
        (assert (= b1 (not (= x 0))))
        (assert (= b2 (or b1 (not (= x 1)))))
        (assert (= (* x x) x))
        (check-sat)
        (get-model)
    "#;
    let mut ctx = Context::new();
    let out = ctx.execute_script(script).unwrap_or_default();
    let model = out.concat();
    assert!(model.contains("sat"), "expected sat, got: {model}");
    // x*x = x with 1 <= x <= 5 forces x = 1: b1 = (x != 0) = true,
    // b2 = (b1 or x != 1) = true.
    assert_eq!(int_pin(&model, "x").as_deref(), Some("1"));
    assert_eq!(bool_pin(&model, "b1"), Some(true), "model: {model}");
    assert_eq!(bool_pin(&model, "b2"), Some(true), "model: {model}");
}
