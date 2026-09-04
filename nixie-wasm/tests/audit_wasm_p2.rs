//! Regression tests for audit package wasm-p2 (nixie-wasm/src/js_api/optimize.rs).
//!
//! Covers two previously-confirmed critical findings:
//!
//! 1. `minimize`/`maximize`/`assertSoft` were silently dropped (the parser
//!    balanced-paren-skipped `(minimize ...)`/`(maximize ...)`/
//!    `(assert-soft ...)` since `Command` has no such variants), and
//!    `optimize()` labeled any plain `sat` result `"optimal"` regardless of
//!    whether an objective was actually optimized.
//! 2. `computeInterpolant` returned `(and <partition A>)` as a fake
//!    "interpolant" for any UNSAT problem, which is not a valid Craig
//!    interpolant in general.
//!
//! Run with `wasm-pack test --node` (or `--headless --chrome`, matching the
//! other files in this directory).

#![cfg(target_arch = "wasm32")]

use nixie_wasm::*;
use wasm_bindgen_test::*;

wasm_bindgen_test_configure!(run_in_node_js);

fn get_str(obj: &wasm_bindgen::JsValue, key: &str) -> Option<String> {
    js_sys::Reflect::get(obj, &key.into())
        .ok()
        .and_then(|v| v.as_string())
}

// ======== minimize / maximize actually change the optimum (not silently dropped) ========

/// Regression: `minimize` must actually constrain the reported optimum.
/// Previously `minimize()` was a no-op (the command was parsed and
/// discarded), so `optimize()` would report an arbitrary satisfying value
/// mislabeled `"optimal"`.
#[wasm_bindgen_test]
fn test_minimize_actually_optimizes() {
    let mut solver = WasmSolver::new();
    solver.set_logic("QF_LIA");
    solver.declare_const("x", "Int").unwrap();
    solver.assert_formula("(>= x 0)").unwrap();
    solver.assert_formula("(<= x 100)").unwrap();
    solver.minimize("x").unwrap();

    let result = solver.optimize().unwrap();
    assert_eq!(get_str(&result, "status").as_deref(), Some("optimal"));

    let model = js_sys::Reflect::get(&result, &"model".into()).unwrap();
    let x_entry = js_sys::Reflect::get(&model, &"x".into()).unwrap();
    let x_value = get_str(&x_entry, "value").unwrap();
    assert_eq!(
        x_value, "0",
        "minimize(x) with x in [0,100] must yield x = 0"
    );
}

/// Regression: `maximize` must actually constrain the reported optimum.
#[wasm_bindgen_test]
fn test_maximize_actually_optimizes() {
    let mut solver = WasmSolver::new();
    solver.set_logic("QF_LIA");
    solver.declare_const("x", "Int").unwrap();
    solver.assert_formula("(>= x 0)").unwrap();
    solver.assert_formula("(<= x 100)").unwrap();
    solver.maximize("x").unwrap();

    let result = solver.optimize().unwrap();
    assert_eq!(get_str(&result, "status").as_deref(), Some("optimal"));

    let model = js_sys::Reflect::get(&result, &"model".into()).unwrap();
    let x_entry = js_sys::Reflect::get(&model, &"x".into()).unwrap();
    let x_value = get_str(&x_entry, "value").unwrap();
    assert_eq!(
        x_value, "100",
        "maximize(x) with x in [0,100] must yield x = 100"
    );
}

/// Regression: with no objectives, a plain sat result is still reported (the
/// vacuous case), but this must not be confused with a real optimization.
#[wasm_bindgen_test]
fn test_optimize_without_objectives_is_plain_sat() {
    let mut solver = WasmSolver::new();
    solver.set_logic("QF_UF");
    solver.declare_const("p", "Bool").unwrap();
    solver.assert_formula("p").unwrap();

    let result = solver.optimize().unwrap();
    assert_eq!(get_str(&result, "status").as_deref(), Some("optimal"));
}

/// Regression: an unsatisfiable problem with an objective must be reported
/// as `"unsat"`, not silently coerced to `"optimal"`.
#[wasm_bindgen_test]
fn test_minimize_reports_unsat() {
    let mut solver = WasmSolver::new();
    solver.set_logic("QF_LIA");
    solver.declare_const("x", "Int").unwrap();
    solver.assert_formula("(> x 0)").unwrap();
    solver.assert_formula("(< x 0)").unwrap();
    solver.minimize("x").unwrap();

    let result = solver.optimize().unwrap();
    assert_eq!(get_str(&result, "status").as_deref(), Some("unsat"));
}

/// Regression: `minimize`/`maximize` must validate the objective's sort
/// (Int/Real), rather than silently accepting anything (which the old
/// paren-skipping "parser" effectively did).
#[wasm_bindgen_test]
fn test_minimize_rejects_non_arithmetic_sort() {
    let mut solver = WasmSolver::new();
    solver.set_logic("QF_UF");
    solver.declare_const("p", "Bool").unwrap();

    let result = solver.minimize("p");
    assert!(
        result.is_err(),
        "minimize() on a Bool term must be rejected"
    );
}

/// Regression: lexicographic priority order (first objective wins ties) is
/// honored via the real `Optimizer`.
#[wasm_bindgen_test]
fn test_lexicographic_priority_order() {
    let mut solver = WasmSolver::new();
    solver.set_logic("QF_LIA");
    solver.declare_const("x", "Int").unwrap();
    solver.declare_const("y", "Int").unwrap();
    solver.assert_formula("(>= x 0)").unwrap();
    solver.assert_formula("(<= x 10)").unwrap();
    solver.assert_formula("(>= y 0)").unwrap();
    solver.assert_formula("(<= y 10)").unwrap();
    solver.assert_formula("(<= (+ x y) 10)").unwrap();

    // Highest priority: maximize x. Lower priority: maximize y.
    solver.maximize("x").unwrap();
    solver.maximize("y").unwrap();

    let result = solver.optimize().unwrap();
    assert_eq!(get_str(&result, "status").as_deref(), Some("optimal"));

    let model = js_sys::Reflect::get(&result, &"model".into()).unwrap();
    let x_entry = js_sys::Reflect::get(&model, &"x".into()).unwrap();
    let x_value = get_str(&x_entry, "value").unwrap();
    assert_eq!(
        x_value, "10",
        "x must be maximized first, to its bound of 10"
    );
}

// ======== assertSoft / MaxSMT actually influences the result ========

/// Regression: `assertSoft` must actually make the solver prefer satisfying
/// the soft constraint. Previously `assertSoft` was a no-op.
#[wasm_bindgen_test]
fn test_assert_soft_prefers_satisfying_high_weight() {
    let mut solver = WasmSolver::new();
    solver.set_logic("QF_UF");
    solver.declare_const("p", "Bool").unwrap();
    solver.declare_const("q", "Bool").unwrap();
    // Hard constraint: exactly one of p, q may be true (not both, not neither
    // would also be allowed by "or", so pin down with xor-like constraints).
    solver.assert_formula("(or p q)").unwrap();
    solver.assert_formula("(not (and p q))").unwrap();

    // Prefer p over q by a large weight margin.
    solver.assert_soft("p", "100").unwrap();
    solver.assert_soft("q", "1").unwrap();

    let result = solver.optimize().unwrap();
    assert_eq!(get_str(&result, "status").as_deref(), Some("optimal"));

    let model = js_sys::Reflect::get(&result, &"model".into()).unwrap();
    let p_entry = js_sys::Reflect::get(&model, &"p".into()).unwrap();
    let p_value = get_str(&p_entry, "value").unwrap();
    assert_eq!(
        p_value, "true",
        "the higher-weight soft constraint must be satisfied"
    );
}

/// Regression: `assertSoft` must validate that the formula is Bool-sorted.
#[wasm_bindgen_test]
fn test_assert_soft_rejects_non_bool_sort() {
    let mut solver = WasmSolver::new();
    solver.set_logic("QF_LIA");
    solver.declare_const("x", "Int").unwrap();

    let result = solver.assert_soft("x", "5");
    assert!(
        result.is_err(),
        "assertSoft() on a non-Bool term must be rejected"
    );
}

// ======== computeInterpolant: honest failure instead of a fake interpolant ========

/// Regression: `computeInterpolant` must never return
/// `(and <partition A>)` (or any other fabricated non-interpolant) as a
/// successful result. It must fail honestly until real Craig interpolation
/// is wired up.
#[wasm_bindgen_test]
fn test_compute_interpolant_never_returns_fake_result() {
    let mut solver = WasmSolver::new();
    solver.set_option("produce-proofs", "true");
    solver.set_logic("QF_LIA");
    solver.declare_const("x", "Int").unwrap();
    solver.declare_const("y", "Int").unwrap();

    let result = solver.compute_interpolant(
        vec!["(> x 0)".to_string()],
        vec!["(< y 0)".to_string(), "(= x y)".to_string()],
    );

    // The old implementation returned `Ok("(and (> x 0))")` here – a
    // non-interpolant. The fix must not return `Ok` with a fabricated
    // formula; an honest error is required instead.
    assert!(
        result.is_err(),
        "computeInterpolant must not fabricate an interpolant; got Ok({:?})",
        result.ok()
    );
}

/// Regression: `computeInterpolant` must still validate its preconditions
/// (non-UNSAT combined formula) before reporting the interpolation-specific
/// error, so callers get an accurate diagnosis.
#[wasm_bindgen_test]
fn test_compute_interpolant_rejects_sat_combination() {
    let mut solver = WasmSolver::new();
    solver.set_option("produce-proofs", "true");
    solver.set_logic("QF_LIA");
    solver.declare_const("x", "Int").unwrap();

    let result =
        solver.compute_interpolant(vec!["(> x 0)".to_string()], vec!["(> x 1)".to_string()]);
    assert!(
        result.is_err(),
        "a satisfiable combination cannot be interpolated"
    );
}
