//! Regression tests for audit package wasm-p4.
//!
//! Covers the two remaining confirmed findings assigned to this package's
//! wasm-final wave that aren't already exercised elsewhere:
//!
//! - `nixie-wasm/src/js_api/diagnostics.rs`: `getStatistics().num_assertions`
//!   was always `0`, because it counted occurrences of the substring
//!   `"(assert"` in `Context::format_assertions()`'s output -- but that
//!   formatter prints each assertion's *term* only (e.g. `"(> x 0)"`), never
//!   wrapped in an `(assert ...)` s-expression, so the substring never
//!   matched regardless of how many assertions were actually present.
//! - `nixie-wasm/src/js_api/solver_core.rs`: `cancel()`'s flag was never
//!   observed by `checkSat()`/`checkSatAsync()` (only the chunked
//!   `executeAsync`/`executeWithProgress` loops consulted it), so a
//!   "cancelled" solver would still run a full `checkSat()` to completion.
//!   A native (non-wasm32) regression test for this already exists at
//!   `nixie-wasm/src/js_api/solver_core.rs`'s `cancel_tests` module (since
//!   `checkSat()` returns a plain `String` and never touches `js_sys`); the
//!   case here additionally confirms `getStatistics()`'s `cancelled` field
//!   agrees, which does require a real wasm32/JS engine since
//!   `getStatistics()` unconditionally builds a `js_sys::Object`.
//!
//! Run with `wasm-pack test --node` (matching `audit_wasm_p2.rs`).

#![cfg(target_arch = "wasm32")]

use nixie_wasm::*;
use wasm_bindgen_test::*;

wasm_bindgen_test_configure!(run_in_node_js);

fn get_f64(obj: &wasm_bindgen::JsValue, key: &str) -> Option<f64> {
    js_sys::Reflect::get(obj, &key.into())
        .ok()
        .and_then(|v| v.as_f64())
}

fn get_bool(obj: &wasm_bindgen::JsValue, key: &str) -> Option<bool> {
    js_sys::Reflect::get(obj, &key.into())
        .ok()
        .and_then(|v| v.as_bool())
}

/// Regression: `num_assertions` must reflect the real assertion count, not
/// always report `0`.
#[wasm_bindgen_test]
fn test_get_statistics_num_assertions_counts_real_assertions() {
    let mut solver = WasmSolver::new();
    solver.set_logic("QF_LIA");
    solver.declare_const("x", "Int").unwrap();
    solver.declare_const("y", "Int").unwrap();

    let stats0 = solver.get_statistics().unwrap();
    assert_eq!(
        get_f64(&stats0, "num_assertions"),
        Some(0.0),
        "no assertions yet"
    );

    solver.assert_formula("(> x 0)").unwrap();
    let stats1 = solver.get_statistics().unwrap();
    assert_eq!(
        get_f64(&stats1, "num_assertions"),
        Some(1.0),
        "one assertion should be counted, not 0"
    );

    solver.assert_formula("(> y 0)").unwrap();
    solver.assert_formula("(< (+ x y) 100)").unwrap();
    let stats3 = solver.get_statistics().unwrap();
    assert_eq!(
        get_f64(&stats3, "num_assertions"),
        Some(3.0),
        "three assertions should be counted"
    );
}

/// Regression: `getStatistics().cancelled` must reflect a pending
/// cancellation, and a cancelled solver's `checkSat()` must not silently
/// report "sat"/"unsat".
#[wasm_bindgen_test]
fn test_cancel_is_observed_by_check_sat_and_statistics() {
    let mut solver = WasmSolver::new();
    solver.set_logic("QF_UF");
    solver.declare_const("p", "Bool").unwrap();
    solver.assert_formula("p").unwrap();

    let stats_before = solver.get_statistics().unwrap();
    assert_eq!(get_bool(&stats_before, "cancelled"), Some(false));

    solver.cancel();
    let stats_after = solver.get_statistics().unwrap();
    assert_eq!(get_bool(&stats_after, "cancelled"), Some(true));

    assert_eq!(
        solver.check_sat(),
        "unknown",
        "a cancelled solver must not run checkSat() to completion and \
         report a real sat/unsat verdict"
    );
}
