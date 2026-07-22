//! End-to-end tests for model-value output completeness, the `:print-success`
//! option, and named `(get-unsat-core)` minimization, all driven through
//! [`Context::execute_script`].

use oxiz_solver::Context;

fn run(script: &str) -> Vec<String> {
    let mut ctx = Context::new();
    ctx.execute_script(script)
        .expect("script should parse and run")
}

// ---------------------------------------------------------------------
// get-model must print valid SMT-LIB values (never the invalid `?`) for
// FP, Array, and uninterpreted-sort constants.
// ---------------------------------------------------------------------

#[test]
fn get_model_uninterpreted_sort_value_is_valid() {
    let output = run(r#"
        (set-logic QF_UF)
        (declare-sort S 0)
        (declare-const x S)
        (assert true)
        (check-sat)
        (get-model)
    "#);
    assert_eq!(output[0], "sat");
    let model = &output[1];
    assert!(!model.contains('?'), "model has invalid ? value:\n{model}");
    assert!(
        model.contains("@uc_S_"),
        "expected an uninterpreted-sort witness:\n{model}"
    );
}

#[test]
fn get_model_distinct_uninterpreted_constants_get_distinct_witnesses() {
    let output = run(r#"
        (set-logic QF_UF)
        (declare-sort S 0)
        (declare-const x S)
        (declare-const y S)
        (assert true)
        (check-sat)
        (get-model)
    "#);
    assert_eq!(output[0], "sat");
    let model = &output[1];
    assert!(
        model.contains("@uc_S_0") && model.contains("@uc_S_1"),
        "distinct uninterpreted constants should get distinct witnesses:\n{model}"
    );
}

#[test]
fn get_model_array_value_is_valid() {
    let output = run(r#"
        (set-logic QF_ALIA)
        (declare-const arr (Array Int Int))
        (assert true)
        (check-sat)
        (get-model)
    "#);
    assert_eq!(output[0], "sat");
    let model = &output[1];
    assert!(!model.contains('?'), "model has invalid ? value:\n{model}");
    assert!(
        model.contains("as const"),
        "expected a constant-array value:\n{model}"
    );
}

#[test]
fn get_model_fp_value_is_valid() {
    let output = run(r#"
        (set-logic QF_FP)
        (declare-const f (_ FloatingPoint 8 24))
        (assert true)
        (check-sat)
        (get-model)
    "#);
    assert_eq!(output[0], "sat");
    let model = &output[1];
    assert!(!model.contains('?'), "model has invalid ? value:\n{model}");
    assert!(
        model.contains("+zero"),
        "expected a concrete FP default value:\n{model}"
    );
}

// ---------------------------------------------------------------------
// :print-success — emit `success` after each silently-succeeding command.
// ---------------------------------------------------------------------

#[test]
fn print_success_emits_acknowledgements() {
    let output = run(r#"
        (set-option :print-success true)
        (declare-const p Bool)
        (assert p)
        (check-sat)
    "#);
    // The enabling set-option, the declaration, and the assertion each
    // acknowledge; check-sat reports its own result instead.
    assert_eq!(
        output,
        vec![
            "success".to_string(),
            "success".to_string(),
            "success".to_string(),
            "sat".to_string(),
        ]
    );
}

#[test]
fn print_success_is_off_by_default() {
    let output = run(r#"
        (declare-const p Bool)
        (assert p)
        (check-sat)
    "#);
    assert_eq!(output, vec!["sat".to_string()]);
}

#[test]
fn print_success_get_option_reflects_enabled_state() {
    let output = run(r#"
        (set-option :print-success true)
        (get-option :print-success)
    "#);
    // set-option acknowledges; get-option reports the real `true`.
    assert_eq!(output, vec!["success".to_string(), "true".to_string()]);
}

// ---------------------------------------------------------------------
// (get-unsat-core) reports the named subset actually used in the
// refutation, minimized to exclude irrelevant named assertions.
// ---------------------------------------------------------------------

#[test]
fn named_unsat_core_reports_used_named_assertions() {
    let output = run(r#"
        (set-option :produce-unsat-cores true)
        (set-logic QF_UF)
        (declare-const p Bool)
        (assert (! p :named a1))
        (assert (! (not p) :named a2))
        (check-sat)
        (get-unsat-core)
    "#);
    assert_eq!(output[0], "unsat");
    let core = &output[1];
    assert!(core.contains("a1"), "core should contain a1: {core}");
    assert!(core.contains("a2"), "core should contain a2: {core}");
}

#[test]
fn unsat_core_excludes_irrelevant_named_assertion() {
    // `a3` (asserting `q`) plays no part in the `p ∧ ¬p` contradiction, so
    // deletion-based minimization must drop it from the reported core.
    let output = run(r#"
        (set-option :produce-unsat-cores true)
        (set-logic QF_UF)
        (declare-const p Bool)
        (declare-const q Bool)
        (assert (! p :named a1))
        (assert (! (not p) :named a2))
        (assert (! q :named a3))
        (check-sat)
        (get-unsat-core)
    "#);
    assert_eq!(output[0], "unsat");
    let core = &output[1];
    assert!(core.contains("a1"), "core should contain a1: {core}");
    assert!(core.contains("a2"), "core should contain a2: {core}");
    assert!(
        !core.contains("a3"),
        "minimization must exclude the irrelevant a3: {core}"
    );
}
