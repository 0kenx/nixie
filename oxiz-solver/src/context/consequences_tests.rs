//! Regression tests for the closing *restore* check of
//! `(get-consequences ...)` — see [`super::consequences_restore_state`].

use super::{Context, SolverResult, consequences_restore_state};

// ---------------------------------------------------------------
// `(get-consequences ...)` closing-restore honesty
// ---------------------------------------------------------------

/// The restore check's verdict used to be discarded and `sat` cached
/// unconditionally, so a restore that came back `unknown` (budget consumed
/// by the certification checks) left the context in `sat` mode with no
/// model behind it.  Only a reproduced `sat` may be published as `sat` or
/// cached; every other verdict degrades to `unknown` and caches nothing.
#[test]
fn consequences_restore_state_only_trusts_sat() {
    assert_eq!(
        consequences_restore_state(SolverResult::Sat),
        ("sat", Some(SolverResult::Sat))
    );
    assert_eq!(
        consequences_restore_state(SolverResult::Unknown),
        ("unknown", None)
    );
    // An `unsat` restore contradicts the opening `sat` of the very same
    // assumption set: the checks disagree, so neither verdict is published.
    assert_eq!(
        consequences_restore_state(SolverResult::Unsat),
        ("unknown", None)
    );
}

/// End-to-end: with the restore check succeeding (no resource limits), the
/// query reports `sat`, the implication list is produced, and the context
/// stays in `sat` mode so a following `(get-model)` is served.
#[test]
fn get_consequences_sat_restore_keeps_model_available() {
    let mut ctx = Context::new();
    let script = r#"
        (set-logic QF_UF)
        (declare-const p Bool)
        (declare-const q Bool)
        (assert p)
        (assert (=> p q))
        (get-consequences () (p q))
        (get-model)
    "#;
    let output = ctx
        .execute_script(script)
        .expect("test operation should succeed");
    assert_eq!(output.len(), 3, "unexpected output: {output:?}");
    assert_eq!(output[0], "sat");
    assert!(output[1].contains("p"), "unexpected list: {}", output[1]);
    assert!(output[1].contains("q"), "unexpected list: {}", output[1]);
    assert_eq!(ctx.last_result, Some(SolverResult::Sat));
    assert!(
        !output[2].contains("error"),
        "get-model must be available after a `sat` restore: {}",
        output[2]
    );
}

/// A degraded restore must leave `assert` mode, so the model queries answer
/// "not available" rather than reading a stale interpretation.  Driven
/// through the same state transition the query performs.
#[test]
fn degraded_consequences_restore_makes_model_unavailable() {
    let mut ctx = Context::new();
    let script = r#"
        (set-logic QF_UF)
        (declare-const p Bool)
        (assert p)
        (check-sat)
    "#;
    let output = ctx
        .execute_script(script)
        .expect("test operation should succeed");
    assert_eq!(output, vec!["sat".to_string()]);
    assert_eq!(ctx.last_result, Some(SolverResult::Sat));

    let (status, cached) = consequences_restore_state(SolverResult::Unknown);
    assert_eq!((status, cached), ("unknown", None));
    ctx.invalidate_last_check();

    assert_eq!(ctx.last_result, None);
    let after = ctx
        .execute_script("(get-model)")
        .expect("test operation should succeed");
    assert_eq!(after.len(), 1);
    assert!(
        after[0].contains("error"),
        "a degraded restore must not serve a model: {}",
        after[0]
    );
}
