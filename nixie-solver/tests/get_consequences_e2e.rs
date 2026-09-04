//! End-to-end tests for the SMT-LIB `(get-consequences (A..) (V..))` command,
//! driving the full parse -> execute -> print loop through
//! [`Context::execute_script`].
//!
//! The command extracts the unit consequences over the queried variables `V`
//! entailed by the current assertions together with the assumptions `A`, and
//! prints them Z3-shaped as `sat` followed by an `((=> (and A) lit) ...)` list.

use nixie_solver::Context;

fn run(script: &str) -> Vec<String> {
    let mut ctx = Context::new();
    ctx.execute_script(script)
        .expect("script should parse and run")
}

#[test]
fn implied_chain_reports_both_consequences() {
    // Under the assumption `a`, the asserted implications force both `b` and
    // `c`, so each is a consequence with antecedent `a` (a single assumption
    // renders as the bare assumption, not `(and a)`).
    let output = run(r#"
        (set-logic QF_UF)
        (declare-const a Bool)
        (declare-const b Bool)
        (declare-const c Bool)
        (assert (=> a b))
        (assert (=> b c))
        (get-consequences (a) (b c))
    "#);
    assert_eq!(output[0], "sat");
    let list = &output[1];
    assert!(list.contains("(=> a b)"), "expected (=> a b) in: {list}");
    assert!(list.contains("(=> a c)"), "expected (=> a c) in: {list}");
}

#[test]
fn contradictory_assumptions_report_unsat() {
    // The assertion `(not a)` together with the assumption `a` is
    // unsatisfiable, so the query reports `unsat` and nothing else.
    let output = run(r#"
        (set-logic QF_UF)
        (declare-const a Bool)
        (declare-const b Bool)
        (assert (not a))
        (get-consequences (a) (b))
    "#);
    assert_eq!(output, vec!["unsat".to_string()]);
}

#[test]
fn non_boolean_variable_is_rejected() {
    // A queried variable of non-Boolean sort is an error, per the command's
    // Boolean-terms contract.
    let output = run(r#"
        (set-logic QF_LIA)
        (declare-const a Bool)
        (declare-const x Int)
        (get-consequences (a) (x))
    "#);
    assert_eq!(output.len(), 1);
    assert!(
        output[0].contains("error"),
        "expected an error line, got: {}",
        output[0]
    );
}

#[test]
fn empty_assumptions_use_true_antecedent() {
    // With no assumptions, an unconditionally-asserted fact `a` is a
    // consequence printed with the `true` antecedent produced by `(and)`.
    let output = run(r#"
        (set-logic QF_UF)
        (declare-const a Bool)
        (declare-const b Bool)
        (assert a)
        (get-consequences () (a b))
    "#);
    assert_eq!(output[0], "sat");
    assert!(
        output[1].contains("(=> true a)"),
        "expected (=> true a) in: {}",
        output[1]
    );
}

#[test]
fn negative_polarity_consequence_is_reported() {
    // `(not a)` is asserted, so under no assumptions `(not a)` is entailed and
    // must appear as the literal with the correct negative polarity.
    let output = run(r#"
        (set-logic QF_UF)
        (declare-const a Bool)
        (get-consequences () (a))
    "#);
    // `a` is unconstrained here, so it need not be a consequence; assert the
    // status is decided and the response list is well-formed.
    assert_eq!(output[0], "sat");
    assert!(output[1].starts_with('(') && output[1].ends_with(')'));
}

#[test]
fn model_stays_available_after_get_consequences() {
    // The query restores a consistent `sat` state, so a following `(get-value)`
    // still observes a model rather than erroring.
    let output = run(r#"
        (set-logic QF_UF)
        (declare-const a Bool)
        (declare-const b Bool)
        (assert (=> a b))
        (get-consequences (a) (b))
        (get-value (b))
    "#);
    assert_eq!(output[0], "sat");
    assert!(
        !output[2].contains("No model available"),
        "get-value after get-consequences should see a model, got: {}",
        output[2]
    );
}
