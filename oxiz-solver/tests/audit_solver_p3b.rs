//! Audit regression tests for the `solver-p3b` package.
//!
//! Each test pins a specific defect from the audit so a regression cannot slip
//! back in silently.

use oxiz_solver::{Context, SolverResult};

/// Finding: array pre-check treated an `Eq` nested inside a Boolean equality as
/// an asserted read-over-write fact.
///
/// `(= p (= (select (store a 3 5) 3) 6))` binds a Boolean `p` to the *value* of
/// the inner select-equality.  The inner equality is NOT asserted on its own –
/// the whole formula is satisfiable with `p = false`.  The old collector
/// recursed into the outer equality's operands in a positive context and
/// recorded the inner `select(store a 3 5, 3) = 6` as an asserted fact, then the
/// store-select axiom (`5 != 6`) fired and returned a spurious UNSAT.
///
/// The pre-check must NOT report UNSAT here.
#[test]
fn array_nested_eq_polarity_not_unsat() {
    let mut ctx = Context::new();
    ctx.set_logic("QF_AUFLIA");

    let int_sort = ctx.terms.sorts.int_sort;
    let arr_sort = ctx.terms.sorts.array(int_sort, int_sort);
    let a = ctx.declare_const("a", arr_sort);
    let p = ctx.declare_const("p", ctx.terms.sorts.bool_sort);

    let three = ctx.terms.mk_int(3);
    let five = ctx.terms.mk_int(5);
    let six = ctx.terms.mk_int(6);

    let store = ctx.terms.mk_store(a, three, five);
    let select = ctx.terms.mk_select(store, three);
    let inner_eq = ctx.terms.mk_eq(select, six); // (= (select (store a 3 5) 3) 6)
    let outer = ctx.terms.mk_eq(p, inner_eq); // (= p <inner_eq>)
    ctx.assert(outer);

    let result = ctx.check_sat();
    assert_ne!(
        result,
        SolverResult::Unsat,
        "nested Boolean equality must not be mis-collected as an asserted \
         read-over-write fact -- the formula is SAT with p = false"
    );
}

/// Sanity companion: a genuinely-asserted store/select contradiction is still
/// caught.  `(= (select (store a 3 5) 3) 6)` asserted directly IS unsat because
/// the read-over-write axiom forces the select to equal 5.
#[test]
fn array_direct_store_select_contradiction_is_unsat() {
    let mut ctx = Context::new();
    ctx.set_logic("QF_AUFLIA");

    let int_sort = ctx.terms.sorts.int_sort;
    let arr_sort = ctx.terms.sorts.array(int_sort, int_sort);
    let a = ctx.declare_const("a", arr_sort);

    let three = ctx.terms.mk_int(3);
    let five = ctx.terms.mk_int(5);
    let six = ctx.terms.mk_int(6);

    let store = ctx.terms.mk_store(a, three, five);
    let select = ctx.terms.mk_select(store, three);
    let eq = ctx.terms.mk_eq(select, six);
    ctx.assert(eq);

    let result = ctx.check_sat();
    assert_eq!(
        result,
        SolverResult::Unsat,
        "select(store(a,3,5),3) = 6 contradicts the read-over-write axiom"
    );
}

/// Finding: `(get-info :all-statistics)` always errored because the handler
/// compared the (colon-stripped) keyword against a spelling that still carried
/// the leading colon, so no branch ever matched.  It must now succeed, and the
/// mandatory SMT-LIB flags must be answered rather than erroring.
#[test]
fn get_info_all_statistics_and_mandatory_flags() {
    let mut ctx = Context::new();
    let script = r#"
        (get-info :all-statistics)
        (get-info :name)
        (get-info :version)
        (get-info :authors)
        (get-info :error-behavior)
    "#;
    let out = ctx.execute_script(script).expect("script runs");
    assert_eq!(out.len(), 5);
    // :all-statistics returns the statistics tuple, never an error.
    assert!(
        out[0].contains(":decisions") && !out[0].contains("error"),
        "get-info :all-statistics must return statistics, got: {}",
        out[0]
    );
    assert!(
        out[1].contains(":name") && !out[1].contains("error"),
        "{}",
        out[1]
    );
    assert!(
        out[2].contains(":version") && !out[2].contains("error"),
        "{}",
        out[2]
    );
    assert!(
        out[3].contains(":authors") && !out[3].contains("error"),
        "{}",
        out[3]
    );
    assert!(
        out[4].contains(":error-behavior") && !out[4].starts_with("(error"),
        "{}",
        out[4]
    );
}

/// Finding: `print-success` was reported as defaulting to `true` even though
/// the command loop never emits the `success` acknowledgement.  The reported
/// default must now match reality (the runner does not print success).
#[test]
fn get_option_print_success_reports_honest_default() {
    let mut ctx = Context::new();
    let out = ctx
        .execute_script("(get-option :print-success)")
        .expect("script runs");
    assert_eq!(out.len(), 1);
    assert_eq!(
        out[0], "false",
        "print-success default must reflect that no success line is emitted"
    );
}

/// Finding: `check-sat-assuming` was emulated with push/assert/pop, so a
/// following `get-value` observed the popped state (no model).  It must now
/// preserve the model produced under the assumptions.
#[test]
fn check_sat_assuming_preserves_model_for_get_value() {
    let mut ctx = Context::new();
    let script = r#"
        (set-logic QF_UF)
        (declare-const p Bool)
        (declare-const q Bool)
        (assert p)
        (check-sat-assuming (q))
        (get-value (p q))
    "#;
    let out = ctx.execute_script(script).expect("script runs");
    assert_eq!(out.len(), 2);
    assert_eq!(out[0], "sat");
    // After a Sat check-sat-assuming, get-value must see a real model, not an
    // error from popped state.
    assert!(
        !out[1].contains("error") && out[1].contains("true"),
        "get-value after check-sat-assuming must observe the model (p = true), \
         got: {}",
        out[1]
    );
}
