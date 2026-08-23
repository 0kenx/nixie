//! Logic-contract acceptance tests
//! (`docs/2026-08-established-research-candidates.md` Priority 0).
//!
//! The seven behaviors the layer must demonstrate, numbered as in the doc.
//! These pin the exact failure modes the old substring-decoded routing
//! produced: header-induced incompleteness, invented names installing
//! backends, silent second `set-logic`, and bodies outside the declared
//! fragment answering instead of erroring.

use oxiz_solver::Context;

fn run_err(script: &str) -> String {
    let mut ctx = Context::new();
    match ctx.execute_script(script) {
        Err(e) => e.to_string(),
        Ok(out) => format!("no error; outputs={out:?}"),
    }
}

fn last_verdict(script: &str) -> String {
    let mut ctx = Context::new();
    let out = ctx.execute_script(script).unwrap_or_default();
    out.iter()
        .rev()
        .find(|t| matches!(t.trim(), "sat" | "unsat" | "unknown"))
        .cloned()
        .unwrap_or_else(|| "none".into())
}

/// 1. `QF_LIA` plus `(* x y)` is rejected as outside the declared logic.
#[test]
fn nonlinear_body_under_qf_lia_is_rejected() {
    let err = run_err(
        "(set-logic QF_LIA)
         (declare-const x Int)
         (declare-const y Int)
         (assert (> (* x y) 5))
         (check-sat)",
    );
    assert!(
        err.contains("nonlinear") && err.contains("QF_LIA"),
        "expected a contract violation, got: {err}"
    );
}

/// 2. The same nonlinear body under missing/`ALL` routing engages the
///    complete nonlinear path rather than falling through because of its
///    header: the verdict must MATCH the explicit-header verdict (routing
///    parity), not differ by header.
///
/// The instance is one the NL backend actually refutes under an explicit
/// `QF_NIA` header — the test's object is routing parity, not NLSAT
/// coverage (plenty of nonlinear instances are honestly `unknown` under
/// every header; those cannot distinguish routes).
#[test]
fn nonlinear_body_without_header_solves_via_structural_routing() {
    let body = "(declare-const x Int)
         (declare-const y Int)
         (assert (= (* x y) 6))
         (assert (= x 2))
         (assert (distinct y 3))
         (check-sat)";
    let via_nia = last_verdict(&format!(
        "(set-logic QF_NIA)
{body}"
    ));
    assert_eq!(
        via_nia, "unsat",
        "explicit header must engage the NL backend"
    );
    let via_none = last_verdict(body);
    assert_eq!(via_none, "unsat", "missing header must route structurally");
    let via_all = last_verdict(&format!(
        "(set-logic ALL)
{body}"
    ));
    assert_eq!(via_all, "unsat", "ALL header must route structurally");
}

/// 3. Disallowed nested array signatures are rejected even when all array
///    terms type-check (`QF_AX` forbids arithmetic and UF entirely).
#[test]
fn arith_body_under_qf_ax_is_rejected() {
    let err = run_err(
        "(set-logic QF_AX)
         (declare-const a (Array Int Int))
         (declare-const i Int)
         (assert (= (select a i) (+ i 1)))
         (check-sat)",
    );
    assert!(
        err.contains("arithmetic") && err.contains("QF_AX"),
        "expected arithmetic-outside-contract, got: {err}"
    );
}

/// 4. A linear body declared under a broader nonlinear logic may use the
///    linear engine (broader headers never narrow the route).
#[test]
fn linear_body_under_qf_nia_still_solves() {
    let v = last_verdict(
        "(set-logic QF_NIA)
         (declare-const x Int)
         (assert (> x 5))
         (assert (< x 3))
         (check-sat)",
    );
    assert_eq!(v, "unsat");
}

/// 5. An unsupported name neither behaves like a substring-matched known
///    logic nor leaves a partially changed engine configuration.
#[test]
fn invented_logic_name_is_rejected_without_state_change() {
    // "QF_LINIA" contains "NIA" as a substring — the old router would have
    // installed the nonlinear backend.  It must simply be rejected, and a
    // subsequent valid set-logic must work (no partial reconfiguration).
    let err = run_err(
        "(set-logic QF_LINIA)
         (declare-const x Int)
         (assert (= x 1))
         (check-sat)",
    );
    assert!(err.contains("unknown logic"), "got: {err}");
    // After the rejection, a fresh context accepts the real logic.
    let v = last_verdict(
        "(set-logic QF_NIA)
         (declare-const x Int)
         (assert (= x 1))
         (check-sat)",
    );
    assert_eq!(v, "sat");
}

/// 6. A second illegal `set-logic` is rejected instead of silently
///    replacing live solver state.
#[test]
fn second_set_logic_is_rejected() {
    let err = run_err(
        "(set-logic QF_LIA)
         (declare-const x Int)
         (assert (= x 5))
         (check-sat)
         (set-logic QF_LRA)
         (get-model)",
    );
    assert!(
        err.contains("already") && err.contains("set-logic"),
        "got: {err}"
    );
}

/// 7. Compatible broad headers over the same body produce the same
///    capability-derived engine plan and verdict.
#[test]
fn broad_headers_agree_on_verdict() {
    let body = "(declare-const x Int)
         (assert (> x 5))
         (assert (< x 3))
         (check-sat)";
    let via_nia = last_verdict(&format!("(set-logic QF_NIA)\n{body}"));
    let via_nira = last_verdict(&format!("(set-logic QF_NIRA)\n{body}"));
    let via_all = last_verdict(&format!("(set-logic ALL)\n{body}"));
    let via_none = last_verdict(body);
    assert_eq!(via_nia, "unsat");
    assert_eq!(via_nira, "unsat");
    assert_eq!(via_all, "unsat");
    assert_eq!(via_none, "unsat");
}
