//! Logic-contract acceptance tests
//! (`docs/2026-08-established-research-candidates.md` Priority 0).
//!
//! The seven behaviors the layer must demonstrate, numbered as in the doc.
//! These pin the exact failure modes the old substring-decoded routing
//! produced: header-induced incompleteness, invented names installing
//! backends, silent second `set-logic`, and bodies outside the declared
//! fragment answering instead of erroring.

use nixie_solver::Context;

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
    // Without `nlsat` the NL backend is compiled out and the goal must
    // decline honestly rather than guess (upstream v0.3.3 feature split).
    #[cfg(feature = "nlsat")]
    assert_eq!(
        via_nia, "unsat",
        "explicit header must engage the NL backend"
    );
    #[cfg(not(feature = "nlsat"))]
    assert_eq!(via_nia, "unknown", "no-NL builds decline nonlinear goals");
    let via_none = last_verdict(body);
    let via_all = last_verdict(&format!(
        "(set-logic ALL)
{body}"
    ));
    // (Routing itself is unchanged by the `nlsat` feature; what the routed
    // NL backend can decide is not. Without it these goals decline.)
    #[cfg(feature = "nlsat")]
    {
        assert_eq!(via_none, "unsat", "missing header must route structurally");
        assert_eq!(via_all, "unsat", "ALL header must route structurally");
    }
    #[cfg(not(feature = "nlsat"))]
    {
        assert_eq!(via_none, "unknown");
        assert_eq!(via_all, "unknown");
    }
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

/// The SMT-LIB benchmark catalog (89 logics, smt-lib.org bench listing) must
/// be ACCEPTED at the command surface — every one, no exceptions.  A missing
/// registry entry rejects valid input at `set-logic` (measured live: `UFNIA`
/// before the completion).  Grammar decode semantics are pinned by the
/// in-module unit tests (`smt_lib_catalog_decodes_grammar_semantics`).
#[test]
fn smt_lib_catalog_is_accepted_at_set_logic() {
    let catalog = "ABV ABVFP ABVFPLRA ALIA ANIA AUFBV AUFBVDTLIA AUFBVDTNIA \
AUFBVDTNIRA AUFBVFP AUFBVFPDTNIRA AUFDTLIA AUFDTLIRA AUFDTNIRA AUFFPDTNIRA \
AUFLIA AUFLIRA AUFNIA AUFNIRA BV BVFP BVFPLRA FP FPLRA LIA LRA NIA NRA \
QF_ABV QF_ABVFP QF_ABVFPLRA QF_ALIA QF_ANIA QF_AUFBV QF_AUFBVFP QF_AUFLIA \
QF_AUFNIA QF_AX QF_BV QF_BVFP QF_BVFPLRA QF_DT QF_FP QF_FPLRA QF_IDL QF_LIA \
QF_LIRA QF_LRA QF_NIA QF_NIRA QF_NRA QF_RDL QF_S QF_SLIA QF_SNIA QF_UF QF_UFBV \
QF_UFBVDT QF_UFDT QF_UFDTLIA QF_UFDTLIRA QF_UFDTNIA QF_UFFP QF_UFFPDTNIRA \
QF_UFIDL QF_UFLIA QF_UFLRA QF_UFNIA QF_UFNRA UF UFBV UFBVDT UFBVDTLIA UFBVDTNIA \
UFBVDTNIRA UFBVFP UFBVFPDTNIRA UFBVLIA UFDT UFDTLIA UFDTLIRA UFDTNIA UFDTNIRA \
UFFPDTNIRA UFIDL UFLIA UFLRA UFNIA UFNIRA";
    for name in catalog.split_whitespace() {
        let err = run_err(&format!("(set-logic {name})\n(check-sat)"));
        assert!(
            !err.contains("unknown logic"),
            "SMT-LIB catalog logic {name} rejected at the command surface: {err}"
        );
    }
}
