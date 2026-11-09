//! Upstream 0.3.4 BV scope and selector integration.
use nixie_solver::Context;

#[test]
fn a_selector_assigned_after_its_bv_atom_is_checked_and_retracted() {
    let script = r#"
(set-logic QF_BV)
(declare-const p Bool)
(declare-const x (_ BitVec 8))
(assert (= x (ite p #x01 #x02)))
(assert (= x #x02))
(check-sat)
(push 1)
(assert p)
(check-sat)
(pop 1)
(assert (not p))
(check-sat)
"#;
    assert_eq!(
        Context::new().execute_script(script).expect("script"),
        ["sat", "unsat", "sat"]
    );
}

#[test]
fn switching_bv_assumptions_keeps_gate_definitions() {
    let script = r#"
(set-logic QF_BV)
(declare-const x (_ BitVec 8))
(declare-const y (_ BitVec 8))
(assert (= y (bvadd x #x01)))
(push 1)
(assert (= x #x02))
(assert (= y #x04))
(check-sat)
(pop 1)
(push 1)
(assert (= x #x02))
(assert (= y #x03))
(check-sat)
(pop 1)
(push 1)
(assert (= x #xff))
(assert (= y #x00))
(check-sat)
(pop 1)
"#;
    assert_eq!(
        Context::new().execute_script(script).expect("script"),
        ["unsat", "sat", "sat"]
    );
}
