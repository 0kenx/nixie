//! Regression tests for the eager QF_BV dispatch's condition-fragment
//! handling and the preprocessing normalizer.
//!
//! Each case pins a shape that once made `dispatch_pure_bv_solve` either
//! refuse (falling back to the slow general path) or, in the
//! `bit_blast_cond_operands` leaf case, risk a partially-encoded circuit.

use oxiz_solver::Context;

fn run(script: &str) -> String {
    let mut ctx = Context::new();
    let responses = ctx.execute_script(script).expect("script executes");
    responses
        .iter()
        .rev()
        .find(|r| r.contains("sat"))
        .cloned()
        .unwrap_or_default()
}

/// `ite` conditions built from `distinct` over 1-bit operands: the condition
/// walk must blast the operands (`2018-Mann/fifo_*` shapes).  A partial
/// blast here used to refuse the whole dispatch; wiring the selector
/// directly to a bit-vector condition would have been unsound instead.
#[test]
fn ite_distinct_condition_blasts() {
    let script = r#"
        (set-logic QF_BV)
        (declare-fun p () (_ BitVec 1))
        (declare-fun q () (_ BitVec 1))
        (declare-fun r () (_ BitVec 1))
        (assert (= r (ite (distinct p q) (_ bv1 1) (_ bv0 1))))
        (assert (= r (_ bv1 1)))
        (assert (= p q))
        (check-sat)
    "#;
    // distinct p q with p = q is false, so r must be 0, contradicting r = 1.
    assert_eq!(run(script), "unsat");
}

/// The same shape, satisfiable polarity: the model must be verifiable
/// (values for every variable) rather than falling back.
#[test]
fn ite_distinct_condition_sat_model() {
    let script = r#"
        (set-logic QF_BV)
        (declare-fun p () (_ BitVec 1))
        (declare-fun q () (_ BitVec 1))
        (declare-fun r () (_ BitVec 1))
        (assert (= r (ite (distinct p q) (_ bv1 1) (_ bv0 1))))
        (assert (= r (_ bv1 1)))
        (check-sat)
    "#;
    assert_eq!(run(script), "sat");
}

/// Boolean `xor`/`=>`/bool-`ite` conditions (`bmc-bv-svcomp14` shapes).
#[test]
fn boolean_connective_conditions_blast() {
    let script = r#"
        (set-logic QF_BV)
        (declare-fun p () Bool)
        (declare-fun q () Bool)
        (declare-fun x () (_ BitVec 8))
        (assert (= x (ite (xor p (=> p q)) (_ bv1 8) (_ bv2 8))))
        (assert (= x (_ bv1 8)))
        (assert (not q))
        (check-sat)
    "#;
    // xor p (p => q) with ¬q: p xor ¬p = true, so x = 1 holds; satisfiable.
    assert_eq!(run(script), "sat");
}

/// Solve-eqs elimination + model reconstruction: every eliminated variable
/// must still receive a value so the original assertions verify.
#[test]
fn solve_eqs_model_reconstruction() {
    let script = r#"
        (set-logic QF_BV)
        (declare-fun a () (_ BitVec 8))
        (declare-fun b () (_ BitVec 8))
        (declare-fun y () (_ BitVec 8))
        (assert (= y (bvadd a b)))
        (assert (= y (_ bv5 8)))
        (assert (= a (_ bv2 8)))
        (check-sat)
        (get-value (b))
    "#;
    let out = run(script);
    assert_eq!(out, "sat");
    // b = 3 must be recoverable.
    let mut ctx = Context::new();
    let responses = ctx.execute_script(script).expect("script executes");
    let model_line = responses
        .iter()
        .find(|r| r.contains("b"))
        .cloned()
        .unwrap_or_default();
    assert!(model_line.contains("3"), "got: {model_line}");
}

/// Left-associative n-ary bit-vector operators parse and decide
/// (`(_ bv7 w) a (bvmul (_ bv9 w) a)` chains; UltimateAutomizer shapes).
#[test]
fn nary_left_associative_bv_ops_solve() {
    let script = r#"
        (set-logic QF_BV)
        (declare-fun a () (_ BitVec 32))
        (declare-fun n () (_ BitVec 32))
        (declare-fun y () (_ BitVec 32))
        (assert (let ((_cse0 (bvmul (_ bv3 32) n)))
          (= y (bvadd (_ bv7 32) _cse0 (bvmul (_ bv9 32) n)))))
        (assert (and (= n (_ bv1 32)) (distinct y (_ bv19 32))))
        (check-sat)
    "#;
    // y = 7 + 3 + 9 = 19, so distinct y 19 is unsat.
    assert_eq!(run(script), "unsat");
}
