//! Regression tests for the eager QF_BV dispatch's condition-fragment
//! handling and the preprocessing normalizer.
//!
//! Each case pins a shape that once made `dispatch_pure_bv_solve` either
//! refuse (falling back to the slow general path) or, in the
//! `bit_blast_cond_operands` leaf case, risk a partially-encoded circuit.

use nixie_solver::Context;

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

/// Ring (Gaussian) solve-eqs: equations like `z + y = 7 + 3n² + 9n` define
/// their variables even without a syntactic `= x t` shape; isolating them
/// (odd coefficients are invertible in ℤ/2ʷ) and substituting decides the
/// UltimateAutomizer `cohencu` translations with zero search.
#[test]
fn ring_solve_eqs_decides_nonlinear_identity() {
    let script = r#"
        (set-logic QF_BV)
        (declare-fun n () (_ BitVec 32))
        (declare-fun y () (_ BitVec 32))
        (declare-fun z () (_ BitVec 32))
        (declare-fun cond () (_ BitVec 32))
        (assert (= cond (ite (= (bvadd (_ bv6 32) (bvmul (_ bv6 32) n)) z) (_ bv1 32) (_ bv0 32))))
        (assert (= (bvadd z y) (bvadd (_ bv7 32) (bvmul (_ bv3 32) n n) (bvmul (_ bv9 32) n))))
        (assert (= (bvadd (bvmul (_ bv3 32) n) (bvmul (_ bv3 32) n n) (_ bv1 32)) y))
        (assert (= cond (_ bv0 32)))
        (check-sat)
    "#;
    // z = 6+6n follows from the two ring equations, so cond = 1 ≠ 0.
    assert_eq!(run(script), "unsat");
}

/// The same shape stays *satisfiable* when the ring equations are weakened:
/// the eliminated variables' model values must reconstruct (n arbitrary,
/// y and z consistent, cond = 0).
#[test]
fn ring_solve_eqs_model_reconstruction() {
    // The original form of this test pinned `y = 4`, which makes the
    // `3n²+3n+1 = y` chain UNSATISFIABLE (n(n+1) is always even, so
    // 3n(n+1)+1 is odd) – the `sat` it asserted was the nonlinear ring
    // elimination bug, fixed alongside this rewrite (see
    // `ring_elimination_respects_nonlinear_occurrences`).  `y = 1` is the
    // satisfiable twin (n = 0 satisfies it), and still exercises the
    // ring/plain elimination replay the test was written for.
    let script = r#"
        (set-logic QF_BV)
        (declare-fun n () (_ BitVec 8))
        (declare-fun y () (_ BitVec 8))
        (declare-fun z () (_ BitVec 8))
        (assert (= (bvadd z y) (bvadd (_ bv7 8) (bvmul (_ bv3 8) n n) (bvmul (_ bv9 8) n))))
        (assert (= (bvadd (bvmul (_ bv3 8) n) (bvmul (_ bv3 8) n n) (_ bv1 8)) y))
        (assert (= y (_ bv1 8)))
        (check-sat)
        (get-value (z))
    "#;
    let out = run(script);
    assert_eq!(out, "sat");
    let mut ctx = Context::new();
    let responses = ctx.execute_script(script).expect("script executes");
    // z = 7+3n²+9n−y with n = 0, y = 1 gives z = 6; whatever n the model
    // picks, z must be printed (the eliminated variable got a model
    // entry), not defaulted.
    let line = responses
        .iter()
        .find(|r| r.contains("z"))
        .cloned()
        .unwrap_or_default();
    assert!(
        line.contains('#') && (line.contains("#b") || line.contains("#x")),
        "got: {line}"
    );
}

/// bit2bool: `(= (_ bv1 1) (bvnot (ite c #b1 #b0)))` is `c`, and 1-bit
/// comparisons are Boolean formulas — decided without any 1-bit words.
#[test]
fn bit2bool_folds_one_bit_world() {
    let script = r#"
        (set-logic QF_BV)
        (declare-fun x () (_ BitVec 16))
        (declare-fun y () (_ BitVec 16))
        (assert (= (_ bv1 1)
                   (bvand (ite (bvult x y) (_ bv1 1) (_ bv0 1))
                          (bvnot (ite (bvult y x) (_ bv1 1) (_ bv0 1))))))
        (assert (= x y))
        (check-sat)
    "#;
    // The conjunction is `x <u y` (the second conjunct is implied by it),
    // and with x = y it is false: the 1-bit equality cannot hold.
    assert_eq!(run(script), "unsat");
    let script = r#"
        (set-logic QF_BV)
        (declare-fun x () (_ BitVec 16))
        (declare-fun y () (_ BitVec 16))
        (assert (= (_ bv1 1)
                   (bvand (ite (bvult x y) (_ bv1 1) (_ bv0 1))
                          (ite (bvult y x) (_ bv1 1) (_ bv0 1)))))
        (assert (not (bvult x y)))
        (check-sat)
    "#;
    // x <u y ∧ y <u x is impossible; the weakening does not matter.
    assert_eq!(run(script), "unsat");
}

/// Ring elimination must refuse *nonlinear* occurrences: solving
/// `3n + 3n² = 3` for `n` yields the self-referential
/// `n = 3⁻¹·(3 − 3n²)`; dropping the equation on that "definition"
/// discards the constraint tying `n` to `n²` and collapses the formula to
/// `true`.  `3n(n+1)+1 = y ∧ y = 4` is **unsatisfiable** (`n(n+1)` is
/// always even, so the left side is odd), and the eliminated rewrite
/// answered `sat` for it before the linearity gate.
#[test]
fn ring_elimination_respects_nonlinear_occurrences() {
    let out = run(r#"
        (set-logic QF_BV)
        (declare-fun n () (_ BitVec 8))
        (declare-fun y () (_ BitVec 8))
        (assert (= (bvadd (bvmul (_ bv3 8) n) (bvmul (_ bv3 8) n n) (_ bv1 8)) y))
        (assert (= y (_ bv4 8)))
        (check-sat)
    "#);
    assert_eq!(out, "unsat");
    // The three-variable form (an absorbing `z` on the other side) is
    // unsatisfiable for the same parity reason: the y-chain pins
    // 3n(n+1) = 3, still impossible.
    let out = run(r#"
        (set-logic QF_BV)
        (declare-fun n () (_ BitVec 8))
        (declare-fun y () (_ BitVec 8))
        (declare-fun z () (_ BitVec 8))
        (assert (= (bvadd z y) (bvadd (_ bv7 8) (bvmul (_ bv3 8) n n) (bvmul (_ bv9 8) n))))
        (assert (= (bvadd (bvmul (_ bv3 8) n) (bvmul (_ bv3 8) n n) (_ bv1 8)) y))
        (assert (= y (_ bv4 8)))
        (check-sat)
    "#);
    assert_eq!(out, "unsat");
}

/// Definition chains under one `and` per program point (the
/// UltimateAutomizer/2018-Mann shape): the normalizer must split the
/// conjunction so every equation is visible to the solving passes.
#[test]
fn conjuncted_equations_are_solved() {
    let script = r#"
        (set-logic QF_BV)
        (declare-fun a () (_ BitVec 8))
        (declare-fun b () (_ BitVec 8))
        (declare-fun c () (_ BitVec 8))
        (assert (and (= c (bvadd a b)) (= c (_ bv9 8)) (= a (_ bv4 8))))
        (assert (not (not (distinct b (_ bv5 8)))))
        (check-sat)
    "#;
    // a + b = 9 with a = 4 forces b = 5; distinct b 5 refutes it.
    assert_eq!(run(script), "unsat");
    // Satisfiable polarity: model must reconstruct b (and the chain).
    let script = r#"
        (set-logic QF_BV)
        (declare-fun a () (_ BitVec 8))
        (declare-fun b () (_ BitVec 8))
        (declare-fun c () (_ BitVec 8))
        (assert (and (= c (bvadd a b)) (= a (_ bv4 8))))
        (check-sat)
        (get-value (c))
    "#;
    let mut ctx = Context::new();
    let responses = ctx.execute_script(script).expect("script executes");
    let line = responses
        .iter()
        .find(|r| r.contains("c"))
        .cloned()
        .unwrap_or_default();
    // c = a + b with both free: any value works, but it must be printed
    // (the eliminated variable got a model entry), not defaulted.  Either
    // literal base is a real value (`#b` from the dispatch's model builder,
    // `#x` from the unified path's – both are well-formed SMT-LIB).
    assert!(
        line.contains('#') && (line.contains("#b") || line.contains("#x")),
        "got: {line}"
    );
}
