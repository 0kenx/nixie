//! QF_NIA soundness: never return sat for integer-unsatisfiable nonlinear formulas.
//!
//! Benchmarks referenced by name (not vendored):
//! - smt-lib/non-incremental/QF_NIA/calypto/problem-000044.cvc.2.smt2
//! - smt-lib/non-incremental/QF_NIA/UltimateAutomizer/gauss_sum_true-unreach-call.i.smt2

use oxiz_solver::{Context, SolverResult};

fn run(src: &str) -> SolverResult {
    let mut ctx = Context::new();
    let out = ctx.execute_script(src).expect("script");
    out.iter()
        .rev()
        .find_map(|l| match l.trim() {
            "sat" => Some(SolverResult::Sat),
            "unsat" => Some(SolverResult::Unsat),
            "unknown" => Some(SolverResult::Unknown),
            _ => None,
        })
        .unwrap_or(SolverResult::Unknown)
}

/// Classic: x*x = 2 has no integer solution.
#[test]
fn square_eq_two_is_unsat() {
    assert_eq!(
        run(r#"(set-logic QF_NIA)(declare-const x Int)(assert (= (* x x) 2))(check-sat)"#),
        SolverResult::Unsat
    );
}

/// Nested let/ite industrial pattern (calypto-style). Must not return sat.
/// Prefer unsat; unknown is an acceptable incomplete answer.
#[test]
fn calypto_style_let_ite_product_not_sat() {
    let src = r#"
(set-logic QF_NIA)
(set-info :status unsat)
(declare-fun P_2 () Bool)
(declare-fun P_3 () Int)
(declare-fun P_4 () Int)
(declare-fun P_5 () Int)
(declare-fun P_6 () Int)
(assert (<= 0 P_3))
(assert (<= P_3 255))
(assert (<= 0 P_4))
(assert (<= P_4 1016))
(assert (<= 0 P_5))
(assert (<= P_5 127))
(assert (<= 0 P_6))
(assert (<= P_6 255))
(declare-fun dz () Int)
(declare-fun rz () Int)
(assert
 (let ((?v_0 (ite P_2 1 0))
       (?v_1 (* P_3 P_6)))
  (let ((?v_5 (= (ite (>= ?v_0 0) ?v_0 (+ ?v_0 2)) 0))
        (?v_2 (* 1 (- 1))))
   (let ((?v_3 (- ?v_2 (ite (not (> (ite (< P_4 512) P_4 (- P_4 1024)) 127)) P_5 ?v_2))))
    (let ((?v_6 (* P_3 (ite (>= ?v_3 0) ?v_3 (+ ?v_3 128)))))
     (let ((?v_4 (* ?v_6 P_6)))
      (let ((?v_7 (- ?v_4)))
       (= (+ (* 134217728 dz) rz)
          (- (ite (not (< (ite ?v_5 ?v_1 (- ?v_1)) 0)) ?v_4 ?v_7)
             (ite (not (< (ite ?v_5 ?v_6 (+ (- ?v_2 ?v_6) 1)) 0)) ?v_4 ?v_7))))))))))
(assert (> rz 0))
(assert (< rz 134217728))
(check-sat)
"#;
    let r = run(src);
    assert_ne!(
        r,
        SolverResult::Sat,
        "soundness: calypto-style NIA must not return sat (got {r:?})"
    );
}

/// ite wrapping a product: with x=y=0 the product cannot be 1 or 2.
#[test]
fn ite_product_zero_unsat() {
    assert_eq!(
        run(
            r#"
            (set-logic QF_NIA)
            (declare-const b Bool)
            (declare-const x Int)
            (declare-const y Int)
            (assert (= x 0))
            (assert (= y 0))
            (assert (= (* x y) (ite b 1 2)))
            (check-sat)
            "#
        ),
        SolverResult::Unsat
    );
}
