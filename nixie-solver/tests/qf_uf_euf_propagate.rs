//! Regression: EUF equality-atom theory propagation.
//!
//! Congruence must force unassigned `(= (f a) (f b))` once `a = b` is
//! asserted, and a finite-domain distinctness must force the other cell
//! values false.

use nixie_solver::{Context, SolverResult};

fn last_result(source: &str) -> Option<SolverResult> {
    let mut ctx = Context::new();
    let outputs = ctx.execute_script(source).expect("script must not abort");
    outputs.iter().rev().find_map(|l| match l.trim() {
        "sat" => Some(SolverResult::Sat),
        "unsat" => Some(SolverResult::Unsat),
        "unknown" => Some(SolverResult::Unknown),
        _ => None,
    })
}

#[test]
fn congruence_forces_unassigned_eq_atom() {
    let source = r#"
(set-logic QF_UF)
(declare-sort U 0)
(declare-fun f (U) U)
(declare-fun a () U)
(declare-fun b () U)
(declare-fun p () Bool)
(assert (= a b))
(assert (or (not (= (f a) (f b))) p))
(assert (not p))
(check-sat)
"#;
    assert_eq!(
        last_result(source),
        Some(SolverResult::Unsat),
        "a=b must force (f a)=(f b) and refute ¬p"
    );
}

#[test]
fn distinct_forces_other_cell_values_false() {
    let source = r#"
(set-logic QF_UF)
(declare-sort U 0)
(declare-fun op (U U) U)
(declare-fun e0 () U)
(declare-fun e1 () U)
(declare-fun e2 () U)
(assert (distinct e0 e1 e2))
(assert (= (op e0 e1) e0))
(assert (or (= (op e0 e1) e1) (= (op e0 e1) e2)))
(check-sat)
"#;
    assert_eq!(
        last_result(source),
        Some(SolverResult::Unsat),
        "op(e0,e1)=e0 plus distinct must refute the other two cell values"
    );
}
