//! End-to-end regression: QF_NIA goals with Boolean structure must be
//! *decided* (or honestly `unknown`), never mis-decoded.
//!
//! Root cause this pins: `dispatch_nia_constraints`'s conjunction-only
//! extraction used to drop top-level disjunctions entirely (flagging the
//! extraction incomplete), so the CAD core solved a strictly weaker
//! relaxation and the whole `(or template₁ template₂ …)` VeryMax/AProVE ITS
//! family fell through to `unknown`. The DPLL case-split driver
//! (`oxiz-theories::nl_dpll`) now splits such goals into conjunction cases;
//! these tests drive the full solver pipeline (parse → dispatch → verdict)
//! over both polarities of the canonical goal shape.

use oxiz_solver::{Context, SolverResult};

fn check(script: &str) -> SolverResult {
    let mut ctx = Context::new();
    let out = ctx.execute_script(script).expect("script executes cleanly");
    assert_eq!(out.len(), 1, "exactly one check-sat in the script");
    match out[0].as_str() {
        "sat" => SolverResult::Sat,
        "unsat" => SolverResult::Unsat,
        _ => SolverResult::Unknown,
    }
}

#[test]
fn verymax_disjunctive_goal_unsat() {
    // Every disjunct is refutable: x,y ≥ 1 (integers) forces x·y ≥ 1, and
    // x ≤ 0 / y ≤ 0 contradict the bounds directly.
    let script = r#"
(set-logic QF_NIA)
(declare-fun x () Int)
(declare-fun y () Int)
(assert (>= x 1))
(assert (>= y 1))
(assert (or (<= x 0) (<= y 0) (< (* x y) 1)))
(check-sat)
"#;
    assert_eq!(check(script), SolverResult::Unsat);
}

#[test]
fn verymax_disjunctive_goal_sat() {
    // The middle template is satisfiable (x = 4, y = 1); the witness must be
    // found through the disjunction, not by relaxing it away.
    let script = r#"
(set-logic QF_NIA)
(declare-fun x () Int)
(declare-fun y () Int)
(assert (>= x 1))
(assert (>= y 1))
(assert (or (<= x 0) (>= (* x y) 4)))
(check-sat)
"#;
    assert_eq!(check(script), SolverResult::Sat);
}

#[test]
fn negated_guard_under_conjunction_is_respected() {
    // `(not (<= x y))` inside a conjunction: the negated-comparison leaf.
    // Regression for the `Not`-polarity inversion that briefly produced a
    // wrong `unsat` on VeryMax `ex36.t2_fixed__p23678`.
    let script_sat = r#"
(set-logic QF_NIA)
(declare-fun x () Int)
(declare-fun y () Int)
(assert (not (<= (* x y) 0)))
(assert (= (* x y) 4))
(check-sat)
"#;
    assert_eq!(check(script_sat), SolverResult::Sat);

    let script_unsat = r#"
(set-logic QF_NIA)
(declare-fun x () Int)
(declare-fun y () Int)
(assert (not (<= (* x y) 0)))
(assert (<= (* x y) 0))
(check-sat)
"#;
    assert_eq!(check(script_unsat), SolverResult::Unsat);
}
