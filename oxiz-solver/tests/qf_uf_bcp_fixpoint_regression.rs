//! Regression: BCP-fixpoint invariant before `final_check` in the CDCL(T)
//! loop.
//!
//! The inner theory loop in `oxiz_sat::Solver::solve_with_theory` handles a
//! theory conflict by calling `learn_clause`, which enqueues the learned
//! clause's asserting literal (its reason is the new clause) but does not
//! itself run BCP. The inner loop only re-reads the trail through
//! `theory.on_assignment` -- never through the watch lists -- so the
//! asserting literal's Boolean consequences sit unprocessed.
//!
//! In the common case the next outer iteration's top-of-loop `propagate`
//! drains them before anything observes the trail, because backtracking from a
//! conflict leaves unassigned variables and `pick_branch_var` returns `Some`.
//! But when the asserting literal happens to *complete* the trail (every
//! variable now assigned), `pick_branch_var` returns `None` and `final_check`
//! runs in the same iteration -- over a trail that still has an unpropagated
//! asserting literal. A genuine conflict hidden in that literal's watch list
//! (e.g. an all-false original clause it now falsifies) is missed, the theory
//! reports `Sat`, and the `trail_falsifies_live_clause` backstop degrades the
//! real `Unsat` to a spurious `Unknown`.
//!
//! This was the root cause of the 10 explicit-`unknown` results in the QF_UF
//! full benchmark (SEQ/PEQ model-finding + QG-classification quasigroup
//! families): z3 answered `unsat`, oxiz answered `unknown` in 7 ms-5.9 s. The
//! fix re-enters the outer loop (so its `propagate` drains BCP to fixpoint)
//! whenever the inner theory loop leaves pending propagation, before any
//! branch decision or model declaration.
//!
//! The canary is `SEQ032_size2` -- the smallest reproducer (~7 ms,
//! deterministically `unknown` before the fix, `unsat` after, matching z3).

use oxiz_solver::{Context, SolverResult};

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

/// SEQ032_size2 from SMT-LIB QF_UF: a 2-element finite-domain model-finding
/// problem. z3: unsat. Before the fix oxiz returned `unknown` (~7 ms) because a
/// theory conflict's asserting literal completed the trail without its Boolean
/// consequences being propagated, leaving an all-false original clause
/// undetected and tripping the `trail_falsifies_live_clause` backstop.
#[test]
fn seq032_size2_is_unsat_not_unknown() {
    let source = r#"
(set-logic QF_UF)
(declare-sort U 0)
(declare-fun c3 () U)
(declare-fun f1 (U U) U)
(declare-fun c2 () U)
(declare-fun f4 (U) U)
(declare-fun c_0 () U)
(declare-fun c_1 () U)
(assert (let ((?v_1 (f1 c3 c_0))) (let ((?v_0 (f1 ?v_1 c_0)) (?v_2 (f1 c_0 c_0))) (let ((?v_10 (f1 c_0 ?v_2)) (?v_4 (f1 c_0 c_1)) (?v_3 (f1 ?v_1 c_1)) (?v_13 (f1 c_1 ?v_2)) (?v_6 (f1 c3 c_1))) (let ((?v_5 (f1 ?v_6 c_0)) (?v_7 (f1 c_1 c_0)) (?v_9 (f1 c_1 c_1))) (let ((?v_12 (f1 c_0 ?v_9)) (?v_8 (f1 ?v_6 c_1)) (?v_15 (f1 c_1 ?v_9)) (?v_11 (f1 c2 c_0)) (?v_14 (f1 c2 c_1)) (?v_16 (f4 c_0))) (let ((?v_17 (f1 c_0 ?v_16)) (?v_18 (f4 c_1))) (let ((?v_19 (f1 c_1 ?v_18))) (and (distinct c_0 c_1) (= (f1 ?v_0 c_0) ?v_10) (= (f1 ?v_0 c_1) (f1 c_0 ?v_4)) (= (f1 ?v_3 c_0) ?v_13) (= (f1 ?v_3 c_1) (f1 c_1 ?v_4)) (= (f1 ?v_5 c_0) (f1 c_0 ?v_7)) (= (f1 ?v_5 c_1) ?v_12) (= (f1 ?v_8 c_0) (f1 c_1 ?v_7)) (= (f1 ?v_8 c_1) ?v_15) (= (f1 ?v_11 c_0) ?v_10) (= (f1 ?v_11 c_1) ?v_12) (= (f1 ?v_14 c_0) ?v_13) (= (f1 ?v_14 c_1) ?v_15) (not (= ?v_17 (f1 ?v_16 ?v_17))) (not (= ?v_19 (f1 ?v_18 ?v_19))) (or (= ?v_2 c_0) (= ?v_2 c_1)) (or (= ?v_4 c_0) (= ?v_4 c_1)) (or (= ?v_7 c_0) (= ?v_7 c_1)) (or (= ?v_9 c_0) (= ?v_9 c_1)) (or (= ?v_16 c_0) (= ?v_16 c_1)) (or (= ?v_18 c_0) (= ?v_18 c_1)) (or (= c3 c_0) (= c3 c_1)) (or (= c2 c_0) (= c2 c_1)))))))))))
(check-sat)
(exit)
"#;
    assert_eq!(
        last_result(source),
        Some(SolverResult::Unsat),
        "SEQ032 is unsat (z3 confirms); a regression to `unknown` here means          the BCP-fixpoint invariant before final_check was lost"
    );
}
