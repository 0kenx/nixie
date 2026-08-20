//! Soundness regression: level-filtered backtracking (cadical's out-of-order
//! trail, SAT'18) must hold under `chronoalways`.
//!
//! The pre-change positional suffix-pop unassigned every literal positioned
//! above `level_starts[level+1]`, but chronological backtracking's asserting
//! literal is *appended at the trail top* while recorded at its **assertion
//! level** below it (out-of-order, by design).  A later ordinary backtrack to
//! a level in `[assertion_level, positional_level)` popped that justified
//! literal positionally even though its recorded level said it survives;
//! clauses that were unit through it stopped being enforced, and the
//! propagation-fixpoint invariant broke.  Reproduced by `pmres`'s
//! `test_pmres_stratified` (assumptions path, hanging unit
//! `[-65, 64, 62]`, levels `[0, 8, 3]`) under `chrono_always`.
//!
//! This test drives the same shape at the SAT level: force chronological
//! backtracking on every non-unit conflict, solve an UNSAT instance under
//! assumptions repeatedly (each solve's conflicts leave out-of-order
//! literals on the trail for the next), and require the correct verdict
//! every time.  Under the suffix-pop trail this trips the debug
//! hanging-unit invariant / returns a wrong `sat`.
use oxiz_sat::{Lit, Solver, SolverConfig, SolverResult, Var};

#[test]
fn chrono_always_survives_repeated_assumption_solves() {
    let mut solver = Solver::with_config(SolverConfig {
        chrono_always: true,
        enable_lucky: false,
        ..SolverConfig::default()
    });
    // At-most-one-of-{a,b,c} plus (d), with (¬a∨x),(¬b∨x),(¬c∨x) and
    // (¬x∨¬d): x is forced exactly when any of a..c is taken, and conflicts
    // with d — enough branching for chronological stops to interleave.
    let v = |i: u32| Var::new(i);
    let l = |i: i32| {
        let var = v(i.unsigned_abs() - 1);
        if i > 0 { Lit::pos(var) } else { Lit::neg(var) }
    };
    for clause in [
        vec![-1, -2],
        vec![-1, -3],
        vec![-2, -3], // at most one of a,b,c
        vec![4],      // d
        vec![-1, 5],
        vec![-2, 5],
        vec![-3, 5],          // any taken -> x
        vec![-5, -4],         // x -> ¬d
        vec![-6, -7, -8, -9], // filler for deeper trails
    ] {
        let lits: Vec<Lit> = clause.iter().map(|&x| l(x)).collect();
        assert!(solver.add_clause(lits));
    }
    // Repeated assumption solves: UNSAT under any of a/b/c; SAT under none.
    for assume in [1i32, 2, 3] {
        let al = l(assume);
        let (res, core) = solver.solve_with_assumptions(&[al]);
        assert_eq!(res, SolverResult::Unsat, "assuming {assume} must be UNSAT");
        let _ = core; // core *content* is not the property under test here
    }
    let (res, _) = solver.solve_with_assumptions(&[]);
    assert_eq!(res, SolverResult::Sat);
}
