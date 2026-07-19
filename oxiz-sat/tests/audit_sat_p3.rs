//! Regression tests for the sat-p3 audit findings.
//!
//! Each test pins the corrected behavior of a confirmed defect so it cannot
//! silently regress.

use std::sync::Arc;
use std::sync::atomic::AtomicBool;

use oxiz_sat::{
    Clause, Cube, CubeResult, CubeSolverConfig, DimacsError, DimacsParser, Lit, ParallelCubeSolver,
    Solver, SolverConfig, SolverResult, Var,
};

fn pos(i: u32) -> Lit {
    Lit::pos(Var::new(i))
}
fn neg(i: u32) -> Lit {
    Lit::neg(Var::new(i))
}

// ---------------------------------------------------------------------------
// Finding 1: Cube-and-Conquer must actually solve, and an empty cube list must
// not fabricate UNSAT.
// ---------------------------------------------------------------------------

#[test]
fn cube_solver_solves_sat_and_unsat_cubes() {
    let config = CubeSolverConfig {
        verbose: false,
        early_termination: false,
        ..Default::default()
    };
    let mut solver = ParallelCubeSolver::new(config);

    // Formula: (x0 ∨ x1). Cube [x0] is SAT (x0 satisfies it directly).
    let clauses = vec![Clause::original([pos(0), pos(1)])];
    let cubes = vec![Cube::new(vec![pos(0)])];
    let (result, results) = solver.solve(cubes, &clauses);
    assert_eq!(result, CubeResult::Sat, "cube [x0] over (x0∨x1) is SAT");
    assert_eq!(results[0].result, CubeResult::Sat);
}

#[test]
fn cube_solver_reports_unsat_only_when_proven() {
    let config = CubeSolverConfig {
        verbose: false,
        early_termination: false,
        ..Default::default()
    };
    let mut solver = ParallelCubeSolver::new(config);

    // Contradictory formula (x0) ∧ (¬x0): every cube is UNSAT.
    let clauses = vec![Clause::original([pos(0)]), Clause::original([neg(0)])];
    let cubes = vec![Cube::new(vec![pos(0)])];
    let (result, _results) = solver.solve(cubes, &clauses);
    assert_eq!(result, CubeResult::Unsat);
}

#[test]
fn cube_solver_empty_cube_list_is_unknown_not_unsat() {
    let config = CubeSolverConfig {
        verbose: false,
        ..Default::default()
    };
    let mut solver = ParallelCubeSolver::new(config);
    let (result, results) = solver.solve(Vec::new(), &[]);
    assert_eq!(
        result,
        CubeResult::Unknown,
        "examining zero cubes proves nothing"
    );
    assert!(results.is_empty());
}

// ---------------------------------------------------------------------------
// Finding 2: an adversarial DIMACS header variable count must be rejected
// rather than triggering an unbounded allocation.
// ---------------------------------------------------------------------------

#[test]
fn dimacs_rejects_absurd_variable_count() {
    let cnf = "p cnf 999999999999 1\n1 0\n";
    let mut parser = DimacsParser::new();
    let mut solver = Solver::new();
    let res = parser.parse_reader(cnf.as_bytes(), &mut solver);
    assert!(
        matches!(res, Err(DimacsError::InvalidProblem)),
        "an absurd var count must be rejected, got {res:?}"
    );
    // The solver must not have been forced to allocate billions of variables.
    assert_eq!(solver.num_vars(), 0);
}

#[test]
fn dimacs_still_parses_reasonable_headers() {
    let cnf = "c ok\np cnf 3 2\n1 -3 0\n2 3 -1 0\n";
    let mut parser = DimacsParser::new();
    let mut solver = Solver::new();
    parser
        .parse_reader(cnf.as_bytes(), &mut solver)
        .expect("a normal header must parse");
    assert_eq!(parser.num_vars(), 3);
    assert_eq!(parser.num_clauses(), 2);
}

#[test]
fn dimacs_max_vars_is_configurable() {
    let cnf = "p cnf 1000 1\n1 0\n";
    let mut parser = DimacsParser::new();
    parser.set_max_vars(10); // lower the cap below the declared count
    let mut solver = Solver::new();
    let res = parser.parse_reader(cnf.as_bytes(), &mut solver);
    assert!(matches!(res, Err(DimacsError::InvalidProblem)));
}

// ---------------------------------------------------------------------------
// Finding 5: the CDCL loop must honor a resource budget / interrupt and return
// Unknown instead of running forever.
// ---------------------------------------------------------------------------

#[test]
fn solve_returns_unknown_when_interrupted() {
    let mut solver = Solver::new();
    solver.new_var();
    solver.new_var();
    // Satisfiable formula so the search would otherwise proceed to a decision.
    solver.add_clause([pos(0), pos(1)]);

    // Pre-set the interrupt: the first loop iteration must bail out.
    let flag = Arc::new(AtomicBool::new(true));
    solver.set_interrupt(flag);
    assert_eq!(solver.solve(), SolverResult::Unknown);
}

#[test]
fn solve_returns_unknown_when_conflict_budget_exhausted() {
    // PHP(4,3): 4 pigeons, 3 holes — UNSAT and requires several conflicts.
    let mut solver = Solver::new();
    for _ in 0..12 {
        solver.new_var();
    }
    // Each pigeon in at least one hole (var 3*(p-1)+h).
    solver.add_clause_dimacs(&[1, 2, 3]);
    solver.add_clause_dimacs(&[4, 5, 6]);
    solver.add_clause_dimacs(&[7, 8, 9]);
    solver.add_clause_dimacs(&[10, 11, 12]);
    for hole in 0..3 {
        let h = hole + 1;
        let occ = [h, h + 3, h + 6, h + 9];
        for i in 0..occ.len() {
            for j in (i + 1)..occ.len() {
                solver.add_clause_dimacs(&[-occ[i], -occ[j]]);
            }
        }
    }

    // A single-conflict budget cannot complete the refutation.
    solver.set_max_conflicts(Some(1));
    let result = solver.solve();
    assert_eq!(result, SolverResult::Unknown);
    assert!(solver.stats().conflicts <= 2);
}

#[test]
fn unlimited_budget_still_solves() {
    // Sanity: with no budget the same instance is refuted.
    let mut solver = Solver::new();
    for _ in 0..12 {
        solver.new_var();
    }
    solver.add_clause_dimacs(&[1, 2, 3]);
    solver.add_clause_dimacs(&[4, 5, 6]);
    solver.add_clause_dimacs(&[7, 8, 9]);
    solver.add_clause_dimacs(&[10, 11, 12]);
    for hole in 0..3 {
        let h = hole + 1;
        let occ = [h, h + 3, h + 6, h + 9];
        for i in 0..occ.len() {
            for j in (i + 1)..occ.len() {
                solver.add_clause_dimacs(&[-occ[i], -occ[j]]);
            }
        }
    }
    assert_eq!(solver.solve(), SolverResult::Unsat);
}

// ---------------------------------------------------------------------------
// Finding 7: inprocessing / vivification strengthening must keep results
// correct (rebuilding watches after removing a watched literal).
// ---------------------------------------------------------------------------

fn php_config_with_inprocessing() -> SolverConfig {
    SolverConfig {
        enable_inprocessing: true,
        inprocessing_interval: 1,
        clause_deletion_threshold: 4,
        ..SolverConfig::default()
    }
}

#[test]
fn inprocessing_keeps_unsat_correct() {
    // PHP(3,2) is UNSAT; with aggressive inprocessing the watch rebuild after
    // literal removal must not corrupt propagation.
    let mut solver = Solver::with_config(php_config_with_inprocessing());
    for _ in 0..6 {
        solver.new_var();
    }
    solver.add_clause_dimacs(&[1, 2]);
    solver.add_clause_dimacs(&[3, 4]);
    solver.add_clause_dimacs(&[5, 6]);
    solver.add_clause_dimacs(&[-1, -3]);
    solver.add_clause_dimacs(&[-1, -5]);
    solver.add_clause_dimacs(&[-3, -5]);
    solver.add_clause_dimacs(&[-2, -4]);
    solver.add_clause_dimacs(&[-2, -6]);
    solver.add_clause_dimacs(&[-4, -6]);
    assert_eq!(solver.solve(), SolverResult::Unsat);
}

#[test]
fn inprocessing_keeps_sat_models_valid() {
    // A satisfiable graph-coloring style instance; the returned model must
    // satisfy every clause even after inprocessing rewrites clauses.
    let clauses: Vec<Vec<i32>> = vec![
        vec![1, 6, 11],
        vec![2, 7, 12],
        vec![3, 8, 13],
        vec![-1, -6],
        vec![-1, -11],
        vec![-6, -11],
        vec![-2, -7],
        vec![-2, -12],
        vec![-7, -12],
        vec![-1, -2],
        vec![-6, -7],
        vec![-11, -12],
    ];

    let mut solver = Solver::with_config(php_config_with_inprocessing());
    for _ in 0..15 {
        solver.new_var();
    }
    for c in &clauses {
        solver.add_clause_dimacs(c);
    }
    assert_eq!(solver.solve(), SolverResult::Sat);

    // Verify the model actually satisfies every clause.
    for c in &clauses {
        let satisfied = c.iter().any(|&d| {
            let v = Var::new(d.unsigned_abs() - 1);
            let val = solver.model_value(v);
            if d > 0 { val.is_true() } else { val.is_false() }
        });
        assert!(satisfied, "clause {c:?} unsatisfied by returned model");
    }
}
