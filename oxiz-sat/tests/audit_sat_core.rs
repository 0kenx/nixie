//! Regression tests for audited sat-core soundness defects.
//!
//! Three critical findings are covered:
//!  1. conflict.rs: binary-implication-graph reason clauses store the propagated
//!     literal at index 1, so the old positional `start = 1` skip dropped the false
//!     antecedent at index 0, producing over-strong learned clauses that can flip
//!     SAT instances to UNSAT.
//!  2. clause.rs: recycling `ClauseId` slots via the free list left stale watchers
//!     pointing at a live-but-different clause, driving bogus unit propagations.
//!  3. mod.rs: `solve_with_assumptions` after a prior `solve()` treated leftover
//!     model decisions as fixed level-0 facts, returning false UNSAT.

use oxiz_sat::{LBool, Lit, Solver, SolverResult};

/// Validate that a model satisfies every clause of a CNF given in DIMACS form.
fn model_satisfies(solver: &Solver, clauses: &[Vec<i32>]) -> bool {
    for clause in clauses {
        let mut sat = false;
        for &dlit in clause {
            let var_idx = (dlit.unsigned_abs() - 1) as usize;
            let val = solver.model_value(oxiz_sat::Var::new(var_idx as u32));
            let want_true = dlit > 0;
            match val {
                LBool::True if want_true => sat = true,
                LBool::False if !want_true => sat = true,
                _ => {}
            }
            if sat {
                break;
            }
        }
        if !sat {
            return false;
        }
    }
    true
}

// ---------------------------------------------------------------------------
// Finding 3: solve() then solve_with_assumptions() must not return false UNSAT
// ---------------------------------------------------------------------------

#[test]
fn assumptions_after_solve_do_not_report_false_unsat() {
    // The canonical counterexample from the audit: (a ∨ b).
    // solve() may pick a model with a = false, b = true. A subsequent
    // solve_with_assumptions([a]) must report SAT because a ∧ (a ∨ b) is SAT.
    let mut solver = Solver::new();
    solver.new_var(); // a  -> dimacs 1
    solver.new_var(); // b  -> dimacs 2
    assert!(solver.add_clause_dimacs(&[1, 2]));

    let first = solver.solve();
    assert_eq!(first, SolverResult::Sat, "(a ∨ b) is trivially SAT");

    let a = Lit::from_dimacs(1);
    let (res_a, _core) = solver.solve_with_assumptions(&[a]);
    assert_eq!(
        res_a,
        SolverResult::Sat,
        "a ∧ (a ∨ b) is SAT — must not be reported UNSAT after a prior solve()"
    );

    // And the opposite assumption is likewise SAT (¬a forces b).
    let not_a = Lit::from_dimacs(-1);
    let (res_not_a, _core) = solver.solve_with_assumptions(&[not_a]);
    assert_eq!(
        res_not_a,
        SolverResult::Sat,
        "¬a ∧ (a ∨ b) is SAT (b becomes true)"
    );
}

#[test]
fn repeated_assumptions_each_side_are_sat() {
    // Two independent free choices; every single-literal assumption is satisfiable.
    // Repeated calls must each restart cleanly from the root.
    let mut solver = Solver::new();
    for _ in 0..4 {
        solver.new_var();
    }
    // (1 ∨ 2) and (3 ∨ 4): both clauses independently satisfiable any which way.
    assert!(solver.add_clause_dimacs(&[1, 2]));
    assert!(solver.add_clause_dimacs(&[3, 4]));

    assert_eq!(solver.solve(), SolverResult::Sat);

    for &lit in &[1i32, -1, 2, -2, 3, -3, 4, -4] {
        let (res, _core) = solver.solve_with_assumptions(&[Lit::from_dimacs(lit)]);
        assert_eq!(
            res,
            SolverResult::Sat,
            "assumption {lit} must be SAT after a prior solve()"
        );
    }
}

#[test]
fn assumptions_genuine_unsat_still_detected() {
    // A real level-0 contradiction with an assumption must still be UNSAT.
    // Unit clause (1) forces a = true at level 0; assuming ¬a must be UNSAT.
    let mut solver = Solver::new();
    solver.new_var();
    solver.new_var();
    assert!(solver.add_clause_dimacs(&[1])); // a must be true
    assert!(solver.add_clause_dimacs(&[1, 2]));

    assert_eq!(solver.solve(), SolverResult::Sat);

    let (res, core) = solver.solve_with_assumptions(&[Lit::from_dimacs(-1)]);
    assert_eq!(
        res,
        SolverResult::Unsat,
        "¬a contradicts the unit clause (a) — genuinely UNSAT"
    );
    assert!(core.is_some(), "UNSAT under assumptions must return a core");
}

// ---------------------------------------------------------------------------
// Finding 1: binary-graph reason clauses must not drop antecedents in analyze()
// ---------------------------------------------------------------------------

#[test]
fn binary_reason_conflict_keeps_instance_sat() {
    // A satisfiable instance dominated by binary clauses so that unit propagation
    // is driven by the binary implication graph (the code path whose reason clause
    // stores the implied literal at index 1). If analyze() drops the index-0
    // antecedent, learned clauses become over-strong and the solver can wrongly
    // report UNSAT. We assert SAT and validate the returned model.
    //
    // Construction: satisfying assignment is x_i = true for all i. All binary
    // implication chains are consistent with that. Extra clauses force decisions
    // and conflicts so conflict analysis actually resolves through binary reasons.
    let clauses: Vec<Vec<i32>> = vec![
        // implication chain 1 -> 2 -> 3 -> 4 -> 5 (as ¬x_i ∨ x_{i+1})
        vec![-1, 2],
        vec![-2, 3],
        vec![-3, 4],
        vec![-4, 5],
        // back-pressure implications 6 -> 7 -> 8
        vec![-6, 7],
        vec![-7, 8],
        // cross links
        vec![-5, 6],
        vec![-8, 1],
        // seed clauses that must be satisfied by all-true
        vec![1, 3],
        vec![2, 8],
        vec![4, 6],
        vec![5, 7],
        // a longer clause to force at least one multi-level decision
        vec![1, 2, 3, 4, 5, 6, 7, 8],
    ];

    let mut solver = Solver::new();
    for _ in 0..8 {
        solver.new_var();
    }
    for c in &clauses {
        assert!(solver.add_clause_dimacs(c));
    }

    let res = solver.solve();
    assert_eq!(
        res,
        SolverResult::Sat,
        "binary-implication-heavy instance is SAT (all-true is a model)"
    );
    assert!(
        model_satisfies(&solver, &clauses),
        "returned model must satisfy every clause"
    );
}

#[test]
fn binary_chain_forced_false_is_sat_with_valid_model() {
    // Assign var 1 false via a decision-forcing structure and let the binary chain
    // propagate. The satisfying model sets all of 1..=6 to false; binary clauses
    // (x_i ∨ ¬x_{i+1}) i.e. dimacs [i, -(i+1)] encode x_{i+1} -> x_i. Forcing the
    // head false ripples through the chain. This exercises the OTHER binary-graph
    // direction (implied literal at index 0 vs 1 depending on sort order).
    let clauses: Vec<Vec<i32>> = vec![
        vec![-1],                     // x1 must be false
        vec![1, -2],                  // x2 -> x1  (so x2 false)
        vec![2, -3],                  // x3 -> x2
        vec![3, -4],                  // x4 -> x3
        vec![4, -5],                  // x5 -> x4
        vec![5, -6],                  // x6 -> x5
        vec![-1, -2, -3, -4, -5, -6], // satisfied when all false
    ];
    let mut solver = Solver::new();
    for _ in 0..6 {
        solver.new_var();
    }
    for c in &clauses {
        assert!(solver.add_clause_dimacs(c));
    }
    assert_eq!(solver.solve(), SolverResult::Sat);
    assert!(model_satisfies(&solver, &clauses));
    // Every variable must be false in the model.
    for i in 0..6 {
        assert_eq!(
            solver.model_value(oxiz_sat::Var::new(i)),
            LBool::False,
            "x{} must be false",
            i + 1
        );
    }
}

// ---------------------------------------------------------------------------
// Finding 2: clause slot reuse must not corrupt propagation under heavy deletion
// ---------------------------------------------------------------------------

#[test]
fn heavy_learning_and_deletion_stays_sound() {
    use oxiz_sat::SolverConfig;

    // Force very frequent clause-database reduction so freed slots would (under the
    // old bug) be recycled while stale watchers still reference them. Solve a
    // satisfiable instance that produces many learned clauses; the answer must stay
    // SAT with a valid model.
    //
    // Every clause below contains at least one positive literal, so the all-true
    // assignment is a model (the instance is provably SAT). With the default
    // negative phase the solver first explores all-false, generating plenty of
    // conflicts and learned clauses to exercise the deletion/reuse path.
    let clauses: Vec<Vec<i32>> = vec![
        vec![1, -2, -3],
        vec![2, -3, -4],
        vec![3, -4, -5],
        vec![4, -5, -6],
        vec![5, -6, -7],
        vec![6, -7, -8],
        vec![7, -8, -9],
        vec![8, -9, -10],
        vec![9, -10, -1],
        vec![10, -1, -2],
        vec![1, 2, 3],
        vec![4, 5, 6],
        vec![7, 8, 9],
        vec![10, 1, 4],
        vec![2, 5, 8],
        vec![3, 6, 9],
        vec![-1, -2, -3, 4],
        vec![-4, -5, -6, 7],
        vec![-7, -8, -9, 10],
        vec![1, -5, -9],
    ];

    let config = SolverConfig {
        clause_deletion_threshold: 1, // reduce after essentially every conflict
        ..SolverConfig::default()
    };
    let mut solver = Solver::with_config(config);
    for _ in 0..10 {
        solver.new_var();
    }
    for c in &clauses {
        assert!(solver.add_clause_dimacs(c));
    }

    let res = solver.solve();
    assert_eq!(
        res,
        SolverResult::Sat,
        "instance is SAT; heavy clause deletion must not corrupt propagation"
    );
    assert!(
        model_satisfies(&solver, &clauses),
        "model must satisfy every clause even after aggressive clause reuse/deletion"
    );
}

#[test]
fn unsat_instance_stays_unsat_under_deletion() {
    use oxiz_sat::SolverConfig;

    // PHP(3,2) is UNSAT; with aggressive deletion the solver must still prove UNSAT
    // (a stale-watcher bug could produce a spurious SAT or a wrong core).
    let clauses: Vec<Vec<i32>> = vec![
        vec![1, 2],
        vec![3, 4],
        vec![5, 6],
        vec![-1, -3],
        vec![-1, -5],
        vec![-3, -5],
        vec![-2, -4],
        vec![-2, -6],
        vec![-4, -6],
    ];
    let config = SolverConfig {
        clause_deletion_threshold: 1,
        ..SolverConfig::default()
    };
    let mut solver = Solver::with_config(config);
    for _ in 0..6 {
        solver.new_var();
    }
    for c in &clauses {
        assert!(solver.add_clause_dimacs(c));
    }
    assert_eq!(
        solver.solve(),
        SolverResult::Unsat,
        "PHP(3,2) must remain UNSAT under aggressive clause deletion"
    );
}
