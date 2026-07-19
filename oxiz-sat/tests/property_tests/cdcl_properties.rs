//! Property-based tests for CDCL SAT solver
//!
//! Tests:
//! - Clause database integrity
//! - Variable assignment consistency
//! - Resolution correctness
//! - Restart strategies
//! - Clause deletion safety

use oxiz_sat::*;
use proptest::prelude::*;

/// Verify that `solver`'s current model satisfies every one of `clauses`
/// (DIMACS-style signed-literal clauses, `1`-indexed variables matching
/// `add_clause_dimacs`/`add_clause_dimacs`'s convention). A clause is
/// satisfied iff at least one of its literals evaluates to true in the
/// model.
///
/// Every property test below that asserts a specific `SolverResult::Sat`
/// outcome (rather than merely "didn't return Unknown") must also call this
/// to confirm the returned *model* actually satisfies the CNF -- a solver
/// bug that returns `Sat` with an inconsistent model would otherwise slip
/// through every one of these tests undetected, since none of them
/// previously inspected the model at all.
fn model_satisfies_dimacs(solver: &Solver, clauses: &[Vec<i32>]) -> bool {
    clauses.iter().all(|clause| {
        clause.iter().any(|&lit| {
            let var = Var(lit.unsigned_abs() - 1);
            let value = solver.model_value(var);
            if lit > 0 {
                value == LBool::True
            } else {
                value == LBool::False
            }
        })
    })
}

#[cfg(test)]
mod cdcl_basic_properties {
    use super::*;

    #[test]
    fn empty_cnf_is_sat() {
        let mut solver = Solver::new();
        let result = solver.solve();

        assert_eq!(result, SolverResult::Sat);
    }

    proptest! {
        #[test]
        fn single_unit_clause_is_sat(lit in -100i32..100i32) {
            if lit != 0 {
                let mut solver = Solver::new();
                let _var = lit.unsigned_abs();
                solver.new_var();

                let clauses = vec![vec![lit]];
                solver.add_clause_dimacs(&clauses[0]);
                let result = solver.solve();

                // A single unit clause is always satisfiable: the sole
                // constraint is that one literal.
                prop_assert_eq!(result, SolverResult::Sat);
                prop_assert!(
                    model_satisfies_dimacs(&solver, &clauses),
                    "model must actually satisfy the unit clause {:?}",
                    clauses
                );
            }
        }

        #[test]
        fn contradictory_units_are_unsat(v in 1u32..100u32) {
            let mut solver = Solver::new();

            for _ in 0..v {
                solver.new_var();
            }

            solver.add_clause_dimacs(&[v as i32]);
            solver.add_clause_dimacs(&[-(v as i32)]);

            let result = solver.solve();

            prop_assert_eq!(result, SolverResult::Unsat);
        }

        #[test]
        fn tautology_clause_ignorable(v in 1u32..50u32) {
            let mut solver = Solver::new();

            for _ in 0..v {
                solver.new_var();
            }

            // v ∨ ¬v (tautology)
            let clauses = vec![vec![v as i32, -(v as i32)]];
            solver.add_clause_dimacs(&clauses[0]);

            let result = solver.solve();

            // A tautology is always satisfied, so the CNF is equivalent to
            // the empty formula.
            prop_assert_eq!(result, SolverResult::Sat);
            prop_assert!(model_satisfies_dimacs(&solver, &clauses));
        }

        #[test]
        fn binary_clause_sat(v1 in 1u32..50u32, v2 in 1u32..50u32) {
            if v1 != v2 {
                let mut solver = Solver::new();
                let max_var = v1.max(v2);

                for _ in 0..=max_var {
                    solver.new_var();
                }

                // v1 ∨ v2
                let clauses = vec![vec![v1 as i32, v2 as i32]];
                solver.add_clause_dimacs(&clauses[0]);

                let result = solver.solve();

                // A single 2-clause is always satisfiable.
                prop_assert_eq!(result, SolverResult::Sat);
                prop_assert!(model_satisfies_dimacs(&solver, &clauses));
            }
        }

        #[test]
        fn horn_clause_decidable(
            v1 in 1u32..20u32,
            v2 in 1u32..20u32,
            v3 in 1u32..20u32
        ) {
            let mut solver = Solver::new();
            let max_var = v1.max(v2).max(v3);

            for _ in 0..=max_var {
                solver.new_var();
            }

            // Horn clause: ¬v1 ∨ ¬v2 ∨ v3
            let clauses = vec![vec![-(v1 as i32), -(v2 as i32), v3 as i32]];
            solver.add_clause_dimacs(&clauses[0]);

            let result = solver.solve();

            // A single Horn clause is always satisfiable (e.g. v1 = false
            // alone already satisfies it), so the known answer here is
            // `Sat`, not merely "decidable" -- and the model must actually
            // satisfy the clause.
            prop_assert_eq!(result, SolverResult::Sat);
            prop_assert!(model_satisfies_dimacs(&solver, &clauses));
        }
    }
}

#[cfg(test)]
mod clause_learning_properties {
    use super::*;

    proptest! {
        #[test]
        fn learned_clause_prevents_reexploration(v in 2u32..10u32) {
            let mut solver = Solver::new();

            for _ in 0..v {
                solver.new_var();
            }

            // Create conflict scenario
            let mut clauses: Vec<Vec<i32>> = Vec::new();
            for i in 1..v {
                clauses.push(vec![i as i32, (i + 1) as i32]);
            }
            clauses.push(vec![-(v as i32)]);
            clauses.push(vec![1]);

            for clause in &clauses {
                solver.add_clause_dimacs(clause);
            }

            let result = solver.solve();

            // var(1) is forced true (satisfying the first chain link
            // regardless of anything else), and var(v-1) can always be set
            // true to satisfy both the chain link into it and the final
            // link out to the now-forced-false var(v): always satisfiable.
            prop_assert_eq!(result, SolverResult::Sat);
            prop_assert!(
                model_satisfies_dimacs(&solver, &clauses),
                "model must satisfy every clause, including the learned-clause-driven chain"
            );
        }

        #[test]
        fn conflict_clause_is_asserting(
            v1 in 1u32..10u32,
            v2 in 1u32..10u32,
            v3 in 1u32..10u32
        ) {
            if v1 != v2 && v2 != v3 && v1 != v3 {
                let mut solver = Solver::new();
                let max_var = v1.max(v2).max(v3);

                for _ in 0..=max_var {
                    solver.new_var();
                }

                // (v1 ∨ v2 ∨ v3) ∧ ¬v1 ∧ ¬v2 ∧ ¬v3
                solver.add_clause_dimacs(&[v1 as i32, v2 as i32, v3 as i32]);
                solver.add_clause_dimacs(&[-(v1 as i32)]);
                solver.add_clause_dimacs(&[-(v2 as i32)]);
                solver.add_clause_dimacs(&[-(v3 as i32)]);

                let result = solver.solve();

                prop_assert_eq!(result, SolverResult::Unsat);
            }
        }

        #[test]
        fn learned_clauses_cumulative(n in 2usize..6usize) {
            let mut solver = Solver::new();

            for _ in 0..n {
                solver.new_var();
            }

            // Add conflicting constraints incrementally
            for i in 1..n {
                solver.add_clause_dimacs(&[i as i32, (i+1) as i32]);
                solver.add_clause_dimacs(&[-(i as i32)]);
            }

            solver.add_clause_dimacs(&[-(n as i32)]);
            solver.add_clause_dimacs(&[1]);

            let result = solver.solve();

            // The loop above always asserts `¬var(1)` (its `i = 1` case),
            // which directly contradicts the trailing unit clause
            // `var(1) = true`: this instance is unconditionally
            // unsatisfiable, not merely "decidable".
            prop_assert_eq!(result, SolverResult::Unsat);
        }
    }
}

#[cfg(test)]
mod resolution_properties {
    use super::*;

    proptest! {
        #[test]
        fn resolution_preserves_satisfiability(
            v1 in 1u32..20u32,
            v2 in 1u32..20u32,
            v3 in 1u32..20u32
        ) {
            if v1 != v2 && v2 != v3 && v1 != v3 {
                let mut solver = Solver::new();
                let max_var = v1.max(v2).max(v3);

                for _ in 0..=max_var {
                    solver.new_var();
                }

                // (v1 ∨ v2) ∧ (¬v2 ∨ v3)
                // Resolution gives: (v1 ∨ v3)
                let clauses = vec![
                    vec![v1 as i32, v2 as i32],
                    vec![-(v2 as i32), v3 as i32],
                ];
                for clause in &clauses {
                    solver.add_clause_dimacs(clause);
                }

                let result = solver.solve();

                prop_assert_eq!(result, SolverResult::Sat);
                prop_assert!(model_satisfies_dimacs(&solver, &clauses));
            }
        }

        #[test]
        fn resolution_detects_empty_clause(v in 1u32..20u32) {
            let mut solver = Solver::new();

            for _ in 0..v {
                solver.new_var();
            }

            // v ∧ ¬v leads to empty clause
            solver.add_clause_dimacs(&[v as i32]);
            solver.add_clause_dimacs(&[-(v as i32)]);

            let result = solver.solve();

            prop_assert_eq!(result, SolverResult::Unsat);
        }

        #[test]
        fn subsumption_removes_redundant_clauses(
            v1 in 1u32..15u32,
            v2 in 1u32..15u32
        ) {
            if v1 != v2 {
                let mut solver = Solver::new();
                let max_var = v1.max(v2);

                for _ in 0..=max_var {
                    solver.new_var();
                }

                // v1 subsumes (v1 ∨ v2)
                let clauses = vec![vec![v1 as i32], vec![v1 as i32, v2 as i32]];
                for clause in &clauses {
                    solver.add_clause_dimacs(clause);
                }

                let result = solver.solve();

                prop_assert_eq!(result, SolverResult::Sat);
                prop_assert!(model_satisfies_dimacs(&solver, &clauses));
            }
        }
    }
}

#[cfg(test)]
mod restart_properties {
    use super::*;

    proptest! {
        #[test]
        fn restart_preserves_learned_clauses(v in 2u32..8u32) {
            let mut solver = Solver::new();

            for _ in 0..v {
                solver.new_var();
            }

            // Add some clauses
            let mut clauses: Vec<Vec<i32>> = Vec::new();
            for i in 1..v {
                clauses.push(vec![i as i32, (i + 1) as i32]);
            }
            for clause in &clauses {
                solver.add_clause_dimacs(clause);
            }

            // Solve (restarts are enabled by default in SolverConfig)
            let result = solver.solve();

            // An unconstrained chain of 2-clauses (no units, no negations)
            // is always satisfiable -- e.g. by setting every variable true.
            prop_assert_eq!(result, SolverResult::Sat);
            prop_assert!(
                model_satisfies_dimacs(&solver, &clauses),
                "model must satisfy every clause even after restarts"
            );
        }

        #[test]
        fn restart_doesnt_affect_correctness(n in 2usize..6usize) {
            // Create solver with Luby restarts
            let config1 = SolverConfig {
                restart_strategy: RestartStrategy::Luby,
                ..SolverConfig::default()
            };
            let mut solver1 = Solver::with_config(config1);

            // Create solver with Geometric restarts
            let config2 = SolverConfig {
                restart_strategy: RestartStrategy::Geometric,
                ..SolverConfig::default()
            };
            let mut solver2 = Solver::with_config(config2);

            for _ in 0..n {
                solver1.new_var();
                solver2.new_var();
            }

            // Add same clauses to both
            let mut clauses: Vec<Vec<i32>> = Vec::new();
            for i in 1..n {
                clauses.push(vec![i as i32, (i + 1) as i32]);
            }
            for clause in &clauses {
                solver1.add_clause_dimacs(clause);
                solver2.add_clause_dimacs(clause);
            }

            let result1 = solver1.solve();
            let result2 = solver2.solve();

            // Both should give same result
            prop_assert_eq!(result1, result2);

            // Same reasoning as `restart_preserves_learned_clauses`: an
            // unconstrained clause chain is always satisfiable, and each
            // solver's own model must satisfy it independently of which
            // restart strategy was used.
            prop_assert_eq!(result1, SolverResult::Sat);
            prop_assert!(model_satisfies_dimacs(&solver1, &clauses));
            prop_assert!(model_satisfies_dimacs(&solver2, &clauses));
        }
    }
}

#[cfg(test)]
mod variable_elimination_properties {
    use super::*;

    proptest! {
        #[test]
        fn pure_literal_elimination(v in 1u32..20u32) {
            let mut solver = Solver::new();

            for _ in 0..=v {
                solver.new_var();
            }

            // v appears only positively (pure literal)
            let clauses = vec![vec![v as i32, 1], vec![v as i32, 2]];
            for clause in &clauses {
                solver.add_clause_dimacs(clause);
            }

            let result = solver.solve();

            prop_assert_eq!(result, SolverResult::Sat);
            prop_assert!(model_satisfies_dimacs(&solver, &clauses));
        }

        #[test]
        fn variable_elimination_preserves_sat(
            v1 in 1u32..15u32,
            v2 in 1u32..15u32
        ) {
            if v1 != v2 {
                let mut solver = Solver::new();
                let max_var = v1.max(v2);

                for _ in 0..=max_var {
                    solver.new_var();
                }

                // (v1 ∨ v2)
                let clauses = vec![vec![v1 as i32, v2 as i32]];
                solver.add_clause_dimacs(&clauses[0]);

                let result = solver.solve();

                prop_assert_eq!(result, SolverResult::Sat);
                prop_assert!(model_satisfies_dimacs(&solver, &clauses));
            }
        }
    }
}

#[cfg(test)]
mod clause_database_properties {
    use super::*;

    proptest! {
        #[test]
        fn clause_database_consistent_after_deletion(n in 2usize..10usize) {
            // Create solver with low clause deletion threshold to trigger deletion
            let config = SolverConfig {
                clause_deletion_threshold: 10,
                ..SolverConfig::default()
            };
            let mut solver = Solver::with_config(config);

            for _ in 0..n {
                solver.new_var();
            }

            // Add many clauses
            let mut clauses: Vec<Vec<i32>> = Vec::new();
            for i in 1..n {
                clauses.push(vec![i as i32, (i + 1) as i32]);
            }
            for clause in &clauses {
                solver.add_clause_dimacs(clause);
            }

            // Clause deletion is enabled via config
            let result = solver.solve();

            // Unconstrained clause chain: always satisfiable, and clause
            // deletion (of *learned* clauses only) must never make the
            // solver forget one of the *original* clauses above.
            prop_assert_eq!(result, SolverResult::Sat);
            prop_assert!(
                model_satisfies_dimacs(&solver, &clauses),
                "model must satisfy every original clause after clause database deletion"
            );
        }

        #[test]
        fn literal_watch_scheme_correct(
            v1 in 1u32..15u32,
            v2 in 1u32..15u32,
            v3 in 1u32..15u32
        ) {
            if v1 != v2 && v2 != v3 && v1 != v3 {
                let mut solver = Solver::new();
                let max_var = v1.max(v2).max(v3);

                for _ in 0..=max_var {
                    solver.new_var();
                }

                // (v1 ∨ v2 ∨ v3)
                let clauses = vec![
                    vec![v1 as i32, v2 as i32, v3 as i32],
                    vec![-(v1 as i32)],
                    vec![-(v2 as i32)],
                ];
                for clause in &clauses {
                    solver.add_clause_dimacs(clause);
                }

                let result = solver.solve();

                // v3 must be true
                prop_assert_eq!(result, SolverResult::Sat);
                prop_assert!(model_satisfies_dimacs(&solver, &clauses));
                prop_assert_eq!(
                    solver.model_value(Var(v3 - 1)),
                    LBool::True,
                    "v3 is forced true once v1 and v2 are both negated"
                );
            }
        }

        #[test]
        fn implication_graph_acyclic(n in 2usize..8usize) {
            let mut solver = Solver::new();

            for _ in 0..n {
                solver.new_var();
            }

            // Create implication chain (DAG structure)
            let mut clauses: Vec<Vec<i32>> = Vec::new();
            for i in 1..n {
                clauses.push(vec![-(i as i32), (i + 1) as i32]);
            }
            for clause in &clauses {
                solver.add_clause_dimacs(clause);
            }

            let result = solver.solve();

            // An unconstrained chain of implications (no unit clauses) is
            // always satisfiable, e.g. by setting every variable false.
            prop_assert_eq!(result, SolverResult::Sat);
            prop_assert!(
                model_satisfies_dimacs(&solver, &clauses),
                "model must satisfy every implication in the chain"
            );
        }
    }
}
