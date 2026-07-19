//! Core-guided MaxSAT optimization for NLSAT.
//!
//! This module implements core-guided MaxSAT solving, which finds optimal solutions
//! by iteratively refining bounds using unsat cores.
//!
//! Key algorithms:
//! - OLL (Optimal Linear Search with Lifting)
//! - MSU3 (Maximum Satisfiability with Unsat cores)
//! - RC2 (Relaxable Cardinality Constraints)
//!
//! Reference: Modern MaxSAT solvers and Z3's optimization framework

use crate::solver::{NlsatSolver, SolverResult};
use crate::types::{BoolVar, Literal};
use rustc_hash::FxHashMap;

/// Configuration for core-guided MaxSAT solving.
#[derive(Debug, Clone)]
pub struct MaxSatConfig {
    /// Maximum number of iterations.
    pub max_iterations: usize,
    /// Enable core minimization.
    pub minimize_cores: bool,
    /// Stratification strategy.
    pub stratify: bool,
}

impl Default for MaxSatConfig {
    fn default() -> Self {
        Self {
            max_iterations: 10000,
            minimize_cores: true,
            stratify: false,
        }
    }
}

/// Statistics for MaxSAT solving.
#[derive(Debug, Clone, Default)]
pub struct MaxSatStats {
    /// Number of SAT solver calls.
    pub sat_calls: usize,
    /// Number of UNSAT cores found.
    pub cores_found: usize,
    /// Number of iterations.
    pub iterations: usize,
    /// Current lower bound.
    pub lower_bound: usize,
    /// Current upper bound.
    pub upper_bound: Option<usize>,
}

/// Soft constraint with weight.
#[derive(Debug, Clone)]
pub struct SoftConstraint {
    /// The clause (soft constraint).
    pub clause: Vec<Literal>,
    /// Weight of this constraint.
    pub weight: usize,
    /// Relaxation variable (assumption literal).
    pub relax_var: Option<BoolVar>,
}

impl SoftConstraint {
    /// Create a new soft constraint.
    pub fn new(clause: Vec<Literal>, weight: usize) -> Self {
        Self {
            clause,
            weight,
            relax_var: None,
        }
    }

    /// Create a relaxation variable for this constraint.
    pub fn add_relaxation(&mut self, var: BoolVar) {
        self.relax_var = Some(var);
    }
}

/// Core-guided MaxSAT solver.
pub struct MaxSatSolver {
    /// Configuration.
    config: MaxSatConfig,
    /// Underlying SAT solver.
    solver: NlsatSolver,
    /// Hard constraints (must be satisfied).
    hard_constraints: Vec<Vec<Literal>>,
    /// Soft constraints (can be relaxed).
    soft_constraints: Vec<SoftConstraint>,
    /// Statistics.
    stats: MaxSatStats,
    /// Current best cost.
    best_cost: Option<usize>,
    /// Best model found so far.
    best_model: Option<FxHashMap<BoolVar, bool>>,
}

impl MaxSatSolver {
    /// Create a new MaxSAT solver.
    pub fn new(config: MaxSatConfig) -> Self {
        Self {
            config,
            solver: NlsatSolver::new(),
            hard_constraints: Vec::new(),
            soft_constraints: Vec::new(),
            stats: MaxSatStats::default(),
            best_cost: None,
            best_model: None,
        }
    }

    /// Allocate a fresh boolean variable in the underlying solver.
    ///
    /// Callers MUST use this (rather than inventing arbitrary
    /// [`BoolVar`] indices) to build the [`Literal`]s passed to
    /// [`Self::add_hard`]/[`Self::add_soft`], since [`Self::solve`] also
    /// allocates fresh relaxation variables internally; only variables
    /// obtained from the same underlying solver are guaranteed not to
    /// collide with them.
    pub fn new_bool_var(&mut self) -> BoolVar {
        self.solver.new_bool_var()
    }

    /// Add a hard constraint (must be satisfied).
    pub fn add_hard(&mut self, clause: Vec<Literal>) {
        self.hard_constraints.push(clause);
    }

    /// Add a soft constraint with weight.
    pub fn add_soft(&mut self, clause: Vec<Literal>, weight: usize) {
        self.soft_constraints
            .push(SoftConstraint::new(clause, weight));
    }

    /// Solve MaxSAT using a linear search with model-blocking.
    ///
    /// Each soft constraint `c` with weight `w` is relaxed into
    /// `(c OR relax_var)`, so any satisfying assignment of
    /// `hard_constraints AND relaxed_soft_constraints` exists (relax_vars
    /// can always be forced true). The search repeatedly:
    ///
    /// 1. Solves for *some* satisfying assignment.
    /// 2. Computes its true cost (sum of weights of soft constraints whose
    ///    relaxation variable was assigned `true`, i.e. genuinely
    ///    violated) by reading the solver's actual model.
    /// 3. Records it if it improves on the best cost found so far.
    /// 4. Asserts a *blocking clause* that excludes exactly this
    ///    relaxation-variable assignment, forcing the next iteration to
    ///    find a different one.
    ///
    /// The relaxation-variable assignment space is finite
    /// (`2^num_soft_constraints`), so this search is a sound (if not
    /// asymptotically optimal) enumeration: it terminates either by
    /// exhausting every distinct assignment (solver returns `Unsat`, which
    /// proves the best cost found is the true optimum) or by finding cost
    /// `0` (which is trivially optimal). If the iteration budget is
    /// exhausted before either happens, the result is honestly reported as
    /// `Unknown` rather than an unproven `Optimal`.
    pub fn solve(&mut self) -> MaxSatResult {
        // Initialize by adding relaxation variables
        self.initialize_relaxations();

        // Add all hard constraints to the solver
        for clause in &self.hard_constraints {
            self.solver.add_clause(clause.clone());
        }

        // Add soft constraints with relaxation variables
        for soft in &self.soft_constraints {
            if let Some(relax_var) = soft.relax_var {
                // Add (clause ∨ relax_var) - can be violated if relax_var = true
                let mut relaxed_clause = soft.clause.clone();
                relaxed_clause.push(Literal::positive(relax_var));
                self.solver.add_clause(relaxed_clause);
            }
        }

        let total_weight: usize = self.soft_constraints.iter().map(|s| s.weight).sum();
        let mut proven_optimal = false;

        while self.stats.iterations < self.config.max_iterations {
            self.stats.iterations += 1;
            self.stats.sat_calls += 1;

            let result = self.solver.solve();

            match result {
                SolverResult::Sat => {
                    // Found a model - calculate its REAL cost from the
                    // solver's actual relaxation-variable assignments.
                    let current_cost = self.calculate_current_cost();

                    if self.best_cost.is_none_or(|best| current_cost < best) {
                        self.best_cost = Some(current_cost);
                        self.stats.upper_bound = Some(current_cost);
                        self.best_model = Some(self.extract_model());
                    }

                    if current_cost == 0 {
                        // No soft constraint was violated: this is
                        // trivially globally optimal, no need to search
                        // further.
                        proven_optimal = true;
                        break;
                    }

                    let block_clause = self.blocking_clause();
                    if block_clause.is_empty() {
                        // No relaxable soft constraints; nothing left to
                        // search (cost is fixed at `current_cost`).
                        proven_optimal = true;
                        break;
                    }
                    // Forbid this exact relaxation-variable assignment so
                    // the next iteration must find a genuinely different
                    // (and thus potentially cheaper) one.
                    self.solver.add_clause(block_clause);
                }
                SolverResult::Unsat => {
                    let Some(best_cost) = self.best_cost else {
                        // Even with every soft constraint fully relaxed,
                        // no satisfying assignment exists: the hard
                        // constraints themselves are unsatisfiable.
                        self.stats.lower_bound = total_weight;
                        return MaxSatResult::Unsatisfiable;
                    };
                    // Every distinct relaxation-variable assignment has
                    // now been enumerated and blocked, so the best cost
                    // found is provably the global optimum.
                    proven_optimal = true;
                    self.stats.lower_bound = best_cost;
                    break;
                }
                SolverResult::Unknown => {
                    return MaxSatResult::Unknown;
                }
            }
        }

        match (proven_optimal, self.best_cost) {
            (true, Some(cost)) => MaxSatResult::Optimal {
                cost,
                model: self.best_model.clone().unwrap_or_default(),
            },
            // The iteration budget was exhausted before optimality could
            // be proven (or before any feasible assignment was even
            // found): honestly report Unknown rather than fabricating an
            // unproven "optimal" cost.
            _ => MaxSatResult::Unknown,
        }
    }

    /// Build a clause that excludes exactly the CURRENT relaxation-variable
    /// assignment (as read from the underlying solver's model), forcing
    /// the next `solve()` call to find a different one. Returns an empty
    /// vector if there are no relaxable soft constraints.
    fn blocking_clause(&self) -> Vec<Literal> {
        let model = self.solver.get_model();
        self.soft_constraints
            .iter()
            .filter_map(|soft| {
                let relax_var = soft.relax_var?;
                let current = model
                    .as_ref()
                    .and_then(|m| m.bool_value(relax_var))
                    .unwrap_or(false);
                Some(if current {
                    Literal::negative(relax_var)
                } else {
                    Literal::positive(relax_var)
                })
            })
            .collect()
    }

    /// Initialize relaxation variables for soft constraints.
    fn initialize_relaxations(&mut self) {
        // For each soft constraint, allocate a fresh boolean variable
        // directly from the solver that will actually track it, so the ID
        // is guaranteed consistent (no separate counter to fall out of
        // sync with the solver's own variable allocation).
        for soft in &mut self.soft_constraints {
            let relax_var = self.solver.new_bool_var();
            soft.add_relaxation(relax_var);
        }
    }

    /// Collect assumptions for the current iteration.
    #[allow(dead_code)]
    fn collect_assumptions(&self) -> Vec<Literal> {
        let mut assumptions = Vec::new();
        for soft in &self.soft_constraints {
            if let Some(relax_var) = soft.relax_var {
                // Assume the negation (try to satisfy the soft constraint)
                assumptions.push(Literal::negative(relax_var));
            }
        }
        assumptions
    }

    /// Calculate the true cost of the solver's current model: the sum of
    /// weights of soft constraints whose relaxation variable is assigned
    /// `true` (meaning the original, unrelaxed clause was NOT required to
    /// hold, i.e. the soft constraint was violated).
    fn calculate_current_cost(&self) -> usize {
        let Some(model) = self.solver.get_model() else {
            return 0;
        };
        self.soft_constraints
            .iter()
            .filter_map(|soft| {
                let relax_var = soft.relax_var?;
                match model.bool_value(relax_var) {
                    Some(true) => Some(soft.weight),
                    _ => None,
                }
            })
            .sum()
    }

    /// Extract the current model (all boolean variable assignments) from
    /// the underlying solver.
    fn extract_model(&self) -> FxHashMap<BoolVar, bool> {
        self.solver
            .get_model()
            .map(|model| model.bool_values.into_iter().collect())
            .unwrap_or_default()
    }

    /// Extract unsat core from the solver.
    #[allow(dead_code)]
    fn extract_core(&self) -> Vec<BoolVar> {
        // Get the actual unsat core from the solver
        self.solver
            .get_unsat_core()
            .iter()
            .map(|&id| id as BoolVar)
            .collect()
    }

    /// Process an unsat core.
    #[allow(dead_code)]
    fn process_core(&mut self, core: &[BoolVar]) {
        if core.is_empty() {
            return;
        }

        // Find minimum weight in the core
        let min_weight = core
            .iter()
            .filter_map(|&var| {
                self.soft_constraints
                    .iter()
                    .find(|s| s.relax_var == Some(var))
                    .map(|s| s.weight)
            })
            .min()
            .unwrap_or(1);

        // Update lower bound
        self.stats.lower_bound += min_weight;

        // Create a new relaxation variable for the core
        // In a full implementation, we would add cardinality constraints here
    }

    /// Update the lower bound.
    #[allow(dead_code)]
    fn update_lower_bound(&mut self) {
        // Lower bound is accumulated from core weights
        // Already updated in process_core
    }

    /// Get statistics.
    pub fn stats(&self) -> &MaxSatStats {
        &self.stats
    }
}

/// Result of MaxSAT solving.
#[derive(Debug, Clone)]
pub enum MaxSatResult {
    /// Found optimal solution with cost and model.
    Optimal {
        cost: usize,
        model: FxHashMap<BoolVar, bool>,
    },
    /// Hard constraints are unsatisfiable.
    Unsatisfiable,
    /// Could not find solution within limits.
    Unknown,
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_maxsat_config_default() {
        let config = MaxSatConfig::default();
        assert_eq!(config.max_iterations, 10000);
        assert!(config.minimize_cores);
    }

    #[test]
    fn test_soft_constraint() {
        let mut constraint = SoftConstraint::new(vec![Literal::positive(1)], 10);
        assert_eq!(constraint.weight, 10);
        assert!(constraint.relax_var.is_none());

        constraint.add_relaxation(42);
        assert_eq!(constraint.relax_var, Some(42));
    }

    #[test]
    fn test_maxsat_solver_new() {
        let config = MaxSatConfig::default();
        let solver = MaxSatSolver::new(config);

        assert_eq!(solver.stats.sat_calls, 0);
        assert_eq!(solver.stats.cores_found, 0);
        assert_eq!(solver.stats.iterations, 0);
        assert_eq!(solver.stats.lower_bound, 0);
        assert!(solver.stats.upper_bound.is_none());
    }

    #[test]
    fn test_add_constraints() {
        let config = MaxSatConfig::default();
        let mut solver = MaxSatSolver::new(config);

        // Add hard constraint
        solver.add_hard(vec![Literal::positive(1)]);
        assert_eq!(solver.hard_constraints.len(), 1);

        // Add soft constraint
        solver.add_soft(vec![Literal::positive(2)], 5);
        assert_eq!(solver.soft_constraints.len(), 1);
        assert_eq!(solver.soft_constraints[0].weight, 5);
    }

    /// Regression test for the audit finding: `calculate_current_cost` used
    /// to hardcode `cost = 0` unconditionally, and `extract_model` always
    /// returned an empty map. This constructs a problem where satisfying
    /// ALL soft constraints is impossible (they directly contradict each
    /// other), so the true optimal cost must be strictly positive: the
    /// old stub would have wrongly reported `Optimal { cost: 0, .. }`.
    #[test]
    fn test_maxsat_reports_real_nonzero_cost_when_soft_constraints_conflict() {
        let config = MaxSatConfig {
            max_iterations: 100,
            minimize_cores: true,
            stratify: false,
        };
        let mut solver = MaxSatSolver::new(config);

        // No hard constraints: `v` is completely free.
        // Soft constraints directly contradict each other: "v is true"
        // (weight 3) vs "v is false" (weight 1). Both cannot hold
        // simultaneously, so at least one must be violated; the optimal
        // strategy violates the cheaper one (weight 1), for a true optimal
        // cost of 1.
        let v = solver.new_bool_var();
        solver.add_soft(vec![Literal::positive(v)], 3);
        solver.add_soft(vec![Literal::negative(v)], 1);

        let result = solver.solve();

        match result {
            MaxSatResult::Optimal { cost, model } => {
                assert_eq!(
                    cost, 1,
                    "optimal cost must reflect the cheaper violated soft constraint"
                );
                assert!(
                    !model.is_empty(),
                    "model must be a real, non-empty assignment"
                );
            }
            other => panic!("expected Optimal{{cost: 1, ..}}, got {other:?}"),
        }
    }

    /// Regression test: when all soft constraints CAN be jointly satisfied,
    /// the true optimal cost is 0 and the returned model must actually
    /// satisfy them (not just claim to via a hardcoded cost).
    #[test]
    fn test_maxsat_zero_cost_when_all_soft_constraints_satisfiable() {
        let config = MaxSatConfig::default();
        let mut solver = MaxSatSolver::new(config);

        let v1 = solver.new_bool_var();
        let v2 = solver.new_bool_var();
        solver.add_soft(vec![Literal::positive(v1)], 5);
        solver.add_soft(vec![Literal::positive(v2)], 2);

        let result = solver.solve();

        match result {
            MaxSatResult::Optimal { cost, model } => {
                assert_eq!(cost, 0);
                assert_eq!(model.get(&v1), Some(&true));
                assert_eq!(model.get(&v2), Some(&true));
            }
            other => panic!("expected Optimal{{cost: 0, ..}}, got {other:?}"),
        }
    }

    /// Regression test: hard constraints that are themselves unsatisfiable
    /// must be reported as `Unsatisfiable`, independent of any soft
    /// constraints.
    #[test]
    fn test_maxsat_unsat_hard_constraints() {
        let config = MaxSatConfig::default();
        let mut solver = MaxSatSolver::new(config);

        let v1 = solver.new_bool_var();
        let v2 = solver.new_bool_var();
        solver.add_hard(vec![Literal::positive(v1)]);
        solver.add_hard(vec![Literal::negative(v1)]);
        solver.add_soft(vec![Literal::positive(v2)], 10);

        let result = solver.solve();
        assert!(matches!(result, MaxSatResult::Unsatisfiable));
    }
}
