//! MaxHS (Maximum Satisfiability using Hitting Sets) solver.
//!
//! MaxHS is a modern MaxSAT algorithm that uses implicit hitting sets.
//! It alternates between finding minimal correction sets (MCSes) and
//! computing minimum-cost hitting sets.
//!
//! **Note**: This is a simplified placeholder implementation. A full MaxHS
//! implementation requires sophisticated MCS extraction and hitting set computation.
//!
//! Reference: Z3's maxhs implementation and the MaxHS paper by Davies & Bacchus

use crate::maxsat::{MaxSatError, MaxSatResult, MaxSatSolver, SoftClause, SoftId, Weight};
use oxiz_sat::{Lit, Solver as SatSolver, SolverResult, Var};
use rustc_hash::{FxHashMap, FxHashSet};
use thiserror::Error;

/// Errors from MaxHS
#[derive(Error, Debug)]
pub enum MaxHsError {
    /// SAT solver error
    #[error("SAT solver error: {0}")]
    SolverError(String),
    /// Hard constraints are unsatisfiable
    #[error("hard constraints unsatisfiable")]
    Unsatisfiable,
    /// Resource limit exceeded
    #[error("resource limit exceeded")]
    ResourceLimit,
}

/// Configuration for MaxHS solver
#[derive(Debug, Clone)]
pub struct MaxHsConfig {
    /// Maximum number of iterations
    pub max_iterations: u32,
    /// Use core extraction optimization
    pub use_cores: bool,
    /// Use preprocessing
    pub preprocess: bool,
}

impl Default for MaxHsConfig {
    fn default() -> Self {
        Self {
            max_iterations: 10000,
            use_cores: true,
            preprocess: true,
        }
    }
}

/// Statistics from MaxHS solving
#[derive(Debug, Clone, Default)]
pub struct MaxHsStats {
    /// Number of SAT solver calls
    pub sat_calls: u32,
    /// Number of minimal correction sets found
    pub mcses_found: u32,
    /// Number of hitting set computations
    pub hitting_sets: u32,
    /// Total number of soft clauses
    pub total_soft: u32,
}

/// Minimal Correction Set (MCS) - a minimal set of soft clauses to remove to make the formula SAT
#[derive(Debug, Clone)]
struct Mcs {
    /// Soft clause IDs in this MCS
    clauses: FxHashSet<SoftId>,
    /// Total weight of this MCS
    #[allow(dead_code)]
    weight: Weight,
}

/// MaxHS solver
pub struct MaxHsSolver {
    /// SAT solver for finding MCSes
    sat_solver: SatSolver,
    /// Hard clauses
    hard_clauses: Vec<Vec<Lit>>,
    /// Soft clauses
    soft_clauses: Vec<SoftClause>,
    /// Map from SoftId to index
    soft_map: FxHashMap<SoftId, usize>,
    /// Configuration
    config: MaxHsConfig,
    /// Statistics
    stats: MaxHsStats,
    /// Found MCSes
    mcses: Vec<Mcs>,
    /// Current best cost
    best_cost: Weight,
}

impl MaxHsSolver {
    /// Create a new MaxHS solver
    pub fn new() -> Self {
        Self::with_config(MaxHsConfig::default())
    }

    /// Create a new MaxHS solver with configuration
    pub fn with_config(config: MaxHsConfig) -> Self {
        Self {
            sat_solver: SatSolver::new(),
            hard_clauses: Vec::new(),
            soft_clauses: Vec::new(),
            soft_map: FxHashMap::default(),
            config,
            stats: MaxHsStats::default(),
            mcses: Vec::new(),
            best_cost: Weight::Infinite,
        }
    }

    /// Add a hard clause
    pub fn add_hard(&mut self, lits: impl IntoIterator<Item = Lit>) {
        let clause: Vec<Lit> = lits.into_iter().collect();
        self.sat_solver.add_clause(clause.iter().copied());
        self.hard_clauses.push(clause);
    }

    /// Add a soft clause
    pub fn add_soft(&mut self, id: SoftId, lits: impl IntoIterator<Item = Lit>, weight: Weight) {
        let clause = SoftClause::new(id, lits, weight);
        let idx = self.soft_clauses.len();
        self.soft_map.insert(id, idx);
        self.soft_clauses.push(clause);
        self.stats.total_soft += 1;
    }

    /// Solve the MaxSAT instance
    pub fn solve(&mut self) -> Result<MaxSatResult, MaxHsError> {
        // Add hard clauses to SAT solver
        for hard_clause in &self.hard_clauses {
            self.sat_solver.add_clause(hard_clause.iter().copied());
        }

        // Add all soft clauses to SAT solver initially
        for clause in &self.soft_clauses {
            self.sat_solver.add_clause(clause.lits.iter().copied());
        }

        // Main MaxHS loop
        for _ in 0..self.config.max_iterations {
            self.stats.sat_calls += 1;
            let (result, _) = self.sat_solver.solve_with_assumptions(&[]);

            match result {
                SolverResult::Sat => {
                    // `self.sat_solver` only ever contains *every* soft
                    // clause (added as a hard constraint) on the very
                    // first iteration -- once a minimal correction set
                    // (MCS) is found, `block_hitting_set` rebuilds
                    // `sat_solver` with the current hitting set's members
                    // removed (see below), so a later SAT here just
                    // confirms that removal is sufficient, not that every
                    // original soft clause is jointly satisfiable.
                    //
                    // On that genuine first-iteration SAT (`self.mcses`
                    // still empty), every soft clause co-exists in
                    // `sat_solver` and is jointly satisfiable, so the true
                    // optimum cost is 0 -- previously left unset, so
                    // `best_cost()` incorrectly reported the
                    // `Weight::Infinite` initial placeholder for such
                    // instances. On any later iteration, `best_cost` was
                    // already set to the correct value (the accepted
                    // hitting set's cost) in the `Unsat` branch below and
                    // must not be overwritten.
                    if self.mcses.is_empty() {
                        self.best_cost = Weight::zero();
                    }
                    return Ok(MaxSatResult::Optimal);
                }
                SolverResult::Unsat => {
                    // Find a minimal correction set (MCS)
                    let mcs = self.find_mcs()?;

                    if mcs.clauses.is_empty() {
                        // Hard constraints are unsatisfiable
                        return Err(MaxHsError::Unsatisfiable);
                    }

                    self.stats.mcses_found += 1;
                    self.mcses.push(mcs);

                    // Compute the true minimum-cost hitting set. `None`
                    // means the inner exact solve couldn't certify an
                    // optimum -- report that honestly rather than
                    // fabricating a result from a partial computation.
                    let Some(hitting_set) = self.compute_hitting_set()? else {
                        return Ok(MaxSatResult::Unknown);
                    };

                    // Update best cost
                    let cost: Weight = hitting_set
                        .iter()
                        .filter_map(|id| self.soft_map.get(id))
                        .filter_map(|&idx| self.soft_clauses.get(idx))
                        .map(|c| &c.weight)
                        .fold(Weight::zero(), |acc, w| acc.add(w));

                    self.best_cost = cost;

                    // Block this hitting set and continue
                    self.block_hitting_set(&hitting_set);
                }
                SolverResult::Unknown => {
                    return Ok(MaxSatResult::Unknown);
                }
            }
        }

        Ok(MaxSatResult::Unknown)
    }

    /// Find a minimal correction set (MCS)
    fn find_mcs(&mut self) -> Result<Mcs, MaxHsError> {
        // An MCS is a minimal set of soft clauses whose removal makes the formula SAT
        // Start with all soft clauses as candidates, then minimize

        let mut candidate: FxHashSet<SoftId> = self.soft_clauses.iter().map(|c| c.id).collect();

        // Minimize: try removing each clause from the candidate
        for &id in &candidate.clone() {
            let mut test_candidate = candidate.clone();
            test_candidate.remove(&id);

            // Test if removing the test_candidate makes formula SAT
            let mut test_solver = SatSolver::new();

            // Add hard clauses
            for hard_clause in &self.hard_clauses {
                test_solver.add_clause(hard_clause.iter().copied());
            }

            // Add soft clauses NOT in test_candidate
            for clause in &self.soft_clauses {
                if !test_candidate.contains(&clause.id) {
                    test_solver.add_clause(clause.lits.iter().copied());
                }
            }

            let (result, _) = test_solver.solve_with_assumptions(&[]);
            if matches!(result, SolverResult::Sat) {
                // Removing test_candidate makes it SAT, so we can shrink the candidate
                candidate = test_candidate;
            }
        }

        // Compute total weight
        let weight = candidate
            .iter()
            .filter_map(|id| self.soft_map.get(id))
            .filter_map(|&idx| self.soft_clauses.get(idx))
            .map(|c| &c.weight)
            .fold(Weight::zero(), |acc, w| acc.add(w));

        Ok(Mcs {
            clauses: candidate,
            weight,
        })
    }

    /// Get soft clauses that are in conflict
    #[allow(dead_code)]
    fn get_unsat_soft_clauses(&self) -> Vec<SoftId> {
        // Simplified: return all soft clause IDs
        // A real implementation would use core extraction
        self.soft_clauses.iter().map(|c| c.id).collect()
    }

    /// Compute the true minimum-cost hitting set of all MCSes found so far.
    ///
    /// This used to greedily hit each MCS with its own locally-cheapest
    /// clause (skipping MCSes already hit by an earlier, unrelated
    /// choice), which is a well-known suboptimal heuristic for weighted
    /// hitting set/set-cover: it can miss a globally cheaper selection
    /// that hits several MCSes at once. `solve()` nonetheless reported
    /// `MaxSatResult::Optimal` on convergence, certifying a cost bound
    /// that was not actually proven minimal.
    ///
    /// This is now solved *exactly*: minimizing the total weight of
    /// selected clauses subject to "every MCS has >=1 selected member" is
    /// itself a weighted MaxSAT instance (one boolean `sel_s` per
    /// candidate clause, one hard "at least one selected" clause per MCS,
    /// one soft `¬sel_s` clause per candidate weighted by its cost), so it
    /// is delegated to [`MaxSatSolver`] -- the same core-guided solver
    /// this crate already proves correct -- rather than reusing the
    /// unsound greedy shortcut.
    ///
    /// Returns `Ok(None)` (never a fabricated hitting set) if the inner
    /// solve can't certify an exact optimum within its own resource
    /// limits.
    fn compute_hitting_set(&mut self) -> Result<Option<FxHashSet<SoftId>>, MaxHsError> {
        self.stats.hitting_sets += 1;

        let mut candidate_ids: Vec<SoftId> = self
            .mcses
            .iter()
            .flat_map(|m| m.clauses.iter().copied())
            .collect();
        candidate_ids.sort_unstable_by_key(|id| id.0);
        candidate_ids.dedup();

        if candidate_ids.is_empty() {
            return Ok(Some(FxHashSet::default()));
        }

        let mut sel_var: FxHashMap<SoftId, Var> = FxHashMap::default();
        for (i, &id) in candidate_ids.iter().enumerate() {
            sel_var.insert(id, Var(i as u32));
        }

        let mut hs_solver = MaxSatSolver::new();

        // Hard: every MCS must have at least one selected member.
        for mcs in &self.mcses {
            let clause: Vec<Lit> = mcs
                .clauses
                .iter()
                .filter_map(|id| sel_var.get(id).map(|&v| Lit::pos(v)))
                .collect();
            if clause.is_empty() {
                // An MCS with no candidates mapped to a selection variable
                // can never be hit -- the hitting-set problem itself is
                // infeasible; report honestly rather than silently
                // proceeding.
                return Ok(None);
            }
            hs_solver.add_hard(clause);
        }

        // Soft: prefer NOT selecting each clause, weighted by its cost --
        // minimizing total selected weight is exactly maximizing
        // satisfaction of these negated-selection soft clauses.
        let mut hs_soft_to_id: FxHashMap<SoftId, SoftId> = FxHashMap::default();
        for &id in &candidate_ids {
            let var = sel_var[&id];
            let weight = self
                .soft_map
                .get(&id)
                .and_then(|&idx| self.soft_clauses.get(idx))
                .map(|c| c.weight.clone())
                .unwrap_or_else(Weight::one);
            let hs_soft_id = hs_solver.add_soft_weighted([Lit::neg(var)], weight);
            hs_soft_to_id.insert(hs_soft_id, id);
        }

        let solve_result = hs_solver.solve();
        match solve_result {
            Ok(MaxSatResult::Optimal) => {
                // A candidate's "don't select" soft clause being
                // unsatisfied means it was forced selected.
                let hitting_set: FxHashSet<SoftId> = hs_solver
                    .unsatisfied_soft()
                    .filter_map(|hs_id| hs_soft_to_id.get(&hs_id).copied())
                    .collect();
                Ok(Some(hitting_set))
            }
            // Every MCS is non-empty and contributes a hard clause with
            // >=1 literal (checked above), so the hitting-set formula is
            // always satisfiable (select every candidate); a genuine
            // `Unsatisfiable` here would indicate an internal
            // inconsistency, not a real hitting-set failure.
            Ok(MaxSatResult::Unknown) | Err(MaxSatError::Unsatisfiable) => Ok(None),
            Ok(other) => Err(MaxHsError::SolverError(format!(
                "unexpected hitting-set solver result: {other}"
            ))),
            Err(e) => Err(MaxHsError::SolverError(e.to_string())),
        }
    }

    /// Block a hitting set from being found again
    fn block_hitting_set(&mut self, hitting_set: &FxHashSet<SoftId>) {
        // Remove the clauses in the hitting set from SAT solver
        // In practice, this is done by creating a new SAT solver instance
        // or by adding blocking clauses

        // For simplicity, we'll rebuild the SAT solver
        self.sat_solver = SatSolver::new();

        // Add hard clauses
        for hard_clause in &self.hard_clauses {
            self.sat_solver.add_clause(hard_clause.iter().copied());
        }

        // Add soft clauses not in hitting set
        for clause in &self.soft_clauses {
            if !hitting_set.contains(&clause.id) {
                self.sat_solver.add_clause(clause.lits.iter().copied());
            }
        }
    }

    /// Get the best cost found
    pub fn best_cost(&self) -> &Weight {
        &self.best_cost
    }

    /// Get statistics
    pub fn stats(&self) -> &MaxHsStats {
        &self.stats
    }
}

impl Default for MaxHsSolver {
    fn default() -> Self {
        Self::new()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_maxhs_solver_new() {
        let solver = MaxHsSolver::new();
        assert_eq!(solver.stats().sat_calls, 0);
        assert_eq!(*solver.best_cost(), Weight::Infinite);
    }

    #[test]
    fn test_maxhs_simple() {
        let mut solver = MaxHsSolver::new();

        // Add soft clauses
        solver.add_soft(SoftId(0), [Lit::from_dimacs(1)], Weight::from(1));
        solver.add_soft(SoftId(1), [Lit::from_dimacs(-1)], Weight::from(1));

        let result = solver.solve();
        if let Err(ref e) = result {
            eprintln!("MaxHS error: {:?}", e);
        }
        assert!(result.is_ok(), "Solve failed: {:?}", result);

        // Should have cost 1 (one clause must be violated)
        assert_eq!(*solver.best_cost(), Weight::from(1));
    }

    /// `OPT-MAXHS-BESTCOST-INF` regression: when every soft clause is
    /// jointly satisfiable on the very first SAT check, `best_cost` must
    /// report the true optimum cost of 0, not the `Weight::Infinite`
    /// initial placeholder.
    #[test]
    fn test_maxhs_immediately_satisfiable_reports_cost_zero() {
        let mut solver = MaxHsSolver::new();

        // Hard: x0 \/ x1 (trivially satisfiable alongside the softs below).
        solver.add_hard([Lit::from_dimacs(1), Lit::from_dimacs(2)]);

        // Soft clauses that can all be satisfied simultaneously (x0=true,
        // x1=true satisfies both).
        solver.add_soft(SoftId(0), [Lit::from_dimacs(1)], Weight::from(1));
        solver.add_soft(SoftId(1), [Lit::from_dimacs(2)], Weight::from(1));

        let result = solver.solve();
        assert!(
            matches!(result, Ok(MaxSatResult::Optimal)),
            "expected Optimal: {result:?}"
        );
        assert_eq!(
            *solver.best_cost(),
            Weight::zero(),
            "every soft clause is jointly satisfiable, so the true optimum \
             cost is 0, not Infinite"
        );
    }

    #[test]
    fn test_maxhs_config() {
        let config = MaxHsConfig {
            max_iterations: 5000,
            use_cores: false,
            preprocess: false,
        };

        let solver = MaxHsSolver::with_config(config);
        assert_eq!(solver.config.max_iterations, 5000);
        assert!(!solver.config.use_cores);
    }

    // -----------------------------------------------------------------------
    // Regression tests for the `sweep-backend-misc` triage sweep.
    // -----------------------------------------------------------------------

    /// `compute_hitting_set` used to greedily hit each MCS with its own
    /// locally-cheapest member, ignoring cross-MCS synergy -- a
    /// textbook-suboptimal heuristic for weighted hitting set. Three
    /// MCSes `{a,z}`, `{b,z}`, `{c,z}` (a/b/c weight 1 each, z weight 2)
    /// have a shared element `z` that alone hits all three for cost 2,
    /// but the old greedy algorithm picked the "locally cheapest" `a`,
    /// `b`, `c` for each MCS in turn (never reconsidering once `z` was
    /// passed over), landing on cost 3 while still reporting
    /// `MaxSatResult::Optimal`.
    #[test]
    fn test_compute_hitting_set_finds_true_minimum_not_greedy_suboptimal() {
        let mut solver = MaxHsSolver::new();
        solver.add_soft(SoftId(0), [Lit::from_dimacs(1)], Weight::from(1)); // a
        solver.add_soft(SoftId(1), [Lit::from_dimacs(2)], Weight::from(1)); // b
        solver.add_soft(SoftId(2), [Lit::from_dimacs(3)], Weight::from(1)); // c
        solver.add_soft(SoftId(3), [Lit::from_dimacs(4)], Weight::from(2)); // z

        solver.mcses.push(Mcs {
            clauses: [SoftId(0), SoftId(3)].into_iter().collect(),
            weight: Weight::from(1),
        });
        solver.mcses.push(Mcs {
            clauses: [SoftId(1), SoftId(3)].into_iter().collect(),
            weight: Weight::from(1),
        });
        solver.mcses.push(Mcs {
            clauses: [SoftId(2), SoftId(3)].into_iter().collect(),
            weight: Weight::from(1),
        });

        let hitting_set = solver
            .compute_hitting_set()
            .expect("exact solve should not error")
            .expect("exact solve should certify an optimum");

        let cost: Weight = hitting_set
            .iter()
            .filter_map(|id| solver.soft_map.get(id))
            .filter_map(|&idx| solver.soft_clauses.get(idx))
            .map(|c| &c.weight)
            .fold(Weight::zero(), |acc, w| acc.add(w));

        assert_eq!(
            hitting_set,
            [SoftId(3)].into_iter().collect::<FxHashSet<_>>(),
            "the true minimum hitting set is just {{z}}"
        );
        assert_eq!(
            cost,
            Weight::from(2),
            "optimal hitting-set cost is 2 (just z), not the greedy 3 (a+b+c)"
        );
    }

    /// `update_soft_values` used to have the `Lit::sign()` polarity
    /// backwards (`sign()` is true for *positive* literals, not
    /// negative), so a soft clause built from a single negative unit
    /// literal had its satisfaction reported inverted. This is exactly
    /// the shape `compute_hitting_set`'s internal `¬sel_s` soft clauses
    /// use, so this exercises the full `MaxHsSolver::solve` path (not
    /// just the isolated hitting-set computation) to confirm the fix
    /// holds end-to-end.
    #[test]
    fn test_maxhs_negative_literal_soft_clause_reports_correct_cost() {
        let mut solver = MaxHsSolver::new();
        // Hard: at least one of x0, x1, x2 must be true.
        solver.add_hard([
            Lit::from_dimacs(1),
            Lit::from_dimacs(2),
            Lit::from_dimacs(3),
        ]);
        // Soft: all three should be false (negative unit literals).
        solver.add_soft(SoftId(0), [Lit::from_dimacs(-1)], Weight::from(1));
        solver.add_soft(SoftId(1), [Lit::from_dimacs(-2)], Weight::from(1));
        solver.add_soft(SoftId(2), [Lit::from_dimacs(-3)], Weight::from(1));

        let result = solver.solve();
        assert!(result.is_ok(), "solve should not error: {result:?}");
        assert_eq!(
            *solver.best_cost(),
            Weight::from(1),
            "exactly one of the three negative-literal soft clauses must \
             be violated at the optimum"
        );
    }
}
