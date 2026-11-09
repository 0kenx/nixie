//! PMRES (Partial MaxRes) algorithm for weighted partial MaxSAT.
//!
//! PMRES is a core-guided algorithm that combines:
//! - Relaxation-based core processing
//! - Weight-aware stratification
//! - Efficient handling of partial MaxSAT (hard + soft constraints)
//!
//! Reference: Z3's `opt/maxcore.cpp` (primal/maxres solvers)
//! Based on:
//! - Nina & Bacchus (2014): "Core-Guided Minimal Correction Set and Core Enumeration" (AAAI)
//! - Ansótegui, Bonet, Levy (2013): "SAT-based MaxSAT algorithms" (Artificial Intelligence)

use crate::maxsat::{MaxSatError, MaxSatResult, SoftClause, SoftId, Weight};
use nixie_sat::{LBool, Lit, Solver as SatSolver, SolverResult, Var};
use smallvec::SmallVec;

/// Configuration for PMRES solver
#[derive(Debug, Clone)]
pub struct PmresConfig {
    /// Maximum number of iterations
    pub max_iterations: u32,
    /// Use stratified solving by weight
    pub stratified: bool,
    /// Enable hill climbing for assumption selection
    pub hill_climb: bool,
    /// Minimum core size for processing
    pub min_core_size: usize,
}

impl Default for PmresConfig {
    fn default() -> Self {
        Self {
            max_iterations: 100000,
            stratified: true,
            hill_climb: true,
            min_core_size: 1,
        }
    }
}

/// Statistics for PMRES solver
#[derive(Debug, Clone, Default)]
pub struct PmresStats {
    /// Number of cores extracted
    pub cores_extracted: u32,
    /// Number of SAT calls
    pub sat_calls: u32,
    /// Total size of all cores
    pub total_core_size: u32,
    /// Number of relaxation variables added
    pub relax_vars: u32,
}

/// PMRES solver for weighted partial MaxSAT
#[derive(Debug)]
pub struct PmresSolver {
    /// Hard clauses (must be satisfied)
    hard_clauses: Vec<SmallVec<[Lit; 4]>>,
    /// Soft clauses (weighted, can be violated)
    soft_clauses: Vec<SoftClause>,
    /// Next variable ID
    next_var: u32,
    /// Configuration
    config: PmresConfig,
    /// Statistics
    stats: PmresStats,
    /// Lower bound on cost
    lower_bound: Weight,
    /// Upper bound on cost
    upper_bound: Weight,
    /// Best model found
    best_model: Option<Vec<LBool>>,
}

impl PmresSolver {
    /// Create a new PMRES solver
    pub fn new() -> Self {
        Self::with_config(PmresConfig::default())
    }

    /// Create a new PMRES solver with configuration
    pub fn with_config(config: PmresConfig) -> Self {
        Self {
            hard_clauses: Vec::new(),
            soft_clauses: Vec::new(),
            next_var: 0,
            config,
            stats: PmresStats::default(),
            lower_bound: Weight::zero(),
            upper_bound: Weight::Infinite,
            best_model: None,
        }
    }

    /// Add a hard clause
    pub fn add_hard(&mut self, lits: impl IntoIterator<Item = Lit>) {
        self.hard_clauses.push(lits.into_iter().collect());
        self.invalidate_model();
    }

    /// Add a soft clause with weight
    pub fn add_soft_weighted(
        &mut self,
        id: u32,
        lits: impl IntoIterator<Item = Lit>,
        weight: Weight,
    ) {
        let clause = SoftClause::new(SoftId(id), lits, weight);
        self.soft_clauses.push(clause);
        self.invalidate_model();
    }

    /// Get statistics
    pub fn stats(&self) -> &PmresStats {
        &self.stats
    }

    /// Get lower bound
    pub fn lower_bound(&self) -> &Weight {
        &self.lower_bound
    }

    /// Get upper bound
    pub fn upper_bound(&self) -> &Weight {
        &self.upper_bound
    }

    /// Get best model
    pub fn best_model(&self) -> Option<&[LBool]> {
        self.best_model.as_deref()
    }

    /// Get cost of best solution
    pub fn cost(&self) -> Weight {
        self.lower_bound.clone()
    }

    /// Solve using PMRES algorithm
    pub fn solve(&mut self) -> Result<MaxSatResult, MaxSatError> {
        self.invalidate_model();
        if self
            .soft_clauses
            .iter()
            .any(|clause| clause.weight.is_infinite() || clause.weight < Weight::zero())
        {
            return Err(MaxSatError::SolverError(
                "PMRES requires finite, nonnegative soft weights".into(),
            ));
        }
        let result = if self.soft_clauses.is_empty() {
            self.check_hard_satisfiable()
        } else if self.config.stratified && self.has_different_weights() {
            self.solve_stratified()
        } else {
            self.solve_pmres_main()
        };
        // A model of an earlier weight stratum need not satisfy the full
        // objective. Only the final certified optimum is published.
        if !matches!(result, Ok(MaxSatResult::Optimal)) {
            self.invalidate_model();
        }
        result
    }

    fn invalidate_model(&mut self) {
        self.best_model = None;
        self.lower_bound = Weight::zero();
        self.upper_bound = Weight::Infinite;
    }

    /// Check the original hard clauses and exact objective independently of
    /// selectors/blocking variables. A mismatch is Unknown, never Optimal.
    fn accept_optimum(
        &mut self,
        solver: &SatSolver,
        soft: &[SoftClause],
        bound: Weight,
    ) -> MaxSatResult {
        let model: Vec<_> = solver
            .model()
            .iter()
            .map(|&v| if v == LBool::Undef { LBool::False } else { v })
            .collect();
        let holds = |lit: Lit| {
            model
                .get(lit.var().index())
                .is_some_and(|&v| (v == LBool::True) == lit.is_pos())
        };
        if self
            .hard_clauses
            .iter()
            .any(|clause| !clause.iter().any(|&lit| holds(lit)))
        {
            return MaxSatResult::Unknown;
        }
        let mut cost = Weight::zero();
        for clause in soft {
            if !clause.lits.iter().any(|&lit| holds(lit)) {
                cost = cost.add(&clause.weight);
            }
        }
        if cost != bound {
            return MaxSatResult::Unknown;
        }
        self.best_model = Some(model);
        self.lower_bound = bound;
        self.upper_bound = cost;
        MaxSatResult::Optimal
    }

    /// Check if soft clauses have different weights
    fn has_different_weights(&self) -> bool {
        if self.soft_clauses.is_empty() {
            return false;
        }
        let first_weight = &self.soft_clauses[0].weight;
        self.soft_clauses.iter().any(|c| &c.weight != first_weight)
    }

    /// Solve using stratified approach (by weight levels)
    fn solve_stratified(&mut self) -> Result<MaxSatResult, MaxSatError> {
        // Collect unique weight levels (sorted descending)
        let mut weight_levels: Vec<Weight> =
            self.soft_clauses.iter().map(|c| c.weight.clone()).collect();
        weight_levels.sort();
        weight_levels.dedup();
        weight_levels.reverse();

        // Solve for each weight level
        for level in weight_levels {
            // Only process soft clauses at or above this level
            let active_soft: Vec<SoftClause> = self
                .soft_clauses
                .iter()
                .filter(|c| c.weight >= level)
                .cloned()
                .collect();

            if active_soft.is_empty() {
                continue;
            }

            // Create temporary solver for this level
            let result = self.solve_level(&active_soft)?;
            match result {
                MaxSatResult::Optimal => {}
                MaxSatResult::Unsatisfiable => return Err(MaxSatError::Unsatisfiable),
                MaxSatResult::Unknown => return Ok(MaxSatResult::Unknown),
                MaxSatResult::Satisfiable => return Ok(MaxSatResult::Unknown),
            }
        }

        Ok(MaxSatResult::Optimal)
    }

    /// Solve a specific weight level using core-guided WPM1 relaxation.
    ///
    /// Each soft clause is augmented with a fresh *selector* variable `s`
    /// (clause `body ∨ s`); asserting `¬s` demands `body` hold. When
    /// `solve_with_assumptions` returns an unsat core over these selectors the
    /// involved soft constraints are relaxed following weighted Fu-Malik (WPM1,
    /// Ansótegui–Bonet–Levy 2013):
    ///   1. the minimum residual weight `w` across the core is added to the
    ///      lower bound;
    ///   2. every core constraint's weight is split so the remainder `weight−w`
    ///      survives as an independent soft constraint;
    ///   3. each core clause gains a fresh blocking variable and a fresh
    ///      selector; and
    ///   4. an ExactlyOne constraint over the blocking variables forces exactly
    ///      one of the core clauses to pay `w`.
    ///
    /// This makes progress on cores of ANY size. The previous scheme only added
    /// an at-most-one constraint over the (unchanged) relaxation variables while
    /// re-asserting the SAME `¬relax` assumptions, so any core with two or more
    /// soft clauses reproduced itself forever – a non-terminating loop that a
    /// now-correct (complete) unsat-core extraction newly exposed. When the SAT
    /// call finally succeeds, the accumulated lower bound IS the optimum for
    /// this level.
    fn solve_level(&mut self, soft_clauses: &[SoftClause]) -> Result<MaxSatResult, MaxSatError> {
        // An active soft constraint in the WPM1 working set.
        struct SoftEntry {
            /// The clause as it now stands: the original literals plus the
            /// blocking variable of every relaxation it took part in (never a
            /// selector).
            body: SmallVec<[Lit; 8]>,
            /// Residual weight still to be paid if this constraint is violated.
            weight: Weight,
            /// Current selector variable; the live clause is `body ∨ … ∨ selector`
            /// and the constraint is enforced by asserting `¬selector`.
            selector: Var,
        }

        let mut solver = self.create_base_solver();

        // Register every variable that occurs in a soft clause and advance
        // `next_var` past all of them, so freshly allocated selector / blocking
        // variables can never collide with a problem variable (a collision would
        // silently corrupt both the assumptions and the computed cost).
        for clause in soft_clauses {
            for &lit in &clause.lits {
                self.ensure_var(&mut solver, lit.var().0);
                self.next_var = self.next_var.max(lit.var().0 + 1);
            }
        }

        // Build the initial working set: one selector per (non-trivial) soft clause.
        let mut entries: Vec<SoftEntry> = Vec::new();
        for clause in soft_clauses {
            if clause.weight.is_zero() {
                continue;
            }
            let selector = self.fresh_var(&mut solver);
            self.stats.relax_vars += 1;
            let body: SmallVec<[Lit; 8]> = clause.lits.iter().copied().collect();
            self.add_relaxed_clause(&mut solver, &body, &[selector]);
            entries.push(SoftEntry {
                body,
                weight: clause.weight.clone(),
                selector,
            });
        }

        let mut lb = Weight::zero();
        let mut iterations: u32 = 0;

        loop {
            iterations += 1;
            if iterations > self.config.max_iterations {
                return Ok(MaxSatResult::Unknown);
            }

            let assumptions: Vec<Lit> = entries.iter().map(|e| Lit::neg(e.selector)).collect();

            // No active soft constraints remain: solve the residual hard problem.
            if assumptions.is_empty() {
                self.stats.sat_calls += 1;
                return match solver.solve() {
                    SolverResult::Sat => Ok(self.accept_optimum(&solver, soft_clauses, lb)),
                    SolverResult::Unsat => Err(MaxSatError::Unsatisfiable),
                    SolverResult::Unknown => Ok(MaxSatResult::Unknown),
                };
            }

            self.stats.sat_calls += 1;
            let (result, core) = solver.solve_with_assumptions(&assumptions);

            match result {
                SolverResult::Sat => {
                    return Ok(self.accept_optimum(&solver, soft_clauses, lb));
                }
                SolverResult::Unknown => return Ok(MaxSatResult::Unknown),
                SolverResult::Unsat => {
                    let Some(core_lits) = core else {
                        return Ok(MaxSatResult::Unknown);
                    };
                    if core_lits.is_empty() {
                        // Confirm the original hard problem independently of
                        // all relaxation clauses before reporting hard UNSAT.
                        return match self.check_hard_satisfiable() {
                            Err(MaxSatError::Unsatisfiable) => Err(MaxSatError::Unsatisfiable),
                            _ => Ok(MaxSatResult::Unknown),
                        };
                    }
                    if core_lits.iter().any(|lit| !assumptions.contains(lit)) {
                        return Ok(MaxSatResult::Unknown);
                    }

                    // Map the core's selector variables back to entry indices.
                    let core_vars: rustc_hash::FxHashSet<u32> =
                        core_lits.iter().map(|l| l.var().0).collect();
                    let core_idx: Vec<usize> = (0..entries.len())
                        .filter(|&i| core_vars.contains(&entries[i].selector.0))
                        .collect();

                    if core_idx.is_empty() {
                        return Ok(MaxSatResult::Unknown);
                    }

                    self.stats.cores_extracted += 1;
                    self.stats.total_core_size += core_idx.len() as u32;

                    // Minimum residual weight across the core.
                    let mut w_min = Weight::Infinite;
                    for &i in &core_idx {
                        w_min = w_min.min_weight(&entries[i].weight);
                    }
                    // Weights are finite and positive here, so this cannot arise;
                    // guard defensively against a non-progress loop regardless.
                    if w_min.is_infinite() || w_min.is_zero() {
                        return Ok(MaxSatResult::Unknown);
                    }

                    lb = lb.add(&w_min);

                    // Relax each core constraint (WPM1).
                    let mut blocking: Vec<Var> = Vec::with_capacity(core_idx.len());
                    let mut split_off: Vec<SoftEntry> = Vec::new();

                    for &i in &core_idx {
                        // Weight split: the remainder `weight − w_min` survives as
                        // an independent soft constraint with its own selector.
                        let residual = entries[i].weight.sub(&w_min);
                        if !residual.is_zero() {
                            let sel_res = self.fresh_var(&mut solver);
                            let body = entries[i].body.clone();
                            self.add_relaxed_clause(&mut solver, &body, &[sel_res]);
                            split_off.push(SoftEntry {
                                body,
                                weight: residual,
                                selector: sel_res,
                            });
                        }

                        // Fresh blocking var + fresh selector for the relaxed clause.
                        let b = self.fresh_var(&mut solver);
                        blocking.push(b);
                        let sel_new = self.fresh_var(&mut solver);
                        self.stats.relax_vars += 1;

                        // (body ∨ b ∨ sel_new): asserting ¬sel_new demands
                        // (body ∨ b), so the body may be violated only when this
                        // constraint is the one that pays via its blocking var `b`.
                        let body = entries[i].body.clone();
                        self.add_relaxed_clause(&mut solver, &body, &[b, sel_new]);

                        // WPM1 relaxes the clause *as it now stands*: the
                        // blocking variable stays in the body, so a constraint
                        // relaxed twice may be paid by either of its blocking
                        // variables.  Dropping it (the body used to stay the
                        // original clause) let each constraint be violated by
                        // its newest blocking variable only, so a core that
                        // needs two violations — at most one of `x0, x1, x2`
                        // with all three wanted — reproduced itself forever.
                        // A `solve_with_assumptions` that silently dropped
                        // assumptions after a backjump used to end that loop
                        // with a `Sat` violating them (fixed 2026-09-28,
                        // `nixie-sat/tests/assumption_retention.rs`).
                        entries[i].body.push(Lit::pos(b));
                        entries[i].selector = sel_new;
                        entries[i].weight = w_min.clone();
                    }

                    entries.extend(split_off);

                    // ExactlyOne(blocking): at least one core clause pays (a sound
                    // lower bound) and at most one pays (no over-counting beyond
                    // the single `w_min` already added to `lb`).
                    self.add_exactly_one(&mut solver, &blocking);
                }
            }
        }
    }

    /// Main PMRES solving loop (non-stratified)
    fn solve_pmres_main(&mut self) -> Result<MaxSatResult, MaxSatError> {
        let soft_clauses = self.soft_clauses.clone();
        self.solve_level(&soft_clauses)
    }

    /// Allocate a fresh SAT variable and ensure the solver has it registered.
    fn fresh_var(&mut self, solver: &mut SatSolver) -> Var {
        let v = Var(self.next_var);
        self.next_var += 1;
        self.ensure_var(solver, v.0);
        v
    }

    /// Add the clause `body ∨ extra_0 ∨ … ∨ extra_k` (each `extra` a positive
    /// literal of the given variable) to `solver`.
    fn add_relaxed_clause(&self, solver: &mut SatSolver, body: &[Lit], extra: &[Var]) {
        let mut clause: SmallVec<[Lit; 10]> = body.iter().copied().collect();
        for &v in extra {
            clause.push(Lit::pos(v));
        }
        solver.add_clause(clause.iter().copied());
    }

    /// Encode ExactlyOne over `vars` as hard clauses: one at-least-one clause,
    /// plus at-most-one via the pairwise encoding for small sets, escalating to
    /// the Sinz sequential-counter encoding (linear in the number of variables)
    /// once the quadratic pairwise clause count would bloat the database.
    fn add_exactly_one(&mut self, solver: &mut SatSolver, vars: &[Var]) {
        if vars.is_empty() {
            return;
        }

        // At least one.
        let at_least_one: SmallVec<[Lit; 16]> = vars.iter().map(|&v| Lit::pos(v)).collect();
        solver.add_clause(at_least_one.iter().copied());

        // At most one.
        if vars.len() <= 5 {
            for i in 0..vars.len() {
                for j in (i + 1)..vars.len() {
                    solver.add_clause([Lit::neg(vars[i]), Lit::neg(vars[j])]);
                }
            }
            return;
        }

        // Sinz sequential (ladder) at-most-one with fresh register variables.
        let n = vars.len();
        let mut s_prev = self.fresh_var(solver);
        solver.add_clause([Lit::neg(vars[0]), Lit::pos(s_prev)]); // ¬x0 ∨ r0
        for (k, &xk) in vars.iter().enumerate().skip(1) {
            if k + 1 == n {
                // Last variable: ¬x_{n-1} ∨ ¬r_{n-2}.
                solver.add_clause([Lit::neg(xk), Lit::neg(s_prev)]);
                break;
            }
            let s_cur = self.fresh_var(solver);
            solver.add_clause([Lit::neg(xk), Lit::pos(s_cur)]); // ¬x_k ∨ r_k
            solver.add_clause([Lit::neg(s_prev), Lit::pos(s_cur)]); // ¬r_{k-1} ∨ r_k
            solver.add_clause([Lit::neg(xk), Lit::neg(s_prev)]); // ¬x_k ∨ ¬r_{k-1}
            s_prev = s_cur;
        }
    }

    /// Create base SAT solver with hard clauses
    fn create_base_solver(&mut self) -> SatSolver {
        let mut solver = SatSolver::new();

        // Add hard clauses
        for clause in &self.hard_clauses {
            for &lit in clause.iter() {
                self.ensure_var(&mut solver, lit.var().0);
                self.next_var = self.next_var.max(lit.var().0 + 1);
            }
            solver.add_clause(clause.iter().copied());
        }

        solver
    }

    /// Ensure variable exists in solver
    fn ensure_var(&self, solver: &mut SatSolver, var_idx: u32) {
        while solver.num_vars() <= var_idx as usize {
            solver.new_var();
        }
    }

    /// Check if hard constraints are satisfiable
    fn check_hard_satisfiable(&mut self) -> Result<MaxSatResult, MaxSatError> {
        let mut solver = self.create_base_solver();

        self.stats.sat_calls += 1;
        match solver.solve() {
            SolverResult::Sat => Ok(self.accept_optimum(&solver, &[], Weight::zero())),
            SolverResult::Unsat => Err(MaxSatError::Unsatisfiable),
            SolverResult::Unknown => Ok(MaxSatResult::Unknown),
        }
    }

    /// Reset the solver
    pub fn reset(&mut self) {
        self.hard_clauses.clear();
        self.soft_clauses.clear();
        self.next_var = 0;
        self.stats = PmresStats::default();
        self.lower_bound = Weight::zero();
        self.upper_bound = Weight::Infinite;
        self.best_model = None;
    }
}

impl Default for PmresSolver {
    fn default() -> Self {
        Self::new()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn lit(v: u32, neg: bool) -> Lit {
        if neg {
            Lit::neg(Var(v))
        } else {
            Lit::pos(Var(v))
        }
    }

    #[test]
    fn unsupported_weights_are_errors_not_false_optima() {
        for weight in [Weight::Int((-1).into()), Weight::Infinite] {
            let mut solver = PmresSolver::new();
            solver.add_soft_weighted(0, [Lit::from_dimacs(1)], weight);
            assert!(matches!(solver.solve(), Err(MaxSatError::SolverError(_))));
            assert!(solver.best_model().is_none());
        }
    }

    #[test]
    fn test_pmres_empty() {
        let mut solver = PmresSolver::new();
        solver.add_hard([lit(0, false)]);
        let result = solver.solve();
        assert!(matches!(result, Ok(MaxSatResult::Optimal)));
        assert_eq!(solver.cost(), Weight::zero());
    }

    #[test]
    fn test_pmres_simple() {
        let mut solver = PmresSolver::new();

        // Hard: x0
        solver.add_hard([lit(0, false)]);

        // Soft: ~x0 (cannot be satisfied)
        solver.add_soft_weighted(0, [lit(0, true)], Weight::one());

        // Soft: x1 (can be satisfied)
        solver.add_soft_weighted(1, [lit(1, false)], Weight::one());

        let result = solver.solve();
        assert!(matches!(result, Ok(MaxSatResult::Optimal)));
        // Cost should be 1 (one soft clause unsatisfied)
        assert_eq!(solver.cost(), Weight::one());
    }

    #[test]
    fn test_pmres_weighted() {
        let mut solver = PmresSolver::new();

        // Hard: x0 \/ x1
        solver.add_hard([lit(0, false), lit(1, false)]);

        // Soft: ~x0 with weight 5
        solver.add_soft_weighted(0, [lit(0, true)], Weight::from(5));

        // Soft: ~x1 with weight 1
        solver.add_soft_weighted(1, [lit(1, true)], Weight::from(1));

        let result = solver.solve();
        assert!(matches!(result, Ok(MaxSatResult::Optimal)));
        // Should violate lower weight constraint
        assert!(solver.cost() >= Weight::one());
    }

    #[test]
    fn test_pmres_all_satisfiable() {
        let mut solver = PmresSolver::new();

        // Soft: x0
        solver.add_soft_weighted(0, [lit(0, false)], Weight::one());

        // Soft: x1
        solver.add_soft_weighted(1, [lit(1, false)], Weight::one());

        let result = solver.solve();
        assert!(matches!(result, Ok(MaxSatResult::Optimal)));
        // All can be satisfied
        assert_eq!(solver.cost(), Weight::zero());
    }

    #[test]
    fn test_pmres_unsatisfiable_hard() {
        let mut solver = PmresSolver::new();

        // Hard: x0 and ~x0 (contradiction)
        solver.add_hard([lit(0, false)]);
        solver.add_hard([lit(0, true)]);

        solver.add_soft_weighted(0, [lit(1, false)], Weight::one());

        let result = solver.solve();
        assert!(matches!(result, Err(MaxSatError::Unsatisfiable)));
    }

    #[test]
    fn test_pmres_stratified() {
        let config = PmresConfig {
            stratified: true,
            ..Default::default()
        };
        let mut solver = PmresSolver::with_config(config);

        // Hard: at most one of x0, x1, x2
        solver.add_hard([lit(0, true), lit(1, true)]);
        solver.add_hard([lit(0, true), lit(2, true)]);
        solver.add_hard([lit(1, true), lit(2, true)]);

        // Soft constraints with different weights
        solver.add_soft_weighted(0, [lit(0, false)], Weight::from(5));
        solver.add_soft_weighted(1, [lit(1, false)], Weight::from(3));
        solver.add_soft_weighted(2, [lit(2, false)], Weight::from(1));

        let result = solver.solve();
        assert!(matches!(result, Ok(MaxSatResult::Optimal)));
        // At least 2 soft clauses must be violated
        assert!(solver.cost() >= Weight::from(3)); // 3+1 or 5 or similar
    }
    #[test]
    fn repeated_weighted_relaxation_preserves_prior_blocking_literals() {
        // At most one of three desired variables can be true. Exhaustively
        // check the cost and returned witness for every positive weight triple.
        for stratified in [false, true] {
            for a in 1u64..=3 {
                for b in 1u64..=3 {
                    for c in 1u64..=3 {
                        let weights = [a, b, c];
                        let mut solver = PmresSolver::with_config(PmresConfig {
                            stratified,
                            max_iterations: 64,
                            ..Default::default()
                        });
                        for i in 0..3 {
                            for j in (i + 1)..3 {
                                solver.add_hard([lit(i, true), lit(j, true)]);
                            }
                            solver.add_soft_weighted(
                                i,
                                [lit(i, false)],
                                Weight::from(weights[i as usize]),
                            );
                        }
                        assert!(
                            matches!(solver.solve(), Ok(MaxSatResult::Optimal)),
                            "{stratified} {weights:?}"
                        );
                        let best = solver.best_model().expect("optimal witness");
                        let truths: Vec<_> =
                            best.iter().take(3).map(|v| *v == LBool::True).collect();
                        assert_eq!(truths.len(), 3);
                        assert!(truths.iter().filter(|&&v| v).count() <= 1);
                        let cost: u64 = weights
                            .iter()
                            .zip(&truths)
                            .filter_map(|(&w, &holds)| (!holds).then_some(w))
                            .sum();
                        let expected = a + b + c - a.max(b).max(c);
                        assert_eq!(cost, expected, "{stratified} {weights:?}");
                        assert_eq!(solver.cost(), Weight::from(expected));
                    }
                }
            }
        }
    }
    #[test]
    fn exhausted_stratified_search_is_unknown_and_invalidates_old_models() {
        let mut solver = PmresSolver::with_config(PmresConfig {
            max_iterations: 0,
            ..Default::default()
        });
        solver.add_soft_weighted(0, [lit(0, false)], Weight::one());
        solver.add_soft_weighted(1, [lit(1, false)], Weight::from(2));
        assert!(matches!(solver.solve(), Ok(MaxSatResult::Unknown)));
        assert!(solver.best_model().is_none());
        solver.config.max_iterations = 64;
        assert!(matches!(solver.solve(), Ok(MaxSatResult::Optimal)));
        assert!(solver.best_model().is_some());
        solver.add_hard([lit(0, true)]);
        assert!(solver.best_model().is_none());
        solver.config.max_iterations = 0;
        assert!(matches!(solver.solve(), Ok(MaxSatResult::Unknown)));
        assert!(solver.best_model().is_none());
        assert!(solver.upper_bound().is_infinite());
    }

    #[test]
    fn candidate_optimum_must_match_the_original_hard_clauses_and_cost() {
        let mut search = SatSolver::new();
        search.new_var();
        search.add_clause([lit(0, false)]);
        assert_eq!(search.solve(), SolverResult::Sat);
        let mut solver = PmresSolver::new();
        solver.add_hard([lit(0, true)]);
        assert_eq!(
            solver.accept_optimum(&search, &[], Weight::zero()),
            MaxSatResult::Unknown
        );
        solver.hard_clauses.clear();
        let soft = [SoftClause::new(SoftId(0), [lit(0, true)], Weight::from(3))];
        assert_eq!(
            solver.accept_optimum(&search, &soft, Weight::one()),
            MaxSatResult::Unknown
        );
        assert_eq!(
            solver.accept_optimum(&search, &soft, Weight::from(3)),
            MaxSatResult::Optimal
        );
    }
}
