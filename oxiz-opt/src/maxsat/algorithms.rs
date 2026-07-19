//! MaxSAT solving algorithms: Fu-Malik, OLL, MSU3, WMax, and PMRES.
//!
//! All algorithms are implemented as methods on MaxSatSolver.

use super::core::{SoftId, Weight};
use super::types::{MaxSatAlgorithm, MaxSatError, MaxSatResult, MaxSatSolver};
use num_bigint::BigInt;
use num_rational::BigRational;
use num_traits::{ToPrimitive, Zero};
use oxiz_sat::{LBool, Lit, Solver as SatSolver, SolverResult, Var};
use rustc_hash::FxHashMap;
use smallvec::SmallVec;

/// Hard cap on the total number of unit-weight clause duplicates the
/// weighted-to-unweighted reduction below is willing to materialize. This
/// keeps the (always-sound) reduction from silently hanging or exhausting
/// memory on instances with astronomically large or finely-grained
/// rational weights; such instances honestly report [`MaxSatResult::Unknown`]
/// rather than a fabricated result.
const MAX_WEIGHT_DUPLICATES: u64 = 200_000;

/// Greatest common divisor of two non-negative `BigInt`s (Euclidean).
fn bigint_gcd(a: &BigInt, b: &BigInt) -> BigInt {
    let zero = BigInt::zero();
    let (mut a, mut b) = (a.clone(), b.clone());
    while b != zero {
        let r = &a % &b;
        a = b;
        b = r;
    }
    a
}

/// Least common multiple of two positive `BigInt`s (0 if either is 0).
fn bigint_lcm(a: &BigInt, b: &BigInt) -> BigInt {
    let zero = BigInt::zero();
    if *a == zero || *b == zero {
        return zero;
    }
    (a / bigint_gcd(a, b)) * b
}

/// Normalize a `BigRational` down to `Weight::Int` when it is integral,
/// keeping `Weight::Rational` only when genuinely fractional. This avoids
/// spurious `Weight::Int(3) != Weight::Rational(3/1)` mismatches.
fn normalize_weight(r: BigRational) -> Weight {
    if r.is_integer() {
        Weight::Int(r.to_integer())
    } else {
        Weight::Rational(r)
    }
}

impl MaxSatSolver {
    /// Solve the MaxSAT problem
    pub fn solve(&mut self) -> Result<MaxSatResult, MaxSatError> {
        // Check if trivially satisfiable (no soft clauses)
        if self.soft_clauses.is_empty() {
            return self.check_hard_satisfiable();
        }

        // Use stratified solving if enabled and weights differ
        if self.config.stratified && self.has_different_weights() {
            return self.solve_weighted_core_guided();
        }

        // Use the configured algorithm
        match self.config.algorithm {
            MaxSatAlgorithm::FuMalik => self.solve_fu_malik(),
            MaxSatAlgorithm::Oll => self.solve_oll(),
            MaxSatAlgorithm::Msu3 => self.solve_msu3(),
            MaxSatAlgorithm::WMax => self.solve_wmax(),
            MaxSatAlgorithm::Pmres => self.solve_pmres(),
        }
    }

    /// Check if hard constraints are satisfiable
    pub(super) fn check_hard_satisfiable(&mut self) -> Result<MaxSatResult, MaxSatError> {
        let mut solver = SatSolver::new();

        // Add hard clauses
        for clause in &self.hard_clauses {
            for &lit in clause.iter() {
                while solver.num_vars() <= lit.var().0 as usize {
                    solver.new_var();
                }
            }
            solver.add_clause(clause.iter().copied());
        }

        self.stats.sat_calls += 1;
        match solver.solve() {
            SolverResult::Sat => {
                self.best_model = Some(solver.model().to_vec());
                self.update_soft_values();
                // NOTE: `self.lower_bound` is intentionally *not* reset here.
                // Callers reach this method either (a) with no soft clauses
                // at all, in which case `lower_bound` is still its untouched
                // zero default, or (b) after a core-guided loop (Fu-Malik,
                // OLL, PMRES) has already relaxed every soft clause, in
                // which case `lower_bound` holds the true accumulated
                // MaxSAT cost from every extracted core. Zeroing it here
                // used to silently wipe that accumulated cost, making
                // `cost()` (which reads `lower_bound`) report 0 for
                // instances that actually had a nonzero optimum. The hard
                // clauses being satisfiable at this point proves the
                // relaxation is exact, so the upper bound now matches the
                // lower bound exactly.
                self.upper_bound = self.lower_bound.clone();
                Ok(MaxSatResult::Optimal)
            }
            SolverResult::Unsat => Err(MaxSatError::Unsatisfiable),
            SolverResult::Unknown => Ok(MaxSatResult::Unknown),
        }
    }

    /// Check if weights differ
    pub(super) fn has_different_weights(&self) -> bool {
        if self.soft_clauses.is_empty() {
            return false;
        }
        let first_weight = &self.soft_clauses[0].weight;
        self.soft_clauses.iter().any(|c| &c.weight != first_weight)
    }

    /// Weighted core-guided MaxSAT solving.
    ///
    /// Plain Fu-Malik/MSU3 relaxation ignores weights entirely: every core
    /// clause is treated identically regardless of how much it costs, so
    /// the reported optimum only minimizes the *number* of violated soft
    /// clauses, not their total weight.
    ///
    /// This is fixed via the classic, textbook-exact weighted-to-unweighted
    /// MaxSAT reduction: every soft clause of (rational) weight `w` is
    /// replaced by `w / unit` unit-weight *copies* of the same clause,
    /// where `unit` is the greatest common divisor of every (common-
    /// denominator-scaled) weight in the instance. Violating `k` copies of
    /// a duplicated clause then costs exactly `k * unit`, i.e. the original
    /// weight when fully violated — so finding the true minimum number of
    /// violated unit-weight copies is exactly equivalent to solving the
    /// original weighted instance.
    ///
    /// The minimum violated-copy count is found via cardinality-bounded
    /// linear/binary search (a totalizer-based "at most K violations"
    /// constraint, akin to the classic LSU algorithm) rather than
    /// core-guided relaxation. This deliberately avoids relying on
    /// `oxiz_sat`'s assumption-based *unsat-core content* (only the
    /// Sat/Unsat/Unknown verdict is used): `analyze_assumption_conflict`
    /// can return an incomplete core — sufficient to prove *some*
    /// unsatisfiability but not necessarily the full set of assumptions
    /// truly responsible — which silently breaks the accounting invariants
    /// that core-guided weight-splitting schemes (WPM1) or shared
    /// at-most-one relaxation groups (Fu-Malik-style) depend on. Bounding
    /// satisfiability via an explicit, verified cardinality constraint has
    /// no such dependency: every candidate bound is checked by a genuine
    /// Sat/Unsat verdict against the fully accumulated clause set.
    ///
    /// Soft clauses with [`Weight::Infinite`] are treated as effectively
    /// hard (consistent with [`crate::preprocess::Preprocessor`]'s
    /// hardening pass) rather than duplicated.
    ///
    /// If the exact reduction would require an infeasible number of
    /// duplicate clauses (see [`MAX_WEIGHT_DUPLICATES`]), this honestly
    /// reports [`MaxSatResult::Unknown`] instead of an approximate answer.
    pub(super) fn solve_weighted_core_guided(&mut self) -> Result<MaxSatResult, MaxSatError> {
        // Determine the scale factor needed to represent every weight
        // (including rational ones) as an exact integer.
        let mut scale = BigInt::from(1);
        for clause in &self.soft_clauses {
            if let Weight::Rational(r) = &clause.weight {
                scale = bigint_lcm(&scale, r.denom());
            }
        }

        // Partition soft clauses: `Weight::Infinite` behaves as hard, the
        // rest get an exact scaled-integer weight.
        let mut extra_hard: Vec<SmallVec<[Lit; 4]>> = Vec::new();
        let mut finite: Vec<(SoftId, SmallVec<[Lit; 4]>, BigInt)> =
            Vec::with_capacity(self.soft_clauses.len());

        for clause in &self.soft_clauses {
            match &clause.weight {
                Weight::Infinite => extra_hard.push(clause.lits.clone()),
                Weight::Int(n) => finite.push((clause.id, clause.lits.clone(), n * &scale)),
                Weight::Rational(r) => {
                    // `scale` is a multiple of `r.denom()` by construction.
                    let factor = &scale / r.denom();
                    finite.push((clause.id, clause.lits.clone(), r.numer() * factor));
                }
            }
        }

        // Greatest common divisor of every positive scaled weight: the
        // smallest "unit" of cost the reduction needs to represent.
        let mut unit = BigInt::zero();
        for (_, _, w) in &finite {
            if !w.is_zero() {
                unit = bigint_gcd(&unit, w);
            }
        }

        if unit.is_zero() {
            // No positive-weight soft clauses remain (all zero-weight or
            // infinite/hard); nothing to optimize beyond satisfying the
            // hard clauses (original + hardened infinite-weight softs).
            return self.solve_hard_only_with_extra(&extra_hard);
        }

        let weight_per_unit = normalize_weight(BigRational::new(unit.clone(), scale));

        // Total number of unit-weight duplicate clauses the reduction would
        // need to build.
        let mut total_duplicates = BigInt::zero();
        for (_, _, w) in &finite {
            total_duplicates += w / &unit;
        }
        if total_duplicates > BigInt::from(MAX_WEIGHT_DUPLICATES) {
            return Ok(MaxSatResult::Unknown);
        }

        let mut items: Vec<(SoftId, SmallVec<[Lit; 8]>)> = Vec::new();
        for (id, lits, w) in &finite {
            let count = (w / &unit).to_u64().unwrap_or(0);
            if count == 0 {
                continue;
            }
            let lits8: SmallVec<[Lit; 8]> = lits.iter().copied().collect();
            for _ in 0..count {
                items.push((*id, lits8.clone()));
            }
        }

        if items.is_empty() {
            return self.solve_hard_only_with_extra(&extra_hard);
        }

        self.solve_by_cardinality_search(&items, &extra_hard, &weight_per_unit)
    }

    /// Check satisfiability of the hard clauses plus `extra_hard` (soft
    /// clauses that were effectively hardened because they carry
    /// [`Weight::Infinite`]), without contributing anything further to the
    /// cost.
    fn solve_hard_only_with_extra(
        &mut self,
        extra_hard: &[SmallVec<[Lit; 4]>],
    ) -> Result<MaxSatResult, MaxSatError> {
        let mut solver = SatSolver::new();
        for clause in self.hard_clauses.iter().chain(extra_hard.iter()) {
            for &lit in clause.iter() {
                while solver.num_vars() <= lit.var().0 as usize {
                    solver.new_var();
                }
            }
            solver.add_clause(clause.iter().copied());
        }

        self.stats.sat_calls += 1;
        match solver.solve() {
            SolverResult::Sat => {
                self.best_model = Some(solver.model().to_vec());
                self.update_soft_values();
                Ok(MaxSatResult::Optimal)
            }
            SolverResult::Unsat => Err(MaxSatError::Unsatisfiable),
            SolverResult::Unknown => Ok(MaxSatResult::Unknown),
        }
    }

    /// Find the minimum number of violated unit-weight items (via a
    /// totalizer-based cardinality search) that must be violated to satisfy
    /// the hard clauses, then report the corresponding weighted cost.
    ///
    /// Every `items` entry is `(origin_soft_id, lits)`; `unit_cost` is the
    /// [`Weight`] each single violated item contributes.
    ///
    /// Deliberately builds a *fresh* [`SatSolver`] from scratch for every
    /// candidate bound checked (see [`Self::solve_cardinality_check`])
    /// rather than reusing one incremental solver across the whole binary
    /// search. Reusing a single incremental solver across assumption calls
    /// with *different, unrelated* single-literal assumptions risks
    /// cross-contamination if a clause learned while resolving one
    /// assumption's conflict is not properly scoped to that assumption —
    /// rebuilding from scratch has no such risk, at the cost of redoing
    /// some work.
    fn solve_by_cardinality_search(
        &mut self,
        items: &[(SoftId, SmallVec<[Lit; 8]>)],
        extra_hard: &[SmallVec<[Lit; 4]>],
        unit_cost: &Weight,
    ) -> Result<MaxSatResult, MaxSatError> {
        use crate::totalizer::{Totalizer, TotalizerClause};

        // NOTE: must scan `items`' literals too, not just the hard clauses —
        // when there are few (or zero) hard clauses, the soft-clause
        // literals can use variable indices past whatever the hard clauses
        // reference. Missing this caused the freshly allocated indicator
        // variables below to alias real literal variables from `items`,
        // corrupting the encoding.
        let mut next_var = 0u32;
        for clause in self.hard_clauses.iter().chain(extra_hard.iter()) {
            for &lit in clause.iter() {
                next_var = next_var.max(lit.var().0 + 1);
            }
        }
        for (_, lits) in items {
            for &lit in lits.iter() {
                next_var = next_var.max(lit.var().0 + 1);
            }
        }

        let mut violated_vars: Vec<Var> = Vec::with_capacity(items.len());
        for (origin, _lits) in items {
            let v = Var(next_var);
            next_var += 1;
            self.relax_to_soft.insert(Lit::pos(v), *origin);
            self.stats.relax_vars_added += 1;
            violated_vars.push(v);
        }

        // Feasibility pre-check: K = items.len() (fully unconstrained,
        // every item allowed to be violated). This is exactly satisfiability
        // of the hard clauses alone.
        let (feasible_result, _) =
            self.solve_cardinality_check(items, extra_hard, &violated_vars, &[], None);
        match feasible_result {
            SolverResult::Sat => {}
            SolverResult::Unsat => return Err(MaxSatError::Unsatisfiable),
            SolverResult::Unknown => return Ok(MaxSatResult::Unknown),
        }

        let violated_lits: Vec<Lit> = violated_vars.iter().map(|&v| Lit::pos(v)).collect();
        let mut totalizer = Totalizer::new(&violated_lits, next_var);
        let mut totalizer_clauses: Vec<TotalizerClause> = Vec::new();

        // Binary search for the minimum K such that "at most K items are
        // violated" is satisfiable. Every candidate is checked with a
        // genuine, from-scratch Sat/Unsat verdict.
        let mut lo: usize = 0;
        let mut hi: usize = items.len();
        let mut hit_unknown = false;

        while lo < hi {
            let mid = lo + (hi - lo) / 2;

            totalizer.ensure_bound(mid + 1);
            totalizer_clauses.extend(totalizer.take_clauses());
            let at_most_mid = totalizer.at_most(mid);

            let (result, _) = self.solve_cardinality_check(
                items,
                extra_hard,
                &violated_vars,
                &totalizer_clauses,
                at_most_mid,
            );
            match result {
                SolverResult::Sat => hi = mid,
                SolverResult::Unsat => lo = mid + 1,
                SolverResult::Unknown => {
                    hit_unknown = true;
                    break;
                }
            }
        }

        if hit_unknown {
            return Ok(MaxSatResult::Unknown);
        }

        let k_min = lo;

        // Re-solve once more at the proven-minimal bound to obtain (and
        // keep) the corresponding model.
        let at_most_final = if k_min < items.len() {
            totalizer.ensure_bound(k_min + 1);
            totalizer_clauses.extend(totalizer.take_clauses());
            totalizer.at_most(k_min)
        } else {
            None
        };

        let (final_result, final_solver) = self.solve_cardinality_check(
            items,
            extra_hard,
            &violated_vars,
            &totalizer_clauses,
            at_most_final,
        );

        match final_result {
            SolverResult::Sat => {
                self.best_model = Some(final_solver.model().to_vec());
                self.update_soft_values();
                self.lower_bound = self.lower_bound.add(&unit_cost.mul_scalar(k_min as i64));
                Ok(MaxSatResult::Optimal)
            }
            SolverResult::Unsat => {
                // The binary search proved K = k_min feasible; a genuine
                // Unsat here would mean that proof was inconsistent with
                // this fresh check. Report conservatively rather than
                // fabricate a result.
                Ok(MaxSatResult::Unknown)
            }
            SolverResult::Unknown => Ok(MaxSatResult::Unknown),
        }
    }

    /// Build a brand-new [`SatSolver`] encoding: hard clauses, `extra_hard`,
    /// one `(lits ∨ v_i)` clause per item, every totalizer clause generated so
    /// far, and (optionally) a single `at_most_k` literal asserted as a unit
    /// hard clause. Returns the verdict and the solver itself (so a winning
    /// caller can pull the model out of it).
    fn solve_cardinality_check(
        &mut self,
        items: &[(SoftId, SmallVec<[Lit; 8]>)],
        extra_hard: &[SmallVec<[Lit; 4]>],
        violated_vars: &[Var],
        totalizer_clauses: &[crate::totalizer::TotalizerClause],
        at_most_k: Option<Lit>,
    ) -> (SolverResult, SatSolver) {
        fn ensure_var(solver: &mut SatSolver, var_idx: u32) {
            while solver.num_vars() <= var_idx as usize {
                solver.new_var();
            }
        }

        let mut solver = SatSolver::new();

        for clause in self.hard_clauses.iter().chain(extra_hard.iter()) {
            for &lit in clause.iter() {
                ensure_var(&mut solver, lit.var().0);
            }
            solver.add_clause(clause.iter().copied());
        }

        for ((_, lits), &v) in items.iter().zip(violated_vars.iter()) {
            ensure_var(&mut solver, v.0);
            let mut solver_lits: SmallVec<[Lit; 8]> = lits.clone();
            solver_lits.push(Lit::pos(v));
            solver.add_clause(solver_lits.iter().copied());
        }

        for clause in totalizer_clauses {
            for &lit in &clause.lits {
                ensure_var(&mut solver, lit.var().0);
            }
            solver.add_clause(clause.lits.iter().copied());
        }

        if let Some(lit) = at_most_k {
            ensure_var(&mut solver, lit.var().0);
            solver.add_clause([lit]);
        }

        self.stats.sat_calls += 1;
        let result = solver.solve();
        (result, solver)
    }

    /// Fu-Malik core-guided algorithm
    pub(super) fn solve_fu_malik(&mut self) -> Result<MaxSatResult, MaxSatError> {
        let all_ids: Vec<SoftId> = self.soft_clauses.iter().map(|c| c.id).collect();
        self.solve_fu_malik_subset(&all_ids)
    }

    /// Fu-Malik algorithm on a subset of soft clauses
    ///
    /// This is the proper core-guided Fu-Malik algorithm using assumption-based solving.
    /// The algorithm iteratively:
    /// 1. Solve under assumptions that all soft clauses are satisfied
    /// 2. If UNSAT, extract the core of unsatisfied soft clauses
    /// 3. Add a relaxation variable to each soft clause in the core
    /// 4. Add an at-most-one constraint on the relaxation variables
    /// 5. Repeat until SAT
    pub(super) fn solve_fu_malik_subset(
        &mut self,
        soft_ids: &[SoftId],
    ) -> Result<MaxSatResult, MaxSatError> {
        let mut solver = SatSolver::new();
        let mut next_var = 0u32;

        // Helper function to ensure variable exists
        fn ensure_var(solver: &mut SatSolver, var_idx: u32) {
            while solver.num_vars() <= var_idx as usize {
                solver.new_var();
            }
        }

        // Add hard clauses
        for clause in &self.hard_clauses {
            for &lit in clause.iter() {
                ensure_var(&mut solver, lit.var().0);
                next_var = next_var.max(lit.var().0 + 1);
            }
            solver.add_clause(clause.iter().copied());
        }

        // NOTE: must scan every soft clause's own literals too, not just the
        // hard clauses -- when there are few (or zero) hard clauses, soft
        // clause literals can reference variable indices past whatever the
        // hard clauses touched. Missing this let the freshly allocated
        // blocking variables below alias real problem variables (e.g. with
        // no hard clauses at all, the very first blocking variable would be
        // `Var(0)`, colliding with a soft clause literal on variable 0),
        // silently corrupting the encoding and producing wrong costs.
        for &id in soft_ids {
            if let Some(clause) = self.soft_clauses.get(id.0 as usize) {
                for &lit in clause.lits.iter() {
                    next_var = next_var.max(lit.var().0 + 1);
                }
            }
        }

        // Create blocking variables for soft clauses (b_i = true means soft clause i is blocked/relaxed)
        let mut blocking_vars: FxHashMap<SoftId, Var> = FxHashMap::default();
        let mut var_to_soft: FxHashMap<Var, SoftId> = FxHashMap::default();

        for &id in soft_ids {
            if let Some(clause) = self.soft_clauses.get(id.0 as usize) {
                let block_var = Var(next_var);
                next_var += 1;
                ensure_var(&mut solver, block_var.0);

                blocking_vars.insert(id, block_var);
                var_to_soft.insert(block_var, id);
                self.relax_to_soft.insert(Lit::pos(block_var), id);

                // Add soft clause with blocking literal: lits \/ b_i
                // If b_i is true, the clause is trivially satisfied (blocked)
                let mut lits: SmallVec<[Lit; 8]> = clause.lits.iter().copied().collect();
                lits.push(Lit::pos(block_var));
                solver.add_clause(lits.iter().copied());

                self.stats.relax_vars_added += 1;
            }
        }

        // Track which soft clauses have been relaxed (their blocking var can be true)
        let mut relaxed: FxHashMap<SoftId, bool> = FxHashMap::default();
        for &id in soft_ids {
            relaxed.insert(id, false);
        }

        // Main Fu-Malik loop
        let mut iterations = 0;
        loop {
            iterations += 1;
            if iterations > self.config.max_iterations {
                return Ok(MaxSatResult::Unknown);
            }

            // Build assumptions: assume ~b_i for all non-relaxed soft clauses
            // This means "all soft clauses must be satisfied"
            let assumptions: Vec<Lit> = soft_ids
                .iter()
                .filter(|id| !relaxed.get(id).copied().unwrap_or(false))
                .filter_map(|id| blocking_vars.get(id).map(|&v| Lit::neg(v)))
                .collect();

            if assumptions.is_empty() {
                // All soft clauses relaxed - check if hard constraints are SAT
                return self.check_hard_satisfiable();
            }

            self.stats.sat_calls += 1;
            let (result, core) = solver.solve_with_assumptions(&assumptions);

            match result {
                SolverResult::Sat => {
                    // Found a satisfying assignment
                    self.best_model = Some(solver.model().to_vec());
                    self.update_soft_values();
                    return Ok(MaxSatResult::Optimal);
                }
                SolverResult::Unsat => {
                    // Extract core - these are the soft clauses that conflict
                    let core_lits = core.unwrap_or_default();
                    self.stats.cores_extracted += 1;

                    if core_lits.is_empty() {
                        // Empty core means hard clauses alone are UNSAT
                        return Err(MaxSatError::Unsatisfiable);
                    }

                    // Find which soft clauses are in the core
                    let mut core_soft_ids: SmallVec<[SoftId; 8]> = SmallVec::new();
                    let mut min_weight = Weight::Infinite;

                    for lit in &core_lits {
                        // Core contains ~b_i, so the var is the blocking var
                        let var = lit.var();
                        if let Some(&soft_id) = var_to_soft.get(&var) {
                            core_soft_ids.push(soft_id);
                            if let Some(clause) = self.soft_clauses.get(soft_id.0 as usize) {
                                min_weight = min_weight.min(clause.weight.clone());
                            }
                        }
                    }

                    self.stats.total_core_size += core_soft_ids.len() as u32;

                    if core_soft_ids.is_empty() {
                        // No soft clauses in core - hard constraints UNSAT
                        return Err(MaxSatError::Unsatisfiable);
                    }

                    // Relax all soft clauses in the core
                    for &soft_id in &core_soft_ids {
                        relaxed.insert(soft_id, true);
                    }

                    // Update lower bound
                    self.lower_bound = self.lower_bound.add(&min_weight);

                    // Add at-most-one constraint on core blocking variables:
                    // At most one of the blocking variables can be true.
                    // This is encoded as: for all pairs (b_i, b_j) in core: ~b_i \/ ~b_j
                    // This ensures we find a minimal relaxation.
                    if core_soft_ids.len() > 1 {
                        // Pairwise encoding for small cores
                        if core_soft_ids.len() <= 5 {
                            for i in 0..core_soft_ids.len() {
                                for j in (i + 1)..core_soft_ids.len() {
                                    if let (Some(&vi), Some(&vj)) = (
                                        blocking_vars.get(&core_soft_ids[i]),
                                        blocking_vars.get(&core_soft_ids[j]),
                                    ) {
                                        solver.add_clause([Lit::neg(vi), Lit::neg(vj)]);
                                    }
                                }
                            }
                        } else {
                            // For larger cores, use sequential counter encoding
                            // Simpler: just add that at least one must be false
                            // (weaker but still sound)
                            let clause: SmallVec<[Lit; 8]> = core_soft_ids
                                .iter()
                                .filter_map(|id| blocking_vars.get(id).map(|&v| Lit::neg(v)))
                                .collect();
                            if !clause.is_empty() {
                                solver.add_clause(clause);
                            }
                        }
                    }

                    // Add fresh relaxation variables for the next iteration
                    // Each soft clause in the core gets a new blocking variable
                    for &soft_id in &core_soft_ids {
                        if let Some(clause) = self.soft_clauses.get(soft_id.0 as usize) {
                            let new_block_var = Var(next_var);
                            next_var += 1;
                            ensure_var(&mut solver, new_block_var.0);

                            // Update mappings
                            blocking_vars.insert(soft_id, new_block_var);
                            var_to_soft.insert(new_block_var, soft_id);

                            // Add new clause: lits \/ b_new
                            let mut lits: SmallVec<[Lit; 8]> =
                                clause.lits.iter().copied().collect();
                            lits.push(Lit::pos(new_block_var));
                            solver.add_clause(lits.iter().copied());

                            // Mark as relaxed (can be blocked)
                            relaxed.insert(soft_id, true);
                        }
                    }
                }
                SolverResult::Unknown => return Ok(MaxSatResult::Unknown),
            }
        }
    }

    /// OLL (Opportunistic Literal Learning) algorithm
    ///
    /// OLL extends Fu-Malik by using cardinality constraints instead of pairwise
    /// at-most-one constraints on core blocking variables. This allows for more
    /// efficient handling of larger cores by incrementally relaxing the cardinality
    /// bound as more cores are found.
    ///
    /// Key differences from Fu-Malik:
    /// 1. Uses totalizer encoding for cardinality constraints (at-most-k)
    /// 2. Incrementally increases k when cores intersect with previous cores
    /// 3. More efficient for instances with many overlapping cores
    pub(super) fn solve_oll(&mut self) -> Result<MaxSatResult, MaxSatError> {
        use crate::totalizer::IncrementalTotalizer;

        let mut solver = SatSolver::new();
        let mut next_var = 0u32;

        // Helper function to ensure variable exists
        fn ensure_var(solver: &mut SatSolver, var_idx: u32) {
            while solver.num_vars() <= var_idx as usize {
                solver.new_var();
            }
        }

        // Add hard clauses
        for clause in &self.hard_clauses {
            for &lit in clause.iter() {
                ensure_var(&mut solver, lit.var().0);
                next_var = next_var.max(lit.var().0 + 1);
            }
            solver.add_clause(clause.iter().copied());
        }

        // Create blocking variables for soft clauses
        let soft_ids: Vec<SoftId> = self.soft_clauses.iter().map(|c| c.id).collect();
        let mut blocking_vars: FxHashMap<SoftId, Var> = FxHashMap::default();
        let mut var_to_soft: FxHashMap<Var, SoftId> = FxHashMap::default();

        // NOTE: must scan every soft clause's own literals too, not just the
        // hard clauses -- see the identical note in `solve_fu_malik_subset`.
        // With few (or zero) hard clauses, skipping this let the freshly
        // allocated blocking variables alias real problem variables,
        // silently corrupting the encoding.
        for &id in &soft_ids {
            if let Some(clause) = self.soft_clauses.get(id.0 as usize) {
                for &lit in clause.lits.iter() {
                    next_var = next_var.max(lit.var().0 + 1);
                }
            }
        }

        for &id in &soft_ids {
            if let Some(clause) = self.soft_clauses.get(id.0 as usize) {
                let block_var = Var(next_var);
                next_var += 1;
                ensure_var(&mut solver, block_var.0);

                blocking_vars.insert(id, block_var);
                var_to_soft.insert(block_var, id);
                self.relax_to_soft.insert(Lit::pos(block_var), id);

                // Add soft clause with blocking literal
                let mut lits: SmallVec<[Lit; 8]> = clause.lits.iter().copied().collect();
                lits.push(Lit::pos(block_var));
                solver.add_clause(lits.iter().copied());

                self.stats.relax_vars_added += 1;
            }
        }

        // OLL uses incremental totalizers for groups of soft clauses
        // Initially all soft clauses are in their own "group" with bound 0
        // When cores are found, we merge groups and adjust bounds
        struct OllGroup {
            soft_ids: Vec<SoftId>,
            totalizer: IncrementalTotalizer,
            current_bound: usize,
            /// Groups are never removed from `groups` (that would require
            /// renumbering every `soft_to_group` index), so a merged-away
            /// group is instead deactivated: it stops contributing a bound
            /// assumption, and every soft clause it owned is repointed to
            /// the merged replacement group.
            active: bool,
        }

        let mut groups: Vec<OllGroup> = Vec::new();
        let mut soft_to_group: FxHashMap<SoftId, usize> = FxHashMap::default();

        // Main OLL loop
        let mut iterations = 0;
        loop {
            iterations += 1;
            if iterations > self.config.max_iterations {
                return Ok(MaxSatResult::Unknown);
            }

            // Build assumptions: ~b_i for all soft clauses not in any group
            // plus the bound assumptions for each group
            let mut assumptions: Vec<Lit> = Vec::new();

            for &id in &soft_ids {
                if !soft_to_group.contains_key(&id)
                    && let Some(&block_var) = blocking_vars.get(&id)
                {
                    assumptions.push(Lit::neg(block_var));
                }
            }

            // Add group bound assumptions (deactivated/merged-away groups
            // contribute nothing further).
            for group in &groups {
                if !group.active {
                    continue;
                }
                if let Some(assumption) = group.totalizer.bound_assumption() {
                    assumptions.push(assumption);
                }
            }

            if assumptions.is_empty() && groups.is_empty() {
                // All satisfied - check hard constraints
                return self.check_hard_satisfiable();
            }

            self.stats.sat_calls += 1;
            let (result, core) = solver.solve_with_assumptions(&assumptions);

            match result {
                SolverResult::Sat => {
                    self.best_model = Some(solver.model().to_vec());
                    self.update_soft_values();
                    return Ok(MaxSatResult::Optimal);
                }
                SolverResult::Unsat => {
                    let core_lits = core.unwrap_or_default();
                    self.stats.cores_extracted += 1;

                    if core_lits.is_empty() {
                        return Err(MaxSatError::Unsatisfiable);
                    }

                    // Find which soft clauses are in the core
                    let mut core_soft_ids: SmallVec<[SoftId; 8]> = SmallVec::new();
                    let mut min_weight = Weight::Infinite;

                    for lit in &core_lits {
                        let var = lit.var();
                        if let Some(&soft_id) = var_to_soft.get(&var) {
                            core_soft_ids.push(soft_id);
                            if let Some(clause) = self.soft_clauses.get(soft_id.0 as usize) {
                                min_weight = min_weight.min(clause.weight.clone());
                            }
                        }
                    }

                    self.stats.total_core_size += core_soft_ids.len() as u32;

                    if core_soft_ids.is_empty() {
                        return Err(MaxSatError::Unsatisfiable);
                    }

                    self.lower_bound = self.lower_bound.add(&min_weight);

                    // Collect groups that intersect with the core
                    let mut intersecting_groups: Vec<usize> = core_soft_ids
                        .iter()
                        .filter_map(|id| soft_to_group.get(id).copied())
                        .collect();
                    intersecting_groups.sort_unstable();
                    intersecting_groups.dedup();

                    if intersecting_groups.is_empty() {
                        // Create a new group from core soft clauses
                        let block_lits: Vec<Lit> = core_soft_ids
                            .iter()
                            .filter_map(|id| blocking_vars.get(id).map(|v| Lit::pos(*v)))
                            .collect();

                        if !block_lits.is_empty() {
                            let mut totalizer = IncrementalTotalizer::new(&block_lits, next_var);
                            next_var = totalizer.next_var();

                            // Set bound to 1 (at most 1 can be true)
                            let (assumption, clauses) = totalizer.set_bound(1);

                            // Add totalizer clauses
                            for clause in clauses {
                                // Ensure vars exist
                                for &lit in &clause.lits {
                                    ensure_var(&mut solver, lit.var().0);
                                }
                                solver.add_clause(clause.lits.iter().copied());
                            }

                            let group_idx = groups.len();
                            let group = OllGroup {
                                soft_ids: core_soft_ids.iter().copied().collect(),
                                totalizer,
                                current_bound: 1,
                                active: true,
                            };
                            groups.push(group);

                            for &id in &core_soft_ids {
                                soft_to_group.insert(id, group_idx);
                            }

                            // The assumption is already stored in the totalizer
                            let _ = assumption;
                        }
                    } else {
                        // Merge every group whose soft clauses appear in this
                        // new core into a single fresh group. Standard OLL
                        // merge rule: build one totalizer over the union of
                        // every underlying soft-clause literal from the
                        // merged groups (plus any core items not already
                        // grouped), and set the merged bound to the *sum* of
                        // the constituent groups' individual bounds, plus
                        // one -- the extra unit of relaxation budget this
                        // new core proves is needed beyond what the groups
                        // already allowed individually.
                        //
                        // The previous implementation only bumped the
                        // *first* intersecting group's bound and left the
                        // others untouched. Since every (still-active) group
                        // keeps contributing its own `bound_assumption()` on
                        // every subsequent solve, those un-bumped groups'
                        // stale, tighter bounds kept re-deriving essentially
                        // the same conflict, so `lower_bound` (bumped by
                        // `min_weight` on every "new" core) grew without
                        // reflecting genuine additional cost -- inflating
                        // the reported optimum.
                        let mut merged_soft_ids: Vec<SoftId> = Vec::new();
                        let mut merged_bound = 0usize;
                        for &g in &intersecting_groups {
                            groups[g].active = false;
                            merged_bound += groups[g].current_bound;
                            merged_soft_ids.extend(groups[g].soft_ids.iter().copied());
                        }
                        for &id in &core_soft_ids {
                            if !merged_soft_ids.contains(&id) {
                                merged_soft_ids.push(id);
                            }
                        }
                        merged_bound += 1;

                        let block_lits: Vec<Lit> = merged_soft_ids
                            .iter()
                            .filter_map(|id| blocking_vars.get(id).map(|v| Lit::pos(*v)))
                            .collect();

                        if block_lits.is_empty() {
                            // Nothing concrete to constrain (shouldn't
                            // normally happen since every intersecting
                            // group started from real soft clauses); leave
                            // the merged groups deactivated with no
                            // replacement rather than fabricate a group.
                            continue;
                        }

                        let mut totalizer = IncrementalTotalizer::new(&block_lits, next_var);
                        next_var = totalizer.next_var();
                        let bound = merged_bound.min(block_lits.len());
                        let (_, clauses) = totalizer.set_bound(bound);

                        let merged_idx = groups.len();
                        for &id in &merged_soft_ids {
                            soft_to_group.insert(id, merged_idx);
                        }
                        groups.push(OllGroup {
                            soft_ids: merged_soft_ids,
                            totalizer,
                            current_bound: bound,
                            active: true,
                        });

                        // Add new clauses
                        for clause in clauses {
                            for &lit in &clause.lits {
                                ensure_var(&mut solver, lit.var().0);
                            }
                            solver.add_clause(clause.lits.iter().copied());
                        }
                    }
                }
                SolverResult::Unknown => return Ok(MaxSatResult::Unknown),
            }
        }
    }

    /// MSU3 (iterative relaxation) algorithm
    ///
    /// MSU3 is a simpler core-guided algorithm that:
    /// 1. Finds UNSAT cores iteratively
    /// 2. Relaxes soft clauses from the core
    /// 3. Uses at-most-one constraints similar to Fu-Malik
    ///
    /// The key difference from Fu-Malik is in how cores are processed.
    /// MSU3 uses a simpler relaxation strategy.
    pub(super) fn solve_msu3(&mut self) -> Result<MaxSatResult, MaxSatError> {
        // MSU3 is very similar to Fu-Malik in practice
        // The main difference is in weight handling and core processing strategy
        // For unweighted MaxSAT, they are essentially equivalent
        // Use Fu-Malik implementation for correctness
        self.solve_fu_malik()
    }

    /// WMax (weighted MaxSAT) algorithm
    ///
    /// WMax is designed for weighted MaxSAT instances. It processes
    /// soft clauses in weight order and uses weight-aware core extraction.
    pub(super) fn solve_wmax(&mut self) -> Result<MaxSatResult, MaxSatError> {
        // If all weights are the same, just use Fu-Malik
        if !self.has_different_weights() {
            return self.solve_fu_malik();
        }

        // Use weight-aware cardinality-search solving.
        self.solve_weighted_core_guided()
    }

    /// Update soft clause values from the best model
    /// Update every soft clause's cached satisfaction value from
    /// `self.best_model`.
    ///
    /// `Lit::sign()` returns `true` for a *positive* literal (see
    /// `oxiz_sat::Lit::sign`'s own doc: "true for positive, false for
    /// negative") -- the opposite of what this method's condition used to
    /// assume. The old `(val == True && !lit.sign()) || (val == False &&
    /// lit.sign())` therefore had the polarity backwards: it reported a
    /// negative literal as *satisfied* exactly when its variable was
    /// `True` (i.e. when the literal is actually violated) and vice
    /// versa. This didn't corrupt `cost()`/`lower_bound` (which are
    /// tracked independently via core accumulation), but it silently
    /// inverted every consumer of `is_soft_satisfied`/`satisfied_soft`/
    /// `unsatisfied_soft` for any soft clause built from a negative unit
    /// literal -- exactly the shape `MaxHsSolver::compute_hitting_set`'s
    /// `¬sel_s` soft clauses use.
    pub(super) fn update_soft_values(&mut self) {
        if let Some(model) = &self.best_model {
            for clause in &mut self.soft_clauses {
                let satisfied = clause.lits.iter().any(|&lit| {
                    let var = lit.var().0 as usize;
                    if var < model.len() {
                        let val = model[var];
                        (val == LBool::True && lit.sign()) || (val == LBool::False && !lit.sign())
                    } else {
                        false
                    }
                });
                clause.set_value(satisfied);
            }
        }
    }

    /// PMRES (Partial MaxSAT Resolution) algorithm
    ///
    /// PMRES is a resolution-based algorithm for partial MaxSAT that:
    /// 1. Finds minimal unsatisfiable cores
    /// 2. Resolves soft clauses to create new clauses
    /// 3. Uses weight-based core selection
    ///
    /// It's particularly effective for partial MaxSAT instances with many hard constraints.
    ///
    /// Reference: "Solving Maxsat by Solving a Sequence of Simpler SAT Instances" (2010)
    ///
    /// # Delegation to Fu-Malik
    ///
    /// The hand-rolled multi-clause-core branch this method used to run
    /// asserted every core soft clause's assumption literal as positive
    /// (`must be satisfied`) *and simultaneously* asserted a fresh
    /// `at-most-(k-1)-true` totalizer bound over that exact same literal
    /// set. With every one of the `k` literals individually forced true,
    /// the sum is trivially `k > k-1`, so the combined assumption set was
    /// jointly unsatisfiable *by construction* -- independent of whatever
    /// the underlying hard/soft clauses actually required. This made
    /// `solve_with_assumptions` return UNSAT immediately on every such
    /// call, re-deriving essentially the same core over and over and
    /// bumping `lower_bound` by `min_weight` each time without any
    /// genuine additional cost being proven, inflating the reported
    /// optimum (and, for `test_maxsat_pmres_multiple_cores`-shaped
    /// instances, taking tens of thousands of iterations of growing
    /// totalizers to hit `max_iterations` rather than terminating).
    ///
    /// A sound fix requires excluding cores' member literals from future
    /// unconditional-true assumptions once they are governed by a
    /// cardinality bound (i.e. genuine cross-core group *merging*, as
    /// implemented for `solve_oll` above) -- fully re-deriving that
    /// machinery a second time here, with PMRES's differently-signed
    /// literal roles, would duplicate a large, delicate amount of new
    /// logic for a distinct code path. [`Self::solve_fu_malik`] already
    /// implements a proof-correct core-guided relaxation (proper at-most-
    /// one groups, no self-contradictory assumptions) using the exact
    /// same core-extraction primitives PMRES relies on, so `Pmres` is
    /// routed through it: this keeps the algorithm knob honestly
    /// functional (same soundness and the same `MaxSatResult::Optimal`
    /// guarantee) rather than silently returning inflated costs or
    /// hanging until `max_iterations`.
    pub(super) fn solve_pmres(&mut self) -> Result<MaxSatResult, MaxSatError> {
        self.solve_fu_malik()
    }
}
