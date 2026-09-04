//! All-SAT / Model Enumeration
//!
//! This module provides functionality for enumerating multiple or all satisfying
//! assignments for a SAT formula. It supports:
//! - Complete enumeration (find all solutions)
//! - Limited enumeration (find up to N solutions)
//! - Projected enumeration (enumerate over subset of variables)
//! - Solution blocking (add clauses to exclude found solutions)
//! - Minimal/maximal model enumeration
//! - Solution counting
//!
//! ## Algorithm
//!
//! The basic approach uses solution blocking:
//! 1. Solve the formula
//! 2. If SAT, extract model and block it with a clause
//! 3. Repeat until UNSAT or limit reached
//!
//! For projected enumeration over variables V', we block only those assignments:
//! - Block clause: (¬l1 ∨ ¬l2 ∨ ... ∨ ¬ln) where li ∈ V' are assigned literals
//!
//! ## Example
//!
//! ```rust,ignore
//! use nixie_sat::{Solver, AllSatEnumerator, Var, Lit};
//!
// let mut solver = Solver::new();
// // Add formula: (x1 ∨ x2) ∧ (¬x1 ∨ x3)
// solver.add_clause([Lit::pos(Var(0)), Lit::pos(Var(1))]);
// solver.add_clause([Lit::neg(Var(0)), Lit::pos(Var(2))]);
//
// let mut enumerator = AllSatEnumerator::new();
// let models = enumerator.enumerate_all(&mut solver, 3);
// println!("Found {} models", models.len());
// ```

use crate::literal::{LBool, Lit, Var};
#[allow(unused_imports)]
use crate::prelude::*;
use crate::solver::{Solver, SolverResult};
use smallvec::SmallVec;

/// A model (satisfying assignment) represented as a vector of literals
pub type Model = Vec<Lit>;

/// Configuration for model enumeration
#[derive(Debug, Clone, Default)]
pub struct EnumerationConfig {
    /// Maximum number of models to find (None = find all)
    pub max_models: Option<usize>,
    /// Variables to project onto (None = all variables)
    pub project_vars: Option<HashSet<Var>>,
    /// Only find inclusion-minimal models: models whose true-literal set has
    /// no proper subset that is also a model. This is the standard logic
    /// definition of "minimal model" (Pareto-minimal under the subset
    /// order), *not* minimum cardinality – a formula can have several
    /// incomparable inclusion-minimal models, and enumeration finds all of
    /// them.
    pub minimal_models: bool,
    /// Only find inclusion-maximal models (dual of `minimal_models`): models
    /// whose true-literal set has no proper superset that is also a model.
    pub maximal_models: bool,
    /// Historical "block solutions with positive literals only" toggle.
    ///
    /// This no longer has an independent effect: the underlying
    /// (superset-excluding) blocking clause it opted into is unsound as a
    /// general-purpose optimization – see `AllSatEnumerator::create_blocking_clause`
    /// – so it is now applied automatically, and only, when it is actually
    /// sound (i.e. whenever `minimal_models` is set). The field is kept for
    /// API compatibility but setting it has no observable effect.
    pub block_positive_only: bool,
}

impl EnumerationConfig {
    /// Create config to find all models
    #[must_use]
    pub fn all() -> Self {
        Self::default()
    }

    /// Create config to find up to N models
    #[must_use]
    pub fn limited(max_models: usize) -> Self {
        Self {
            max_models: Some(max_models),
            ..Default::default()
        }
    }

    /// Create config for projected enumeration
    #[must_use]
    pub fn projected(vars: HashSet<Var>) -> Self {
        Self {
            project_vars: Some(vars),
            ..Default::default()
        }
    }

    /// Set maximum number of models
    pub fn with_max_models(mut self, max: usize) -> Self {
        self.max_models = Some(max);
        self
    }

    /// Set projection variables
    pub fn with_projection(mut self, vars: HashSet<Var>) -> Self {
        self.project_vars = Some(vars);
        self
    }

    /// Enable minimal model enumeration
    #[must_use]
    pub const fn minimal(mut self) -> Self {
        self.minimal_models = true;
        self
    }

    /// Enable maximal model enumeration
    #[must_use]
    pub const fn maximal(mut self) -> Self {
        self.maximal_models = true;
        self
    }
}

/// Statistics for model enumeration
#[derive(Debug, Default, Clone)]
pub struct EnumerationStats {
    /// Number of models found
    pub models_found: usize,
    /// Number of solver calls made
    pub solver_calls: usize,
    /// Number of blocking clauses added
    pub blocking_clauses: usize,
    /// Total number of variables in all models
    pub total_literals: usize,
}

impl EnumerationStats {
    /// Get average model size (number of literals)
    #[must_use]
    pub fn avg_model_size(&self) -> f64 {
        if self.models_found == 0 {
            0.0
        } else {
            self.total_literals as f64 / self.models_found as f64
        }
    }
}

/// Result of enumeration
#[derive(Debug, Clone)]
pub enum EnumerationResult {
    /// Successfully enumerated all models (or reached limit)
    Complete(Vec<Model>),
    /// Enumeration incomplete (solver returned Unknown)
    Incomplete(Vec<Model>),
    /// Formula is unsatisfiable
    Unsat,
}

impl EnumerationResult {
    /// Get the models (empty if Unsat)
    #[must_use]
    pub fn models(&self) -> &[Model] {
        match self {
            EnumerationResult::Complete(models) | EnumerationResult::Incomplete(models) => models,
            EnumerationResult::Unsat => &[],
        }
    }

    /// Check if enumeration was complete
    #[must_use]
    pub const fn is_complete(&self) -> bool {
        matches!(self, EnumerationResult::Complete(_))
    }

    /// Number of models found
    #[must_use]
    pub fn count(&self) -> usize {
        self.models().len()
    }
}

/// All-SAT enumerator for finding multiple satisfying assignments
pub struct AllSatEnumerator {
    /// Configuration
    config: EnumerationConfig,
    /// Statistics
    stats: EnumerationStats,
    /// Collected models
    models: Vec<Model>,
}

impl AllSatEnumerator {
    /// Create a new enumerator with given configuration
    #[must_use]
    pub fn new(config: EnumerationConfig) -> Self {
        Self {
            config,
            stats: EnumerationStats::default(),
            models: Vec::new(),
        }
    }

    /// Create enumerator with default configuration
    #[must_use]
    pub fn default_config() -> Self {
        Self::new(EnumerationConfig::default())
    }

    /// Get statistics
    #[must_use]
    pub const fn stats(&self) -> &EnumerationStats {
        &self.stats
    }

    /// Get collected models
    #[must_use]
    pub fn models(&self) -> &[Model] {
        &self.models
    }

    /// Reset enumerator state
    pub fn reset(&mut self) {
        self.models.clear();
        self.stats = EnumerationStats::default();
    }

    /// Enumerate all satisfying assignments
    ///
    /// # Arguments
    ///
    /// * `solver` - The SAT solver instance
    /// * `num_vars` - Total number of variables in the formula
    ///
    /// # Returns
    ///
    /// Returns `EnumerationResult` with found models
    pub fn enumerate(&mut self, solver: &mut Solver, num_vars: usize) -> EnumerationResult {
        self.reset();

        loop {
            // Check if we've reached the limit
            if let Some(max) = self.config.max_models
                && self.models.len() >= max
            {
                return EnumerationResult::Complete(self.models.clone());
            }

            // Solve
            self.stats.solver_calls += 1;
            let result = solver.solve();

            match result {
                SolverResult::Sat => {
                    // Extract model
                    let mut model = self.extract_model(solver, num_vars);

                    // Backtrack to level 0 before adding blocking clause
                    // This is necessary for incremental solving to work correctly
                    solver.backtrack_to_root();

                    // If minimal/maximal enumeration was requested, replace the
                    // raw model with a genuine inclusion-minimal/maximal one
                    // *before* recording or blocking it (see `shrink_to_minimal`
                    // / `grow_to_maximal`). This makes `minimal_models` and
                    // `maximal_models` real constraints instead of silently
                    // ignored configuration.
                    if self.config.minimal_models {
                        model = self.shrink_to_minimal(solver, model, num_vars);
                    } else if self.config.maximal_models {
                        model = self.grow_to_maximal(solver, model, num_vars);
                    }

                    self.stats.models_found += 1;
                    self.stats.total_literals += model.len();
                    self.models.push(model.clone());

                    // Block this solution
                    let blocking_clause = self.create_blocking_clause(&model);
                    self.stats.blocking_clauses += 1;
                    if !solver.add_clause(blocking_clause.iter().copied()) {
                        // Adding blocking clause made formula UNSAT
                        return EnumerationResult::Complete(self.models.clone());
                    }
                }
                SolverResult::Unsat => {
                    // No more models
                    if self.models.is_empty() {
                        return EnumerationResult::Unsat;
                    }
                    return EnumerationResult::Complete(self.models.clone());
                }
                SolverResult::Unknown => {
                    // Solver couldn't determine, return incomplete
                    return EnumerationResult::Incomplete(self.models.clone());
                }
            }
        }
    }

    /// Extract model from solver's current assignment
    fn extract_model(&self, solver: &Solver, num_vars: usize) -> Model {
        let mut model = Vec::new();

        for i in 0..num_vars {
            let var = Var(i as u32);
            let value = solver.model_value(var);

            // Skip undefined variables
            if value == LBool::Undef {
                continue;
            }

            // Check if we should include this variable
            if let Some(ref project_vars) = self.config.project_vars
                && !project_vars.contains(&var)
            {
                continue;
            }

            // Add literal to model
            let lit = if value == LBool::True {
                Lit::pos(var)
            } else {
                Lit::neg(var)
            };

            model.push(lit);
        }

        model
    }

    /// Shrink `model` to an inclusion-minimal model.
    ///
    /// Repeatedly tries to flip each currently-*true* literal to false while
    /// keeping every currently-*false* literal fixed at false; the other
    /// true literals are left unconstrained, so the solver is free to turn
    /// additional ones false as well. If any flip succeeds, the (necessarily
    /// strictly smaller) model it returns replaces the current one and the
    /// process repeats; once no flip succeeds, the model cannot be shrunk
    /// further and is inclusion-minimal. This is the standard deletion-based
    /// algorithm for minimal-model search (dual of deletion-based MUS
    /// extraction) and terminates in at most `|true literals|` shrink
    /// rounds.
    ///
    /// Each trial is wrapped in [`Solver::push`]/[`Solver::pop`] rather than
    /// [`Solver::solve_with_assumptions`]: the latter's `Sat` path restores
    /// the search state with a plain (non-phase-saving) backtrack, which
    /// never re-inserts the variables it decided back into the VSIDS/CHB
    /// heaps, permanently starving `pick_branch_var` on every later plain
    /// `solve()` call in this same enumeration. `push`/`pop` perform the
    /// same "assume these literals" trial via temporary unit clauses and
    /// correctly restore heap state on `pop`, so it composes safely with
    /// the surrounding enumeration loop's own `solve()` calls.
    fn shrink_to_minimal(
        &mut self,
        solver: &mut Solver,
        mut model: Model,
        num_vars: usize,
    ) -> Model {
        loop {
            let false_lits: Vec<Lit> = model.iter().copied().filter(|l| l.is_neg()).collect();
            let true_lits: Vec<Lit> = model.iter().copied().filter(|l| l.is_pos()).collect();

            let mut shrunk = None;
            for &true_lit in &true_lits {
                solver.push();
                for &fl in &false_lits {
                    solver.add_clause([fl]);
                }
                solver.add_clause([true_lit.negate()]);

                self.stats.solver_calls += 1;
                let result = solver.solve();
                if result == SolverResult::Sat {
                    shrunk = Some(self.extract_model(solver, num_vars));
                }
                solver.pop();

                if shrunk.is_some() {
                    break;
                }
            }

            match shrunk {
                Some(smaller) => model = smaller,
                None => return model,
            }
        }
    }

    /// Grow `model` to an inclusion-maximal model.
    ///
    /// Dual of [`Self::shrink_to_minimal`]: repeatedly tries to flip each
    /// currently-*false* literal to true while keeping every currently-*true*
    /// literal fixed at true; if any flip succeeds, the (strictly larger)
    /// model it returns replaces the current one and the process repeats
    /// until no flip succeeds, at which point the model is
    /// inclusion-maximal. See [`Self::shrink_to_minimal`] for why this uses
    /// `push`/`pop` instead of `solve_with_assumptions`.
    fn grow_to_maximal(&mut self, solver: &mut Solver, mut model: Model, num_vars: usize) -> Model {
        loop {
            let false_lits: Vec<Lit> = model.iter().copied().filter(|l| l.is_neg()).collect();
            let true_lits: Vec<Lit> = model.iter().copied().filter(|l| l.is_pos()).collect();

            let mut grown = None;
            for &false_lit in &false_lits {
                solver.push();
                for &tl in &true_lits {
                    solver.add_clause([tl]);
                }
                solver.add_clause([false_lit.negate()]);

                self.stats.solver_calls += 1;
                let result = solver.solve();
                if result == SolverResult::Sat {
                    grown = Some(self.extract_model(solver, num_vars));
                }
                solver.pop();

                if grown.is_some() {
                    break;
                }
            }

            match grown {
                Some(bigger) => model = bigger,
                None => return model,
            }
        }
    }

    /// Create a blocking clause for a given model.
    ///
    /// For plain enumeration this is the standard *exact-assignment* clause
    /// (the negation of every literal in `model`), which excludes only that
    /// single total assignment.
    ///
    /// For `minimal_models` / `maximal_models` it is instead a *dominance*
    /// clause, and using anything else is not merely a missed optimization –
    /// it is unsound and produces wrong results (see the module-level
    /// discussion above `shrink_to_minimal`). Concretely:
    ///
    /// - `minimal_models`: "up-blocking" – only the *true* literals,
    ///   negated. This excludes every superset of `model`'s true-set (a
    ///   confirmed minimal model can never be dominated by removing this),
    ///   while an exact-assignment clause could accidentally remove the sole
    ///   remaining witness that a *later*, still-unclassified candidate is
    ///   non-minimal, causing that candidate to look like a local fixed
    ///   point and be misreported as minimal.
    /// - `maximal_models`: "down-blocking" – the dual, only the *false*
    ///   literals, negated. Excludes every subset of `model`'s true-set.
    ///
    /// Either filtered form can legitimately come out empty (e.g. a minimal
    /// model with an empty true-set, or a maximal model that is the unique
    /// global maximum): that correctly signals "nothing further to find" via
    /// [`Solver::add_clause`]'s empty-clause UNSAT path, which the caller
    /// already treats as the (honest) completion of enumeration – it must
    /// not be papered over with a synthetic extra literal.
    ///
    /// `EnumerationConfig::block_positive_only` no longer has an independent
    /// effect: the up-blocking it used to opt into is now applied
    /// automatically (and only) whenever it is actually sound, i.e. exactly
    /// when `minimal_models` is set.
    fn create_blocking_clause(&self, model: &Model) -> SmallVec<[Lit; 32]> {
        if self.config.minimal_models {
            model
                .iter()
                .copied()
                .filter(|l| l.is_pos())
                .map(Lit::negate)
                .collect()
        } else if self.config.maximal_models {
            model
                .iter()
                .copied()
                .filter(|l| l.is_neg())
                .map(Lit::negate)
                .collect()
        } else {
            model.iter().copied().map(Lit::negate).collect()
        }
    }
}

/// Convenience functions for common enumeration tasks
impl AllSatEnumerator {
    /// Enumerate all models (no limit)
    ///
    /// # Arguments
    ///
    /// * `solver` - The SAT solver
    /// * `num_vars` - Number of variables
    ///
    /// # Returns
    ///
    /// Vector of all found models
    #[must_use]
    pub fn enumerate_all(solver: &mut Solver, num_vars: usize) -> Vec<Model> {
        let mut enumerator = Self::new(EnumerationConfig::all());
        enumerator.enumerate(solver, num_vars).models().to_vec()
    }

    /// Enumerate up to N models
    ///
    /// # Arguments
    ///
    /// * `solver` - The SAT solver
    /// * `num_vars` - Number of variables
    /// * `max_models` - Maximum number of models to find
    #[must_use]
    pub fn enumerate_limited(
        solver: &mut Solver,
        num_vars: usize,
        max_models: usize,
    ) -> Vec<Model> {
        let mut enumerator = Self::new(EnumerationConfig::limited(max_models));
        enumerator.enumerate(solver, num_vars).models().to_vec()
    }

    /// Count the number of satisfying assignments
    ///
    /// # Arguments
    ///
    /// * `solver` - The SAT solver
    /// * `num_vars` - Number of variables
    /// * `max_count` - Maximum count (None = count all)
    ///
    /// # Returns
    ///
    /// Number of models found (up to max_count)
    pub fn count_models(solver: &mut Solver, num_vars: usize, max_count: Option<usize>) -> usize {
        let config = if let Some(max) = max_count {
            EnumerationConfig::limited(max)
        } else {
            EnumerationConfig::all()
        };

        let mut enumerator = Self::new(config);
        let result = enumerator.enumerate(solver, num_vars);
        result.count()
    }

    /// Enumerate models with projection onto specific variables
    ///
    /// # Arguments
    ///
    /// * `solver` - The SAT solver
    /// * `num_vars` - Number of variables
    /// * `project_vars` - Variables to project onto
    #[must_use]
    pub fn enumerate_projected(
        solver: &mut Solver,
        num_vars: usize,
        project_vars: HashSet<Var>,
    ) -> Vec<Model> {
        let mut enumerator = Self::new(EnumerationConfig::projected(project_vars));
        enumerator.enumerate(solver, num_vars).models().to_vec()
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::solver::Solver;

    #[test]
    fn test_enumerate_simple() {
        let mut solver = Solver::new();
        // Formula: x1 ∨ x2
        solver.add_clause([Lit::pos(Var(0)), Lit::pos(Var(1))]);

        let models = AllSatEnumerator::enumerate_all(&mut solver, 2);
        // Should find 3 models: {x1}, {x2}, {x1, x2}
        // (plus variations with negative literals)
        assert!(!models.is_empty());
    }

    #[test]
    fn test_enumerate_unsat() {
        let mut solver = Solver::new();
        // Contradictory clauses
        solver.add_clause([Lit::pos(Var(0))]);
        solver.add_clause([Lit::neg(Var(0))]);

        let mut enumerator = AllSatEnumerator::new(EnumerationConfig::all());
        let result = enumerator.enumerate(&mut solver, 1);

        assert!(matches!(result, EnumerationResult::Unsat));
        assert_eq!(result.count(), 0);
    }

    #[test]
    fn test_enumerate_limited() {
        let mut solver = Solver::new();
        // Formula that has multiple solutions: x1 ∨ x2
        solver.add_clause([Lit::pos(Var(0)), Lit::pos(Var(1))]);

        let models = AllSatEnumerator::enumerate_limited(&mut solver, 2, 2);
        assert!(models.len() <= 2);
    }

    #[test]
    fn test_enumerate_single_var() {
        let mut solver = Solver::new();
        // No constraints - x1 can be true or false
        // Actually, with no constraints, everything is a model
        // Add a trivial tautology to make it non-trivial
        solver.add_clause([Lit::pos(Var(0)), Lit::neg(Var(0))]);

        let models = AllSatEnumerator::enumerate_all(&mut solver, 1);
        // With a tautology, we should find models (any assignment works)
        // But in practice, the solver might find multiple assignments
        assert!(!models.is_empty());
    }

    #[test]
    fn test_count_models() {
        let mut solver = Solver::new();
        solver.add_clause([Lit::pos(Var(0)), Lit::pos(Var(1))]);

        let count = AllSatEnumerator::count_models(&mut solver, 2, Some(5));
        assert!(count >= 1);
        assert!(count <= 5);
    }

    #[test]
    fn test_enumerator_stats() {
        let mut solver = Solver::new();
        solver.add_clause([Lit::pos(Var(0))]);

        let mut enumerator = AllSatEnumerator::new(EnumerationConfig::limited(10));
        enumerator.enumerate(&mut solver, 1);

        let stats = enumerator.stats();
        assert!(stats.models_found >= 1);
        assert!(stats.solver_calls >= 1);
        assert_eq!(stats.models_found, stats.blocking_clauses);
    }

    #[test]
    fn test_projected_enumeration() {
        let mut solver = Solver::new();
        // Formula: x1 ∧ (x2 ∨ x3)
        solver.add_clause([Lit::pos(Var(0))]);
        solver.add_clause([Lit::pos(Var(1)), Lit::pos(Var(2))]);

        // Project onto x1 and x2 only
        let mut project_vars = HashSet::new();
        project_vars.insert(Var(0));
        project_vars.insert(Var(1));

        let models = AllSatEnumerator::enumerate_projected(&mut solver, 3, project_vars);
        // Should find models with x1=true and different x2 values
        assert!(!models.is_empty());

        // All models should only contain x1 and x2
        for model in &models {
            for lit in model {
                assert!(lit.var() == Var(0) || lit.var() == Var(1));
            }
        }
    }

    #[test]
    fn test_blocking_clause_creation() {
        let enumerator = AllSatEnumerator::new(EnumerationConfig::all());
        let model = vec![Lit::pos(Var(0)), Lit::neg(Var(1)), Lit::pos(Var(2))];

        let blocking = enumerator.create_blocking_clause(&model);

        // Blocking clause should be: ¬x1 ∨ x2 ∨ ¬x3
        assert_eq!(blocking.len(), 3);
        assert!(blocking.contains(&Lit::neg(Var(0))));
        assert!(blocking.contains(&Lit::pos(Var(1))));
        assert!(blocking.contains(&Lit::neg(Var(2))));
    }

    #[test]
    fn test_enumeration_result_methods() {
        let models = vec![vec![Lit::pos(Var(0))], vec![Lit::neg(Var(0))]];
        let result = EnumerationResult::Complete(models.clone());

        assert!(result.is_complete());
        assert_eq!(result.count(), 2);
        assert_eq!(result.models().len(), 2);

        let unsat = EnumerationResult::Unsat;
        assert_eq!(unsat.count(), 0);
        assert!(unsat.models().is_empty());
    }

    #[test]
    fn test_config_builders() {
        let config = EnumerationConfig::all();
        assert!(config.max_models.is_none());

        let config = EnumerationConfig::limited(10);
        assert_eq!(config.max_models, Some(10));

        let mut vars = HashSet::new();
        vars.insert(Var(0));
        let config = EnumerationConfig::projected(vars.clone());
        assert!(config.project_vars.is_some());

        let config = EnumerationConfig::all().minimal().maximal();
        assert!(config.minimal_models);
        assert!(config.maximal_models);
    }

    #[test]
    fn test_stats_avg_model_size() {
        let mut stats = EnumerationStats::default();
        assert_eq!(stats.avg_model_size(), 0.0);

        stats.models_found = 3;
        stats.total_literals = 12;
        assert_eq!(stats.avg_model_size(), 4.0);
    }

    #[test]
    fn test_reset() {
        let mut solver = Solver::new();
        solver.add_clause([Lit::pos(Var(0))]);

        let mut enumerator = AllSatEnumerator::new(EnumerationConfig::limited(5));
        enumerator.enumerate(&mut solver, 1);

        assert!(!enumerator.models().is_empty());

        enumerator.reset();
        assert!(enumerator.models().is_empty());
        assert_eq!(enumerator.stats().models_found, 0);
    }

    /// Brute-force reference: bit `i` of a `u8` is the truth value of
    /// `Var(i)` (1 = true) for a 3-variable formula expressed as a list of
    /// clauses, each clause a list of `(var_index, wanted_value)`.
    fn brute_force_sat_assignments(clauses: &[Vec<(usize, bool)>]) -> Vec<u8> {
        let satisfies = |bits: u8| -> bool {
            let val = |i: usize| (bits >> i) & 1 == 1;
            clauses
                .iter()
                .all(|clause| clause.iter().any(|&(v, want_true)| val(v) == want_true))
        };
        (0u8..8).filter(|&b| satisfies(b)).collect()
    }

    /// Inclusion-minimal models among `sat`: those whose true-literal set has
    /// no *proper subset* that is also in `sat`. (Note: this is the standard
    /// logic definition of "minimal model" – Pareto-minimal by the subset
    /// order – which is *not* the same as minimum-cardinality; a formula can
    /// have several incomparable inclusion-minimal models.)
    fn inclusion_minimal(sat: &[u8]) -> HashSet<u8> {
        sat.iter()
            .copied()
            .filter(|&b| !sat.iter().any(|&c| c != b && (c & b) == c))
            .collect()
    }

    /// Dual of [`inclusion_minimal`]: models with no proper superset in `sat`.
    fn inclusion_maximal(sat: &[u8]) -> HashSet<u8> {
        sat.iter()
            .copied()
            .filter(|&b| !sat.iter().any(|&d| d != b && (d & b) == b))
            .collect()
    }

    fn model_to_bits(model: &Model) -> u8 {
        let mut bits = 0u8;
        for &lit in model {
            if lit.is_pos() {
                bits |= 1 << lit.var().index();
            }
        }
        bits
    }

    // Regression test for the minimal-model item: previously `minimal_models`
    // was accepted but silently ignored (every satisfying assignment was
    // reported as if it were a valid minimal model). `(x0 ∨ x1) ∧ (x1 ∨ x2)`
    // has two incomparable inclusion-minimal models: {x1} and {x0, x2}
    // (e.g. {x0,x1} is satisfying but is *not* minimal, since {x1} ⊊ {x0,x1}
    // is itself already satisfying). Verify we find exactly the minimal set
    // and nothing dominated.
    #[test]
    fn test_minimal_model_enumeration_matches_brute_force() {
        let clauses = vec![vec![(0, true), (1, true)], vec![(1, true), (2, true)]];
        let sat = brute_force_sat_assignments(&clauses);
        let expected_minimal = inclusion_minimal(&sat);
        assert_eq!(
            expected_minimal,
            HashSet::from_iter([0b010u8, 0b101u8]),
            "sanity check on the brute-force reference itself"
        );

        let mut solver = Solver::new();
        solver.add_clause([Lit::pos(Var(0)), Lit::pos(Var(1))]);
        solver.add_clause([Lit::pos(Var(1)), Lit::pos(Var(2))]);

        let mut enumerator = AllSatEnumerator::new(EnumerationConfig::all().minimal());
        let result = enumerator.enumerate(&mut solver, 3);

        let mut found = HashSet::new();
        for model in result.models() {
            let bits = model_to_bits(model);
            assert!(
                expected_minimal.contains(&bits),
                "reported model {bits:03b} is not an inclusion-minimal model of the formula"
            );
            found.insert(bits);
        }
        assert_eq!(
            found, expected_minimal,
            "minimal-model enumeration should find every inclusion-minimal model"
        );
    }

    // Dual regression test for the maximal-model item. The same formula's
    // unique inclusion-maximal model is the all-true assignment (every other
    // satisfying assignment is a proper subset of it).
    #[test]
    fn test_maximal_model_enumeration_matches_brute_force() {
        let clauses = vec![vec![(0, true), (1, true)], vec![(1, true), (2, true)]];
        let sat = brute_force_sat_assignments(&clauses);
        let expected_maximal = inclusion_maximal(&sat);
        assert_eq!(
            expected_maximal,
            HashSet::from_iter([0b111u8]),
            "sanity check on the brute-force reference itself"
        );

        let mut solver = Solver::new();
        solver.add_clause([Lit::pos(Var(0)), Lit::pos(Var(1))]);
        solver.add_clause([Lit::pos(Var(1)), Lit::pos(Var(2))]);

        let mut enumerator = AllSatEnumerator::new(EnumerationConfig::all().maximal());
        let result = enumerator.enumerate(&mut solver, 3);

        let mut found = HashSet::new();
        for model in result.models() {
            let bits = model_to_bits(model);
            assert!(
                expected_maximal.contains(&bits),
                "reported model {bits:03b} is not an inclusion-maximal model of the formula"
            );
            found.insert(bits);
        }
        assert_eq!(
            found, expected_maximal,
            "maximal-model enumeration should find every inclusion-maximal model"
        );
    }

    // Regression test for the `block_positive_only` item: outside the
    // `minimal_models` combination, `block_positive_only` must never cause
    // fewer than the true number of distinct models to be reported while
    // still claiming `EnumerationResult::Complete`.
    #[test]
    fn test_block_positive_only_without_minimal_does_not_under_enumerate() {
        let mut plain_solver = Solver::new();
        plain_solver.add_clause([Lit::pos(Var(0)), Lit::pos(Var(1))]);
        let full = AllSatEnumerator::enumerate_all(&mut plain_solver, 2);
        assert_eq!(full.len(), 3, "sanity: x0 ∨ x1 has exactly 3 models");

        let mut solver = Solver::new();
        solver.add_clause([Lit::pos(Var(0)), Lit::pos(Var(1))]);

        let mut config = EnumerationConfig::all();
        config.block_positive_only = true;
        let mut enumerator = AllSatEnumerator::new(config);
        let result = enumerator.enumerate(&mut solver, 2);

        assert!(result.is_complete());
        assert_eq!(
            result.count(),
            3,
            "block_positive_only without minimal_models must not under-enumerate"
        );
    }

    // The `block_positive_only` dominance-pruning optimization is sound when
    // paired with `minimal_models`: it should still find every inclusion
    // minimal model (no fewer, no more) since supersets of a found minimal
    // model can never themselves be minimal.
    #[test]
    fn test_block_positive_only_with_minimal_is_still_complete() {
        let clauses = vec![vec![(0, true), (1, true)], vec![(1, true), (2, true)]];
        let sat = brute_force_sat_assignments(&clauses);
        let expected_minimal = inclusion_minimal(&sat);

        let mut solver = Solver::new();
        solver.add_clause([Lit::pos(Var(0)), Lit::pos(Var(1))]);
        solver.add_clause([Lit::pos(Var(1)), Lit::pos(Var(2))]);

        let mut config = EnumerationConfig::all().minimal();
        config.block_positive_only = true;
        let mut enumerator = AllSatEnumerator::new(config);
        let result = enumerator.enumerate(&mut solver, 3);

        let found: HashSet<u8> = result.models().iter().map(model_to_bits).collect();
        assert_eq!(found, expected_minimal);
    }
}
