//! MaxSMT solver.
//!
//! This module implements MaxSMT (Maximum Satisfiability Modulo Theories),
//! which extends MaxSAT to SMT formulas. It handles:
//! - Soft constraints with weights over SMT formulas
//! - Integration with theory solvers
//! - Incremental optimization
//!
//! Reference: Z3's `opt/maxsmt.cpp`

use crate::maxsat::{MaxSatConfig, MaxSatError, MaxSatResult, Weight};
use nixie_core::ast::{TermId, TermKind, TermManager};
use nixie_solver::{Solver, SolverResult};
use num_bigint::BigInt;
use rustc_hash::FxHashMap;
use smallvec::SmallVec;
use thiserror::Error;

/// Compute the greatest common divisor of two `BigInt`s (Euclidean algorithm).
fn bigint_gcd(a: &BigInt, b: &BigInt) -> BigInt {
    let zero = BigInt::from(0);
    let (mut a, mut b) = (a.clone(), b.clone());
    while b != zero {
        let r = &a % &b;
        a = b;
        b = r;
    }
    a
}

/// Compute the least common multiple of two positive `BigInt`s.
fn bigint_lcm(a: &BigInt, b: &BigInt) -> BigInt {
    let zero = BigInt::from(0);
    if *a == zero || *b == zero {
        return zero;
    }
    (a / bigint_gcd(a, b)) * b
}

/// Convert a soft-constraint [`Weight`] to an exact integer cost scaled by
/// `scale` (a common multiple of every rational weight's denominator, so
/// rational weights are represented exactly rather than coerced).
fn scaled_weight_int(weight: &Weight, scale: &BigInt) -> BigInt {
    match weight {
        Weight::Int(n) => n * scale,
        Weight::Rational(r) => {
            let factor = scale / r.denom();
            r.numer() * factor
        }
        // Effectively-hard: dominate every finite soft weight.
        Weight::Infinite => BigInt::from(i64::MAX / 2) * scale,
    }
}

/// Errors that can occur during MaxSMT solving
#[derive(Error, Debug)]
pub enum MaxSmtError {
    /// Hard constraints unsatisfiable
    #[error("hard constraints unsatisfiable")]
    Unsatisfiable,
    /// MaxSAT level error
    #[error("maxsat error: {0}")]
    MaxSat(#[from] MaxSatError),
    /// Theory conflict
    #[error("theory conflict")]
    TheoryConflict,
    /// Resource limit
    #[error("resource limit")]
    ResourceLimit,
    /// [`MaxSmtSolver::solve`] was called without a term manager.
    ///
    /// MaxSMT optimization needs the [`TermManager`] that owns the constraint
    /// terms to build the selector encoding and drive the SMT solver. Use
    /// [`MaxSmtSolver::solve_with`] instead.
    #[error("MaxSMT requires a term manager: call solve_with(&mut terms)")]
    RequiresTermManager,
}

/// Result of MaxSMT solving
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum MaxSmtResult {
    /// Optimal solution found
    Optimal,
    /// Solution found but optimality not proven
    Satisfiable,
    /// No solution exists
    Unsatisfiable,
    /// Could not determine
    Unknown,
}

impl From<MaxSatResult> for MaxSmtResult {
    fn from(r: MaxSatResult) -> Self {
        match r {
            MaxSatResult::Optimal => MaxSmtResult::Optimal,
            MaxSatResult::Satisfiable => MaxSmtResult::Satisfiable,
            MaxSatResult::Unsatisfiable => MaxSmtResult::Unsatisfiable,
            MaxSatResult::Unknown => MaxSmtResult::Unknown,
        }
    }
}

/// Unique identifier for a soft SMT constraint
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct SoftSmtId(pub u32);

impl SoftSmtId {
    /// Create a new soft SMT ID
    #[must_use]
    pub const fn new(id: u32) -> Self {
        Self(id)
    }

    /// Get the raw ID value
    #[must_use]
    pub const fn raw(self) -> u32 {
        self.0
    }
}

/// A soft SMT constraint
#[derive(Debug, Clone)]
pub struct SoftSmtConstraint {
    /// Unique identifier
    pub id: SoftSmtId,
    /// The term representing the constraint
    pub term: TermId,
    /// Weight of this soft constraint
    pub weight: Weight,
    /// Whether this constraint is currently satisfied
    satisfied: bool,
}

impl SoftSmtConstraint {
    /// Create a new soft SMT constraint
    pub fn new(id: SoftSmtId, term: TermId, weight: Weight) -> Self {
        Self {
            id,
            term,
            weight,
            satisfied: false,
        }
    }

    /// Check if satisfied
    pub fn is_satisfied(&self) -> bool {
        self.satisfied
    }

    /// Set satisfaction status
    pub fn set_satisfied(&mut self, satisfied: bool) {
        self.satisfied = satisfied;
    }
}

/// Configuration for MaxSMT solver
#[derive(Debug, Clone)]
pub struct MaxSmtConfig {
    /// Underlying MaxSAT configuration
    pub maxsat: MaxSatConfig,
    /// Enable theory-aware optimization
    pub theory_aware: bool,
    /// Maximum iterations
    pub max_iterations: u32,
}

impl Default for MaxSmtConfig {
    fn default() -> Self {
        Self {
            maxsat: MaxSatConfig::default(),
            theory_aware: true,
            max_iterations: 100000,
        }
    }
}

/// Statistics from MaxSMT solving
#[derive(Debug, Clone, Default)]
pub struct MaxSmtStats {
    /// Number of SMT solver calls
    pub smt_calls: u32,
    /// Number of cores extracted
    pub cores_extracted: u32,
    /// Number of theory propagations
    pub theory_propagations: u32,
}

/// MaxSMT solver
///
/// This solver handles optimization of soft SMT constraints.
/// It uses a core-guided approach similar to MaxSAT but
/// integrates with theory solvers for SMT-level reasoning.
#[derive(Debug)]
pub struct MaxSmtSolver {
    /// Hard constraints (must be satisfied)
    hard_constraints: Vec<TermId>,
    /// Soft constraints with weights
    soft_constraints: Vec<SoftSmtConstraint>,
    /// Next soft ID
    next_soft_id: u32,
    /// Configuration
    #[allow(dead_code)]
    config: MaxSmtConfig,
    /// Statistics
    stats: MaxSmtStats,
    /// Current lower bound
    lower_bound: Weight,
    /// Current upper bound
    upper_bound: Weight,
    /// Term to Boolean variable mapping (for SAT encoding)
    term_to_var: FxHashMap<TermId, u32>,
    /// Next Boolean variable
    next_var: u32,
    /// Soft constraint groups (for stratified solving)
    groups: FxHashMap<String, Vec<SoftSmtId>>,
}

impl Default for MaxSmtSolver {
    fn default() -> Self {
        Self::new()
    }
}

impl MaxSmtSolver {
    /// Create a new MaxSMT solver
    pub fn new() -> Self {
        Self::with_config(MaxSmtConfig::default())
    }

    /// Create a new MaxSMT solver with configuration
    pub fn with_config(config: MaxSmtConfig) -> Self {
        Self {
            hard_constraints: Vec::new(),
            soft_constraints: Vec::new(),
            next_soft_id: 0,
            config,
            stats: MaxSmtStats::default(),
            lower_bound: Weight::zero(),
            upper_bound: Weight::Infinite,
            term_to_var: FxHashMap::default(),
            next_var: 0,
            groups: FxHashMap::default(),
        }
    }

    /// Add a hard constraint
    pub fn add_hard(&mut self, term: TermId) {
        self.hard_constraints.push(term);
    }

    /// Add a soft constraint with unit weight
    pub fn add_soft(&mut self, term: TermId) -> SoftSmtId {
        self.add_soft_weighted(term, Weight::one())
    }

    /// Add a soft constraint with weight
    pub fn add_soft_weighted(&mut self, term: TermId, weight: Weight) -> SoftSmtId {
        let id = SoftSmtId(self.next_soft_id);
        self.next_soft_id += 1;

        let constraint = SoftSmtConstraint::new(id, term, weight.clone());
        self.soft_constraints.push(constraint);

        // Update upper bound
        self.upper_bound = self.upper_bound.add(&weight);

        id
    }

    /// Add a soft constraint to a group
    pub fn add_soft_to_group(&mut self, term: TermId, weight: Weight, group: &str) -> SoftSmtId {
        let id = self.add_soft_weighted(term, weight);
        self.groups.entry(group.to_string()).or_default().push(id);
        id
    }

    /// Get the number of hard constraints
    pub fn num_hard(&self) -> usize {
        self.hard_constraints.len()
    }

    /// Get the number of soft constraints
    pub fn num_soft(&self) -> usize {
        self.soft_constraints.len()
    }

    /// Get the lower bound
    pub fn lower_bound(&self) -> &Weight {
        &self.lower_bound
    }

    /// Get the upper bound
    pub fn upper_bound(&self) -> &Weight {
        &self.upper_bound
    }

    /// Get statistics
    pub fn stats(&self) -> &MaxSmtStats {
        &self.stats
    }

    /// Get the cost (sum of weights of unsatisfied soft constraints)
    pub fn cost(&self) -> Weight {
        self.soft_constraints
            .iter()
            .filter(|c| !c.is_satisfied())
            .fold(Weight::zero(), |acc, c| acc.add(&c.weight))
    }

    /// Allocate a Boolean variable for a term
    #[allow(dead_code)]
    fn allocate_var(&mut self, term: TermId) -> u32 {
        if let Some(&var) = self.term_to_var.get(&term) {
            return var;
        }
        let var = self.next_var;
        self.next_var += 1;
        self.term_to_var.insert(term, var);
        var
    }

    /// Solve the MaxSMT problem.
    ///
    /// MaxSMT optimization cannot proceed without the [`TermManager`] that owns
    /// the constraint terms – it is needed to build the selector-variable
    /// encoding and invoke the SMT solver. Historically this method was a stub
    /// that always returned `Unknown` regardless of the input, silently
    /// mis-reporting every instance as unsolved. It now fails honestly; use
    /// [`Self::solve_with`] and pass the owning term manager instead.
    pub fn solve(&mut self) -> Result<MaxSmtResult, MaxSmtError> {
        Err(MaxSmtError::RequiresTermManager)
    }

    /// Solve the MaxSMT problem against the [`TermManager`] that owns the
    /// constraint terms.
    ///
    /// Uses a selector-variable encoding: each soft constraint `t_i` with
    /// weight `w_i` gets a fresh boolean selector `b_i` and the hard
    /// implication `b_i → t_i`, plus an integer cost variable `cost_i` that is
    /// `0` when `b_i` holds and `w_i` otherwise. Binary search over the total
    /// cost budget then finds the minimum-cost (maximum-satisfaction)
    /// assignment. Rational weights are scaled to exact integers, so mixed
    /// integer/rational weights are handled without coercion.
    ///
    /// On success the per-constraint satisfaction flags and the lower/upper
    /// cost bounds are updated so [`Self::cost`], [`Self::satisfied`], and
    /// [`Self::unsatisfied`] report the optimal assignment.
    pub fn solve_with(&mut self, terms: &mut TermManager) -> Result<MaxSmtResult, MaxSmtError> {
        let int_sort = terms.sorts.int_sort;
        let bool_sort = terms.sorts.bool_sort;

        // Trivial case: no soft constraints – just check hard feasibility.
        if self.soft_constraints.is_empty() {
            let mut solver = Solver::new();
            for &h in &self.hard_constraints {
                solver.assert(h, terms);
            }
            self.stats.smt_calls += 1;
            return Ok(match solver.check(terms) {
                SolverResult::Sat => MaxSmtResult::Optimal,
                SolverResult::Unsat => MaxSmtResult::Unsatisfiable,
                SolverResult::Unknown => MaxSmtResult::Unknown,
            });
        }

        // Scale so every (possibly rational) weight is an exact integer.
        let mut weight_scale = BigInt::from(1);
        for sc in &self.soft_constraints {
            if let Weight::Rational(r) = &sc.weight {
                weight_scale = bigint_lcm(&weight_scale, r.denom());
            }
        }

        let total_weight: BigInt = self
            .soft_constraints
            .iter()
            .map(|sc| scaled_weight_int(&sc.weight, &weight_scale))
            .fold(BigInt::from(0), |acc, w| acc + w);

        // Build selectors, implications, and cost definitions.
        let num_soft = self.soft_constraints.len();
        let mut sel_vars: Vec<TermId> = Vec::with_capacity(num_soft);
        let mut cost_vars: Vec<TermId> = Vec::with_capacity(num_soft);
        let mut selector_implications: Vec<TermId> = Vec::with_capacity(num_soft);
        let mut cost_defs: Vec<TermId> = Vec::with_capacity(num_soft * 2);

        for sc in &self.soft_constraints {
            let sel_name = format!("__maxsmt_sel_{}", sc.id.0);
            let cost_name = format!("__maxsmt_cost_{}", sc.id.0);
            let sel = terms.mk_var(&sel_name, bool_sort);
            let cost_var = terms.mk_var(&cost_name, int_sort);
            sel_vars.push(sel);
            cost_vars.push(cost_var);

            // b_i → t_i
            selector_implications.push(terms.mk_implies(sel, sc.term));

            // cost_i = ite(b_i, 0, w_i), encoded as two implications.
            let weight_int = scaled_weight_int(&sc.weight, &weight_scale);
            let w_term = terms.mk_int(weight_int);
            let zero = terms.mk_int(0i64);
            let not_sel = terms.mk_not(sel);
            let cost_eq_zero = terms.mk_eq(cost_var, zero);
            let cost_eq_w = terms.mk_eq(cost_var, w_term);
            cost_defs.push(terms.mk_implies(sel, cost_eq_zero));
            cost_defs.push(terms.mk_implies(not_sel, cost_eq_w));
        }

        let cost_sum = terms.mk_add(cost_vars.iter().copied());

        // Feasibility of the hard part.
        let feasible = {
            let mut solver = Solver::new();
            for &h in &self.hard_constraints {
                solver.assert(h, terms);
            }
            for &imp in &selector_implications {
                solver.assert(imp, terms);
            }
            for &cd in &cost_defs {
                solver.assert(cd, terms);
            }
            self.stats.smt_calls += 1;
            solver.check(terms) == SolverResult::Sat
        };
        if !feasible {
            return Ok(MaxSmtResult::Unsatisfiable);
        }

        // Binary search for the minimum feasible cost budget.
        let mut lo = BigInt::from(0);
        let mut hi = total_weight.clone();
        let mut search_incomplete = false;

        while lo < hi {
            let mid: BigInt = (lo.clone() + hi.clone()) / 2i32;
            let bound_term = terms.mk_int(mid.clone());
            let cost_le_mid = terms.mk_le(cost_sum, bound_term);

            let mut solver = Solver::new();
            for &h in &self.hard_constraints {
                solver.assert(h, terms);
            }
            for &imp in &selector_implications {
                solver.assert(imp, terms);
            }
            for &cd in &cost_defs {
                solver.assert(cd, terms);
            }
            solver.assert(cost_le_mid, terms);

            self.stats.smt_calls += 1;
            match solver.check(terms) {
                SolverResult::Sat => hi = mid,
                SolverResult::Unsat => lo = mid + BigInt::from(1),
                SolverResult::Unknown => {
                    search_incomplete = true;
                    break;
                }
            }
        }

        // Final solve at `lo` to read the optimal model and per-constraint
        // satisfaction from the selector variables.
        let mut sel_truth = vec![false; sel_vars.len()];
        let mut have_model = false;
        {
            let bound_term = terms.mk_int(lo.clone());
            let cost_le_lo = terms.mk_le(cost_sum, bound_term);
            let mut solver = Solver::new();
            for &h in &self.hard_constraints {
                solver.assert(h, terms);
            }
            for &imp in &selector_implications {
                solver.assert(imp, terms);
            }
            for &cd in &cost_defs {
                solver.assert(cd, terms);
            }
            solver.assert(cost_le_lo, terms);
            self.stats.smt_calls += 1;
            match solver.check(terms) {
                SolverResult::Sat => {
                    if solver.model().is_some() {
                        for (i, &sel) in sel_vars.iter().enumerate() {
                            // Re-borrow the model each step: `eval` needs
                            // `&mut terms`, which the borrow checker keeps
                            // disjoint from the immutable model borrow.
                            if let Some(model) = solver.model() {
                                let v = model.eval(sel, terms);
                                sel_truth[i] =
                                    matches!(terms.get(v).map(|t| &t.kind), Some(TermKind::True));
                            }
                        }
                        have_model = true;
                    }
                }
                SolverResult::Unsat | SolverResult::Unknown => search_incomplete = true,
            }
        }

        if !have_model {
            return Ok(MaxSmtResult::Unknown);
        }

        // Record per-constraint satisfaction from the selectors.
        for (i, &sat) in sel_truth.iter().enumerate() {
            self.soft_constraints[i].set_satisfied(sat);
        }

        // The exact optimal cost, in the original (unscaled) weight domain.
        let opt_cost = self.cost();
        self.lower_bound = opt_cost.clone();
        self.upper_bound = opt_cost;

        if search_incomplete {
            Ok(MaxSmtResult::Satisfiable)
        } else {
            Ok(MaxSmtResult::Optimal)
        }
    }

    /// Get satisfied soft constraint IDs
    pub fn satisfied(&self) -> impl Iterator<Item = SoftSmtId> + '_ {
        self.soft_constraints
            .iter()
            .filter(|c| c.is_satisfied())
            .map(|c| c.id)
    }

    /// Get unsatisfied soft constraint IDs
    pub fn unsatisfied(&self) -> impl Iterator<Item = SoftSmtId> + '_ {
        self.soft_constraints
            .iter()
            .filter(|c| !c.is_satisfied())
            .map(|c| c.id)
    }

    /// Get the weight of a soft constraint
    pub fn weight(&self, id: SoftSmtId) -> Option<&Weight> {
        self.soft_constraints.get(id.0 as usize).map(|c| &c.weight)
    }

    /// Check if a soft constraint is satisfied
    pub fn is_satisfied(&self, id: SoftSmtId) -> bool {
        self.soft_constraints
            .get(id.0 as usize)
            .is_some_and(|c| c.is_satisfied())
    }

    /// Reset the solver
    pub fn reset(&mut self) {
        self.hard_constraints.clear();
        self.soft_constraints.clear();
        self.next_soft_id = 0;
        self.stats = MaxSmtStats::default();
        self.lower_bound = Weight::zero();
        self.upper_bound = Weight::Infinite;
        self.term_to_var.clear();
        self.next_var = 0;
        self.groups.clear();
    }
}

/// Theory-aware core extraction
///
/// Represents a core extracted from an unsatisfiable SMT query,
/// including both Boolean and theory-level information.
#[derive(Debug, Clone)]
pub struct SmtCore {
    /// Soft constraint IDs in this core
    pub soft_ids: SmallVec<[SoftSmtId; 8]>,
    /// Theory lemmas involved in the conflict
    pub theory_lemmas: Vec<TermId>,
    /// Minimum weight in the core
    pub min_weight: Weight,
}

impl SmtCore {
    /// Create a new SMT core
    pub fn new(soft_ids: impl IntoIterator<Item = SoftSmtId>) -> Self {
        let ids: SmallVec<[SoftSmtId; 8]> = soft_ids.into_iter().collect();
        Self {
            soft_ids: ids,
            theory_lemmas: Vec::new(),
            min_weight: Weight::Infinite,
        }
    }

    /// Get the size of this core
    pub fn size(&self) -> usize {
        self.soft_ids.len()
    }

    /// Check if this core is empty
    pub fn is_empty(&self) -> bool {
        self.soft_ids.is_empty()
    }

    /// Add a theory lemma
    pub fn add_lemma(&mut self, lemma: TermId) {
        self.theory_lemmas.push(lemma);
    }

    /// Set the minimum weight
    pub fn set_min_weight(&mut self, weight: Weight) {
        self.min_weight = weight;
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_soft_smt_id() {
        let id = SoftSmtId::new(42);
        assert_eq!(id.raw(), 42);
    }

    #[test]
    fn test_soft_constraint() {
        let id = SoftSmtId::new(0);
        let term = TermId::from(1);
        let mut constraint = SoftSmtConstraint::new(id, term, Weight::from(5));

        assert_eq!(constraint.id, id);
        assert_eq!(constraint.term, term);
        assert_eq!(constraint.weight, Weight::from(5));
        assert!(!constraint.is_satisfied());

        constraint.set_satisfied(true);
        assert!(constraint.is_satisfied());
    }

    #[test]
    fn test_maxsmt_solver_new() {
        let solver = MaxSmtSolver::new();
        assert_eq!(solver.num_hard(), 0);
        assert_eq!(solver.num_soft(), 0);
    }

    #[test]
    fn test_add_hard() {
        let mut solver = MaxSmtSolver::new();
        solver.add_hard(TermId::from(1));
        solver.add_hard(TermId::from(2));
        assert_eq!(solver.num_hard(), 2);
    }

    #[test]
    fn test_add_soft() {
        let mut solver = MaxSmtSolver::new();
        let id1 = solver.add_soft(TermId::from(1));
        let id2 = solver.add_soft_weighted(TermId::from(2), Weight::from(5));

        assert_eq!(id1.raw(), 0);
        assert_eq!(id2.raw(), 1);
        assert_eq!(solver.num_soft(), 2);

        assert_eq!(solver.weight(id1), Some(&Weight::one()));
        assert_eq!(solver.weight(id2), Some(&Weight::from(5)));
    }

    #[test]
    fn test_groups() {
        let mut solver = MaxSmtSolver::new();
        solver.add_soft_to_group(TermId::from(1), Weight::one(), "g1");
        solver.add_soft_to_group(TermId::from(2), Weight::one(), "g1");
        solver.add_soft_to_group(TermId::from(3), Weight::one(), "g2");

        assert_eq!(solver.groups.get("g1").map(|v| v.len()), Some(2));
        assert_eq!(solver.groups.get("g2").map(|v| v.len()), Some(1));
    }

    #[test]
    fn test_cost() {
        let mut solver = MaxSmtSolver::new();
        solver.add_soft_weighted(TermId::from(1), Weight::from(3));
        solver.add_soft_weighted(TermId::from(2), Weight::from(5));

        // All unsatisfied initially
        assert_eq!(solver.cost(), Weight::from(8));

        // Mark one as satisfied
        solver.soft_constraints[0].set_satisfied(true);
        assert_eq!(solver.cost(), Weight::from(5));

        // Mark both as satisfied
        solver.soft_constraints[1].set_satisfied(true);
        assert_eq!(solver.cost(), Weight::zero());
    }

    #[test]
    fn test_reset() {
        let mut solver = MaxSmtSolver::new();
        solver.add_hard(TermId::from(1));
        solver.add_soft(TermId::from(2));

        solver.reset();

        assert_eq!(solver.num_hard(), 0);
        assert_eq!(solver.num_soft(), 0);
    }

    #[test]
    fn test_smt_core() {
        let mut core = SmtCore::new([SoftSmtId(0), SoftSmtId(1), SoftSmtId(2)]);

        assert_eq!(core.size(), 3);
        assert!(!core.is_empty());

        core.add_lemma(TermId::from(10));
        core.set_min_weight(Weight::from(5));

        assert_eq!(core.theory_lemmas.len(), 1);
        assert_eq!(core.min_weight, Weight::from(5));
    }

    #[test]
    fn test_maxsmt_result_from_maxsat() {
        assert_eq!(
            MaxSmtResult::from(MaxSatResult::Optimal),
            MaxSmtResult::Optimal
        );
        assert_eq!(
            MaxSmtResult::from(MaxSatResult::Satisfiable),
            MaxSmtResult::Satisfiable
        );
        assert_eq!(
            MaxSmtResult::from(MaxSatResult::Unsatisfiable),
            MaxSmtResult::Unsatisfiable
        );
        assert_eq!(
            MaxSmtResult::from(MaxSatResult::Unknown),
            MaxSmtResult::Unknown
        );
    }
}
