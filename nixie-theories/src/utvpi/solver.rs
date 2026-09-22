//! UTVPI Theory Solver
//!
//! Implements satisfiability checking for UTVPI constraints using
//! Bellman-Ford algorithm on the doubled graph.

use super::graph::{DoubledGraph, DoubledNode, Sign, UtConstraint};
use crate::arithmetic::BigDeltaRational;
#[allow(unused_imports)]
use crate::prelude::*;
use nixie_core::ast::TermId;
use num_rational::{BigRational, Rational64};
use num_traits::{One, Signed, ToPrimitive, Zero};

/// Configuration for UTVPI solver
#[derive(Debug, Clone)]
pub struct UtvpiConfig {
    /// Use SPFA instead of standard Bellman-Ford
    pub use_spfa: bool,
    /// Enable propagation of tight bounds
    pub propagate_bounds: bool,
    /// Enable lemma learning from conflicts
    pub learn_lemmas: bool,
}

impl Default for UtvpiConfig {
    fn default() -> Self {
        Self {
            use_spfa: true,
            propagate_bounds: true,
            learn_lemmas: true,
        }
    }
}

/// Statistics for UTVPI solver
#[derive(Debug, Clone, Default)]
pub struct UtvpiStats {
    /// Number of constraints added
    pub constraints_added: u64,
    /// Number of consistency checks
    pub checks: u64,
    /// Number of conflicts detected
    pub conflicts: u64,
    /// Number of propagations
    pub propagations: u64,
    /// Number of push operations
    pub pushes: u64,
    /// Number of pop operations
    pub pops: u64,
}

/// Result of UTVPI solver operations
#[derive(Debug, Clone)]
pub enum UtvpiResult {
    /// Satisfiable, no conflicts
    Ok,
    /// Conflict detected, returns constraint indices forming the conflict
    Conflict(Vec<usize>),
    /// Unknown (e.g., resource limit)
    Unknown,
}

impl PartialEq for UtvpiResult {
    fn eq(&self, other: &Self) -> bool {
        match (self, other) {
            (UtvpiResult::Ok, UtvpiResult::Ok) => true,
            (UtvpiResult::Unknown, UtvpiResult::Unknown) => true,
            (UtvpiResult::Conflict(a), UtvpiResult::Conflict(b)) => a == b,
            _ => false,
        }
    }
}

/// UTVPI Theory Solver
#[derive(Debug)]
pub struct UtvpiSolver {
    /// Configuration
    config: UtvpiConfig,
    /// Doubled graph
    graph: DoubledGraph,
    /// Distances from source
    distances: Vec<BigDeltaRational>,
    /// Independently validated exact variable assignments.
    model: Vec<BigRational>,
    /// Are distances valid?
    distances_valid: bool,
    /// Statistics
    stats: UtvpiStats,
}

impl UtvpiSolver {
    /// Create a new UTVPI solver
    pub fn new(is_integer: bool) -> Self {
        Self {
            config: UtvpiConfig::default(),
            graph: DoubledGraph::new(is_integer),
            distances: Vec::new(),
            model: Vec::new(),
            distances_valid: false,
            stats: UtvpiStats::default(),
        }
    }

    /// Create with custom configuration
    pub fn with_config(is_integer: bool, config: UtvpiConfig) -> Self {
        Self {
            config,
            graph: DoubledGraph::new(is_integer),
            distances: Vec::new(),
            model: Vec::new(),
            distances_valid: false,
            stats: UtvpiStats::default(),
        }
    }

    /// Get or create a variable for a term
    pub fn get_or_create_var(&mut self, term: TermId) -> u32 {
        self.distances_valid = false;
        self.graph.get_or_create_var(term)
    }

    /// Add a UTVPI constraint
    pub fn add_constraint(&mut self, constraint: UtConstraint) -> usize {
        self.stats.constraints_added += 1;
        self.distances_valid = false;
        self.graph.add_constraint(constraint)
    }

    /// Add constraint: x - y ≤ c
    pub fn add_diff(&mut self, x: u32, y: u32, bound: Rational64, origin: TermId) -> usize {
        self.add_constraint(UtConstraint::diff(x, y, bound, origin))
    }

    /// Add constraint: x + y ≤ c
    pub fn add_sum(&mut self, x: u32, y: u32, bound: Rational64, origin: TermId) -> usize {
        self.add_constraint(UtConstraint::sum(x, y, bound, origin))
    }

    /// Add constraint: -x - y ≤ c
    pub fn add_neg_sum(&mut self, x: u32, y: u32, bound: Rational64, origin: TermId) -> usize {
        self.add_constraint(UtConstraint::neg_sum(x, y, bound, origin))
    }

    /// Add constraint: x ≤ c
    pub fn add_upper(&mut self, x: u32, bound: Rational64, origin: TermId) -> usize {
        self.add_constraint(UtConstraint::upper(x, bound, origin))
    }

    /// Add constraint: -x ≤ c (i.e., x ≥ -c)
    pub fn add_lower(&mut self, x: u32, bound: Rational64, origin: TermId) -> usize {
        self.add_constraint(UtConstraint::lower(x, bound, origin))
    }

    /// Add general UTVPI constraint: ax + by ≤ c
    pub fn add_general(
        &mut self,
        x: u32,
        a: Sign,
        y: u32,
        b: Sign,
        bound: Rational64,
        origin: TermId,
    ) -> usize {
        self.add_constraint(UtConstraint::new(x, a, y, b, bound, origin))
    }

    /// Check consistency, including integer parity and a concrete witness.
    pub fn check(&mut self) -> UtvpiResult {
        self.stats.checks += 1;
        self.distances_valid = false;
        self.model.clear();
        let vars = self.graph.num_vars();
        if self
            .graph
            .active_constraints()
            .any(|(_, c)| (c.a != Sign::Zero && c.x >= vars) || (c.b != Sign::Zero && c.y >= vars))
        {
            return UtvpiResult::Unknown;
        }
        let consistent = if self.config.use_spfa {
            self.run_spfa()
        } else {
            self.run_bellman_ford()
        };
        if !consistent {
            return self.conflict();
        }
        if self.graph.is_integer() {
            match self.enforce_parity() {
                UtvpiResult::Ok => {}
                UtvpiResult::Conflict(_) => return self.conflict(),
                UtvpiResult::Unknown => return UtvpiResult::Unknown,
            }
        }
        if !self.build_model() {
            self.model.clear();
            return UtvpiResult::Unknown;
        }
        self.distances_valid = true;
        UtvpiResult::Ok
    }

    fn conflict(&mut self) -> UtvpiResult {
        self.stats.conflicts += 1;
        // All active constraints are a sound (possibly nonminimal) core. The
        // old reconstruction guessed a predecessor from a constraint ID even
        // though each binary constraint has TWO edges, yielding invalid cores.
        UtvpiResult::Conflict(self.graph.active_constraints().map(|(i, _)| i).collect())
    }

    fn node_index(&self, node: DoubledNode) -> usize {
        if node.is_source() {
            self.graph.num_nodes() as usize
        } else {
            2 * node.var_id as usize + usize::from(!node.positive)
        }
    }

    fn plus(a: &BigDeltaRational, b: &BigDeltaRational) -> BigDeltaRational {
        BigDeltaRational {
            real: &a.real + &b.real,
            delta: &a.delta + &b.delta,
        }
    }

    /// Multi-source Bellman–Ford over exact infinitesimal weights. An update
    /// on pass |V| certifies a negative cycle; no guessed cycle is needed.
    fn run_bellman_ford(&mut self) -> bool {
        let n = self.graph.num_nodes() as usize + 1;
        self.distances = vec![BigDeltaRational::zero(); n];
        for pass in 0..n {
            let mut changed = false;
            for edge in self.graph.all_edges() {
                let from = self.node_index(edge.from);
                let to = self.node_index(edge.to);
                let next = Self::plus(&self.distances[from], &edge.weight);
                if next < self.distances[to] {
                    self.distances[to] = next;
                    changed = true;
                }
            }
            if !changed {
                return true;
            }
            if pass + 1 == n {
                return false;
            }
        }
        true
    }

    /// Queue scheduling is only an optimization. Too many enqueues trigger
    /// Bellman–Ford, never a conflict inferred from an enqueue count alone.
    fn run_spfa(&mut self) -> bool {
        let n = self.graph.num_nodes() as usize + 1;
        self.distances = vec![BigDeltaRational::zero(); n];
        let nodes: Vec<_> = self
            .graph
            .all_nodes()
            .chain(core::iter::once(DoubledNode::SOURCE))
            .collect();
        let mut queue: VecDeque<_> = nodes.into_iter().collect();
        let mut queued = vec![true; n];
        let mut counts = vec![1usize; n];
        let mut fallback = false;
        'search: while let Some(node) = queue.pop_front() {
            let from = self.node_index(node);
            queued[from] = false;
            for edge in self.graph.get_edges(node) {
                let to = self.node_index(edge.to);
                let next = Self::plus(&self.distances[from], &edge.weight);
                if next < self.distances[to] {
                    self.distances[to] = next;
                    if !queued[to] {
                        counts[to] += 1;
                        if counts[to] > n {
                            fallback = true;
                            break 'search;
                        }
                        queued[to] = true;
                        queue.push_back(edge.to);
                    }
                }
            }
        }
        if fallback {
            self.run_bellman_ford()
        } else {
            true
        }
    }

    /// Nodes reachable along tight edges. This is an explicit heap walk.
    fn tight_successors(&self, start: DoubledNode) -> Vec<bool> {
        let mut seen = vec![false; self.distances.len()];
        let mut todo = vec![start];
        seen[self.node_index(start)] = true;
        while let Some(node) = todo.pop() {
            let from = self.node_index(node);
            for edge in self.graph.get_edges(node) {
                let to = self.node_index(edge.to);
                if !seen[to]
                    && self.distances[to] == Self::plus(&self.distances[from], &edge.weight)
                {
                    seen[to] = true;
                    todo.push(edge.to);
                }
            }
        }
        seen
    }

    /// Z3 theory_utvpi::check_z_consistency/enforce_parity: opposite nodes
    /// with odd potential difference cannot be in the same tight SCC. Otherwise
    /// decrement a tight successor closure excluding the complementary node.
    fn enforce_parity(&mut self) -> UtvpiResult {
        let n = self.graph.num_vars();
        // Deterministic resource bound; reaching it is never a proof of UNSAT.
        let budget = (n as usize + 1)
            .saturating_mul(n as usize + 1)
            .saturating_mul(16);
        for _ in 0..budget {
            let odd = (0..n).find(|&v| {
                let difference =
                    &self.distances[2 * v as usize].real - &self.distances[2 * v as usize + 1].real;
                !(difference / BigRational::from_integer(2.into())).is_integer()
            });
            let Some(v) = odd else {
                return UtvpiResult::Ok;
            };
            let pos = DoubledNode::positive(v);
            let neg = DoubledNode::negative(v);
            let mut closure = self.tight_successors(pos);
            if closure[self.node_index(neg)] {
                closure = self.tight_successors(neg);
                if closure[self.node_index(pos)] {
                    return UtvpiResult::Conflict(Vec::new());
                }
            }
            for (i, reached) in closure.into_iter().enumerate() {
                if reached {
                    self.distances[i].real -= BigRational::one();
                }
            }
        }
        UtvpiResult::Unknown
    }

    fn build_model(&mut self) -> bool {
        let two = BigRational::from_integer(2.into());
        let mut epsilon = BigRational::new(1.into(), 4.into());
        // Choose one positive rational infinitesimal that preserves EVERY
        // edge, as in Z3 theory_utvpi::compute_delta.
        for edge in self.graph.all_edges() {
            let from = &self.distances[self.node_index(edge.from)];
            let to = &self.distances[self.node_index(edge.to)];
            let real = &to.real - &from.real - &edge.weight.real;
            let delta = &to.delta - &from.delta - &edge.weight.delta;
            if real.is_positive() || (real.is_zero() && delta.is_positive()) {
                return false;
            }
            if delta.is_positive() {
                epsilon = epsilon.min(-real / (&two * delta));
            }
        }
        self.model = (0..self.graph.num_vars() as usize)
            .map(|v| {
                let pos = &self.distances[2 * v];
                let neg = &self.distances[2 * v + 1];
                (&pos.real - &neg.real + (&pos.delta - &neg.delta) * &epsilon) / &two
            })
            .collect();
        if self.graph.is_integer() && self.model.iter().any(|v| !v.is_integer()) {
            return false;
        }
        // Independently evaluate ORIGINAL constraints, not just their encoding.
        self.graph.active_constraints().all(|(_, c)| {
            let value = |var: u32, sign: Sign| match sign {
                Sign::Zero => BigRational::zero(),
                Sign::Positive => self.model[var as usize].clone(),
                Sign::Negative => -self.model[var as usize].clone(),
            };
            let lhs = value(c.x, c.a) + value(c.y, c.b);
            let rhs = BigRational::new((*c.bound.numer()).into(), (*c.bound.denom()).into());
            if c.strict { lhs < rhs } else { lhs <= rhs }
        })
    }

    /// Push a new decision level
    pub fn push(&mut self) {
        self.distances_valid = false;
        self.stats.pushes += 1;
        self.graph.push();
    }

    /// Pop to a previous level
    pub fn pop(&mut self, levels: u32) {
        if levels > 0 {
            self.stats.pops += 1;
            self.distances_valid = false;
            self.graph.pop(levels);
        }
    }

    /// Exact validated value; unavailable after mutation or a non-SAT check.
    pub fn get_value_exact(&self, var: u32) -> Option<&BigRational> {
        if !self.distances_valid {
            return None;
        }
        self.model.get(var as usize)
    }

    /// Get a value if its numerator and denominator fit the narrow API.
    pub fn get_value(&self, var: u32) -> Option<Rational64> {
        let v = self.get_value_exact(var)?;
        Some(Rational64::new_raw(
            v.numer().to_i64()?,
            v.denom().to_i64()?,
        ))
    }

    /// Narrow model. Wide values are omitted, never truncated; use
    /// `get_value_exact` when the narrow API cannot represent a value.
    pub fn get_model(&self) -> HashMap<u32, Rational64> {
        (0..self.graph.num_vars())
            .filter_map(|v| self.get_value(v).map(|x| (v, x)))
            .collect()
    }

    /// Entailed (inclusive) upper bound from paths x⁻ -> x⁺, divided by two.
    pub fn get_upper_bound(&self, var: u32) -> Option<Rational64> {
        self.implied_bound(var, true)
    }

    /// Entailed (inclusive) lower bound from paths x⁺ -> x⁻, divided by -two.
    pub fn get_lower_bound(&self, var: u32) -> Option<Rational64> {
        self.implied_bound(var, false)
    }

    fn implied_bound(&self, var: u32, upper: bool) -> Option<Rational64> {
        if !self.distances_valid || var >= self.graph.num_vars() {
            return None;
        }
        let start = DoubledNode {
            var_id: var,
            positive: !upper,
        };
        let target = start.complement();
        let n = self.distances.len();
        let mut distance: Vec<Option<BigDeltaRational>> = vec![None; n];
        distance[self.node_index(start)] = Some(BigDeltaRational::zero());
        for _ in 1..n {
            let mut changed = false;
            for edge in self.graph.all_edges() {
                if let Some(from) = &distance[self.node_index(edge.from)] {
                    let next = Self::plus(from, &edge.weight);
                    let to = self.node_index(edge.to);
                    if distance[to].as_ref().is_none_or(|old| &next < old) {
                        distance[to] = Some(next);
                        changed = true;
                    }
                }
            }
            if !changed {
                break;
            }
        }
        let mut bound = distance[self.node_index(target)].as_ref()?.real.clone()
            / BigRational::from_integer(2.into());
        if self.graph.is_integer() {
            bound = bound.floor();
        }
        if !upper {
            bound = -bound;
        }
        Some(Rational64::new_raw(
            bound.numer().to_i64()?,
            bound.denom().to_i64()?,
        ))
    }

    /// Get statistics
    pub fn stats(&self) -> &UtvpiStats {
        &self.stats
    }

    /// Reset the solver
    pub fn reset(&mut self) {
        self.graph.reset();
        self.distances.clear();
        self.model.clear();
        self.distances_valid = false;
    }

    /// Number of variables
    pub fn num_vars(&self) -> u32 {
        self.graph.num_vars()
    }

    /// Number of constraints
    pub fn num_constraints(&self) -> usize {
        self.graph.num_constraints()
    }

    /// Current decision level
    pub fn current_level(&self) -> u32 {
        self.graph.current_level()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn r(n: i64) -> Rational64 {
        Rational64::from_integer(n)
    }

    #[test]
    fn test_solver_creation() {
        let solver = UtvpiSolver::new(true);
        assert_eq!(solver.num_vars(), 0);
        assert_eq!(solver.num_constraints(), 0);
    }

    #[test]
    fn test_satisfiable_diff() {
        let mut solver = UtvpiSolver::new(true);
        let origin = TermId::from(100u32);

        let x = solver.get_or_create_var(TermId::from(1u32));
        let y = solver.get_or_create_var(TermId::from(2u32));

        // x - y ≤ 5 and y - x ≤ 3
        solver.add_diff(x, y, r(5), origin);
        solver.add_diff(y, x, r(3), origin);

        let result = solver.check();
        assert!(matches!(result, UtvpiResult::Ok));
    }

    #[test]
    fn test_satisfiable_sum() {
        let mut solver = UtvpiSolver::new(true);
        let origin = TermId::from(100u32);

        let x = solver.get_or_create_var(TermId::from(1u32));
        let y = solver.get_or_create_var(TermId::from(2u32));

        // x + y ≤ 10
        solver.add_sum(x, y, r(10), origin);

        let result = solver.check();
        assert!(matches!(result, UtvpiResult::Ok));
    }

    #[test]
    fn test_unsatisfiable_diff() {
        let mut solver = UtvpiSolver::new(true);
        let origin = TermId::from(100u32);

        let x = solver.get_or_create_var(TermId::from(1u32));
        let y = solver.get_or_create_var(TermId::from(2u32));

        // x - y ≤ -1 and y - x ≤ -1
        // This means x < y and y < x, contradiction
        solver.add_diff(x, y, r(-1), origin);
        solver.add_diff(y, x, r(-1), origin);

        let result = solver.check();
        assert!(matches!(result, UtvpiResult::Conflict(_)));
    }

    #[test]
    fn test_unsatisfiable_sum() {
        let mut solver = UtvpiSolver::new(true);
        let origin = TermId::from(100u32);

        let x = solver.get_or_create_var(TermId::from(1u32));
        let y = solver.get_or_create_var(TermId::from(2u32));

        // x + y ≤ -1 and -x - y ≤ -1
        // This means x + y ≤ -1 and x + y ≥ 1, contradiction
        solver.add_sum(x, y, r(-1), origin);
        solver.add_neg_sum(x, y, r(-1), origin);

        let result = solver.check();
        assert!(matches!(result, UtvpiResult::Conflict(_)));
    }

    #[test]
    fn test_bounds() {
        let mut solver = UtvpiSolver::new(true);
        let origin = TermId::from(100u32);

        let x = solver.get_or_create_var(TermId::from(1u32));

        // x ≤ 10 and x ≥ 5 (i.e., -x ≤ -5)
        solver.add_upper(x, r(10), origin);
        solver.add_lower(x, r(-5), origin);

        let result = solver.check();
        assert!(matches!(result, UtvpiResult::Ok));
    }

    #[test]
    fn test_unsatisfiable_bounds() {
        let mut solver = UtvpiSolver::new(true);
        let origin = TermId::from(100u32);

        let x = solver.get_or_create_var(TermId::from(1u32));

        // x ≤ 5 and x ≥ 10 (i.e., -x ≤ -10)
        solver.add_upper(x, r(5), origin);
        solver.add_lower(x, r(-10), origin);

        let result = solver.check();
        assert!(matches!(result, UtvpiResult::Conflict(_)));
    }

    #[test]
    fn test_model_extraction() {
        let mut solver = UtvpiSolver::new(true);
        let origin = TermId::from(100u32);

        let x = solver.get_or_create_var(TermId::from(1u32));
        let y = solver.get_or_create_var(TermId::from(2u32));

        // x - y ≤ 5
        solver.add_diff(x, y, r(5), origin);

        let result = solver.check();
        assert!(matches!(result, UtvpiResult::Ok));

        let model = solver.get_model();
        assert!(!model.is_empty());
    }

    #[test]
    fn test_push_pop() {
        let mut solver = UtvpiSolver::new(true);
        let origin = TermId::from(100u32);

        let x = solver.get_or_create_var(TermId::from(1u32));
        let y = solver.get_or_create_var(TermId::from(2u32));

        // Level 0: x - y ≤ 5
        solver.add_diff(x, y, r(5), origin);
        assert_eq!(solver.check(), UtvpiResult::Ok);

        solver.push();
        assert_eq!(solver.current_level(), 1);

        // Level 1: y - x ≤ -10 (would make x - y ≥ 10, conflict with ≤ 5)
        solver.add_diff(y, x, r(-10), origin);
        let result = solver.check();
        assert!(matches!(result, UtvpiResult::Conflict(_)));

        // Pop back to level 0
        solver.pop(1);
        assert_eq!(solver.current_level(), 0);

        // Should be satisfiable again
        let result = solver.check();
        assert!(matches!(result, UtvpiResult::Ok));
    }

    #[test]
    fn test_reset() {
        let mut solver = UtvpiSolver::new(true);
        let origin = TermId::from(100u32);

        let x = solver.get_or_create_var(TermId::from(1u32));
        solver.add_upper(x, r(5), origin);

        solver.reset();

        assert_eq!(solver.num_vars(), 0);
        assert_eq!(solver.num_constraints(), 0);
    }

    #[test]
    fn test_triangle() {
        let mut solver = UtvpiSolver::new(true);
        let origin = TermId::from(100u32);

        let x = solver.get_or_create_var(TermId::from(1u32));
        let y = solver.get_or_create_var(TermId::from(2u32));
        let z = solver.get_or_create_var(TermId::from(3u32));

        // x - y ≤ 3
        // y - z ≤ 2
        // z - x ≤ 1
        // Sum: 0 ≤ 6 (satisfiable)
        solver.add_diff(x, y, r(3), origin);
        solver.add_diff(y, z, r(2), origin);
        solver.add_diff(z, x, r(1), origin);

        let result = solver.check();
        assert!(matches!(result, UtvpiResult::Ok));
    }

    #[test]
    fn test_negative_triangle() {
        let mut solver = UtvpiSolver::new(true);
        let origin = TermId::from(100u32);

        let x = solver.get_or_create_var(TermId::from(1u32));
        let y = solver.get_or_create_var(TermId::from(2u32));
        let z = solver.get_or_create_var(TermId::from(3u32));

        // x - y ≤ -1
        // y - z ≤ -1
        // z - x ≤ -1
        // Sum: 0 ≤ -3 (unsatisfiable - negative cycle)
        solver.add_diff(x, y, r(-1), origin);
        solver.add_diff(y, z, r(-1), origin);
        solver.add_diff(z, x, r(-1), origin);

        let result = solver.check();
        assert!(matches!(result, UtvpiResult::Conflict(_)));
    }

    #[test]
    fn test_mixed_constraints() {
        let mut solver = UtvpiSolver::new(true);
        let origin = TermId::from(100u32);

        let x = solver.get_or_create_var(TermId::from(1u32));
        let y = solver.get_or_create_var(TermId::from(2u32));

        // x - y ≤ 5 (difference)
        // x + y ≤ 10 (sum)
        // x ≤ 8 (upper bound)
        solver.add_diff(x, y, r(5), origin);
        solver.add_sum(x, y, r(10), origin);
        solver.add_upper(x, r(8), origin);

        let result = solver.check();
        assert!(matches!(result, UtvpiResult::Ok));
    }

    #[test]
    fn test_bounds_extraction() {
        let mut solver = UtvpiSolver::new(true);
        let origin = TermId::from(100u32);

        let x = solver.get_or_create_var(TermId::from(1u32));

        // x ≤ 10
        solver.add_upper(x, r(10), origin);
        // x ≥ 3 (i.e., -x ≤ -3)
        solver.add_lower(x, r(-3), origin);

        let result = solver.check();
        assert!(matches!(result, UtvpiResult::Ok));

        // Check bounds
        if let Some(upper) = solver.get_upper_bound(x) {
            assert!(upper <= r(10));
        }
        if let Some(lower) = solver.get_lower_bound(x) {
            assert!(lower >= r(3));
        }
    }

    #[test]
    fn test_spfa_mode() {
        let config = UtvpiConfig {
            use_spfa: true,
            ..Default::default()
        };
        let mut solver = UtvpiSolver::with_config(true, config);
        let origin = TermId::from(100u32);

        let x = solver.get_or_create_var(TermId::from(1u32));
        let y = solver.get_or_create_var(TermId::from(2u32));

        solver.add_diff(x, y, r(5), origin);
        solver.add_diff(y, x, r(3), origin);

        let result = solver.check();
        assert!(matches!(result, UtvpiResult::Ok));
    }

    #[test]
    fn test_bellman_ford_mode() {
        let config = UtvpiConfig {
            use_spfa: false,
            ..Default::default()
        };
        let mut solver = UtvpiSolver::with_config(true, config);
        let origin = TermId::from(100u32);

        let x = solver.get_or_create_var(TermId::from(1u32));
        let y = solver.get_or_create_var(TermId::from(2u32));

        solver.add_diff(x, y, r(5), origin);
        solver.add_diff(y, x, r(3), origin);

        let result = solver.check();
        assert!(matches!(result, UtvpiResult::Ok));
    }
}
