//! Difference Logic Theory Solver
//!
//! Main solver implementation that integrates with the CDCL(T) framework.

use super::bellman_ford::{BellmanFord, BellmanFordResult, NegativeCycle, Spfa};
use super::dense::DenseDiffLogic;
use super::graph::{ConstraintGraph, ConstraintType, DiffConstraint, DiffVar};
#[allow(unused_imports)]
use crate::prelude::*;
use num_rational::Rational64;
use oxiz_core::ast::TermId;

/// Configuration for the difference logic solver
#[derive(Debug, Clone)]
pub struct DiffLogicConfig {
    /// Use SPFA instead of standard Bellman-Ford
    pub use_spfa: bool,
    /// Use dense representation for small problems
    pub use_dense: bool,
    /// Threshold for switching to dense representation
    pub dense_threshold: usize,
    /// Enable theory propagation
    pub propagate: bool,
    /// Maximum propagation rounds per call
    pub max_propagation_rounds: usize,
}

impl Default for DiffLogicConfig {
    fn default() -> Self {
        Self {
            use_spfa: true,
            use_dense: true,
            dense_threshold: 50,
            propagate: true,
            max_propagation_rounds: 10,
        }
    }
}

/// Statistics for the difference logic solver
#[derive(Debug, Clone, Default)]
pub struct DiffLogicStats {
    /// Number of constraints added
    pub constraints_added: usize,
    /// Number of propagations
    pub propagations: usize,
    /// Number of conflicts detected
    pub conflicts: usize,
    /// Number of consistency checks
    pub checks: usize,
    /// Number of model queries
    pub model_queries: usize,
}

/// Result of a difference logic operation
#[derive(Debug, Clone)]
pub enum DiffLogicResult {
    /// Operation succeeded
    Ok,
    /// Conflict detected with explanation
    Conflict(Vec<TermId>),
    /// Theory propagation (implied constraint)
    Propagation {
        /// The implied constraint
        implied: TermId,
        /// Reason for the implication
        reason: Vec<TermId>,
    },
}

/// Difference Logic Theory Solver
///
/// Handles constraints of the form x - y ≤ c (or x - y < c).
#[derive(Debug)]
pub struct DiffLogicSolver {
    /// Configuration
    config: DiffLogicConfig,
    /// Constraint graph (sparse representation)
    graph: ConstraintGraph,
    /// Dense solver (for small problems)
    dense: Option<DenseDiffLogic>,
    /// Bellman-Ford solver
    bf: BellmanFord,
    /// SPFA solver
    spfa: Spfa,
    /// Current distances (cached from last check)
    distances: HashMap<DiffVar, Rational64>,
    /// Whether distances are up-to-date
    distances_valid: bool,
    /// Statistics
    stats: DiffLogicStats,
    /// Decision level stack for backtracking
    level_stack: Vec<usize>,
    /// Current decision level
    current_level: u32,
    /// Pending constraints to process
    pending: Vec<usize>,
    /// Term to constraint mapping
    term_to_constraint: HashMap<TermId, Vec<usize>>,
}

/// Outcome of an incremental edge add (see [`DiffLogicSolver::add_leq_check`]).
enum IncAdd {
    /// Immediate self-conflict (x == y, c < 0).
    Conflict(Vec<TermId>),
    /// Edge added; run the seeded SPFA from this source node.
    Ok(DiffVar),
    /// Distances are stale or a new variable appeared – fall back to a full
    /// [`DiffLogicSolver::check`].
    FullCheck,
}

impl DiffLogicSolver {
    /// Create a new solver with default configuration
    pub fn new(is_integer: bool) -> Self {
        Self::with_config(is_integer, DiffLogicConfig::default())
    }

    /// Create a new solver with custom configuration
    pub fn with_config(is_integer: bool, config: DiffLogicConfig) -> Self {
        Self {
            graph: ConstraintGraph::new(is_integer),
            dense: if config.use_dense {
                Some(DenseDiffLogic::new(is_integer))
            } else {
                None
            },
            bf: BellmanFord::new(),
            spfa: Spfa::new(),
            distances: HashMap::new(),
            distances_valid: false,
            stats: DiffLogicStats::default(),
            level_stack: vec![0],
            current_level: 0,
            pending: Vec::new(),
            term_to_constraint: HashMap::new(),
            config,
        }
    }

    /// Get the configuration
    pub fn config(&self) -> &DiffLogicConfig {
        &self.config
    }

    /// Get statistics
    pub fn stats(&self) -> &DiffLogicStats {
        &self.stats
    }

    /// Reset statistics
    pub fn reset_stats(&mut self) {
        self.stats = DiffLogicStats::default();
    }

    /// Register a variable (term)
    pub fn register_var(&mut self, term: TermId) -> DiffVar {
        self.distances_valid = false;
        self.graph.get_or_create_var(term)
    }

    /// Add a constraint x - y ≤ c
    pub fn add_leq(
        &mut self,
        x: TermId,
        y: TermId,
        c: Rational64,
        origin: TermId,
    ) -> DiffLogicResult {
        self.add_constraint_internal(x, y, c, ConstraintType::LeqConst, origin)
    }

    /// Add a constraint x - y < c
    pub fn add_lt(
        &mut self,
        x: TermId,
        y: TermId,
        c: Rational64,
        origin: TermId,
    ) -> DiffLogicResult {
        self.add_constraint_internal(x, y, c, ConstraintType::LtConst, origin)
    }

    /// Internal method to add a constraint
    fn add_constraint_internal(
        &mut self,
        x_term: TermId,
        y_term: TermId,
        c: Rational64,
        constraint_type: ConstraintType,
        origin: TermId,
    ) -> DiffLogicResult {
        self.stats.constraints_added += 1;
        self.distances_valid = false;

        // Get or create variables
        let x = self.graph.get_or_create_var(x_term);
        let y = self.graph.get_or_create_var(y_term);

        // Create constraint
        let mut constraint = match constraint_type {
            ConstraintType::LeqConst => DiffConstraint::new_leq(x, y, c, origin),
            ConstraintType::LtConst => DiffConstraint::new_lt(x, y, c, origin),
        };
        constraint.level = self.current_level;
        constraint.asserted = true;

        // Add to graph
        let idx = self.graph.add_constraint(constraint);

        // Track constraint by origin term
        self.term_to_constraint.entry(origin).or_default().push(idx);

        // Add to pending for next propagation
        self.pending.push(idx);

        // Quick check: does this create an obvious conflict?
        // A simple heuristic: if x == y and c < 0, immediate conflict
        if x == y && c < Rational64::from_integer(0) {
            self.stats.conflicts += 1;
            return DiffLogicResult::Conflict(vec![origin]);
        }

        DiffLogicResult::Ok
    }

    /// Check consistency of current constraints
    pub fn check(&mut self) -> DiffLogicResult {
        self.stats.checks += 1;

        // Always use Bellman-Ford/SPFA for now (dense solver is for future optimization)
        // Run Bellman-Ford or SPFA
        let result = if self.config.use_spfa {
            self.spfa.run(&self.graph)
        } else {
            self.bf.run(&self.graph)
        };

        match result {
            BellmanFordResult::Distances(dists) => {
                // Convert to our format
                self.distances = dists;
                self.distances_valid = true;
                DiffLogicResult::Ok
            }
            BellmanFordResult::NegativeCycle(cycle) => {
                self.stats.conflicts += 1;
                // Extract conflict clause from cycle
                let conflict = self.cycle_to_conflict(&cycle);
                DiffLogicResult::Conflict(conflict)
            }
        }
    }

    /// Convert a negative cycle to a conflict clause
    fn cycle_to_conflict(&self, cycle: &NegativeCycle) -> Vec<TermId> {
        let mut conflict = Vec::new();

        for &idx in cycle.constraint_indices() {
            if let Some(constraint) = self.graph.get_constraint(idx) {
                conflict.push(constraint.origin);
            }
        }

        conflict
    }

    /// Add a constraint edge WITHOUT invalidating the cached distances, and
    /// report whether an incremental check is usable.
    fn add_constraint_inc(
        &mut self,
        x_term: TermId,
        y_term: TermId,
        c: Rational64,
        constraint_type: ConstraintType,
        origin: TermId,
    ) -> IncAdd {
        self.stats.constraints_added += 1;
        let x = self.graph.get_or_create_var(x_term);
        let y = self.graph.get_or_create_var(y_term);
        // A brand-new variable has no cached distance: must recompute fully.
        let new_var = !self.distances.contains_key(&x) || !self.distances.contains_key(&y);
        let mut constraint = match constraint_type {
            ConstraintType::LeqConst => DiffConstraint::new_leq(x, y, c, origin),
            ConstraintType::LtConst => DiffConstraint::new_lt(x, y, c, origin),
        };
        constraint.level = self.current_level;
        constraint.asserted = true;
        // Immediate self-conflict (matches `add_constraint_internal`).
        if x == y && c < Rational64::from_integer(0) {
            self.stats.conflicts += 1;
            self.distances_valid = false;
            return IncAdd::Conflict(vec![origin]);
        }
        let idx = self.graph.add_constraint(constraint);
        self.term_to_constraint.entry(origin).or_default().push(idx);
        self.pending.push(idx);
        if new_var || !self.distances_valid {
            self.distances_valid = false;
            return IncAdd::FullCheck;
        }
        IncAdd::Ok(y)
    }

    /// Seeded SPFA from `src`: update the cached distances over the asserted
    /// edges and detect a negative cycle.  O(affected nodes), far cheaper than
    /// a full Bellman-Ford on a sparse graph.  On a detected cycle, falls back
    /// to [`Self::check`] to extract the conflict terms (rare path).
    fn check_incremental_from(&mut self, src: DiffVar) -> DiffLogicResult {
        let inf = Rational64::from_integer(i64::MAX);
        let n = self.graph.num_vars() + 1;
        let mut queue: VecDeque<DiffVar> = VecDeque::new();
        let mut in_queue: HashMap<DiffVar, bool> = HashMap::new();
        let mut count: HashMap<DiffVar, u32> = HashMap::new();
        queue.push_back(src);
        in_queue.insert(src, true);
        while let Some(u) = queue.pop_front() {
            in_queue.insert(u, false);
            let Some(&du) = self.distances.get(&u) else {
                continue;
            };
            if du == inf {
                continue;
            }
            // Collect this node's edges first so the immutable borrow of
            // `self.graph` ends before we mutate `self.distances` below.
            let edges: Vec<(DiffVar, Rational64)> = self
                .graph
                .get_edges(u)
                .filter(|e| e.from != DiffVar::SOURCE)
                .map(|e| (e.to, e.weight))
                .collect();
            for (to, weight) in edges {
                let nd = du + weight;
                let cur = self.distances.get(&to).copied().unwrap_or(inf);
                if nd < cur {
                    self.distances.insert(to, nd);
                    if !in_queue.get(&to).copied().unwrap_or(false) {
                        queue.push_back(to);
                        in_queue.insert(to, true);
                        let cnt = count.entry(to).or_insert(0);
                        *cnt += 1;
                        // A node pushed more than |V| times lies on a negative
                        // cycle reachable from `src`.
                        if *cnt > n {
                            self.stats.conflicts += 1;
                            return self.check();
                        }
                    }
                }
            }
        }
        DiffLogicResult::Ok
    }

    /// Add `x - y ≤ c` and incrementally check for a negative cycle
    /// (seeded SPFA, O(affected)). See `check_incremental_from`.
    pub fn add_leq_check(
        &mut self,
        x: TermId,
        y: TermId,
        c: Rational64,
        origin: TermId,
    ) -> DiffLogicResult {
        match self.add_constraint_inc(x, y, c, ConstraintType::LeqConst, origin) {
            IncAdd::Conflict(t) => DiffLogicResult::Conflict(t),
            IncAdd::Ok(src) => self.check_incremental_from(src),
            IncAdd::FullCheck => self.check(),
        }
    }

    /// Add `x - y < c` and incrementally check (see [`Self::add_leq_check`]).
    pub fn add_lt_check(
        &mut self,
        x: TermId,
        y: TermId,
        c: Rational64,
        origin: TermId,
    ) -> DiffLogicResult {
        match self.add_constraint_inc(x, y, c, ConstraintType::LtConst, origin) {
            IncAdd::Conflict(t) => DiffLogicResult::Conflict(t),
            IncAdd::Ok(src) => self.check_incremental_from(src),
            IncAdd::FullCheck => self.check(),
        }
    }

    /// Propagate implied bounds
    pub fn propagate(&mut self) -> Vec<DiffLogicResult> {
        let mut results = Vec::new();

        if !self.config.propagate {
            return results;
        }

        // Ensure distances are computed
        if !self.distances_valid
            && let DiffLogicResult::Conflict(c) = self.check()
        {
            results.push(DiffLogicResult::Conflict(c));
            return results;
        }

        // Theory propagation: if dist[x] - dist[y] ≤ c is tighter
        // than an unasserted constraint, propagate it
        // (This is a simplified version - full implementation would
        // require tracking unasserted constraints)

        self.pending.clear();
        results
    }

    /// Get the current value of a variable in the model
    pub fn get_value(&mut self, term: TermId) -> Option<Rational64> {
        self.stats.model_queries += 1;

        if !self.distances_valid
            && let DiffLogicResult::Conflict(_) = self.check()
        {
            return None;
        }

        if let Some(var) = self.graph.get_var(term) {
            self.distances.get(&var).copied()
        } else {
            None
        }
    }

    /// Get a complete model
    pub fn get_model(&mut self) -> HashMap<TermId, Rational64> {
        let mut model = HashMap::new();

        if !self.distances_valid
            && let DiffLogicResult::Conflict(_) = self.check()
        {
            return model;
        }

        for (var, dist) in &self.distances {
            if !var.is_source()
                && let Some(term) = self.graph.get_term(*var)
            {
                model.insert(term, *dist);
            }
        }

        model
    }

    /// Push a new decision level
    pub fn push(&mut self) {
        self.current_level += 1;
        self.graph.push();
        self.level_stack.push(self.graph.num_constraints());
    }

    /// Pop to a previous decision level
    pub fn pop(&mut self, levels: u32) {
        if levels == 0 {
            return;
        }

        self.graph.pop(levels);
        self.current_level = self.current_level.saturating_sub(levels);

        // Truncate level stack
        let target = (self.current_level + 1) as usize;
        if target < self.level_stack.len() {
            self.level_stack.truncate(target);
        }

        self.distances_valid = false;
    }

    /// Reset the solver
    pub fn reset(&mut self) {
        self.graph.reset();
        if let Some(ref mut dense) = self.dense {
            dense.clear();
        }
        self.distances.clear();
        self.distances_valid = false;
        self.pending.clear();
        self.term_to_constraint.clear();
        self.level_stack = vec![0];
        self.current_level = 0;
        self.reset_stats();
    }

    /// Get the explanation for a constraint
    pub fn explain(&self, constraint_origin: TermId) -> Vec<TermId> {
        let mut explanation = Vec::new();

        if let Some(indices) = self.term_to_constraint.get(&constraint_origin) {
            for &idx in indices {
                if let Some(constraint) = self.graph.get_constraint(idx) {
                    // For a difference constraint, the explanation is the path
                    // from y to x in the constraint graph
                    // Simplified: just return the constraint itself
                    explanation.push(constraint.origin);
                }
            }
        }

        explanation
    }

    /// Check if a potential constraint would cause a conflict.
    ///
    /// **Unsound as an implication test – do not use for theory propagation.**
    /// This reduces to `dist[x] - dist[y] <= c` where `dist` are the virtual-
    /// source Bellman-Ford distances. That quantity is only a *lower bound* on
    /// the true shortest path `d(y, x)`, so it over-reports: e.g. a single
    /// asserted edge `a - b <= 5` gives `dist[a] = dist[b] = 0`, which this
    /// test accepts as implying `a - b <= 3` – false. A controlled re-de-risk
    /// measured the over-count at ~10x (53-69% "implied" vs 1-6% soundly
    /// implied on inequality atoms). For sound theory propagation use
    /// [`Self::entailed_reason`], which computes the actual shortest path.
    pub fn would_conflict(&mut self, x: TermId, y: TermId, c: Rational64, strict: bool) -> bool {
        // Quick check: get current bounds and see if new constraint conflicts
        if !self.distances_valid
            && let DiffLogicResult::Conflict(_) = self.check()
        {
            return true;
        }

        let x_var = self.graph.get_var(x);
        let y_var = self.graph.get_var(y);

        match (x_var, y_var) {
            (Some(xv), Some(yv)) => {
                // Current constraint implies: x ≤ y + dist[x] - dist[y]
                // New constraint: x - y ≤ c (or < c)
                // Combined: we need to check if the cycle y → x → ... → y is negative

                let dx = self
                    .distances
                    .get(&xv)
                    .copied()
                    .unwrap_or(Rational64::from_integer(0));
                let dy = self
                    .distances
                    .get(&yv)
                    .copied()
                    .unwrap_or(Rational64::from_integer(0));

                // The implied bound from current solution
                let current_diff = dx - dy;

                // Check if adding x - y ≤ c would create a negative cycle
                // This happens if there's a path y → ... → x with weight w
                // and w + c < 0

                // For simplicity, check if the triangle inequality is violated
                // This is conservative but fast
                if strict {
                    c <= -current_diff
                } else {
                    c < -current_diff
                }
            }
            _ => false,
        }
    }

    /// Look up the difference-logic variable for a term, if registered.
    pub fn get_diff_var(&self, term: TermId) -> Option<DiffVar> {
        self.graph.get_var(term)
    }

    /// Run single-source shortest path from `src` over the constraint edges.
    ///
    /// Returns `(dist, pred_edge)` where `pred_edge[node]` is the constraint
    /// index whose edge last improved `dist[node]` (for path reconstruction).
    /// Returns `None` if a negative cycle is reachable from `src` – under
    /// normal CDCL(T) use [`Self::check`] has already turned that into a
    /// `Conflict`, so `None` here only means the caller should not propagate.
    ///
    /// This is the SOUND foundation for theory propagation: the true
    /// shortest-path distance `d(src, node)` over asserted edges, not the
    /// virtual-source distance difference (a lower bound – see
    /// [`Self::would_conflict`]).  Exposed so a propagation pass can compute
    /// it once per distinct source and amortize the cost over many atom
    /// queries ([`Self::entailed_from_sssp`]).
    pub fn sssp_from(
        &self,
        src: DiffVar,
    ) -> Option<(HashMap<DiffVar, Rational64>, HashMap<DiffVar, usize>)> {
        let zero = Rational64::from_integer(0);
        let inf = Rational64::from_integer(i64::MAX);
        let mut dist: HashMap<DiffVar, Rational64> = HashMap::new();
        let mut pred: HashMap<DiffVar, usize> = HashMap::new();
        dist.insert(src, zero);

        // SPFA (Shortest Path Faster Algorithm): a queue-driven Bellman-Ford
        // that relaxes an edge only when its source node's distance just
        // improved.  On the sparse difference-logic graphs encountered during
        // theory propagation this is near O(E) per source – orders of
        // magnitude faster than the |V|-passes-over-all-edges textbook
        // Bellman-Ford (which dominated runtime and prevented convergence on
        // qlock-4-10-7).  Edges from the virtual SOURCE are skipped: they are
        // not asserted constraints and are unreachable from a real `src`.
        let n = self.graph.num_vars() + 1;
        let mut queue: VecDeque<DiffVar> = VecDeque::new();
        let mut in_queue: HashMap<DiffVar, bool> = HashMap::new();
        let mut count: HashMap<DiffVar, u32> = HashMap::new();
        queue.push_back(src);
        in_queue.insert(src, true);
        while let Some(u) = queue.pop_front() {
            in_queue.insert(u, false);
            let Some(&du) = dist.get(&u) else {
                continue;
            };
            for edge in self.graph.get_edges(u) {
                let nd = du + edge.weight;
                let cur = dist.get(&edge.to).copied().unwrap_or(inf);
                if nd < cur {
                    dist.insert(edge.to, nd);
                    pred.insert(edge.to, edge.constraint_idx);
                    if !in_queue.get(&edge.to).copied().unwrap_or(false) {
                        queue.push_back(edge.to);
                        in_queue.insert(edge.to, true);
                        let c = count.entry(edge.to).or_insert(0);
                        *c += 1;
                        // A node dequeued more than |V| times is on a negative
                        // cycle reachable from `src`.
                        if *c > n {
                            return None;
                        }
                    }
                }
            }
        }

        Some((dist, pred))
    }

    /// Reconstruct the asserted-atom origins on the predecessor path
    /// `src -> ... -> x`, in path order. Returns an empty `Vec` if `x == src`
    /// (a trivial path has no asserted atom on it) so callers can treat an
    /// empty reason as "not derived": the SAT core installs an empty-reason
    /// propagation as a level-0 unit (see `search_ext::install_theory_units`),
    /// which is unsound for a mid-search propagated literal.
    fn reason_path(&self, src: DiffVar, x: DiffVar, pred: &HashMap<DiffVar, usize>) -> Vec<TermId> {
        if x == src {
            return Vec::new();
        }
        let mut path = Vec::new();
        let mut cur = x;
        let mut guard = 0;
        let max_steps = self.graph.num_constraints() + 1;
        while cur != src {
            let Some(&edge_idx) = pred.get(&cur) else {
                break;
            };
            let Some(constraint) = self.graph.get_constraint(edge_idx) else {
                break;
            };
            path.push(constraint.origin);
            // The edge for `x_c - y_c <= c` runs y_c -> x_c; having improved
            // `dist[cur == x_c]`, its predecessor node is y_c.
            cur = constraint.y;
            guard += 1;
            if guard > max_steps {
                break;
            }
        }
        path
    }

    /// **Sound** theory-propagation reason, given a precomputed single-source
    /// shortest-path tree from `yv` ([`Self::sssp_from`]).
    ///
    /// This is the amortized core of [`Self::entailed_reason`]: a propagation
    /// pass computes one SSSP tree per distinct source, then queries many
    /// `(xv, yv, c)` bounds against it in O(1) plus path-reconstruction cost.
    ///
    /// Semantics and SOUNDNESS are identical to [`Self::entailed_reason`]:
    /// returns the asserted-atom origins on the path entailing `xv - yv ≤ c`
    /// (or `< c` if `strict`), requiring the ACTUAL `d(yv, xv) ≤ c_eff`, or
    /// `None`.  Integer tightening applies for `strict`.  Returns `None` for an
    /// empty reason path (a trivial bound not derived from asserted atoms –
    /// see [`Self::entailed_reason`]).
    pub fn entailed_from_sssp(
        &self,
        xv: DiffVar,
        yv: DiffVar,
        c: Rational64,
        strict: bool,
        dist_from_y: &HashMap<DiffVar, Rational64>,
        pred_from_y: &HashMap<DiffVar, usize>,
    ) -> Option<Vec<TermId>> {
        let c_eff = if strict && self.is_integer() {
            c - Rational64::from_integer(1)
        } else {
            c
        };
        let inf = Rational64::from_integer(i64::MAX);
        let &dx = dist_from_y.get(&xv)?;
        if dx == inf {
            return None;
        }
        let entailed = if strict && !self.is_integer() {
            dx < c
        } else {
            dx <= c_eff
        };
        if !entailed {
            return None;
        }
        let path = self.reason_path(yv, xv, pred_from_y);
        if path.is_empty() { None } else { Some(path) }
    }

    /// **Sound** theory-propagation reason.
    ///
    /// Returns the asserted atoms on a shortest path entailing `x - y ≤ c`
    /// (or `x - y < c` when `strict`), or `None` if the bound is not entailed
    /// by the currently-asserted difference constraints.
    ///
    /// SOUNDNESS: entailment of `x - y ≤ c` requires the ACTUAL shortest-path
    /// distance `d(y, x) ≤ c` over the asserted edges – the quantity that
    /// determines the tightest derivable bound on `x - y`. This computes
    /// `d(y, x)` by a single-source Bellman-Ford from `y` ([`Self::sssp_from`]).
    /// It is NOT the virtual-source distance difference `dist[x] - dist[y]`,
    /// which is only a lower bound on `d(y, x)` and over-reports implications
    /// (see [`Self::would_conflict`]).
    ///
    /// Integer tightening: for an integer solver, `x - y < c` is equivalent to
    /// `x - y ≤ c - 1`, applied here so callers pass the raw constant.
    ///
    /// Returns `None` (does *not* propagate) when the reason path is empty –
    /// i.e. when the bound holds trivially (`x == y`) rather than being
    /// derived from asserted atoms – because an empty reason is installed by
    /// the SAT core as a level-0 unit, which is unsound for a mid-search
    /// propagated literal.
    ///
    /// For a propagation pass querying many atoms, prefer
    /// [`Self::entailed_from_sssp`] with a per-source SSSP cache.
    pub fn entailed_reason(
        &self,
        x: TermId,
        y: TermId,
        c: Rational64,
        strict: bool,
    ) -> Option<Vec<TermId>> {
        let xv = self.graph.get_var(x)?;
        let yv = self.graph.get_var(y)?;
        let (dist, pred) = self.sssp_from(yv)?;
        self.entailed_from_sssp(xv, yv, c, strict, &dist, &pred)
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
        self.current_level
    }

    /// Is this an integer solver?
    pub fn is_integer(&self) -> bool {
        self.graph.is_integer()
    }
}

impl Default for DiffLogicSolver {
    fn default() -> Self {
        Self::new(true)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn term(id: u32) -> TermId {
        TermId::from(id)
    }

    #[test]
    fn test_solver_creation() {
        let solver = DiffLogicSolver::new(true);
        assert_eq!(solver.num_vars(), 0);
        assert_eq!(solver.num_constraints(), 0);
        assert!(solver.is_integer());
    }

    #[test]
    fn test_add_constraint() {
        let mut solver = DiffLogicSolver::new(true);
        let x = term(1);
        let y = term(2);
        let origin = term(100);

        // x - y ≤ 5
        let result = solver.add_leq(x, y, Rational64::from_integer(5), origin);
        assert!(matches!(result, DiffLogicResult::Ok));
        assert_eq!(solver.num_constraints(), 1);
    }

    #[test]
    fn test_consistency_check() {
        let mut solver = DiffLogicSolver::new(true);
        let x = term(1);
        let y = term(2);
        let z = term(3);
        let o1 = term(100);
        let o2 = term(101);
        let o3 = term(102);

        // Add consistent constraints
        // x - y ≤ 3
        // y - z ≤ 2
        // z - x ≤ 1
        // Total cycle: 3 + 2 + 1 = 6 ≥ 0, so consistent
        solver.add_leq(x, y, Rational64::from_integer(3), o1);
        solver.add_leq(y, z, Rational64::from_integer(2), o2);
        solver.add_leq(z, x, Rational64::from_integer(1), o3);

        let result = solver.check();
        assert!(matches!(result, DiffLogicResult::Ok));
    }

    #[test]
    fn test_conflict_detection() {
        let mut solver = DiffLogicSolver::new(true);
        let x = term(1);
        let y = term(2);
        let z = term(3);
        let o1 = term(100);
        let o2 = term(101);
        let o3 = term(102);

        // Add inconsistent constraints (negative cycle)
        // x - y ≤ -1
        // y - z ≤ -1
        // z - x ≤ -1
        // Total cycle: -3 < 0, so inconsistent
        solver.add_leq(x, y, Rational64::from_integer(-1), o1);
        solver.add_leq(y, z, Rational64::from_integer(-1), o2);
        solver.add_leq(z, x, Rational64::from_integer(-1), o3);

        let result = solver.check();
        assert!(matches!(result, DiffLogicResult::Conflict(_)));
    }

    #[test]
    fn test_model_extraction() {
        let mut solver = DiffLogicSolver::new(true);
        let x = term(1);
        let y = term(2);
        let origin = term(100);

        // x - y ≤ 5
        solver.add_leq(x, y, Rational64::from_integer(5), origin);

        let result = solver.check();
        assert!(matches!(result, DiffLogicResult::Ok));

        let model = solver.get_model();
        assert!(!model.is_empty());

        // Check that the constraint is satisfied
        if let (Some(&vx), Some(&vy)) = (model.get(&x), model.get(&y)) {
            assert!(vx - vy <= Rational64::from_integer(5));
        }
    }

    #[test]
    fn test_push_pop() {
        let mut solver = DiffLogicSolver::new(true);
        let x = term(1);
        let y = term(2);
        let o1 = term(100);
        let o2 = term(101);

        // Level 0: x - y ≤ 5
        solver.add_leq(x, y, Rational64::from_integer(5), o1);
        assert_eq!(solver.num_constraints(), 1);

        // Push to level 1
        solver.push();
        assert_eq!(solver.current_level(), 1);

        // Level 1: x - y ≤ 3
        solver.add_leq(x, y, Rational64::from_integer(3), o2);
        assert_eq!(solver.num_constraints(), 2);

        // Pop to level 0
        solver.pop(1);
        assert_eq!(solver.current_level(), 0);

        // Should still be consistent
        let result = solver.check();
        assert!(matches!(result, DiffLogicResult::Ok));
    }

    #[test]
    fn test_strict_constraint() {
        let mut solver = DiffLogicSolver::new(true);
        let x = term(1);
        let y = term(2);
        let origin = term(100);

        // x - y < 5 (becomes x - y ≤ 4 for integers)
        let result = solver.add_lt(x, y, Rational64::from_integer(5), origin);
        assert!(matches!(result, DiffLogicResult::Ok));

        let check_result = solver.check();
        assert!(matches!(check_result, DiffLogicResult::Ok));
    }

    #[test]
    fn test_immediate_conflict() {
        let mut solver = DiffLogicSolver::new(true);
        let x = term(1);
        let origin = term(100);

        // x - x ≤ -1 (immediate conflict)
        let result = solver.add_leq(x, x, Rational64::from_integer(-1), origin);
        assert!(matches!(result, DiffLogicResult::Conflict(_)));
    }

    #[test]
    fn test_would_conflict() {
        let mut solver = DiffLogicSolver::new(true);
        let x = term(1);
        let y = term(2);
        let origin = term(100);

        // x - y ≤ 0
        solver.add_leq(x, y, Rational64::from_integer(0), origin);
        solver.check();

        // Adding y - x ≤ -1 would create a conflict
        // (cycle x - y ≤ 0, y - x ≤ -1 has total -1 < 0)
        let would_conflict = solver.would_conflict(y, x, Rational64::from_integer(-1), false);
        assert!(would_conflict);
    }

    #[test]
    fn test_reset() {
        let mut solver = DiffLogicSolver::new(true);
        let x = term(1);
        let y = term(2);
        let origin = term(100);

        solver.add_leq(x, y, Rational64::from_integer(5), origin);
        assert_eq!(solver.num_constraints(), 1);

        solver.reset();
        assert_eq!(solver.num_constraints(), 0);
        assert_eq!(solver.num_vars(), 0);
    }

    #[test]
    fn test_real_arithmetic() {
        let mut solver = DiffLogicSolver::new(false); // Real arithmetic
        let x = term(1);
        let y = term(2);
        let origin = term(100);

        // x - y < 0.5 (remains strict for reals)
        let result = solver.add_lt(x, y, Rational64::new(1, 2), origin);
        assert!(matches!(result, DiffLogicResult::Ok));
    }

    // ======== incremental check (add_*_check) tests ========

    #[test]
    fn incremental_check_detects_negative_cycle() {
        // Add the 3-edge negative cycle one edge at a time via the incremental
        // API; the third edge must report Conflict (same as full `check`).
        let mut s = DiffLogicSolver::new(true);
        let (a, b, c) = (term(1), term(2), term(3));
        assert!(matches!(
            s.add_leq_check(a, b, Rational64::from_integer(-1), term(10)),
            DiffLogicResult::Ok
        ));
        assert!(matches!(
            s.add_leq_check(b, c, Rational64::from_integer(-1), term(11)),
            DiffLogicResult::Ok
        ));
        // a-b<=-1, b-c<=-1, c-a<=-1  =>  cycle sum -3 < 0
        assert!(
            matches!(
                s.add_leq_check(c, a, Rational64::from_integer(-1), term(12)),
                DiffLogicResult::Conflict(_)
            ),
            "incremental check must detect the negative cycle"
        );
    }

    #[test]
    fn incremental_check_stays_ok_when_consistent() {
        let mut s = DiffLogicSolver::new(true);
        let (a, b, c) = (term(1), term(2), term(3));
        // a-b<=3, b-c<=2, c-a<=1  =>  cycle sum 6 >= 0, consistent
        assert!(matches!(
            s.add_leq_check(a, b, Rational64::from_integer(3), term(10)),
            DiffLogicResult::Ok
        ));
        assert!(matches!(
            s.add_leq_check(b, c, Rational64::from_integer(2), term(11)),
            DiffLogicResult::Ok
        ));
        assert!(matches!(
            s.add_leq_check(c, a, Rational64::from_integer(1), term(12)),
            DiffLogicResult::Ok
        ));
    }

    #[test]
    fn incremental_check_matches_full_after_push_pop() {
        // After a push/pop, distances are invalidated; incremental must fall back
        // to full check and still detect the cycle.
        let mut s = DiffLogicSolver::new(true);
        let (a, b) = (term(1), term(2));
        s.add_leq_check(a, b, Rational64::from_integer(0), term(10));
        s.push();
        // b-a<=-1 + a-b<=0  => cycle -1
        assert!(matches!(
            s.add_leq_check(b, a, Rational64::from_integer(-1), term(11)),
            DiffLogicResult::Conflict(_)
        ));
    }

    // ======== entailed_reason soundness tests ========
    //
    // These pin the SOUND behaviour that distinguishes `entailed_reason` from
    // the unsound `would_conflict` approximation (see that method's doc).

    #[test]
    fn entailed_reason_counterexample_not_implied() {
        // The decisive counter-example: a single asserted edge `a - b <= 5`
        // must NOT entail `a - b <= 3`. (`would_conflict` would wrongly say
        // implied: dist[a]-dist[b] = 0 <= 3.)
        let mut s = DiffLogicSolver::new(true);
        let a = term(1);
        let b = term(2);
        s.add_leq(a, b, Rational64::from_integer(5), term(100));
        s.check();
        assert_eq!(
            s.entailed_reason(a, b, Rational64::from_integer(3), false),
            None,
            "a-b<=3 is NOT entailed by a-b<=5"
        );
        // But a-b<=5 (the asserted bound itself) and any looser bound ARE.
        assert!(
            s.entailed_reason(a, b, Rational64::from_integer(5), false)
                .is_some(),
            "a-b<=5 is entailed by the asserted a-b<=5"
        );
        assert!(
            s.entailed_reason(a, b, Rational64::from_integer(6), false)
                .is_some(),
            "a-b<=6 is entailed (looser than asserted)"
        );
    }

    #[test]
    fn entailed_reason_transitive_chain() {
        // a-b<=0, b-c<=0  =>  a-c<=0 entailed (reason = the two origins).
        let mut s = DiffLogicSolver::new(true);
        let a = term(1);
        let b = term(2);
        let c = term(3);
        s.add_leq(a, b, Rational64::from_integer(0), term(10));
        s.add_leq(b, c, Rational64::from_integer(0), term(11));
        s.check();
        let reason = s.entailed_reason(a, c, Rational64::from_integer(0), false);
        assert!(reason.is_some(), "a-c<=0 entailed by chain");
        let reason = reason.unwrap();
        assert_eq!(reason.len(), 2, "reason is the two edge origins");
        // a-c<=-1 must NOT be entailed (the chain only gives <=0).
        assert_eq!(
            s.entailed_reason(a, c, Rational64::from_integer(-1), false),
            None
        );
    }

    #[test]
    fn entailed_reason_strict_integer_tightening() {
        // a-b<=2 asserted. a-b<3 (int) = a-b<=2 entailed; a-b<2 (int) = a-b<=1 NOT.
        let mut s = DiffLogicSolver::new(true);
        let a = term(1);
        let b = term(2);
        s.add_leq(a, b, Rational64::from_integer(2), term(10));
        s.check();
        assert!(
            s.entailed_reason(a, b, Rational64::from_integer(3), true)
                .is_some(),
            "a-b<3 == a-b<=2 entailed"
        );
        assert_eq!(
            s.entailed_reason(a, b, Rational64::from_integer(2), true),
            None,
            "a-b<2 == a-b<=1 NOT entailed by a-b<=2"
        );
    }

    #[test]
    fn entailed_reason_negative_bound_via_reverse() {
        // a-b<=0 asserted. The reverse direction b-a<=0 is NOT entailed, but
        // b-a<=k for any k>=0 also not; b-a<=0 would need b<=a. Check a few:
        let mut s = DiffLogicSolver::new(true);
        let a = term(1);
        let b = term(2);
        s.add_leq(a, b, Rational64::from_integer(0), term(10)); // a <= b
        s.check();
        // b - a <= 0 is NOT entailed (a<=b does not imply b<=a).
        assert_eq!(
            s.entailed_reason(b, a, Rational64::from_integer(0), false),
            None
        );
    }

    #[test]
    fn entailed_reason_equality_bidirectional() {
        // Equality a=b is fed as two edges (a-b<=0 and b-a<=0). Then both
        // a-b<=0 and b-a<=0 are entailed, and a-b<=-1 / b-a<=-1 are NOT.
        let mut s = DiffLogicSolver::new(true);
        let a = term(1);
        let b = term(2);
        s.add_leq(a, b, Rational64::from_integer(0), term(10));
        s.add_leq(b, a, Rational64::from_integer(0), term(11));
        s.check();
        assert!(
            s.entailed_reason(a, b, Rational64::from_integer(0), false)
                .is_some()
        );
        assert!(
            s.entailed_reason(b, a, Rational64::from_integer(0), false)
                .is_some()
        );
        assert_eq!(
            s.entailed_reason(a, b, Rational64::from_integer(-1), false),
            None
        );
    }
}
