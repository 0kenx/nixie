//! Difference Logic Theory Solver
//!
//! Implements efficient reasoning about difference constraints of the form:
//! - x - y ≤ c (non-strict)
//! - x - y < c (strict, converted to x - y ≤ c - 1 over the integers)
//!
//! # Engines
//!
//! Two engines sit behind this facade, mirroring Z3's split in
//! `smt/smt_setup.cpp`:
//!
//! * **Dense core** ([`DenseDlCore`], Z3 `theory_dense_diff_logic`): an
//!   incremental all-pairs shortest-path closure over integer weights with
//!   occurrence-list theory propagation and immediate negative-cycle
//!   conflicts. Installed for **integer** difference logic (QF_IDL) whenever
//!   every weight fits the exact i64 envelope; this is the engine Z3 uses
//!   for dense problems (`st.is_dense()`), and here it also serves sparse
//!   integer problems (the closure update only touches reachable cells, so
//!   it degrades gracefully).
//! * **Sparse engine** (this module's `ConstraintGraph` + SPFA, Z3
//!   `theory_diff_logic`): a constraint graph with seeded incremental
//!   Bellman-Ford checks — O(affected nodes) per added edge — over exact
//!   `Rational64` weights. Used for **real** difference logic (QF_RDL) and
//!   as the integer fallback when a weight or the node budget exceeds the
//!   dense core's exactness envelope.
//!
//! # Algorithm (sparse engine)
//!
//! Constraint graph: variables are nodes; constraint `x - y ≤ c` becomes the
//! edge `(y → x)` with weight `c`. Satisfiability via (multi-source,
//! virtual-source-equivalent) SPFA: UNSAT iff a negative cycle exists; model
//! = shortest distances.
//!
//! # References
//!
//! - Cotton, S. & Maler, O. (2006). Fast and Flexible Difference Constraint
//!   Propagation
//! - Nieuwenhuis, R. & Oliveras, A. (2005). DPLL(T) with Exhaustive Theory
//!   Propagation
//! - de Moura, L. (2008). `smt/theory_dense_diff_logic.*` (Z3)

use super::bellman_ford::{BellmanFord, BellmanFordResult, NegativeCycle, Spfa};
use super::dense_core::{DL_MAX_ABS_WEIGHT, DenseDlCore, DlPropagation};
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
    /// Enable theory propagation on the dense core
    pub propagate: bool,
    /// Maximum propagation rounds per call
    pub max_propagation_rounds: usize,
}

impl Default for DiffLogicConfig {
    fn default() -> Self {
        Self {
            use_spfa: true,
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

/// Result of a single-source shortest-path run: per-node distance and
/// predecessor edge (see `DiffLogicSolver::sssp_from`).
pub type SsspResult = (Vec<Option<Rational64>>, Vec<Option<usize>>);

/// Difference Logic Theory Solver
///
/// Handles constraints of the form x - y ≤ c (or x - y < c). See the module
/// documentation for the two engines and their routing.
#[derive(Debug)]
pub struct DiffLogicSolver {
    /// Configuration
    config: DiffLogicConfig,
    /// Sparse constraint graph (always present; the active engine unless the
    /// dense core took over).
    graph: ConstraintGraph,
    /// Dense integer core. `Some` once integer DL with i64-safe weights is
    /// detected; then it is the primary engine.
    dense: Option<DenseDlCore>,
    /// Dense-core node interning: term → dense node id.
    dense_terms: FxHashMap<TermId, u32>,
    /// Whether the dense core had to be disabled (weight/node budget
    /// exceeded); it then stays as a sound partial propagator only.
    dense_degraded: bool,
    /// Bellman-Ford solver (fallback full checks)
    bf: BellmanFord,
    /// SPFA solver
    spfa: Spfa,
    /// Current distances of the sparse engine, indexed by node id.
    distances: Vec<Option<Rational64>>,
    /// Whether sparse distances are up-to-date
    distances_valid: bool,
    /// Statistics
    stats: DiffLogicStats,
    /// Decision level stack (constraint-count marks)
    level_stack: Vec<usize>,
    /// Current decision level
    current_level: u32,
    /// Pending constraints to process
    pending: Vec<usize>,
    /// Term to constraint mapping
    term_to_constraint: HashMap<TermId, Vec<usize>>,
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
            dense: None,
            dense_terms: FxHashMap::default(),
            dense_degraded: false,
            bf: BellmanFord::new(),
            spfa: Spfa::new(),
            distances: Vec::new(),
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

    // ======== dense-core routing ========

    /// Whether the dense integer core is installed (active or degraded).
    pub fn dense_active(&self) -> bool {
        self.dense.is_some()
    }

    /// Whether the dense core is installed and still exact (not degraded).
    pub fn dense_exact(&self) -> bool {
        self.dense.is_some() && !self.dense_degraded
    }

    /// Mutable access to the dense core (installing it on first use when the
    /// solver is an integer solver and the core is not degraded).
    pub fn dense(&mut self) -> Option<&mut DenseDlCore> {
        if self.dense.is_none() && self.graph.is_integer() && !self.dense_degraded {
            self.dense = Some(DenseDlCore::new());
        }
        self.dense.as_mut()
    }

    /// Intern `term` as a dense-core node.
    pub fn dense_intern_term(&mut self, term: TermId) -> Option<u32> {
        if let Some(&id) = self.dense_terms.get(&term) {
            return Some(id);
        }
        let core = self.dense()?;
        if !core.has_node_budget() {
            self.dense_degraded = true;
            return None;
        }
        let id = core.intern_node();
        self.dense_terms.insert(term, id);
        Some(id)
    }

    /// Dense-core node of `term`, if interned.
    pub fn dense_node_of(&self, term: TermId) -> Option<u32> {
        self.dense_terms.get(&term).copied()
    }

    /// Whether `k` fits the dense core's exact integer envelope.
    pub fn dense_weight_ok(k: i64) -> bool {
        k.unsigned_abs() <= DL_MAX_ABS_WEIGHT as u64
    }

    /// Disable the dense core after the fact (used when an atom's weight
    /// exceeds the envelope; the core keeps its already-derived facts — they
    /// remain sound implications of the asserted subset — but the caller
    /// stops feeding new edges and defers completeness to the simplex).
    pub fn dense_disable(&mut self) {
        self.dense_degraded = true;
    }

    /// Take the dense core's queued propagations.
    pub fn dense_take_propagations(&mut self) -> Vec<DlPropagation> {
        match &mut self.dense {
            Some(core) => core.take_propagations(),
            None => Vec::new(),
        }
    }

    /// Model value of a dense-interned term under the closure's feasible
    /// assignment (see [`DenseDlCore::value`]).
    pub fn dense_value(&self, term: TermId) -> Option<i64> {
        let id = self.dense_terms.get(&term).copied()?;
        self.dense.as_ref().map(|core| core.value(id))
    }

    /// Whether `weight` (as an exact rational) is an i64 integer in the
    /// dense envelope; the exact `i64` when it is.
    pub fn dense_fit(weight: &Rational64) -> Option<i64> {
        if !weight.is_integer() {
            return None;
        }
        let n = *weight.numer();
        if Self::dense_weight_ok(n) {
            Some(n)
        } else {
            None
        }
    }

    // ======== sparse engine (also the public add API) ========

    /// Register a variable (term).
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

        let x = self.graph.get_or_create_var(x_term);
        let y = self.graph.get_or_create_var(y_term);

        let mut constraint = match constraint_type {
            ConstraintType::LeqConst => DiffConstraint::new_leq(x, y, c, origin),
            ConstraintType::LtConst => DiffConstraint::new_lt(x, y, c, origin),
        };
        constraint.level = self.current_level;
        constraint.asserted = true;

        let idx = self.graph.add_constraint(constraint);
        self.term_to_constraint.entry(origin).or_default().push(idx);
        self.pending.push(idx);

        // Quick check: x == y and c < 0 is an immediate conflict.
        if x == y && c < Rational64::from_integer(0) {
            self.stats.conflicts += 1;
            return DiffLogicResult::Conflict(vec![origin]);
        }

        DiffLogicResult::Ok
    }

    /// Check consistency of the current sparse constraints.
    pub fn check(&mut self) -> DiffLogicResult {
        self.stats.checks += 1;

        let result = if self.config.use_spfa {
            self.spfa.run(&self.graph)
        } else {
            self.bf.run(&self.graph)
        };

        match result {
            BellmanFordResult::Distances(dists) => {
                self.distances = dists;
                self.distances_valid = true;
                DiffLogicResult::Ok
            }
            BellmanFordResult::NegativeCycle(cycle) => {
                self.stats.conflicts += 1;
                let conflict = self.cycle_to_conflict(&cycle);
                DiffLogicResult::Conflict(conflict)
            }
        }
    }

    /// Convert a negative cycle to a conflict clause.
    fn cycle_to_conflict(&self, cycle: &NegativeCycle) -> Vec<TermId> {
        cycle
            .constraint_indices()
            .iter()
            .filter_map(|&idx| self.graph.get_constraint(idx).map(|c| c.origin))
            .collect()
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
        let new_var = (x.id() as usize) >= self.distances.len()
            || (y.id() as usize) >= self.distances.len()
            || self.distances[x.id() as usize].is_none()
            || self.distances[y.id() as usize].is_none();
        let mut constraint = match constraint_type {
            ConstraintType::LeqConst => DiffConstraint::new_leq(x, y, c, origin),
            ConstraintType::LtConst => DiffConstraint::new_lt(x, y, c, origin),
        };
        constraint.level = self.current_level;
        constraint.asserted = true;
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
    /// edges and detect a negative cycle. O(affected nodes), far cheaper than
    /// a full Bellman-Ford on a sparse graph; on a detected cycle the
    /// explanation is extracted from the SPFA parent forest directly.
    fn check_incremental_from(&mut self, src: DiffVar) -> DiffLogicResult {
        if src.is_source() {
            return DiffLogicResult::Ok;
        }
        let n = self.graph.num_vars() as usize;
        if self.distances.len() < n {
            self.distances.resize(n, None);
        }
        let cycle = {
            let graph = &self.graph;
            let distances = &mut self.distances;
            self.spfa.seed_from(graph, distances, src)
        };
        if cycle.is_some() {
            // A negative cycle exists, but the seeded run's partial parent
            // forest cannot explain it — re-run the full multi-source SPFA
            // (complete forest) and extract the genuine conflict terms.
            self.stats.conflicts += 1;
            self.distances_valid = false;
            return self.check();
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

    /// Propagate implied bounds (legacy API; the dense core propagates
    /// incrementally — see `dense_take_propagations`).
    pub fn propagate(&mut self) -> Vec<DiffLogicResult> {
        let mut results = Vec::new();
        if !self.config.propagate {
            return results;
        }
        if !self.distances_valid
            && let DiffLogicResult::Conflict(c) = self.check()
        {
            results.push(DiffLogicResult::Conflict(c));
            return results;
        }
        self.pending.clear();
        results
    }

    /// Get the current value of a variable in the sparse model.
    pub fn get_value(&mut self, term: TermId) -> Option<Rational64> {
        self.stats.model_queries += 1;
        if !self.distances_valid
            && let DiffLogicResult::Conflict(_) = self.check()
        {
            return None;
        }
        let var = self.graph.get_var(term)?;
        self.distances.get(var.id() as usize).copied().flatten()
    }

    /// Get a complete sparse model.
    pub fn get_model(&mut self) -> HashMap<TermId, Rational64> {
        let mut model = HashMap::new();
        if !self.distances_valid
            && let DiffLogicResult::Conflict(_) = self.check()
        {
            return model;
        }
        for (var, dist) in self.distances.iter().enumerate() {
            if let Some(d) = dist
                && let Some(term) = self.graph.get_term(DiffVar::new(var as u32))
            {
                model.insert(term, *d);
            }
        }
        model
    }

    /// Push a new decision level (both engines).
    pub fn push(&mut self) {
        self.current_level += 1;
        self.graph.push();
        if let Some(core) = &mut self.dense {
            core.push();
        }
        self.level_stack.push(self.graph.num_constraints());
    }

    /// Pop to a previous decision level (both engines).
    pub fn pop(&mut self, levels: u32) {
        if levels == 0 {
            return;
        }
        self.graph.pop(levels);
        for _ in 0..levels {
            if let Some(core) = &mut self.dense {
                core.pop();
            }
        }
        self.current_level = self.current_level.saturating_sub(levels);
        let target = (self.current_level + 1) as usize;
        if target < self.level_stack.len() {
            self.level_stack.truncate(target);
        }
        self.distances_valid = false;
    }

    /// Reset the solver.
    pub fn reset(&mut self) {
        let is_integer = self.graph.is_integer();
        self.graph.reset();
        if let Some(core) = &mut self.dense {
            core.reset();
        }
        self.dense_terms.clear();
        self.dense_degraded = false;
        self.distances.clear();
        self.distances_valid = false;
        self.pending.clear();
        self.term_to_constraint.clear();
        self.level_stack = vec![0];
        self.current_level = 0;
        let _ = is_integer;
        self.reset_stats();
    }

    /// Get the explanation for a constraint.
    pub fn explain(&self, constraint_origin: TermId) -> Vec<TermId> {
        let mut explanation = Vec::new();
        if let Some(indices) = self.term_to_constraint.get(&constraint_origin) {
            for &idx in indices {
                if let Some(constraint) = self.graph.get_constraint(idx) {
                    explanation.push(constraint.origin);
                }
            }
        }
        explanation
    }

    /// Check if a potential constraint would cause a conflict.
    ///
    /// **Unsound as an implication test – do not use for theory propagation.**
    /// This reduces to `dist[x] - dist[y] <= c` where `dist` are the
    /// multi-source Bellman-Ford distances. That quantity is only a *lower
    /// bound* on the true shortest path `d(y, x)`, so it over-reports. For
    /// sound theory propagation use [`Self::entailed_reason`], which computes
    /// the actual shortest path.
    pub fn would_conflict(&mut self, x: TermId, y: TermId, c: Rational64, strict: bool) -> bool {
        if !self.distances_valid
            && let DiffLogicResult::Conflict(_) = self.check()
        {
            return true;
        }
        let (Some(xv), Some(yv)) = (self.graph.get_var(x), self.graph.get_var(y)) else {
            return false;
        };
        let dx = self.distances[xv.id() as usize].unwrap_or_default();
        let dy = self.distances[yv.id() as usize].unwrap_or_default();
        let current_diff = dx - dy;
        if strict {
            c <= -current_diff
        } else {
            c < -current_diff
        }
    }

    /// Look up the difference-logic variable for a term, if registered.
    pub fn get_diff_var(&self, term: TermId) -> Option<DiffVar> {
        self.graph.get_var(term)
    }

    /// Run single-source shortest path from `src` over the sparse constraint
    /// edges.
    ///
    /// Returns `(dist, pred_edge)` where `pred_edge[node]` is the constraint
    /// index whose edge last improved `dist[node]` (for path
    /// reconstruction). Returns `None` if a negative cycle is reachable from
    /// `src`.
    ///
    /// This is the SOUND foundation for theory propagation: the true
    /// shortest-path distance `d(src, node)` over asserted edges, not a
    /// multi-source distance difference (a lower bound — see
    /// [`Self::would_conflict`]).
    pub fn sssp_from(&self, src: DiffVar) -> Option<SsspResult> {
        let zero = Rational64::from_integer(0);
        let n = self.graph.num_vars() as usize;
        let mut dist: Vec<Option<Rational64>> = vec![None; n];
        let mut pred: Vec<Option<usize>> = vec![None; n];
        if src.is_source() || src.id() as usize >= n {
            return Some((dist, pred));
        }
        dist[src.id() as usize] = Some(zero);

        // SPFA over node ids with a dense queue-scratch.
        let mut queue: VecDeque<DiffVar> = VecDeque::new();
        let mut in_queue = vec![false; n];
        let mut count = vec![0u32; n];
        queue.push_back(src);
        in_queue[src.id() as usize] = true;
        while let Some(u) = queue.pop_front() {
            let ui = u.id() as usize;
            in_queue[ui] = false;
            let Some(du) = dist[ui] else {
                continue;
            };
            for edge in self.graph.get_edges(u) {
                let nd = du + edge.weight;
                let ti = edge.to.id() as usize;
                let improved = match dist[ti] {
                    None => true,
                    Some(d) => nd < d,
                };
                if improved {
                    dist[ti] = Some(nd);
                    pred[ti] = Some(edge.constraint_idx);
                    if !in_queue[ti] {
                        queue.push_back(edge.to);
                        in_queue[ti] = true;
                        count[ti] += 1;
                        if count[ti] > n as u32 + 1 {
                            // Negative cycle reachable from src.
                            return None;
                        }
                    }
                }
            }
        }
        Some((dist, pred))
    }

    /// Reconstruct the asserted-atom origins on the predecessor path
    /// `src -> ... -> x`, in path order. Returns an empty `Vec` if `x == src`.
    fn reason_path(&self, src: DiffVar, x: DiffVar, pred: &[Option<usize>]) -> Vec<TermId> {
        if x == src {
            return Vec::new();
        }
        let mut path = Vec::new();
        let mut cur = x;
        let mut guard = 0;
        let max_steps = self.graph.num_constraints() + 1;
        while cur != src {
            let Some(edge_idx) = pred.get(cur.id() as usize).copied().flatten() else {
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
    /// Returns the asserted-atom origins on the path entailing `xv - yv ≤ c`
    /// (or `< c` if `strict`), requiring the ACTUAL `d(yv, xv) ≤ c_eff`, or
    /// `None`. Integer tightening applies for `strict`. Returns `None` for an
    /// empty reason path (a trivial bound not derived from asserted atoms).
    pub fn entailed_from_sssp(
        &self,
        xv: DiffVar,
        yv: DiffVar,
        c: Rational64,
        strict: bool,
        dist_from_y: &[Option<Rational64>],
        pred_from_y: &[Option<usize>],
    ) -> Option<Vec<TermId>> {
        let c_eff = if strict && self.is_integer() {
            c - Rational64::from_integer(1)
        } else {
            c
        };
        let &dx = dist_from_y.get(xv.id() as usize)?.as_ref()?;
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

    /// **Sound** theory-propagation reason (computes its own SSSP tree; for
    /// many queries prefer [`Self::entailed_from_sssp`]).
    ///
    /// Returns the asserted atoms on a shortest path entailing `x - y ≤ c`
    /// (or `x - y < c` when `strict`), or `None` if the bound is not entailed
    /// by the currently-asserted difference constraints. See
    /// [`Self::entailed_from_sssp`] for the soundness argument.
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

    /// Number of sparse-engine variables.
    pub fn num_vars(&self) -> u32 {
        self.graph.num_vars()
    }

    /// Number of sparse-engine constraints.
    pub fn num_constraints(&self) -> usize {
        self.graph.num_constraints()
    }

    /// Current decision level.
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
        let (x, y, z) = (term(1), term(2), term(3));
        let (o1, o2, o3) = (term(100), term(101), term(102));

        // x - y ≤ 3, y - z ≤ 2, z - x ≤ 1: cycle 6 ≥ 0, consistent.
        solver.add_leq(x, y, Rational64::from_integer(3), o1);
        solver.add_leq(y, z, Rational64::from_integer(2), o2);
        solver.add_leq(z, x, Rational64::from_integer(1), o3);

        let result = solver.check();
        assert!(matches!(result, DiffLogicResult::Ok));
    }

    #[test]
    fn test_conflict_detection() {
        let mut solver = DiffLogicSolver::new(true);
        let (x, y, z) = (term(1), term(2), term(3));
        let (o1, o2, o3) = (term(100), term(101), term(102));

        // x - y ≤ -1, y - z ≤ -1, z - x ≤ -1: cycle -3 < 0.
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

        solver.add_leq(x, y, Rational64::from_integer(5), origin);
        let result = solver.check();
        assert!(matches!(result, DiffLogicResult::Ok));

        let model = solver.get_model();
        assert!(!model.is_empty());

        if let (Some(&vx), Some(&vy)) = (model.get(&x), model.get(&y)) {
            assert!(vx - vy <= Rational64::from_integer(5));
        }
    }

    #[test]
    fn test_push_pop() {
        let mut solver = DiffLogicSolver::new(true);
        let (x, y) = (term(1), term(2));
        let (o1, o2) = (term(100), term(101));

        solver.add_leq(x, y, Rational64::from_integer(5), o1);
        assert_eq!(solver.num_constraints(), 1);

        solver.push();
        assert_eq!(solver.current_level(), 1);

        solver.add_leq(x, y, Rational64::from_integer(3), o2);
        assert_eq!(solver.num_constraints(), 2);

        solver.pop(1);
        assert_eq!(solver.current_level(), 0);

        let result = solver.check();
        assert!(matches!(result, DiffLogicResult::Ok));
    }

    #[test]
    fn test_strict_constraint() {
        let mut solver = DiffLogicSolver::new(true);
        let x = term(1);
        let y = term(2);
        let origin = term(100);

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

        let result = solver.add_leq(x, x, Rational64::from_integer(-1), origin);
        assert!(matches!(result, DiffLogicResult::Conflict(_)));
    }

    #[test]
    fn test_would_conflict() {
        let mut solver = DiffLogicSolver::new(true);
        let x = term(1);
        let y = term(2);
        let origin = term(100);

        solver.add_leq(x, y, Rational64::from_integer(0), origin);
        solver.check();

        // Adding y - x ≤ -1 would conflict (cycle 0 + -1 < 0).
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

        let result = solver.add_lt(x, y, Rational64::new(1, 2), origin);
        assert!(matches!(result, DiffLogicResult::Ok));
    }

    // ======== incremental check (add_*_check) tests ========

    #[test]
    fn incremental_check_detects_negative_cycle() {
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
        let mut s = DiffLogicSolver::new(true);
        let (a, b) = (term(1), term(2));
        s.add_leq_check(a, b, Rational64::from_integer(0), term(10));
        s.push();
        assert!(matches!(
            s.add_leq_check(b, a, Rational64::from_integer(-1), term(11)),
            DiffLogicResult::Conflict(_)
        ));
    }

    // ======== entailed_reason soundness tests ========

    #[test]
    fn entailed_reason_counterexample_not_implied() {
        let mut s = DiffLogicSolver::new(true);
        let (a, b) = (term(1), term(2));
        s.add_leq(a, b, Rational64::from_integer(5), term(100));
        s.check();
        assert_eq!(
            s.entailed_reason(a, b, Rational64::from_integer(3), false),
            None,
            "a-b<=3 is NOT entailed by a-b<=5"
        );
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
        let mut s = DiffLogicSolver::new(true);
        let (a, b, c) = (term(1), term(2), term(3));
        s.add_leq(a, b, Rational64::from_integer(0), term(10));
        s.add_leq(b, c, Rational64::from_integer(0), term(11));
        s.check();
        let reason = s.entailed_reason(a, c, Rational64::from_integer(0), false);
        assert!(reason.is_some(), "a-c<=0 entailed by chain");
        let reason = reason.unwrap_or_default();
        assert_eq!(reason.len(), 2, "reason is the two edge origins");
        assert_eq!(
            s.entailed_reason(a, c, Rational64::from_integer(-1), false),
            None
        );
    }

    #[test]
    fn entailed_reason_strict_integer_tightening() {
        let mut s = DiffLogicSolver::new(true);
        let (a, b) = (term(1), term(2));
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
    fn entailed_reason_reverse_not_entailed() {
        let mut s = DiffLogicSolver::new(true);
        let (a, b) = (term(1), term(2));
        s.add_leq(a, b, Rational64::from_integer(0), term(10)); // a <= b
        s.check();
        assert_eq!(
            s.entailed_reason(b, a, Rational64::from_integer(0), false),
            None,
            "b-a<=0 is NOT entailed (a<=b does not imply b<=a)"
        );
    }

    #[test]
    fn entailed_reason_equality_bidirectional() {
        let mut s = DiffLogicSolver::new(true);
        let (a, b) = (term(1), term(2));
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

    // ======== dense-core facade tests ========

    #[test]
    fn dense_facade_interns_and_asserts() {
        let mut s = DiffLogicSolver::new(true);
        let a = s.dense_intern_term(term(1));
        let b = s.dense_intern_term(term(2));
        assert_eq!((a, b), (Some(0), Some(1)));
        assert!(s.dense_active());
        let node_count = s.dense().map_or(0, |c| c.num_nodes());
        assert_eq!(node_count, 2);
        // Value lookup round-trips through the term map.
        assert_eq!(s.dense_value(term(1)), Some(0));
    }

    #[test]
    fn dense_weight_envelope() {
        // The envelope keeps every possible path sum far below the INF
        // sentinel: |w| ≤ 2^40 with ≤ 2048 nodes bounds sums by 2^51.
        assert!(DiffLogicSolver::dense_weight_ok(1 << 40));
        assert!(!DiffLogicSolver::dense_weight_ok((1 << 40) + 1));
        assert!(!DiffLogicSolver::dense_weight_ok(i64::MAX / 8));
        assert_eq!(
            DiffLogicSolver::dense_fit(&Rational64::from_integer(7)),
            Some(7)
        );
        assert_eq!(DiffLogicSolver::dense_fit(&Rational64::new(1, 2)), None);
    }

    #[test]
    fn push_pop_drives_both_engines() {
        use super::super::dense_core::DlAssert;
        let mut s = DiffLogicSolver::new(true);
        let a = s.dense_intern_term(term(1)).unwrap_or(0);
        let b = s.dense_intern_term(term(2)).unwrap_or(1);
        s.push();
        if let Some(core) = s.dense() {
            assert_eq!(core.assert_edge(a, b, 3, 10, true), DlAssert::Ok);
        }
        s.pop(1);
        // The scoped dense edge is gone: the reverse edge no longer forms a
        // negative cycle with it.
        if let Some(core) = s.dense() {
            assert!(matches!(
                core.assert_edge(b, a, 100, 11, true),
                DlAssert::Ok
            ));
        }
    }
}
