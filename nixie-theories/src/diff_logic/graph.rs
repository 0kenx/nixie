//! Constraint graph for difference logic — array-based adjacency.
//!
//! Represents difference constraints as a weighted directed graph:
//! - Each variable is a node (`DiffVar`, a dense `u32` index).
//! - Constraint `x - y ≤ c` is the edge `(y → x)` with weight `c`.
//!
//! This is a rewrite of the original hash-map-backed graph. The adjacency
//! lists live in a flat `Vec<Vec<DiffEdge>>` indexed by node id (Z3's
//! `dl_graph` layout: `vector<edge_id_vector> m_out_edges`), so hot-path
//! traversals (`BellmanFord`/`Spfa`/seeded incremental checks) index memory
//! instead of hashing — on the QF_IDL families the removed `HashMap`
//! operations were >50% of solver runtime.
//!
//! Term↔node interning stays in `FxHashMap`s (cold path: one lookup per
//! asserted atom, not per relax step).

#[allow(unused_imports)]
use crate::prelude::*;
use nixie_core::ast::TermId;
use num_rational::Rational64;

/// Variable identifier in difference logic.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct DiffVar(pub u32);

impl DiffVar {
    /// Virtual source node for Bellman-Ford.
    pub const SOURCE: Self = Self(u32::MAX);

    /// Create a new variable.
    pub const fn new(id: u32) -> Self {
        Self(id)
    }

    /// Get the variable ID.
    pub const fn id(self) -> u32 {
        self.0
    }

    /// Check if this is the source node.
    pub fn is_source(self) -> bool {
        self == Self::SOURCE
    }
}

impl From<u32> for DiffVar {
    fn from(id: u32) -> Self {
        Self(id)
    }
}

/// Type of difference constraint.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum ConstraintType {
    /// x - y ≤ c (non-strict)
    LeqConst,
    /// x - y < c (strict) - converted to ≤ (c - ε); for integers, ≤ (c - 1)
    LtConst,
}

/// A difference constraint: x - y ≤ c or x - y < c.
#[derive(Debug, Clone)]
pub struct DiffConstraint {
    /// Left variable (x in x - y ≤ c).
    pub x: DiffVar,
    /// Right variable (y in x - y ≤ c).
    pub y: DiffVar,
    /// Constant bound (c).
    pub bound: Rational64,
    /// Constraint type (≤ or <).
    pub constraint_type: ConstraintType,
    /// Original term ID for explanations.
    pub origin: TermId,
    /// Decision level when added.
    pub level: u32,
    /// Whether this is asserted (not just propagated).
    pub asserted: bool,
}

impl DiffConstraint {
    /// Create a new constraint x - y ≤ c.
    pub fn new_leq(x: DiffVar, y: DiffVar, bound: Rational64, origin: TermId) -> Self {
        Self {
            x,
            y,
            bound,
            constraint_type: ConstraintType::LeqConst,
            origin,
            level: 0,
            asserted: false,
        }
    }

    /// Create a new constraint x - y < c.
    pub fn new_lt(x: DiffVar, y: DiffVar, bound: Rational64, origin: TermId) -> Self {
        Self {
            x,
            y,
            bound,
            constraint_type: ConstraintType::LtConst,
            origin,
            level: 0,
            asserted: false,
        }
    }

    /// Effective bound: strict `< c` becomes `≤ c - 1` over the integers
    /// (the caller keeps `< c` over the reals; real strictness is tracked by
    /// [`DiffEdge::strict`] and handled by the search algorithms).
    pub fn effective_bound(&self, is_integer: bool) -> Rational64 {
        match self.constraint_type {
            ConstraintType::LeqConst => self.bound,
            ConstraintType::LtConst => {
                if is_integer {
                    self.bound - Rational64::from_integer(1)
                } else {
                    self.bound
                }
            }
        }
    }
}

/// Edge in the constraint graph.
#[derive(Debug, Clone)]
pub struct DiffEdge {
    /// Source node (`y` in the constraint `x - y ≤ c`).
    pub from: DiffVar,
    /// Target node (`x` in the constraint `x - y ≤ c`).
    pub to: DiffVar,
    /// Edge weight (effective `c`).
    pub weight: Rational64,
    /// Constraint index for explanation.
    pub constraint_idx: usize,
    /// Whether this is a strict edge (real arithmetic only).
    pub strict: bool,
}

impl DiffEdge {
    /// Create a new edge.
    pub fn new(from: DiffVar, to: DiffVar, weight: Rational64, constraint_idx: usize) -> Self {
        Self {
            from,
            to,
            weight,
            constraint_idx,
            strict: false,
        }
    }

    /// Create a new strict edge.
    pub fn new_strict(
        from: DiffVar,
        to: DiffVar,
        weight: Rational64,
        constraint_idx: usize,
    ) -> Self {
        Self {
            from,
            to,
            weight,
            constraint_idx,
            strict: true,
        }
    }
}

/// Constraint graph for difference logic (array-based adjacency).
#[derive(Debug, Clone)]
pub struct ConstraintGraph {
    /// Number of real (non-source) variables.
    num_vars: u32,
    /// Term → node.
    var_to_node: FxHashMap<TermId, DiffVar>,
    /// Node → term.
    node_to_var: Vec<TermId>,
    /// Adjacency: `edges[node.0]` lists outgoing edges; `edges[SOURCE slot]`
    /// is the virtual source's 0-weight edges.
    edges: Vec<Vec<DiffEdge>>,
    /// All constraints (append-only; popped by truncation).
    constraints: Vec<DiffConstraint>,
    /// Constraint-count scope marks: `constraint_marks[level]` = number of
    /// constraints live at `level` (the pop boundary).
    constraint_marks: Vec<usize>,
    /// Current decision level.
    current_level: u32,
    /// Whether this is integer arithmetic.
    is_integer: bool,
}

impl ConstraintGraph {
    /// Create a new constraint graph.
    pub fn new(is_integer: bool) -> Self {
        Self {
            num_vars: 0,
            var_to_node: FxHashMap::default(),
            node_to_var: Vec::new(),
            // Slot 0 is reserved for the virtual source; real nodes start at 1.
            edges: vec![Vec::new()],
            constraints: Vec::new(),
            constraint_marks: vec![0],
            current_level: 0,
            is_integer,
        }
    }

    /// Get or create a node for a term.
    pub fn get_or_create_var(&mut self, term: TermId) -> DiffVar {
        if let Some(&var) = self.var_to_node.get(&term) {
            return var;
        }
        let var = DiffVar::new(self.num_vars);
        self.num_vars += 1;
        self.var_to_node.insert(term, var);
        self.node_to_var.push(term);
        self.edges.push(Vec::new());
        // Edge source → node with weight 0 anchors the virtual-source
        // Bellman-Ford (every node reachable at 0).
        self.edges[0].push(DiffEdge::new(
            DiffVar::SOURCE,
            var,
            Rational64::from_integer(0),
            0,
        ));
        var
    }

    /// Get the term for a variable.
    pub fn get_term(&self, var: DiffVar) -> Option<TermId> {
        if var.is_source() {
            return None;
        }
        self.node_to_var.get(var.id() as usize).copied()
    }

    /// Get the variable for a term.
    pub fn get_var(&self, term: TermId) -> Option<DiffVar> {
        self.var_to_node.get(&term).copied()
    }

    /// Add a constraint `x - y ≤ c`: creates the edge `(y → x)`.
    pub fn add_constraint(&mut self, constraint: DiffConstraint) -> usize {
        let idx = self.constraints.len();
        let weight = constraint.effective_bound(self.is_integer);
        let edge = if constraint.constraint_type == ConstraintType::LtConst && !self.is_integer {
            DiffEdge::new_strict(constraint.y, constraint.x, weight, idx)
        } else {
            DiffEdge::new(constraint.y, constraint.x, weight, idx)
        };
        let slot = self.edge_slot(constraint.y);
        self.edges[slot].push(edge);

        while self.constraint_marks.len() <= self.current_level as usize {
            self.constraint_marks.push(self.constraints.len());
        }
        self.constraint_marks[self.current_level as usize] = idx + 1;

        self.constraints.push(constraint);
        idx
    }

    /// Adjacency slot of a node (source maps to slot 0, real nodes to `id+1`).
    #[inline]
    fn edge_slot(&self, v: DiffVar) -> usize {
        if v.is_source() {
            0
        } else {
            v.id() as usize + 1
        }
    }

    /// Get all edges from a node.
    #[inline]
    pub fn get_edges(&self, from: DiffVar) -> impl Iterator<Item = &DiffEdge> {
        self.edges[self.edge_slot(from)].iter()
    }

    /// Get all edges in the graph.
    pub fn all_edges(&self) -> impl Iterator<Item = &DiffEdge> {
        self.edges.iter().flatten()
    }

    /// Get a constraint by index.
    pub fn get_constraint(&self, idx: usize) -> Option<&DiffConstraint> {
        self.constraints.get(idx)
    }

    /// Get all constraints.
    pub fn constraints(&self) -> &[DiffConstraint] {
        &self.constraints
    }

    /// Number of variables (excluding source).
    pub fn num_vars(&self) -> u32 {
        self.num_vars
    }

    /// Number of constraints.
    pub fn num_constraints(&self) -> usize {
        self.constraints.len()
    }

    /// All variable nodes.
    pub fn vars(&self) -> impl Iterator<Item = DiffVar> + '_ {
        (0..self.num_vars).map(DiffVar::new)
    }

    /// All nodes including source.
    pub fn nodes(&self) -> impl Iterator<Item = DiffVar> + '_ {
        core::iter::once(DiffVar::SOURCE).chain(self.vars())
    }

    /// Push a new decision level.  The new level's rollback mark starts at
    /// the CURRENT constraint count — the exact boundary a pop to this level
    /// must restore.  (It previously started at `0`, so popping back to a
    /// level that had seen no constraint additions truncated the constraint
    /// list to zero — silently discarding every lower-level fact, up to and
    /// including level-0 units.  Under-constraining only: the solver missed
    /// conflicts, and once the sparse engine could own a verdict (the pure
    /// QF_IDL route) that became a false `sat` on `qlock-4-10-11.base`.)
    pub fn push(&mut self) {
        self.current_level += 1;
        self.constraint_marks.push(self.constraints.len());
    }

    /// Pop to a previous decision level: truncates the constraint vector
    /// and every adjacency list back to the boundary recorded at the
    /// surviving level. Adjacency lists are append-ordered by constraint
    /// index and every edge carries its constraint index, so a retain pass
    /// per touched slot is exact; the common case (only the tail slot of a
    /// few nodes grew) costs a single `last()` probe per slot.
    pub fn pop(&mut self, levels: u32) {
        if levels == 0 {
            return;
        }
        let target_level = self.current_level.saturating_sub(levels);
        let keep = self.constraint_marks[target_level as usize];
        self.constraints.truncate(keep);
        for edges in &mut self.edges {
            if let Some(last) = edges.last()
                && last.constraint_idx >= keep
            {
                edges.retain(|e| e.constraint_idx < keep);
            }
        }
        self.constraint_marks.truncate(target_level as usize + 1);
        self.current_level = target_level;
    }

    /// Current decision level.
    pub fn current_level(&self) -> u32 {
        self.current_level
    }

    /// Is integer arithmetic?
    pub fn is_integer(&self) -> bool {
        self.is_integer
    }

    /// Clear all constraints (keeping variables).
    pub fn clear(&mut self) {
        self.constraints.clear();
        self.constraint_marks = vec![0];
        self.current_level = 0;
        // Keep only the source's anchor edges.
        for (slot, edges) in self.edges.iter_mut().enumerate() {
            if slot == 0 {
                edges.truncate(self.num_vars as usize);
            } else {
                edges.clear();
            }
        }
    }

    /// Full reset including variables.
    pub fn reset(&mut self) {
        *self = Self::new(self.is_integer);
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_constraint_graph_creation() {
        let graph = ConstraintGraph::new(true);
        assert_eq!(graph.num_vars(), 0);
        assert!(graph.is_integer());
    }

    #[test]
    fn test_variable_creation() {
        let mut graph = ConstraintGraph::new(true);
        let term1 = TermId::from(1u32);
        let term2 = TermId::from(2u32);

        let var1 = graph.get_or_create_var(term1);
        let var2 = graph.get_or_create_var(term2);

        assert_eq!(graph.num_vars(), 2);
        assert_ne!(var1, var2);
        assert_eq!(graph.get_var(term1), Some(var1));
        assert_eq!(graph.get_term(var1), Some(term1));
    }

    #[test]
    fn test_add_constraint() {
        let mut graph = ConstraintGraph::new(true);
        let term_x = TermId::from(1u32);
        let term_y = TermId::from(2u32);
        let origin = TermId::from(100u32);

        let x = graph.get_or_create_var(term_x);
        let y = graph.get_or_create_var(term_y);

        // Add constraint x - y ≤ 5
        let constraint = DiffConstraint::new_leq(x, y, Rational64::from_integer(5), origin);
        let idx = graph.add_constraint(constraint);

        assert_eq!(graph.num_constraints(), 1);
        assert!(graph.get_constraint(idx).is_some());

        // Check that edge y → x exists with weight 5
        let edges: Vec<_> = graph.get_edges(y).collect();
        assert!(!edges.is_empty());
        assert_eq!(edges[0].to, x);
        assert_eq!(edges[0].weight, Rational64::from_integer(5));
    }

    #[test]
    fn test_strict_constraint_integer() {
        let mut graph = ConstraintGraph::new(true);
        let term_x = TermId::from(1u32);
        let term_y = TermId::from(2u32);
        let origin = TermId::from(100u32);

        let x = graph.get_or_create_var(term_x);
        let y = graph.get_or_create_var(term_y);

        // Add constraint x - y < 5 (becomes x - y ≤ 4 for integers)
        let constraint = DiffConstraint::new_lt(x, y, Rational64::from_integer(5), origin);
        let effective = constraint.effective_bound(true);

        assert_eq!(effective, Rational64::from_integer(4));
    }

    #[test]
    fn test_push_pop() {
        let mut graph = ConstraintGraph::new(true);
        let term_x = TermId::from(1u32);
        let term_y = TermId::from(2u32);
        let origin = TermId::from(100u32);

        let x = graph.get_or_create_var(term_x);
        let y = graph.get_or_create_var(term_y);

        // Level 0: add constraint x - y ≤ 5
        let constraint1 = DiffConstraint::new_leq(x, y, Rational64::from_integer(5), origin);
        graph.add_constraint(constraint1);
        assert_eq!(graph.num_constraints(), 1);

        // Push to level 1
        graph.push();
        assert_eq!(graph.current_level(), 1);

        // Level 1: add constraint x - y ≤ 3
        let constraint2 = DiffConstraint::new_leq(x, y, Rational64::from_integer(3), origin);
        graph.add_constraint(constraint2);
        assert_eq!(graph.num_constraints(), 2);

        // Pop to level 0
        graph.pop(1);
        assert_eq!(graph.current_level(), 0);
        assert_eq!(graph.num_constraints(), 1);

        // Edge for constraint2 should be removed
        let edges: Vec<_> = graph
            .get_edges(y)
            .filter(|e| e.constraint_idx == 1)
            .collect();
        assert!(edges.is_empty());
        // Edge for constraint1 survives.
        assert_eq!(graph.get_edges(y).count(), 1);
    }

    #[test]
    fn source_edges_anchored() {
        let mut graph = ConstraintGraph::new(true);
        let t1 = TermId::from(1u32);
        let t2 = TermId::from(2u32);
        graph.get_or_create_var(t1);
        graph.get_or_create_var(t2);
        // Every node has a 0-weight anchor from SOURCE.
        assert_eq!(graph.get_edges(DiffVar::SOURCE).count(), 2);
        assert!(
            graph
                .get_edges(DiffVar::SOURCE)
                .all(|e| e.weight == Rational64::from_integer(0))
        );
    }
}
