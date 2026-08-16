//! Bellman-Ford / SPFA for difference logic — array-based.
//!
//! Multi-source shortest paths over the constraint graph with negative-cycle
//! detection. All per-node state lives in flat `Vec`s indexed by `DiffVar`
//! id (Z3's `dl_graph` layout), so relax steps index memory instead of
//! hashing. The virtual source of the original design is subsumed by
//! initialising every node at distance 0 (equivalent to a 0-weight edge from
//! a virtual source to each node).

use super::graph::{ConstraintGraph, DiffEdge, DiffVar};
#[allow(unused_imports)]
use crate::prelude::*;
use num_rational::Rational64;

/// A negative cycle detected in the constraint graph.
#[derive(Debug, Clone)]
pub struct NegativeCycle {
    /// Edge indices forming the cycle.
    pub edges: Vec<usize>,
    /// Total weight of the cycle (negative).
    pub total_weight: Rational64,
}

impl NegativeCycle {
    /// Create a new negative cycle.
    pub fn new(edges: Vec<usize>, total_weight: Rational64) -> Self {
        Self {
            edges,
            total_weight,
        }
    }

    /// Get the constraint indices in the cycle.
    pub fn constraint_indices(&self) -> &[usize] {
        &self.edges
    }
}

/// Result of a Bellman-Ford computation: per-node distances indexed by node
/// id (`None` = unreachable), or a negative cycle.
#[derive(Debug, Clone)]
pub enum BellmanFordResult {
    /// Shortest paths found (no negative cycle).
    Distances(Vec<Option<Rational64>>),
    /// Negative cycle detected.
    NegativeCycle(NegativeCycle),
}

/// Bellman-Ford algorithm: `|V|` relaxation passes over all edges.
#[derive(Debug, Default)]
pub struct BellmanFord {
    /// Per-node distance (index = node id).
    distances: Vec<Option<Rational64>>,
    /// Per-node parent edge (index = node id).
    parent_edge: Vec<Option<usize>>,
}

impl BellmanFord {
    /// Create a new Bellman-Ford solver.
    pub fn new() -> Self {
        Self::default()
    }

    /// Run multi-source Bellman-Ford (every node starts at 0).
    pub fn run(&mut self, graph: &ConstraintGraph) -> BellmanFordResult {
        let n = graph.num_vars() as usize;
        self.distances = vec![Some(Rational64::from_integer(0)); n];
        self.parent_edge = vec![None; n];

        // Relax edges up to |V| times.
        for _ in 0..n.saturating_sub(1) {
            let mut changed = false;
            for edge in graph.all_edges() {
                if edge.from.is_source() {
                    continue; // virtual-source anchors are implicit (all-0 init)
                }
                if let Some(dist_from) = self.distances[edge.from.id() as usize] {
                    let new_dist = dist_from + edge.weight;
                    let improved = match self.distances[edge.to.id() as usize] {
                        None => true,
                        Some(d) => new_dist < d,
                    };
                    if improved {
                        let ti = edge.to.id() as usize;
                        self.distances[ti] = Some(new_dist);
                        self.parent_edge[ti] = Some(edge.constraint_idx);
                        changed = true;
                    }
                }
            }
            if !changed {
                break;
            }
        }

        // One more pass: any further improvement exposes a negative cycle.
        for edge in graph.all_edges() {
            if edge.from.is_source() {
                continue;
            }
            if let Some(dist_from) = self.distances[edge.from.id() as usize] {
                let new_dist = dist_from + edge.weight;
                if let Some(dist_to) = self.distances[edge.to.id() as usize]
                    && new_dist < dist_to
                {
                    let cycle =
                        extract_negative_cycle(graph, &self.parent_edge, edge.to, Some(edge));
                    return BellmanFordResult::NegativeCycle(cycle);
                }
            }
        }

        BellmanFordResult::Distances(self.distances.clone())
    }
}

/// SPFA (Shortest Path Faster Algorithm) — queue-driven Bellman-Ford.
#[derive(Debug, Default)]
pub struct Spfa {
    /// Per-node distance (index = node id).
    distances: Vec<Option<Rational64>>,
    /// Per-node parent edge (index = node id).
    parent_edge: Vec<Option<usize>>,
    /// Per-node in-queue flag.
    in_queue: Vec<bool>,
    /// Per-node enqueue count (negative-cycle witness).
    count: Vec<u32>,
    /// Node queue.
    queue: VecDeque<DiffVar>,
}

impl Spfa {
    /// Create a new SPFA solver.
    pub fn new() -> Self {
        Self::default()
    }

    /// Run multi-source SPFA (every node starts at 0).
    pub fn run(&mut self, graph: &ConstraintGraph) -> BellmanFordResult {
        let n = graph.num_vars() as usize;
        self.distances = vec![Some(Rational64::from_integer(0)); n];
        self.parent_edge = vec![None; n];
        self.in_queue = vec![false; n];
        self.count = vec![0; n];
        self.queue.clear();
        for i in 0..n {
            let v = DiffVar::new(i as u32);
            self.queue.push_back(v);
            self.in_queue[i] = true;
            self.count[i] = 1;
        }

        if let Some(cycle_node) = self.spfa_loop(graph, n) {
            let trigger = self
                .parent_edge
                .get(cycle_node.id() as usize)
                .copied()
                .flatten()
                .and_then(|idx| edge_instance(graph, idx));
            let cycle = extract_negative_cycle(graph, &self.parent_edge, cycle_node, trigger);
            return BellmanFordResult::NegativeCycle(cycle);
        }
        BellmanFordResult::Distances(self.distances.clone())
    }

    /// The SPFA core loop over the pre-seeded queue. Returns the id of a
    /// node known to lie on a negative cycle, if one was detected.
    fn spfa_loop(&mut self, graph: &ConstraintGraph, n: usize) -> Option<DiffVar> {
        while let Some(u) = self.queue.pop_front() {
            let ui = u.id() as usize;
            self.in_queue[ui] = false;
            let Some(du) = self.distances[ui] else {
                continue;
            };
            for edge in graph.get_edges(u) {
                if edge.from.is_source() {
                    continue;
                }
                let new_dist = du + edge.weight;
                let ti = edge.to.id() as usize;
                let improved = match self.distances[ti] {
                    None => true,
                    Some(d) => new_dist < d,
                };
                if improved {
                    self.distances[ti] = Some(new_dist);
                    self.parent_edge[ti] = Some(edge.constraint_idx);
                    if !self.in_queue[ti] {
                        self.queue.push_back(edge.to);
                        self.in_queue[ti] = true;
                        self.count[ti] += 1;
                        // A node enqueued more than |V| times lies on (or is
                        // reachable from) a negative cycle.
                        if self.count[ti] > n as u32 + 1 {
                            return Some(edge.to);
                        }
                    }
                }
            }
        }
        None
    }

    /// Seeded incremental check: given the cached multi-source `distances`
    /// (indexed by node id), relax from `src` only (the just-added edge's
    /// source), updating `distances` in place. Returns `Some(())` when a
    /// negative cycle was detected — the caller must then re-run the full
    /// multi-source SPFA to extract the conflict (this run's parent forest
    /// is partial and cannot explain the cycle).
    pub fn seed_from(
        &mut self,
        graph: &ConstraintGraph,
        distances: &mut Vec<Option<Rational64>>,
        src: DiffVar,
    ) -> Option<()> {
        let n = graph.num_vars() as usize;
        if src.is_source() || src.id() as usize >= n {
            return None;
        }
        if distances.len() < n {
            distances.resize(n, None);
        }
        self.distances = core::mem::take(distances);
        self.parent_edge = vec![None; n];
        self.in_queue = vec![false; n];
        self.count = vec![0; n];
        self.queue.clear();
        // A source with no cached distance has never been touched by a full
        // check; HEAD's seeded check skipped it entirely (the distances map
        // held no entry), and seeding it at 0 here changes which cycles the
        // incremental pass can see.  Keep the historical behaviour: no
        // distance, no seeded run (the caller's full check covers it).
        if self.distances[src.id() as usize].is_none() {
            *distances = core::mem::take(&mut self.distances);
            return None;
        }
        self.queue.push_back(src);
        self.in_queue[src.id() as usize] = true;
        self.count[src.id() as usize] = 1;

        let cycle = self.spfa_loop(graph, n);
        *distances = core::mem::take(&mut self.distances);
        // The seeded run's parent forest is PARTIAL (only edges relaxed in
        // this run have parents), so a detected cycle cannot be extracted
        // from it: the cycle spans edges asserted in earlier runs.  Signal
        // the cycle to the caller, which re-runs the full multi-source SPFA
        // — whose forest is complete — to extract a genuine explanation.
        cycle.map(|_| ())
    }
}

/// Any live edge instance of constraint `idx` (edges of one constraint share
/// weight; only the indices matter for the cycle explanation).
fn edge_instance(graph: &ConstraintGraph, idx: usize) -> Option<&DiffEdge> {
    graph.all_edges().find(|e| e.constraint_idx == idx)
}

/// Extract a negative cycle from the parent forest, starting from a node
/// known to lie on (or be improved by) a negative cycle. `trigger` (when
/// known) is a fallback witness edge for the degenerate no-parent case.
fn extract_negative_cycle(
    graph: &ConstraintGraph,
    parent_edge: &[Option<usize>],
    start: DiffVar,
    trigger: Option<&DiffEdge>,
) -> NegativeCycle {
    let n = graph.num_vars() as usize;
    // Walk back n steps from `start` to land inside the cycle.
    let mut current = start;
    for _ in 0..=n {
        match parent_edge.get(current.id() as usize).copied().flatten() {
            Some(edge_idx) => {
                if let Some(constraint) = graph.get_constraint(edge_idx) {
                    current = constraint.y;
                } else {
                    break;
                }
            }
            None => break,
        }
    }

    // Collect the cycle by following parent edges until we return.
    let cycle_start = current;
    let mut cycle_edges = Vec::new();
    let mut total_weight = Rational64::from_integer(0);
    while let Some(edge_idx) = parent_edge.get(current.id() as usize).copied().flatten()
        && let Some(constraint) = graph.get_constraint(edge_idx)
    {
        cycle_edges.push(edge_idx);
        total_weight += constraint.effective_bound(graph.is_integer());
        current = constraint.y;
        if current == cycle_start && !cycle_edges.is_empty() {
            break;
        }
        if cycle_edges.len() > n + 1 {
            break;
        }
    }

    if cycle_edges.is_empty()
        && let Some(trigger) = trigger
    {
        cycle_edges.push(trigger.constraint_idx);
        total_weight = trigger.weight;
    }

    NegativeCycle::new(cycle_edges, total_weight)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::diff_logic::graph::DiffConstraint;
    use oxiz_core::ast::TermId;

    fn create_test_graph() -> ConstraintGraph {
        let mut graph = ConstraintGraph::new(true);
        let term_x = TermId::from(1u32);
        let term_y = TermId::from(2u32);
        let term_z = TermId::from(3u32);
        let origin = TermId::from(100u32);

        let x = graph.get_or_create_var(term_x);
        let y = graph.get_or_create_var(term_y);
        let z = graph.get_or_create_var(term_z);

        // x - y ≤ 3, y - z ≤ 2, z - x ≤ 1 (cycle 6 ≥ 0).
        graph.add_constraint(DiffConstraint::new_leq(
            x,
            y,
            Rational64::from_integer(3),
            origin,
        ));
        graph.add_constraint(DiffConstraint::new_leq(
            y,
            z,
            Rational64::from_integer(2),
            origin,
        ));
        graph.add_constraint(DiffConstraint::new_leq(
            z,
            x,
            Rational64::from_integer(1),
            origin,
        ));

        let _ = (x, y, z);
        graph
    }

    #[test]
    fn test_bellman_ford_no_cycle() {
        let graph = create_test_graph();
        let mut bf = BellmanFord::new();
        match bf.run(&graph) {
            BellmanFordResult::Distances(dists) => {
                assert_eq!(dists.len(), 3);
                // Multi-source: every distance ≤ 0.
                assert!(
                    dists
                        .iter()
                        .flatten()
                        .all(|d| *d <= Rational64::from_integer(0))
                );
            }
            BellmanFordResult::NegativeCycle(_) => {
                panic!("Should not detect negative cycle");
            }
        }
    }

    #[test]
    fn test_bellman_ford_negative_cycle() {
        let mut graph = ConstraintGraph::new(true);
        let term_x = TermId::from(1u32);
        let term_y = TermId::from(2u32);
        let term_z = TermId::from(3u32);
        let origin = TermId::from(100u32);

        let x = graph.get_or_create_var(term_x);
        let y = graph.get_or_create_var(term_y);
        let z = graph.get_or_create_var(term_z);

        // x - y ≤ -1, y - z ≤ -1, z - x ≤ -1 (cycle -3 < 0).
        graph.add_constraint(DiffConstraint::new_leq(
            x,
            y,
            Rational64::from_integer(-1),
            origin,
        ));
        graph.add_constraint(DiffConstraint::new_leq(
            y,
            z,
            Rational64::from_integer(-1),
            origin,
        ));
        graph.add_constraint(DiffConstraint::new_leq(
            z,
            x,
            Rational64::from_integer(-1),
            origin,
        ));

        let mut bf = BellmanFord::new();
        match bf.run(&graph) {
            BellmanFordResult::Distances(_) => {
                panic!("Should detect negative cycle");
            }
            BellmanFordResult::NegativeCycle(cycle) => {
                assert!(!cycle.edges.is_empty());
                assert!(cycle.total_weight < Rational64::from_integer(0));
            }
        }
    }

    #[test]
    fn test_spfa_no_cycle() {
        let graph = create_test_graph();
        let mut spfa = Spfa::new();
        match spfa.run(&graph) {
            BellmanFordResult::Distances(dists) => {
                assert_eq!(dists.len(), 3);
            }
            BellmanFordResult::NegativeCycle(_) => {
                panic!("Should not detect negative cycle");
            }
        }
    }

    #[test]
    fn test_spfa_negative_cycle() {
        let mut graph = ConstraintGraph::new(true);
        let term_x = TermId::from(1u32);
        let term_y = TermId::from(2u32);
        let origin = TermId::from(100u32);

        let x = graph.get_or_create_var(term_x);
        let y = graph.get_or_create_var(term_y);

        // x - y ≤ -1, y - x ≤ -1 (cycle -2 < 0).
        graph.add_constraint(DiffConstraint::new_leq(
            x,
            y,
            Rational64::from_integer(-1),
            origin,
        ));
        graph.add_constraint(DiffConstraint::new_leq(
            y,
            x,
            Rational64::from_integer(-1),
            origin,
        ));

        let mut spfa = Spfa::new();
        match spfa.run(&graph) {
            BellmanFordResult::Distances(_) => {
                panic!("Should detect negative cycle");
            }
            BellmanFordResult::NegativeCycle(cycle) => {
                assert!(!cycle.edges.is_empty());
            }
        }
    }

    #[test]
    fn seeded_spfa_detects_cycle_added_last() {
        // Consistent graph, then the cycle-closing edge — seeded from the
        // new edge's source, the check must fire.
        let mut graph = ConstraintGraph::new(true);
        let tx = TermId::from(1u32);
        let ty = TermId::from(2u32);
        let origin = TermId::from(9u32);
        let x = graph.get_or_create_var(tx);
        let y = graph.get_or_create_var(ty);
        graph.add_constraint(DiffConstraint::new_leq(
            x,
            y,
            Rational64::from_integer(0),
            origin,
        ));
        let mut spfa = Spfa::new();
        let dists = match spfa.run(&graph) {
            BellmanFordResult::Distances(d) => d,
            _ => panic!("consistent"),
        };
        // Now add y - x ≤ -1 (edge x → y, source = x).
        graph.add_constraint(DiffConstraint::new_leq(
            y,
            x,
            Rational64::from_integer(-1),
            origin,
        ));
        let mut mut_dists = dists;
        let r = spfa.seed_from(&graph, &mut mut_dists, x);
        assert!(r.is_some(), "seeded check must detect the cycle");
    }

    #[test]
    fn seeded_spfa_updates_distances() {
        let mut graph = ConstraintGraph::new(true);
        let tx = TermId::from(1u32);
        let ty = TermId::from(2u32);
        let origin = TermId::from(9u32);
        let x = graph.get_or_create_var(tx);
        let y = graph.get_or_create_var(ty);
        graph.add_constraint(DiffConstraint::new_leq(
            x,
            y,
            Rational64::from_integer(3),
            origin,
        ));
        let mut spfa = Spfa::new();
        let mut dists = match spfa.run(&graph) {
            BellmanFordResult::Distances(d) => d,
            _ => panic!("consistent"),
        };
        assert_eq!(dists[y.id() as usize], Some(Rational64::from_integer(0)));
        // No cycle possible from re-seeding; distances stay multi-source.
        assert!(spfa.seed_from(&graph, &mut dists, y).is_none());
    }
}
