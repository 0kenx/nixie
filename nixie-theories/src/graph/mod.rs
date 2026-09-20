//! Explained finite directed-graph constraints for the user-propagator API.
//!
//! This module provides **symbolic graph constraints over a fixed finite
//! vertex universe**: each graph is a set of Boolean edge terms, and
//! reachability and acyclicity are reified as Boolean atoms whose value the
//! solver must determine. This is an *integrated* capability — the
//! constraints run inside the CDCL(T) search through
//! [`crate::user_propagator`], unlike the standalone
//! [`crate::special_relations::SpecialRelationSolver`], which is a
//! bookkeeping helper that no solver path consults.
//!
//! # Semantics
//!
//! - Graphs are **directed**. The vertex universe is fixed at construction
//!   (`add_vertex`); vertices are opaque indices.
//! - An **edge** is a Boolean term; the edge is present in a graph exactly
//!   when its term is true. Parallel edges (several terms for the same
//!   ordered pair) and self-loops are allowed.
//! - `reach(g, u, v)` reifies reachability: it is true iff there is a
//!   directed path from `u` to `v` of **length ≥ 1** over present edges.
//!   **Zero-length paths do not count**: `reach(g, u, u)` is true exactly
//!   when `u` lies on a directed cycle (a self-loop suffices). This differs
//!   from MonoSAT's `reach` predicate, which counts the empty path and
//!   therefore holds trivially for `u = v`; the strict reading is the more
//!   expressive primitive (reflexive reachability is `(u = v) ∨
//!   reach(g,u,v)`, which callers can encode when wanted).
//! - `acyclic(g)` reifies acyclicity: true iff the present-edge subgraph
//!   contains no directed cycle (self-loops included).
//!
//! # Procedure
//!
//! The propagator implements the monotonic-theory scheme of Bayless, Bayless,
//! Hoos and Hu, *"SAT Modulo Monotonic Theories"* (AAAI 2015), as realized in
//! MonoSAT's `ReachDetector`/`CycleDetector`, adapted to Nixie's explained
//! user-propagator API:
//!
//! - **Under-approximation** ("forced" graph): edges assigned true.
//!   **Over-approximation** ("possible" graph): edges not assigned false.
//!   Reachability is monotone increasing in edges; acyclicity is monotone
//!   decreasing.
//! - A path in the forced graph proves `reach(u,v)`; its explanation is the
//!   path's edge literals (all true). The refutation of `reach(u,v)` is a
//!   cut of the possible graph — every false edge into the
//!   *backward-reachable* set of `v` (MonoSAT's `buildNonReachReason`) —
//!   explained by those edges' negated literals (all currently true). The
//!   cut is taken over the backward closure because a forward-closure cut
//!   is not a valid learned clause: it can justify `¬reach(u,u)` with an
//!   empty justification, which would wrongly forbid cycles in branches
//!   that re-enable the cut edges (a false-`unsat` class caught by the
//!   exhaustive oracles). Cycles are explained by their edge literals; a
//!   cycle-free possible graph forces `acyclic` with the trivial
//!   all-false-edges explanation (MonoSAT's `buildNoDirectedCycleReason`).
//! - Every propagation and conflict is emitted as a `Consequence` whose
//!   justification is a set of **signed edge assignments** (plus, for
//!   conflicts, the offending atom's literal), so the solver learns ordinary
//!   clauses. Theory atoms are lazy: they propagate only once determined,
//!   and `final_check` enforces the full biconditional on complete
//!   assignments.
//! - The propagator is **stateless**: every event re-derives the graph views
//!   from the current fixed values, so search `push`/`pop` needs no trail.
//!   The cost is a full graph recomputation per watched-atom event — fine
//!   for the documented scale (tens of vertices, hundreds of edges).
//!
//! # Proof and certification boundary
//!
//! Graph registrations are *trusted client callbacks*: like arbitrary user
//! propagators, they carry no independently checkable certificate, so
//! proof-producing and certified checks fail closed to `Unknown`
//! (see `docs/CP.md`'s callback trust contract). Ordinary (non-certified)
//! solving is complete for this fragment, and returned models are
//! independently replayed through the propagator before being reported.
//!
//! # Example
//!
//! ```rust,ignore
//! use nixie_core::ast::TermManager;
//! use nixie_solver::Solver;
//! use nixie_theories::graph::GraphModel;
//!
//! let mut tm = TermManager::new();
//! let mut graphs = GraphModel::new(&tm);
//! let g = graphs.new_graph();
//! let a = graphs.add_vertex(g).unwrap();
//! let b = graphs.add_vertex(g).unwrap();
//! graphs.new_edge(g, a, b, &mut tm).unwrap();
//! let reaches = graphs.reach(g, a, b, &mut tm).unwrap();
//! graphs.acyclic(g, &mut tm).unwrap();
//! let mut solver = Solver::new();
//! solver.register_graph(graphs, &mut tm).unwrap();
//! solver.assert(reaches, &mut tm); // a must reach b
//! assert_eq!(solver.check(&mut tm), nixie_solver::SolverResult::Sat);
//! ```

use crate::prelude::*;
use crate::user_propagator::{Consequence, PropagatorContext, PropagatorResult, UserPropagator};
use nixie_core::ast::{TermId, TermManager};

/// Invalid graph construction (rejected before installing any constraint).
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct GraphError(pub &'static str);

impl core::fmt::Display for GraphError {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        f.write_str(self.0)
    }
}
impl core::error::Error for GraphError {}

/// A vertex in one graph's fixed finite universe. Indices are handed out
/// consecutively by [`GraphModel::add_vertex`] and are local to their graph.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct VertexId(u32);

impl VertexId {
    /// The vertex with index `index` (zero-based). Only indices below the
    /// owning graph's vertex count are meaningful; all APIs validate them.
    #[must_use]
    pub const fn new(index: u32) -> Self {
        Self(index)
    }

    /// The vertex's zero-based index.
    #[must_use]
    pub const fn index(self) -> u32 {
        self.0
    }
}

/// Handle to one graph inside a [`GraphModel`]. Obtained from
/// [`GraphModel::new_graph`]; the zero-based index is addressable via
/// [`GraphHandle::new`] for serialization-style tooling.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct GraphHandle(usize);

impl GraphHandle {
    /// The graph with zero-based index `index`. Only indices below the
    /// owning model's graph count are meaningful; all APIs validate them.
    #[must_use]
    pub const fn new(index: usize) -> Self {
        Self(index)
    }

    /// The handle's zero-based index.
    #[must_use]
    pub const fn index(self) -> usize {
        self.0
    }
}

/// Assignment state of one edge term.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum EdgeValue {
    /// Edge term fixed true.
    True,
    /// Edge term fixed false.
    False,
    /// Edge term not yet fixed.
    Unknown,
}

/// Whether an edge in this state belongs to a view: the forced view keeps
/// true edges; the possible view keeps everything but false edges.
fn in_view(value: EdgeValue, forced: bool) -> bool {
    match value {
        EdgeValue::True => true,
        EdgeValue::False => false,
        EdgeValue::Unknown => !forced,
    }
}

/// One edge: ordered pair plus its Boolean presence term.
struct EdgeSpec {
    from: VertexId,
    to: VertexId,
    atom: TermId,
    negation: TermId,
}

/// One reified reachability atom.
struct ReachSpec {
    from: VertexId,
    to: VertexId,
    atom: TermId,
    negation: TermId,
}

/// One graph's vertices, edges and constraints.
struct GraphSpec {
    vertices: usize,
    edges: Vec<EdgeSpec>,
    reach: Vec<ReachSpec>,
    /// Acyclicity atom (atom, negation), if requested.
    acyclic: Option<(TermId, TermId)>,
    /// (from, to) -> index into `reach`, so `reach()` is idempotent.
    reach_cache: FxHashMap<(u32, u32), u32>,
}

impl GraphSpec {
    fn new(vertices: usize) -> Self {
        Self {
            vertices,
            edges: Vec::new(),
            reach: Vec::new(),
            acyclic: None,
            reach_cache: FxHashMap::default(),
        }
    }
}

/// Flat CSR adjacency over one view: `offsets[v]..offsets[v+1]` indexes
/// into `neighbours` (the adjacent vertex) and `edges` (the edge index),
/// with each row's entries in edge declaration order. Rebuilt in place
/// (buffers are reused across rebuilds — no per-edge allocations).
#[derive(Default)]
struct Csr {
    offsets: Vec<u32>,
    neighbours: Vec<u32>,
    edges: Vec<u32>,
}

impl Csr {
    /// Rebuild from the current edge assignment. `forced` selects the
    /// true-edge view; otherwise the non-false (possible) view. `incoming`
    /// builds the reverse adjacency (row = destination).
    fn rebuild(&mut self, spec: &GraphSpec, values: &[EdgeValue], forced: bool, incoming: bool) {
        self.offsets.clear();
        self.offsets.resize(spec.vertices + 1, 0);
        self.neighbours.clear();
        self.edges.clear();
        // Pass 1: row sizes.
        for (i, edge) in spec.edges.iter().enumerate() {
            if in_view(values[i], forced) {
                let row = if incoming { edge.to.0 } else { edge.from.0 };
                self.offsets[row as usize + 1] += 1;
            }
        }
        // Prefix sums.
        for v in 0..spec.vertices {
            self.offsets[v + 1] += self.offsets[v];
        }
        let count = spec
            .edges
            .iter()
            .zip(values)
            .filter(|&(_, &v)| in_view(v, forced))
            .count();
        self.neighbours.clear();
        self.neighbours.resize(count, 0);
        self.edges.clear();
        self.edges.resize(count, 0);
        // Pass 2: fill rows through a moving cursor, preserving declaration
        // order within each row (bit-identity with the uncached propagator).
        let mut cursor = self.offsets.clone();
        for (i, edge) in spec.edges.iter().enumerate() {
            if in_view(values[i], forced) {
                let row = if incoming { edge.to.0 } else { edge.from.0 };
                let k = cursor[row as usize] as usize;
                cursor[row as usize] += 1;
                self.neighbours[k] = if incoming { edge.from.0 } else { edge.to.0 };
                self.edges[k] = i as u32;
            }
        }
    }

    /// Rebuild as a flat snapshot of growable rows (same row contents and
    /// order); used only by the occasional forced-view cycle check.
    fn rebuild_from_rows(&mut self, rows: &[Vec<(u32, u32)>], vertices: usize) {
        self.offsets.clear();
        self.offsets.resize(vertices + 1, 0);
        let count: usize = rows.iter().map(|r| r.len()).sum();
        self.neighbours.clear();
        self.neighbours.resize(count, 0);
        self.edges.clear();
        self.edges.resize(count, 0);
        let mut cursor = 0;
        for (v, row) in rows.iter().enumerate() {
            self.offsets[v] = cursor as u32;
            for &(to, edge) in row {
                self.neighbours[cursor] = to;
                self.edges[cursor] = edge;
                cursor += 1;
            }
        }
        if let Some(last) = self.offsets.last_mut() {
            *last = cursor as u32;
        }
    }

    fn row(&self, v: usize) -> Range<usize> {
        let lo = self.offsets.get(v).copied().unwrap_or(0) as usize;
        let hi = self.offsets.get(v + 1).copied().unwrap_or(lo as u32) as usize;
        lo..hi
    }
}

use core::ops::Range;

/// Result of a breadth-first search over one adjacency view. `visited`
/// includes the source itself (the zero-length closure); paths of length
/// ≥ 1 are recovered through `parent_edge` and in-edge tests.
#[derive(Default)]
struct Bfs {
    source: usize,
    visited: Vec<bool>,
    /// Edge index through which each visited vertex (other than the source)
    /// was first reached.
    parent_edge: Vec<Option<u32>>,
}

/// BFS from `source` over growable adjacency rows (the maintained forced
/// view), seeding the source itself.
fn bfs_rows(adj: &[Vec<(u32, u32)>], vertices: usize, source: VertexId) -> Bfs {
    let mut visited = vec![false; vertices];
    let mut parent_edge = vec![None; vertices];
    let s = source.0 as usize;
    let mut queue = Vec::new();
    if s < vertices {
        visited[s] = true;
        queue.push(s);
    }
    let mut head = 0;
    while head < queue.len() {
        let v = queue[head];
        head += 1;
        for &(to, edge) in &adj[v] {
            let t = to as usize;
            if !visited[t] {
                visited[t] = true;
                parent_edge[t] = Some(edge);
                queue.push(t);
            }
        }
    }
    Bfs {
        source: s,
        visited,
        parent_edge,
    }
}

/// BFS from `source` over `adj`, seeding the source itself. Iterative: no
/// native recursion over user-controlled graphs.
fn bfs(adj: &Csr, vertices: usize, source: VertexId) -> Bfs {
    let mut visited = vec![false; vertices];
    let mut parent_edge = vec![None; vertices];
    let s = source.0 as usize;
    let mut queue = Vec::new();
    if s < vertices {
        visited[s] = true;
        queue.push(s);
    }
    let mut head = 0;
    while head < queue.len() {
        let v = queue[head];
        head += 1;
        for k in adj.row(v) {
            let t = adj.neighbours[k] as usize;
            if !visited[t] {
                visited[t] = true;
                parent_edge[t] = Some(adj.edges[k]);
                queue.push(t);
            }
        }
    }
    Bfs {
        source: s,
        visited,
        parent_edge,
    }
}

impl Bfs {
    fn visits(&self, v: VertexId) -> bool {
        self.visited.get(v.0 as usize).copied().unwrap_or(false)
    }

    /// Is `target` reachable from the search source through **at least one**
    /// true edge? For `target` different from the source this is plain
    /// `visited`; for `target == source` it means the source lies on a
    /// cycle of true edges, established by a true in-edge of the source from
    /// a visited vertex (a self-loop is such an in-edge). Only the *forced*
    /// view uses this; negative reasoning uses [`Backward::possible_reaches`]
    /// over the backward closure instead.
    fn reaches_forced(&self, spec: &GraphSpec, values: &[EdgeValue], target: VertexId) -> bool {
        if !self.visits(target) {
            return false;
        }
        if target.0 as usize != self.source {
            return true;
        }
        spec.edges
            .iter()
            .enumerate()
            .any(|(i, e)| e.to == target && self.visits(e.from) && values[i] == EdgeValue::True)
    }

    /// Edge atoms of the witnessed path `source ->+ target` in the **forced**
    /// view (every emitted edge is currently true). Returns `None` if the
    /// path invariant does not hold; callers treat that as fail-closed.
    fn path_atoms(
        &self,
        spec: &GraphSpec,
        values: &[EdgeValue],
        target: VertexId,
    ) -> Option<Vec<TermId>> {
        let source = VertexId(self.source as u32);
        if target == source {
            // A cycle through the source: close it with any *true* in-edge
            // of the source from a visited vertex, then walk parents back.
            for (i, edge) in spec.edges.iter().enumerate() {
                if edge.to == target && self.visits(edge.from) && values[i] == EdgeValue::True {
                    let mut atoms = vec![edge.atom];
                    let mut x = edge.from;
                    while x != source {
                        let e = self.parent_edge[x.0 as usize]?;
                        atoms.push(spec.edges[e as usize].atom);
                        x = spec.edges[e as usize].from;
                    }
                    return Some(atoms);
                }
            }
            return None;
        }
        // Ordinary path: walk parents from `target` back to the source.
        let mut atoms = Vec::new();
        let mut x = target;
        while x != source {
            let e = self.parent_edge[x.0 as usize]?;
            atoms.push(spec.edges[e as usize].atom);
            x = spec.edges[e as usize].from;
        }
        Some(atoms)
    }
}

/// Negative ("possible") reachability over the backward closure, following
/// MonoSAT's `buildNonReachReason`: `seen` is the set of vertices that can
/// reach the target through possible edges (paths of length ≥ 0).
#[derive(Default)]
struct Backward {
    target: usize,
    seen: Vec<bool>,
}

fn backward_seen(possible_in: &Csr, vertices: usize, target: VertexId) -> Backward {
    let search = bfs(possible_in, vertices, target);
    Backward {
        target: search.source,
        seen: search.visited,
    }
}

impl Backward {
    fn sees(&self, v: VertexId) -> bool {
        self.seen.get(v.0 as usize).copied().unwrap_or(false)
    }

    /// Can `u` reach the target through at least one possible edge? For
    /// `u != target` this is `u ∈ seen`; for `u == target` a possible cycle
    /// must exist: some possible out-edge of `u` whose head lies in the
    /// backward closure of `u` (a self-loop included).
    fn possible_reaches(&self, spec: &GraphSpec, values: &[EdgeValue], u: VertexId) -> bool {
        if u.0 as usize == self.target {
            return spec
                .edges
                .iter()
                .enumerate()
                .any(|(i, e)| e.from == u && self.sees(e.to) && in_view(values[i], false));
        }
        self.sees(u)
    }

    /// Signed reasons that the source cannot reach the target through
    /// possible edges: **every false edge into the backward closure** of
    /// the target (MonoSAT's cut; non-false edges into the closure are the
    /// closure's own possible edges and are not part of the cut). The
    /// implication these reasons justify is valid for *arbitrary* graphs,
    /// not only completions of the current state — which is what learned
    /// clauses require: any path (for a self-pair, any cycle) from the
    /// source to the target whose edges into the closure are not among
    /// these reasons consists entirely of possible edges, which would place
    /// the source in the closure and contradict the refutation. Every
    /// emitted edge is currently false, so its negation is a true literal.
    /// An empty cut means the refutation is unconditional over the whole
    /// fixed edge universe.
    fn cut_negations(&self, spec: &GraphSpec, values: &[EdgeValue]) -> Vec<TermId> {
        let mut reasons = Vec::new();
        for (i, edge) in spec.edges.iter().enumerate() {
            if self.sees(edge.to) && values[i] == EdgeValue::False {
                reasons.push(edge.negation);
            }
        }
        reasons
    }
}

/// Iterative DFS cycle search over one adjacency view. Returns the edge
/// indices of a directed cycle, if one exists. Explicit heap stack: no
/// native recursion over user-controlled graphs.
/// Content-addressed cache of one graph's derived results, keyed by the
/// exact packed membership bits of the view they were computed from.
///
/// This is memoization, not incremental state: validity is re-checked
/// against the *full* current edge assignment on every run (the packed key
/// must match bit-for-bit), so no event history, trail, or push/pop
/// bookkeeping is involved. A key match means the derived results are
/// literally the same function outputs as a fresh recomputation, which
/// keeps every emitted consequence bit-identical (semantics-inert).
impl ViewCache {
    /// Size the per-vertex tables for a graph with `vertices` vertices and
    /// `edges` edges; everything starts invalid/empty.
    fn sized(vertices: usize, edges: usize) -> Self {
        Self {
            forced_valid: false,
            forced_bits: vec![0; edges / 64 + 1],
            possible_bits: vec![u64::MAX; edges / 64 + 1],
            values: vec![EdgeValue::Unknown; edges],
            forced_rows: vec![Vec::new(); vertices],
            forced_searches: (0..vertices).map(|_| None).collect(),
            forced_cycle: None,
            possible_dirty: true,
            possible_out: Csr::default(),
            possible_in: Csr::default(),
            backward_searches: (0..vertices).map(|_| None).collect(),
            possible_cycle: None,
            pending: Vec::new(),
        }
    }

    /// Full invalidation (backtrack/reset): the next run re-reads the
    /// manager from scratch.
    fn invalidate(&mut self) {
        self.forced_valid = false;
        self.possible_dirty = true;
        self.pending.clear();
    }

    fn bit_write(bits: &mut [u64], i: usize, value: bool) {
        if value {
            bits[i / 64] |= 1u64 << (i % 64);
        } else {
            bits[i / 64] &= !(1u64 << (i % 64));
        }
    }

    /// Apply one edge event to the maintained state. Must only be called
    /// while `forced_valid`. A true addition appends the adjacency row and
    /// merges every memoized search whose reachable set can grow; a false
    /// assignment only shrinks the possible view.
    fn apply_edge_event(&mut self, spec: &GraphSpec, edge: u32, value: EdgeValue) {
        let i = edge as usize;
        let previous = self.values[i];
        if previous == value {
            return;
        }
        self.values[i] = value;
        let was_true = previous == EdgeValue::True;
        let now_true = value == EdgeValue::True;
        let now_false = value == EdgeValue::False;
        Self::bit_write(&mut self.forced_bits, i, now_true);
        Self::bit_write(&mut self.possible_bits, i, !now_false);
        if now_true && !was_true {
            let e = &spec.edges[i];
            self.forced_rows[e.from.0 as usize].push((e.to.0, edge));
            self.forced_cycle = None;
            self.merge_new_edge(spec, e.from, e.to, edge);
        }
        if now_false && previous != EdgeValue::False {
            self.possible_dirty = true;
        }
    }

    /// Merge one added true edge `(from -> to, idx)` into every memoized
    /// forced-view BFS tree whose reachable set gains vertices. Merged
    /// trees remain genuine trees of the current forced graph: every
    /// parent edge is real, so extracted paths stay valid justifications.
    fn merge_new_edge(&mut self, spec: &GraphSpec, from: VertexId, to: VertexId, idx: u32) {
        let u = from.0 as usize;
        let v = to.0 as usize;
        for search in self.forced_searches.iter_mut() {
            let Some(tree) = search else { continue };
            if tree.visited[u] && !tree.visited[v] {
                // Discover everything newly reachable through the edge.
                tree.visited[v] = true;
                tree.parent_edge[v] = Some(idx);
                let mut queue = vec![v];
                let mut head = 0;
                while head < queue.len() {
                    let x = queue[head];
                    head += 1;
                    for &(y, e) in &self.forced_rows[x] {
                        let t = y as usize;
                        if !tree.visited[t] {
                            tree.visited[t] = true;
                            tree.parent_edge[t] = Some(e);
                            queue.push(t);
                        }
                    }
                }
            }
        }
        let _ = spec;
    }
}

struct ViewCache {
    /// **Incrementally maintained forced view.** `forced_valid` is false
    /// until the first full read; afterwards the packed true-edge bits, the
    /// per-edge values, and the growable adjacency rows are updated from
    /// `(term, value)` events in O(1) per event, and memoized BFS trees are
    /// *merged* (not recomputed) when an added edge extends a source's
    /// reachable set. A backtrack (`UserPropagator::pop`) clears
    /// `forced_valid`: the next run re-reads everything from the manager.
    /// While valid, the derived state is exactly a function of the
    /// manager's current fixations — the same fixations the full read
    /// would observe.
    forced_valid: bool,
    /// Packed true-edge bits (edge i is true iff bit set).
    forced_bits: Vec<u64>,
    /// Packed non-false-edge bits (edge i is false iff bit clear).
    possible_bits: Vec<u64>,
    /// Per-edge assignment state derived from events.
    values: Vec<EdgeValue>,
    /// Growable per-vertex rows of (neighbour, edge index) over true edges,
    /// in edge declaration order within each row.
    forced_rows: Vec<Vec<(u32, u32)>>,
    /// Forced-view BFS by source vertex (maintained by merges).
    forced_searches: Vec<Option<Bfs>>,
    /// `find_cycle` over the forced view (`Some(None)` = computed, acyclic).
    /// Any true-edge addition invalidates it.
    forced_cycle: Option<Option<Vec<u32>>>,
    /// True when the possible view changed since the possible-side CSR and
    /// memos were built (false-edge assignments shrink it).
    possible_dirty: bool,
    possible_out: Csr,
    possible_in: Csr,
    /// Possible-view backward BFS by target vertex.
    backward_searches: Vec<Option<Backward>>,
    possible_cycle: Option<Option<Vec<u32>>>,
    /// Edge events waiting to be applied at the next run:
    /// (edge index, new value).
    pending: Vec<(u32, EdgeValue)>,
}

fn find_cycle(adj: &Csr, vertices: usize) -> Option<Vec<u32>> {
    // colors: 0 = white (unvisited), 1 = gray (on the DFS path), 2 = black.
    let mut color = vec![0u8; vertices];
    let mut parent_edge = vec![None::<u32>; vertices];
    for start in 0..vertices {
        if color[start] != 0 {
            continue;
        }
        color[start] = 1;
        // Stack of (vertex, next adjacency position); the frames are exactly
        // the gray vertices, so a back edge to a gray vertex closes a cycle
        // along the stack.
        let mut stack: Vec<(usize, usize)> = vec![(start, 0)];
        while let Some(&mut (v, ref mut next)) = stack.last_mut() {
            let row = adj.row(v);
            let Some(k) = row.clone().nth(*next) else {
                color[v] = 2;
                stack.pop();
                continue;
            };
            let to = adj.neighbours[k];
            let edge = adj.edges[k];
            *next += 1;
            let t = to as usize;
            match color[t] {
                0 => {
                    color[t] = 1;
                    parent_edge[t] = Some(edge);
                    stack.push((t, 0));
                }
                1 => {
                    // Back edge `v -> t` with `t` gray: the cycle is
                    // t ->+ v -> t along the stack frames after `t`. Every
                    // frame beyond `t` was discovered through its parent
                    // edge, which is exactly the path edge into it.
                    let mut cycle = vec![edge];
                    if let Some(pos) = stack.iter().position(|&(x, _)| x == t) {
                        for &(x, _) in &stack[pos + 1..] {
                            if let Some(e) = parent_edge[x] {
                                cycle.push(e);
                            }
                        }
                    }
                    return Some(cycle);
                }
                _ => {}
            }
        }
    }
    None
}

/// Per-instance salt for minted atom names, so two models over one term
/// manager never silently share atoms through name interning.
fn next_model_uid() -> u64 {
    static COUNTER: core::sync::atomic::AtomicU64 = core::sync::atomic::AtomicU64::new(0);
    COUNTER.fetch_add(1, core::sync::atomic::Ordering::Relaxed)
}

/// A collection of finite directed graphs with reified reachability and
/// acyclicity constraints, installable with `Solver::register_graph`.
///
/// Construct the model before registering it; handles are local to one model.
/// The model itself becomes the propagator, so all constraints must be
/// declared before `into_propagator`/`register_graph`. Atoms minted by
/// `new_edge`/`reach`/`acyclic` carry a per-model unique salt, so several
/// models over one term manager stay disjoint; user-supplied edge terms may
/// deliberately be shared (the same term cannot be reused twice *within* a
/// model).
pub struct GraphModel {
    uid: u64,
    graphs: Vec<GraphSpec>,
    /// One incrementally maintained cache per graph (see [`ViewCache`]).
    caches: Vec<ViewCache>,
    /// Edge atom -> (graph index, edge index), for O(1) event routing.
    edge_index: FxHashMap<TermId, (u32, u32)>,
    /// Every term used as an edge atom (across graphs), for uniqueness.
    edge_terms: FxHashSet<TermId>,
    /// Terms created by this model (reach/acyclicity atoms), which edge
    /// declarations must not shadow.
    system_terms: FxHashSet<TermId>,
    true_term: TermId,
    false_term: TermId,
}

impl core::fmt::Debug for GraphModel {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        f.debug_struct("GraphModel")
            .field("graphs", &self.graphs.len())
            .field("edges", &self.edge_terms.len())
            .field("atoms", &self.system_terms.len())
            .finish()
    }
}

impl GraphModel {
    /// Start a graph model using the same term manager as the SMT solver.
    pub fn new(tm: &TermManager) -> Self {
        Self {
            uid: next_model_uid(),
            graphs: Vec::new(),
            caches: Vec::new(),
            edge_index: FxHashMap::default(),
            edge_terms: FxHashSet::default(),
            system_terms: FxHashSet::default(),
            true_term: tm.mk_bool(true),
            false_term: tm.mk_bool(false),
        }
    }

    fn graph_mut(&mut self, g: GraphHandle) -> Result<&mut GraphSpec, GraphError> {
        self.graphs
            .get_mut(g.0)
            .ok_or(GraphError("unknown graph handle"))
    }

    fn graph(&self, g: GraphHandle) -> Result<&GraphSpec, GraphError> {
        self.graphs
            .get(g.0)
            .ok_or(GraphError("unknown graph handle"))
    }

    /// Create a new, initially empty graph.
    pub fn new_graph(&mut self) -> GraphHandle {
        self.graphs.push(GraphSpec::new(0));
        self.caches.push(ViewCache::sized(0, 0));
        GraphHandle(self.graphs.len() - 1)
    }

    /// Extend graph `g`'s fixed vertex universe by one; returns the new
    /// vertex's index.
    pub fn add_vertex(&mut self, g: GraphHandle) -> Result<VertexId, GraphError> {
        if g.0 >= self.graphs.len() {
            return Err(GraphError("unknown graph handle"));
        }
        let id = VertexId(self.graphs[g.0].vertices as u32);
        self.graphs[g.0].vertices += 1;
        // The graph grew: re-size the per-vertex tables from scratch.
        if g.0 < self.caches.len() {
            let vertices = self.graphs[g.0].vertices;
            let edges = self.graphs[g.0].edges.len();
            self.caches[g.0] = ViewCache::sized(vertices, edges);
        }
        Ok(id)
    }

    /// Add edge `from -> to` with an existing Boolean term as its presence
    /// atom. The term must have Boolean sort, must not be a Boolean
    /// constant, and must not already name an edge or a graph atom in this
    /// model. Returns the atom for convenience.
    pub fn add_edge(
        &mut self,
        g: GraphHandle,
        from: VertexId,
        to: VertexId,
        atom: TermId,
        tm: &mut TermManager,
    ) -> Result<TermId, GraphError> {
        {
            let spec = self.graph(g)?;
            if from.0 as usize >= spec.vertices || to.0 as usize >= spec.vertices {
                return Err(GraphError("vertex out of range"));
            }
        }
        let node = tm.get(atom).ok_or(GraphError("unknown term"))?;
        if node.sort != tm.sorts.bool_sort {
            return Err(GraphError("edge atoms must have Boolean sort"));
        }
        if matches!(
            node.kind,
            nixie_core::ast::TermKind::True | nixie_core::ast::TermKind::False
        ) {
            return Err(GraphError("edge atoms must not be Boolean constants"));
        }
        if self.edge_terms.contains(&atom) || self.system_terms.contains(&atom) {
            return Err(GraphError("edge atom already used by this model"));
        }
        self.edge_terms.insert(atom);
        let negation = tm.mk_not(atom);
        let spec = self.graph_mut(g)?;
        spec.edges.push(EdgeSpec {
            from,
            to,
            atom,
            negation,
        });
        Ok(atom)
    }

    /// Add edge `from -> to` with a fresh Boolean variable as its presence
    /// atom and return it.
    pub fn new_edge(
        &mut self,
        g: GraphHandle,
        from: VertexId,
        to: VertexId,
        tm: &mut TermManager,
    ) -> Result<TermId, GraphError> {
        let index = self.graph(g)?.edges.len();
        let atom = tm.mk_var(
            &format!("gm{}_g{}_edge{}_{}_{}", self.uid, g.0, from.0, to.0, index),
            tm.sorts.bool_sort,
        );
        self.add_edge(g, from, to, atom, tm)
    }

    /// Reify reachability `u ->+ v` (paths of length ≥ 1; see the module
    /// docs) with a fresh Boolean atom, or return the existing atom for the
    /// same pair. The atom is *defined* by the graph: the solver must
    /// assign it exactly the reachability value of the final graph.
    pub fn reach(
        &mut self,
        g: GraphHandle,
        u: VertexId,
        v: VertexId,
        tm: &mut TermManager,
    ) -> Result<TermId, GraphError> {
        {
            let spec = self.graph(g)?;
            if u.0 as usize >= spec.vertices || v.0 as usize >= spec.vertices {
                return Err(GraphError("vertex out of range"));
            }
            if let Some(&index) = spec.reach_cache.get(&(u.0, v.0)) {
                return Ok(spec.reach[index as usize].atom);
            }
        }
        let atom = tm.mk_var(
            &format!("gm{}_g{}_reach{}_{}", self.uid, g.0, u.0, v.0),
            tm.sorts.bool_sort,
        );
        let negation = tm.mk_not(atom);
        self.system_terms.insert(atom);
        let spec = self.graph_mut(g)?;
        let index = spec.reach.len() as u32;
        spec.reach.push(ReachSpec {
            from: u,
            to: v,
            atom,
            negation,
        });
        spec.reach_cache.insert((u.0, v.0), index);
        Ok(atom)
    }

    /// Reify acyclicity of graph `g` with a fresh Boolean atom (true iff the
    /// present-edge subgraph has no directed cycle), or return the existing
    /// atom. Assert the atom to demand a DAG; negate it to demand a cycle.
    pub fn acyclic(&mut self, g: GraphHandle, tm: &mut TermManager) -> Result<TermId, GraphError> {
        if let Some((atom, _)) = self.graph(g)?.acyclic {
            return Ok(atom);
        }
        let atom = tm.mk_var(
            &format!("gm{}_g{}_acyclic", self.uid, g.0),
            tm.sorts.bool_sort,
        );
        let negation = tm.mk_not(atom);
        self.system_terms.insert(atom);
        self.graph_mut(g)?.acyclic = Some((atom, negation));
        Ok(atom)
    }

    /// Number of vertices in graph `g`'s fixed universe.
    pub fn num_vertices(&self, g: GraphHandle) -> Result<usize, GraphError> {
        Ok(self.graph(g)?.vertices)
    }

    /// Graph `g`'s edges as `(from, to, atom)` triples, in declaration order.
    pub fn edges(&self, g: GraphHandle) -> Result<Vec<(VertexId, VertexId, TermId)>, GraphError> {
        Ok(self
            .graph(g)?
            .edges
            .iter()
            .map(|e| (e.from, e.to, e.atom))
            .collect())
    }

    /// Graph `g`'s reachability atoms as `(from, to, atom)` triples.
    pub fn reach_atoms(
        &self,
        g: GraphHandle,
    ) -> Result<Vec<(VertexId, VertexId, TermId)>, GraphError> {
        Ok(self
            .graph(g)?
            .reach
            .iter()
            .map(|r| (r.from, r.to, r.atom))
            .collect())
    }

    /// Graph `g`'s acyclicity atom, if declared.
    pub fn acyclic_atom(&self, g: GraphHandle) -> Result<Option<TermId>, GraphError> {
        Ok(self.graph(g)?.acyclic.map(|(atom, _)| atom))
    }

    /// All terms the propagator must watch: edge atoms, reachability atoms
    /// and acyclicity atoms (in no particular order).
    pub fn watches(&self) -> Vec<TermId> {
        let mut watches = Vec::new();
        for spec in &self.graphs {
            watches.extend(spec.edges.iter().map(|e| e.atom));
            watches.extend(spec.reach.iter().map(|r| r.atom));
            if let Some((atom, _)) = spec.acyclic {
                watches.push(atom);
            }
        }
        watches
    }

    /// Consume the model into a callback and the watch list for
    /// `Solver::register_user_propagator` (or use `Solver::register_graph`).
    pub fn into_propagator(mut self) -> (Box<dyn UserPropagator>, Vec<TermId>) {
        let watches = self.watches();
        for (g, spec) in self.graphs.iter().enumerate() {
            for (i, edge) in spec.edges.iter().enumerate() {
                self.edge_index.insert(edge.atom, (g as u32, i as u32));
            }
        }
        (Box::new(self), watches)
    }

    /// The term manager's Boolean true constant (for tests and oracles).
    pub fn true_term(&self) -> TermId {
        self.true_term
    }

    /// The term manager's Boolean false constant (for tests and oracles).
    pub fn false_term(&self) -> TermId {
        self.false_term
    }

    /// Full theory run: check all graphs against the currently fixed atoms,
    /// queue determined consequences, and report the verdict.
    fn run(&mut self, ctx: &mut PropagatorContext) -> PropagatorResult {
        let mut complete = true;
        for g in 0..self.graphs.len() {
            match self.run_graph(g, ctx) {
                PropagatorResult::Unsat(reasons) => {
                    // The queued consequence carries the same signed reasons
                    // so search-time conflicts become ordinary clauses.
                    ctx.propagate(Consequence::new(self.false_term, reasons.clone()));
                    return PropagatorResult::Unsat(reasons);
                }
                PropagatorResult::Sat => {}
                PropagatorResult::Unknown => complete = false,
            }
        }
        if complete {
            PropagatorResult::Sat
        } else {
            PropagatorResult::Unknown
        }
    }

    /// One graph's check. The maintained forced view (bits, values,
    /// adjacency, memoized searches) is trusted only while `forced_valid`;
    /// the first run after construction or a backtrack re-reads every edge
    /// from the manager. Afterwards each event was applied in O(1) and the
    /// memoized trees were merged, so this scan is lookups only.
    fn run_graph(&mut self, g: usize, ctx: &mut PropagatorContext) -> PropagatorResult {
        let spec = &self.graphs[g];
        let vertices = spec.vertices;
        let edge_count = spec.edges.len();
        let mut all_fixed = true;

        {
            let cache = &mut self.caches[g];
            if !cache.forced_valid {
                // Full re-read path (first run, or after a backtrack).
                cache.values.clear();
                cache.values.resize(edge_count, EdgeValue::Unknown);
                cache.forced_bits.clear();
                cache.forced_bits.resize(edge_count / 64 + 1, 0);
                cache.possible_bits.clear();
                cache.possible_bits.resize(edge_count / 64 + 1, u64::MAX);
                for row in cache.forced_rows.iter_mut() {
                    row.clear();
                }
                cache.forced_searches.clear();
                cache.forced_searches.extend((0..vertices).map(|_| None));
                cache.forced_cycle = None;
                for (i, edge) in spec.edges.iter().enumerate() {
                    match ctx.get_fixed_value(edge.atom) {
                        None => {
                            all_fixed = false;
                        }
                        Some(v) if v == self.true_term => {
                            cache.values[i] = EdgeValue::True;
                            ViewCache::bit_write(&mut cache.forced_bits, i, true);
                            cache.forced_rows[edge.from.0 as usize].push((edge.to.0, i as u32));
                        }
                        Some(v) if v == self.false_term => {
                            cache.values[i] = EdgeValue::False;
                            ViewCache::bit_write(&mut cache.possible_bits, i, false);
                        }
                        Some(_) => return PropagatorResult::Unknown,
                    }
                }
                cache.pending.clear();
                cache.forced_valid = true;
                // The possible view may have changed relative to whatever
                // was cached before invalidation.
                cache.possible_dirty = true;
            } else {
                // Apply queued edge events (recorded by on_fixed).
                let pending = core::mem::take(&mut cache.pending);
                for (edge, value) in pending {
                    cache.apply_edge_event(spec, edge, value);
                }
            }
        }

        // Destructure the cache into disjoint borrows: adjacency and values
        // are read-only below; the memos fill in lazily.
        let cache = &mut self.caches[g];
        if cache.possible_dirty {
            let mut possible_out = core::mem::take(&mut cache.possible_out);
            let mut possible_in = core::mem::take(&mut cache.possible_in);
            possible_out.rebuild(spec, &cache.values, false, false);
            possible_in.rebuild(spec, &cache.values, false, true);
            cache.possible_out = possible_out;
            cache.possible_in = possible_in;
            cache.backward_searches.clear();
            cache.backward_searches.extend((0..vertices).map(|_| None));
            cache.possible_cycle = None;
            cache.possible_dirty = false;
        }
        let values: &Vec<EdgeValue> = &cache.values;
        let forced_rows: &Vec<Vec<(u32, u32)>> = &cache.forced_rows;
        let possible_out: &Csr = &cache.possible_out;
        let possible_in: &Csr = &cache.possible_in;
        let forced_searches = &mut cache.forced_searches;
        let backward_searches = &mut cache.backward_searches;
        let forced_cycle = &mut cache.forced_cycle;
        let possible_cycle = &mut cache.possible_cycle;

        // A flat temporary CSR over the growable rows, only when a cycle
        // check is actually needed (acyclic atom present and undecided).
        let mut forced_csr = Csr::default();

        // 1. Acyclicity atom.
        if let Some((atom, negation)) = spec.acyclic {
            let fixed = match ctx.get_fixed_value(atom) {
                None => {
                    all_fixed = false;
                    None
                }
                Some(v) if v == self.true_term => Some(true),
                Some(v) if v == self.false_term => Some(false),
                Some(_) => return PropagatorResult::Unknown,
            };
            // The forced cycle status may have changed since the last
            // computation only through recorded edge events; recompute on
            // demand (any true addition cleared the memo).
            let forced_result = forced_cycle.get_or_insert_with(|| {
                forced_csr.rebuild_from_rows(forced_rows, vertices);
                find_cycle(&forced_csr, vertices)
            });
            if let Some(cycle) = forced_result.clone() {
                let reasons: Vec<TermId> =
                    cycle.iter().map(|&e| spec.edges[e as usize].atom).collect();
                match fixed {
                    Some(true) => {
                        let mut conflict = reasons;
                        conflict.push(atom);
                        return PropagatorResult::Unsat(conflict);
                    }
                    None => {
                        ctx.propagate(Consequence::new(negation, reasons));
                    }
                    Some(false) => {}
                }
            } else {
                let possible_result =
                    possible_cycle.get_or_insert_with(|| find_cycle(possible_out, vertices));
                if possible_result.clone().is_none() {
                    let reasons: Vec<TermId> = spec
                        .edges
                        .iter()
                        .zip(values)
                        .filter(|&(_, v)| *v == EdgeValue::False)
                        .map(|(edge, _)| edge.negation)
                        .collect();
                    match fixed {
                        Some(false) => {
                            let mut conflict = reasons;
                            conflict.push(negation);
                            return PropagatorResult::Unsat(conflict);
                        }
                        None => {
                            ctx.propagate(Consequence::new(atom, reasons));
                        }
                        Some(true) => {}
                    }
                }
            }
        }

        // 2. Reachability atoms.
        for reach in &spec.reach {
            let fixed = match ctx.get_fixed_value(reach.atom) {
                None => {
                    all_fixed = false;
                    None
                }
                Some(v) if v == self.true_term => Some(true),
                Some(v) if v == self.false_term => Some(false),
                Some(_) => return PropagatorResult::Unknown,
            };
            match fixed {
                Some(false) => {
                    let search = forced_searches.get_mut(reach.from.0 as usize).map(|slot| {
                        slot.get_or_insert_with(|| bfs_rows(forced_rows, vertices, reach.from))
                    });
                    let (search_reaches, path) = match search {
                        Some(s) => (
                            s.reaches_forced(spec, values, reach.to),
                            s.path_atoms(spec, values, reach.to),
                        ),
                        None => (false, None),
                    };
                    if search_reaches {
                        let Some(mut conflict) = path else {
                            return PropagatorResult::Unknown;
                        };
                        conflict.push(reach.negation);
                        return PropagatorResult::Unsat(conflict);
                    }
                }
                Some(true) => {
                    let backward = backward_searches.get_mut(reach.to.0 as usize).map(|slot| {
                        slot.get_or_insert_with(|| backward_seen(possible_in, vertices, reach.to))
                    });
                    let Some(backward) = backward else {
                        continue;
                    };
                    if !backward.possible_reaches(spec, values, reach.from) {
                        let mut conflict = backward.cut_negations(spec, values);
                        conflict.push(reach.atom);
                        return PropagatorResult::Unsat(conflict);
                    }
                }
                None => {
                    let forced = forced_searches.get_mut(reach.from.0 as usize).map(|slot| {
                        slot.get_or_insert_with(|| bfs_rows(forced_rows, vertices, reach.from))
                    });
                    let mut forced_reaches = false;
                    let mut forced_path = None;
                    if let Some(f) = forced {
                        forced_reaches = f.reaches_forced(spec, values, reach.to);
                        forced_path = f.path_atoms(spec, values, reach.to);
                    }
                    if forced_reaches {
                        if let Some(reasons) = forced_path {
                            ctx.propagate(Consequence::new(reach.atom, reasons));
                        }
                        continue;
                    }
                    let backward = backward_searches.get_mut(reach.to.0 as usize).map(|slot| {
                        slot.get_or_insert_with(|| backward_seen(possible_in, vertices, reach.to))
                    });
                    let Some(backward) = backward else {
                        continue;
                    };
                    if !backward.possible_reaches(spec, values, reach.from) {
                        let reasons = backward.cut_negations(spec, values);
                        ctx.propagate(Consequence::new(reach.negation, reasons));
                    }
                }
            }
        }

        if all_fixed && values.iter().all(|v| *v != EdgeValue::Unknown) {
            PropagatorResult::Sat
        } else {
            PropagatorResult::Unknown
        }
    }
}

impl UserPropagator for GraphModel {
    fn on_fixed(&mut self, term: TermId, value: TermId, ctx: &mut PropagatorContext) {
        // Route edge events in O(1): record them for the next run instead
        // of re-reading every edge from the manager. Atom events carry no
        // derived state (atom values are read on demand in the scan).
        if let Some(&(g, edge)) = self.edge_index.get(&term) {
            let g = g as usize;
            if value == self.true_term {
                self.caches[g].pending.push((edge, EdgeValue::True));
            } else if value == self.false_term {
                self.caches[g].pending.push((edge, EdgeValue::False));
            } else {
                // Non-Boolean fixation: fail closed to the full re-read.
                self.caches[g].invalidate();
            }
        }
        self.run(ctx);
    }

    fn final_check(&mut self, ctx: &mut PropagatorContext) -> PropagatorResult {
        self.run(ctx)
    }

    fn push(&mut self) {
        // Events continue to route while valid; nothing to do.
    }

    fn pop(&mut self, _levels: usize) {
        // Backtracking retracts fixations without individual events: the
        // maintained state can no longer be trusted until re-read.
        for cache in &mut self.caches {
            cache.invalidate();
        }
    }

    fn reset(&mut self) {
        for (g, spec) in self.graphs.iter().enumerate() {
            self.caches[g] = ViewCache::sized(spec.vertices, spec.edges.len());
        }
    }
}

#[cfg(test)]
mod tests;
