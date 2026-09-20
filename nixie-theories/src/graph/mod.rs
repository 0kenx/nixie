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
#[derive(Default)]
struct ViewCache {
    /// Packed true-edge bits of the forced view the cached results belong to.
    /// An empty key is an empty graph's key (no true edges packed), which is
    /// exactly what a fresh graph produces, so it is always valid.
    forced_key: Vec<u64>,
    forced_adjacency: Csr,
    /// Forced-view BFS by source vertex.
    forced_searches: Vec<Option<Bfs>>,
    /// `find_cycle` over the forced view (`Some(None)` = computed, acyclic).
    forced_cycle: Option<Option<Vec<u32>>>,
    /// Packed non-false-edge bits of the possible view.
    possible_key: Vec<u64>,
    possible_out: Csr,
    possible_in: Csr,
    /// Possible-view backward BFS by target vertex.
    backward_searches: Vec<Option<Backward>>,
    possible_cycle: Option<Option<Vec<u32>>>,
}

impl ViewCache {
    fn new(vertices: usize) -> Self {
        Self {
            forced_searches: (0..vertices).map(|_| None).collect(),
            backward_searches: (0..vertices).map(|_| None).collect(),
            ..Self::default()
        }
    }

    fn reset(&mut self, vertices: usize) {
        *self = Self::new(vertices);
    }
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
    /// One content-addressed cache per graph (see [`ViewCache`]).
    caches: Vec<ViewCache>,
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
        self.caches.push(ViewCache::new(0));
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
        // The graph grew: any cached per-vertex tables are the wrong size.
        if g.0 < self.caches.len() {
            self.caches[g.0].reset(self.graphs[g.0].vertices);
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
    pub fn into_propagator(self) -> (Box<dyn UserPropagator>, Vec<TermId>) {
        let watches = self.watches();
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

    /// One graph's check. See the module docs for the case analysis: every
    /// violation of the defining biconditionals over currently-fixed atoms
    /// is reported as `Unsat` with signed reasons, and every atom whose
    /// value is already determined (but unassigned) is queued.
    fn run_graph(&mut self, g: usize, ctx: &mut PropagatorContext) -> PropagatorResult {
        let spec = &self.graphs[g];

        // 1. Read the edge assignment; fail closed on non-Boolean fixations.
        // While reading, pack each view's membership bits so the caches can
        // be validated by exact comparison against the current assignment.
        let mut values = Vec::with_capacity(spec.edges.len());
        let mut forced_bits = Vec::with_capacity(spec.edges.len() / 64 + 1);
        let mut possible_bits = Vec::with_capacity(spec.edges.len() / 64 + 1);
        let mut all_fixed = true;
        let mut forced_word = 0u64;
        let mut possible_word = 0u64;
        for (i, edge) in spec.edges.iter().enumerate() {
            let bit = 1u64 << (i % 64);
            match ctx.get_fixed_value(edge.atom) {
                None => {
                    values.push(EdgeValue::Unknown);
                    all_fixed = false;
                    possible_word |= bit;
                }
                Some(v) if v == self.true_term => {
                    values.push(EdgeValue::True);
                    forced_word |= bit;
                    possible_word |= bit;
                }
                Some(v) if v == self.false_term => {
                    values.push(EdgeValue::False);
                }
                Some(_) => return PropagatorResult::Unknown,
            }
            if i % 64 == 63 {
                forced_bits.push(forced_word);
                possible_bits.push(possible_word);
                forced_word = 0;
                possible_word = 0;
            }
        }
        let tail = spec.edges.len() % 64;
        if tail != 0 || spec.edges.is_empty() {
            forced_bits.push(forced_word);
            possible_bits.push(possible_word);
        }

        // Split borrows: the adjacency tables are immutable for the rest of
        // the run, while the per-vertex memos fill in lazily — disjoint
        // fields of the same cache, borrowed through one destructuring.
        let ViewCache {
            forced_key,
            forced_adjacency,
            forced_searches,
            forced_cycle,
            possible_key,
            possible_out,
            possible_in,
            backward_searches,
            possible_cycle,
        } = &mut self.caches[g];
        if forced_key != &forced_bits {
            forced_adjacency.rebuild(spec, &values, true, false);
            *forced_key = forced_bits;
            forced_searches.clear();
            forced_searches.extend((0..spec.vertices).map(|_| None));
            *forced_cycle = None;
        }
        if possible_key != &possible_bits {
            possible_out.rebuild(spec, &values, false, false);
            possible_in.rebuild(spec, &values, false, true);
            *possible_key = possible_bits;
            backward_searches.clear();
            backward_searches.extend((0..spec.vertices).map(|_| None));
            *possible_cycle = None;
        }

        // 3. Acyclicity atom. `forced ⊆ possible`, so a forced cycle makes
        // the possible-cycle test moot; the two cases below are exclusive.
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
            let forced_cycle = forced_cycle
                .get_or_insert_with(|| find_cycle(forced_adjacency, spec.vertices))
                .clone();
            if let Some(cycle) = forced_cycle {
                // The graph already contains a cycle. `acyclic = false` is
                // the correct value; anything else conflicts or propagates.
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
                let possible_cycle = possible_cycle
                    .get_or_insert_with(|| find_cycle(possible_out, spec.vertices))
                    .clone();
                if possible_cycle.is_none() {
                    // Even the possible graph is acyclic: no completion can
                    // contain a cycle, so `acyclic` must be true. The
                    // trivial all-false-edges explanation follows MonoSAT.
                    let reasons: Vec<TermId> = spec
                        .edges
                        .iter()
                        .zip(&values)
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

        // 4. Reachability atoms.
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
                // Atom says unreachable: the forced graph must agree.
                Some(false) => {
                    let search = forced_searches.get_mut(reach.from.0 as usize).map(|slot| {
                        slot.get_or_insert_with(|| bfs(forced_adjacency, spec.vertices, reach.from))
                    });
                    let (search_reaches, path) = match search {
                        Some(s) => (
                            s.reaches_forced(spec, &values, reach.to),
                            s.path_atoms(spec, &values, reach.to),
                        ),
                        None => (false, None),
                    };
                    if search_reaches {
                        let Some(mut conflict) = path else {
                            // Reachability was witnessed but its path could
                            // not be extracted; fail closed rather than emit
                            // an unjustified conflict.
                            return PropagatorResult::Unknown;
                        };
                        conflict.push(reach.negation);
                        return PropagatorResult::Unsat(conflict);
                    }
                }
                // Atom says reachable: the possible graph must agree.
                Some(true) => {
                    let backward = backward_searches.get_mut(reach.to.0 as usize).map(|slot| {
                        slot.get_or_insert_with(|| {
                            backward_seen(possible_in, spec.vertices, reach.to)
                        })
                    });
                    let Some(backward) = backward else {
                        continue;
                    };
                    if !backward.possible_reaches(spec, &values, reach.from) {
                        let mut conflict = backward.cut_negations(spec, &values);
                        conflict.push(reach.atom);
                        return PropagatorResult::Unsat(conflict);
                    }
                }
                // Undetermined: propagate once either approximation decides.
                None => {
                    let forced = forced_searches.get_mut(reach.from.0 as usize).map(|slot| {
                        slot.get_or_insert_with(|| bfs(forced_adjacency, spec.vertices, reach.from))
                    });
                    let mut forced_reaches = false;
                    let mut forced_path = None;
                    if let Some(f) = forced {
                        forced_reaches = f.reaches_forced(spec, &values, reach.to);
                        forced_path = f.path_atoms(spec, &values, reach.to);
                    }
                    if forced_reaches {
                        if let Some(reasons) = forced_path {
                            ctx.propagate(Consequence::new(reach.atom, reasons));
                        }
                        continue;
                    }
                    let backward = backward_searches.get_mut(reach.to.0 as usize).map(|slot| {
                        slot.get_or_insert_with(|| {
                            backward_seen(possible_in, spec.vertices, reach.to)
                        })
                    });
                    let Some(backward) = backward else {
                        continue;
                    };
                    if !backward.possible_reaches(spec, &values, reach.from) {
                        let reasons = backward.cut_negations(spec, &values);
                        ctx.propagate(Consequence::new(reach.negation, reasons));
                    }
                }
            }
        }

        if all_fixed {
            PropagatorResult::Sat
        } else {
            PropagatorResult::Unknown
        }
    }
}

impl UserPropagator for GraphModel {
    fn on_fixed(&mut self, _term: TermId, _value: TermId, ctx: &mut PropagatorContext) {
        self.run(ctx);
    }

    fn final_check(&mut self, ctx: &mut PropagatorContext) -> PropagatorResult {
        self.run(ctx)
    }

    fn reset(&mut self) {
        // The caches are content-addressed and self-validating, so clearing
        // them is pure hygiene (e.g. a reset between unrelated problems).
        for cache in &mut self.caches {
            cache.reset(0);
        }
    }
}

#[cfg(test)]
mod tests;
