//! EUF Theory Solver
//!
//! The solver is split across three files along the seams of what each one is
//! responsible for:
//!
//! * this module – the e-graph's data model (`ENode`, the trails, the context
//!   stack), term interning, and the [`Theory`] implementation (`push`/`pop`/
//!   `reset`);
//! * [`congruence`] – everything that *mutates* the e-graph: use lists,
//!   signature-table maintenance and merge propagation;
//! * [`explain`] – everything that *justifies* a derived equality: conflict
//!   detection and proof-forest explanation.
//!
//! Reference: Z3's `euf_egraph.cpp` for the overall congruence-closure design.

use super::union_find::UnionFind;
#[allow(unused_imports)]
use crate::prelude::*;
use crate::theory::{Theory, TheoryId, TheoryResult};
use nixie_core::ast::TermId;
use nixie_core::error::Result;
use smallvec::SmallVec;

mod congruence;
mod explain;
#[cfg(test)]
mod tests;

/// Capacity of the explanation cache: how many (a, b) -> reasons entries to retain.
/// Each entry records the BFS-derived reason set for a pair of E-graph node indices.
/// 1024 covers the vast majority of repeated sub-explanation queries that arise from
/// congruence closure without consuming significant memory.
const EUF_EXPL_CACHE_CAPACITY: usize = 1024;

/// Bound on the pending forced-equality-atom queue.  Equality-atom propagation
/// is *search guidance*: a dropped notification only delays the propagation
/// until the decision machinery assigns the atom (at which point the theory
/// refutes the wrong polarity), it never changes the verdict.  The bound keeps
/// a long theory-replay (resync) from growing the queue without limit.
const FORCED_EQ_QUEUE_CAP: usize = 1024;

/// Records an insertion into sig_table or fingerprint_table for undo on pop().
#[derive(Debug, Clone)]
enum SigTrailEntry {
    /// Inserted `key -> node` into sig_table; undo removes `key` and restores
    /// `node_sig_key[node]` to `None` (the state before this registration).
    InsertedSig {
        key: (u32, SmallVec<[u32; 4]>),
        node: u32,
    },
    /// Removed `key -> node` from sig_table because the node's signature changed
    /// in `propagate`; undo re-inserts `key -> node` and restores
    /// `node_sig_key[node] = Some(key)`.
    RemovedSig {
        key: (u32, SmallVec<[u32; 4]>),
        node: u32,
    },
    /// Pushed node_idx into fingerprint_table[fp]; undo removes it from the bucket.
    InsertedFingerprint { fp: ENodeFingerprint, node_idx: u32 },
}

/// Function properties for dynamic arity support
#[derive(Debug, Clone, Copy, PartialEq, Eq, Default)]
pub struct FunctionProperties {
    /// Is the function associative? (e.g., +, *, and, or)
    pub associative: bool,
    /// Is the function commutative? (e.g., +, *, and, or)
    pub commutative: bool,
    /// Does the function have an identity element?
    pub has_identity: bool,
}

/// 64-bit fingerprint for fast congruence pre-filtering.
/// Before doing full signature comparison in the congruence table,
/// we compare fingerprints first (cheap u64 comparison) to avoid
/// expensive argument-level equality checks.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Default)]
pub struct ENodeFingerprint(u64);

impl ENodeFingerprint {
    /// Compute a fingerprint from a function symbol and canonical argument representatives.
    /// Uses a fast multiplicative hash to combine func and args into a single u64.
    #[must_use]
    pub fn compute(func: u32, args: &[u32]) -> Self {
        let mut h = func as u64;
        for &arg in args {
            h = h
                .wrapping_mul(0x517c_c1b7_2722_0a95)
                .wrapping_add(arg as u64);
        }
        Self(h)
    }

    /// Return the raw fingerprint value
    #[must_use]
    pub fn raw(self) -> u64 {
        self.0
    }
}

/// Congruence-closed view of one interned function application, produced by
/// [`EufSolver::function_application_entries`] for model extraction.
///
/// All representatives are canonical equivalence-class node indices (taken
/// through `find`), so applications whose arguments are pairwise congruent share
/// identical `arg_reps`/`result_rep` and collapse onto the same value class.
#[derive(Debug, Clone)]
pub struct FuncAppEntry {
    /// Canonical class representative (node index) of each argument, in order.
    pub arg_reps: SmallVec<[u32; 4]>,
    /// Every `TermId` interned into each argument's equivalence class, in the
    /// same order as `arg_reps`.  A model builder can scan these to find a
    /// member that carries a concrete value.
    pub arg_class_terms: SmallVec<[Vec<TermId>; 4]>,
    /// Canonical class representative (node index) of the application result.
    pub result_rep: u32,
    /// Every `TermId` interned into the result's equivalence class.
    pub result_class_terms: Vec<TermId>,
}

/// A term node in the E-graph
#[derive(Debug, Clone)]
struct ENode {
    /// Function symbol index; `u32::MAX` (= `ENode::NO_FUNC`) means leaf (no application).
    /// Placed first so that the hot `func` discriminant is at offset 0 of the struct.
    func: u32,
    /// 64-bit fingerprint for fast congruence pre-filtering.
    /// Placed second (after the 4-byte func + 4-byte implicit pad) so it aligns to 8 bytes
    /// without additional padding waste.
    fingerprint: ENodeFingerprint,
    /// Arguments (indices into nodes)
    args: SmallVec<[u32; 4]>,
    /// The original term
    term: TermId,
}

impl ENode {
    /// Sentinel value meaning "no function symbol" (leaf node).
    const NO_FUNC: u32 = u32::MAX;

    /// Create a leaf node (no function application).
    fn leaf(term: TermId) -> Self {
        ENode {
            func: Self::NO_FUNC,
            fingerprint: ENodeFingerprint::default(),
            args: SmallVec::new(),
            term,
        }
    }

    /// Create a function application node.
    fn app(
        func: u32,
        args: SmallVec<[u32; 4]>,
        fingerprint: ENodeFingerprint,
        term: TermId,
    ) -> Self {
        debug_assert!(
            func != Self::NO_FUNC,
            "func must not be u32::MAX (reserved sentinel)"
        );
        ENode {
            func,
            fingerprint,
            args,
            term,
        }
    }

    /// Returns true if this node is a function application (not a leaf).
    #[inline]
    fn is_app(&self) -> bool {
        self.func != Self::NO_FUNC
    }
}

/// Disequality constraint
#[derive(Debug, Clone)]
struct Diseq {
    /// First term
    lhs: u32,
    /// Second term
    rhs: u32,
    /// Reason for the disequality
    reason: TermId,
    /// `ordered_pair(find(lhs), find(rhs))` as of the last `assert_diseq` or
    /// pair-rewrite in `propagate`.  Kept in lockstep with the union-find so
    /// [`EufSolver::are_proven_disequal`] can answer from the
    /// `diseq_pair_counts` map in O(1) instead of re-walking the watch list
    /// and re-finding both endpoints of every watched disequality per query.
    cached_pair: (u32, u32),
}

/// Undo entry for mutations of the `diseq_pair_counts` map, replayed in LIFO
/// order by `pop()`.
#[derive(Debug, Clone, Copy)]
enum DiseqPairTrailEntry {
    /// `diseqs[idx]` was appended and its `cached_pair` key counted into the map.
    /// Undo: decrement the count for `diseqs[idx].cached_pair` (the disequality
    /// itself is truncated by the same pop).
    Asserted { idx: u32 },
    /// `diseqs[idx].cached_pair` was rewritten from `old` to its current value
    /// by a merge.  Undo: decrement the current key, restore `old`, count it.
    Rewrote { idx: u32, old: (u32, u32) },
}

/// A watch registered by the theory manager on a pair of nodes, fired when the
/// pair becomes equal or proven disequal in the e-graph.
///
/// This is Nixie's analogue of Z3 keeping `=`-applications as parents in the
/// e-graph (`euf_egraph.cpp`: `reinsert_parents` → congruence merge of two
/// equality enodes → `add_literal`): instead of rescanning every equality atom
/// after each merge, the atoms are indexed on the *classes of their endpoints*
/// and only the ones whose classes actually changed are revisited.
#[derive(Debug, Clone, Copy)]
pub struct EqAtomWatch {
    /// First watched node.
    pub a: u32,
    /// Second watched node.
    pub b: u32,
    /// The SAT variable of the equality/disequality atom (opaque to EUF).
    pub var: nixie_sat::Var,
    /// Whether the atom is an equality atom (`(= a b)`) as opposed to a
    /// disequality atom (`(distinct a b)` / `(not (= a b))`).
    pub is_eq: bool,
}

/// A merge reason: why two nodes became equal
#[derive(Debug, Clone)]
enum MergeReason {
    /// Direct equality assertion
    Assertion(TermId),
    /// Congruence: f(a1,...,an) = f(b1,...,bn) because ai = bi for all i
    Congruence {
        /// The terms that became equal by congruence
        term1: u32,
        term2: u32,
    },
}

/// Normalize a node pair so that `(a, b)` and `(b, a)` map to the same key.
#[inline]
fn ordered_pair(a: u32, b: u32) -> (u32, u32) {
    if a <= b { (a, b) } else { (b, a) }
}

/// A merge edge in the proof forest
#[derive(Debug, Clone)]
struct MergeEdge {
    /// The other node in the merge
    other: u32,
    /// The reason for the merge
    reason: MergeReason,
    /// Derivation-order timestamp: both directed edges of one merge share it,
    /// and it is strictly greater than the stamp of every edge that justified
    /// the merge. `try_explain_equality` picks the path that minimises this
    /// value to keep explanations acyclic (earliest-path / bottleneck search).
    stamp: u32,
}

/// EUF Theory Solver using congruence closure
#[derive(Debug)]
pub struct EufSolver {
    /// Union-Find for equivalence classes
    uf: UnionFind,
    /// E-nodes
    nodes: Vec<ENode>,
    /// Term to node index mapping.
    ///
    /// Every entry points at the node that was *created* for that term, and
    /// nodes are truncated in LIFO order by `pop()`, so the index-based `retain`
    /// there is exact.  An application is never mapped onto a pre-existing
    /// congruent node: see [`EufSolver::intern_app`].
    term_to_node: FxHashMap<TermId, u32>,
    /// Disequality constraints
    diseqs: Vec<Diseq>,
    /// Pending merges for congruence closure.
    ///
    /// Each entry carries the justification that will label the proof-forest edge
    /// once the merge is actually performed. The edge is *not* created at
    /// detection time: doing so would connect two nodes in the proof forest
    /// without performing the corresponding union, and a later merge joining the
    /// same two classes through a different route would then close a cycle in
    /// what must remain a spanning forest (see `propagate`).
    pending: Vec<(u32, u32, MergeReason)>,
    /// Use list: for each node, which applications use it as an argument.
    ///
    /// An application is registered on the *representative* of each argument, and
    /// `propagate` splices the absorbed root's list into the survivor's, so the
    /// invariant "`use_list[r]` holds every application with an argument in `r`'s
    /// class" holds for every root `r`.  Registering on the raw argument instead
    /// breaks it: an application interned while its argument was a non-root would
    /// never be re-canonicalized when that argument's class merged again, and the
    /// congruence would be missed.
    use_list: Vec<SmallVec<[u32; 8]>>,
    /// Signature table for congruence closure
    sig_table: FxHashMap<(u32, SmallVec<[u32; 4]>), u32>,
    /// For each node, the key under which it is currently registered in
    /// `sig_table` (`None` for leaf nodes and for app nodes merged into a
    /// congruent existing node on intern). `propagate` consults this to remove a
    /// node's *old* signature entry when its canonical arguments change, so that
    /// stale entries keyed by obsolete representatives never accumulate (the
    /// root cause of missed congruences / spurious sat). Parallel to `nodes`;
    /// truncated in lockstep on `pop`.
    node_sig_key: Vec<Option<(u32, SmallVec<[u32; 4]>)>>,
    /// Per-representative watch list of disequality indices: `diseq_watch[rep]`
    /// holds every asserted disequality with an endpoint currently in `rep`'s
    /// class. On a merge the loser class's watched disequalities are tested
    /// (both endpoints now equal -> conflict) and copied to the winner, so a
    /// violation is caught at the merge that causes it and `check_conflicts`
    /// never scans all disequalities. Mirrors the `use_list` migration + trailing.
    diseq_watch: Vec<Vec<u32>>,
    /// Undo trail for `diseq_watch` appends: the rep whose list was extended.
    diseq_watch_trail: Vec<u32>,
    /// Scope checkpoints into `diseq_watch_trail`, parallel to `sig_trail_limits`.
    diseq_watch_trail_limits: Vec<usize>,
    /// Refcounted map from `ordered_pair(find(lhs), find(rhs))` of every *live*
    /// asserted disequality to how many disequalities currently share that key.
    /// Maintained incrementally: `assert_diseq` counts its key in, and every
    /// merge rewrites the cached keys of the disequalities watched on either
    /// merged class (a key can only change when one of its endpoint classes
    /// merges, and the watch lists cover exactly those disequalities).  Lets
    /// [`Self::are_proven_disequal`] answer with two root lookups + one hash
    /// probe instead of walking (and re-finding) the whole per-class watch list.
    diseq_pair_counts: FxHashMap<(u32, u32), u32>,
    /// Undo trail for `diseq_pair_counts` mutations, replayed LIFO by `pop()`.
    diseq_pair_trail: Vec<DiseqPairTrailEntry>,
    /// Scope checkpoints into `diseq_pair_trail`, parallel to `sig_trail_limits`.
    diseq_pair_trail_limits: Vec<usize>,
    /// Per-disequality generation stamps used to deduplicate the walk of both
    /// merged classes' watch lists during a merge event.
    diseq_stamp: Vec<u64>,
    /// Generation counter for `diseq_stamp`.  u64: the wrap case is not merely
    /// unlikely but physically unreachable (each stamped merge costs at least a
    /// few cycles, so 2^64 stamped merges exceeds any machine's lifetime), and
    /// a wrap would make a stale stamp collide with the live generation and
    /// silently skip a cached-pair rewrite.
    diseq_stamp_gen: u64,
    /// Watch lists for equality atoms, indexed by node id: every registered
    /// [`EqAtomWatch`] whose endpoint `a` or `b` is currently in this node's
    /// class.  Migrated on merge exactly like `use_list`, so a merge only
    /// revisits the atoms whose classes changed – never the whole atom set.
    atom_watch: Vec<Vec<EqAtomWatch>>,
    /// Undo trail for `atom_watch` appends: the node whose list was extended.
    atom_watch_trail: Vec<u32>,
    /// Scope checkpoints into `atom_watch_trail`, parallel to `sig_trail_limits`.
    atom_watch_trail_limits: Vec<usize>,
    /// Atoms whose two endpoints just became equal or proven disequal, awaiting
    /// the theory manager to turn them into SAT propagations.  Bounded: the
    /// propagation is search guidance only (any dropped notification is later
    /// rediscovered by the decision machinery), so a bound costs completeness
    /// of *propagation*, never of the verdict.
    forced_eq_queue: Vec<EqAtomWatch>,
    /// Monotonic epoch, bumped on every `pop()`.  An atom is enqueued at most
    /// once per epoch (see `atom_enqueued_epoch`): within one epoch – i.e.
    /// between two backtracks – a delivered notification cannot become more
    /// true, so re-triggering merges would only rebuild the same entry.  A pop
    /// changes the epoch, making every atom re-eligible exactly when the SAT
    /// core may have unassigned it.
    atom_epoch: u64,
    /// Epoch at which each variable's atom was last enqueued (indexed by
    /// `Var::index()`), suppressing duplicate queue churn.
    atom_enqueued_epoch: Vec<u64>,
    /// Index (into `diseqs`) of a disequality detected violated during a merge or
    /// at `assert_diseq`, awaiting `check_conflicts` to surface it. None = none.
    pending_diseq_conflict: Option<u32>,
    /// Saved `pending_diseq_conflict` per scope so `pop()` restores it: a
    /// violation found inside a popped scope retracts with the merge that caused it.
    pending_trail: Vec<Option<u32>>,
    /// Scope checkpoints into `pending_trail`.
    pending_trail_limits: Vec<usize>,
    /// The two *witness nodes* of a merge that united two different
    /// distinguished values, awaiting `check_conflicts` to surface it.
    /// Recorded *after* the union and its proof-forest edges are in place:
    /// the two witnesses sat in different classes before it, so every
    /// proof-forest path between them crosses the merge's own edge and the
    /// explanation of `w1 = w2` is exactly the complete core – the literals
    /// that force the two distinguished constants together.  The value
    /// distinctness itself is a hard semantic fact that names no literal.
    /// First conflict wins, mirroring `pending_diseq_conflict`.  None = none.
    pending_value_conflict: Option<(u32, u32)>,
    /// Saved `pending_value_conflict` per scope, restored by `pop()` – a value
    /// conflict found inside a popped scope retracts with the merge that caused
    /// it (the proof edges and the union both rewind together).
    value_conflict_trail: Vec<Option<(u32, u32)>>,
    /// Scope checkpoints into `value_conflict_trail`.
    value_conflict_trail_limits: Vec<usize>,
    /// Distinctness summary of each equivalence class, indexed by node id and
    /// meaningful at roots only: `class_value[r] = Some((id, w))` iff `r` is the
    /// root of a class containing the distinguished value `id`, `w` being one
    /// node of that class carrying it (the conflict-explanation witness);
    /// `None` = the class holds no distinguished value.
    ///
    /// Non-root slots are stale by design and never read.  A merge combines the
    /// two summaries into the surviving root (two *different* ids is itself the
    /// conflict) and trails the overwritten slot so `pop()` restores it in
    /// lockstep with the union it belonged to.
    ///
    /// Parallel to `nodes`; truncated together on `pop()`.
    class_value: Vec<Option<(u32, u32)>>,
    /// Undo trail of `class_value` writes made by merges: `(root, previous)`.
    /// Rewound LIFO by `pop()`; entries naming nodes truncated away by the same
    /// pop are skipped (their slots are gone regardless).
    value_summary_trail: Vec<(u32, Option<(u32, u32)>)>,
    /// Scope checkpoints into `value_summary_trail`.
    value_summary_trail_limits: Vec<usize>,
    /// Terms the caller declared to denote pairwise-distinct distinguished
    /// values, with their distinctness ids.
    ///
    /// Symbol-level fact, *not* incremental state: it survives `reset()` (which
    /// rebuilds all nodes) and every `pop()`, so a node recreated for the same
    /// term during a rebase/replay reacquires its mark.  Keyed by `TermId`, and
    /// `intern` consults it only on a `term_to_node` miss, so the steady-state
    /// cost is zero.
    value_consts: FxHashMap<TermId, u32>,
    /// Monotone source of distinctness ids for distinguished values.
    /// Survives `reset()` alongside the registry so an id is never reused
    /// for a different constant across rebuilds (see
    /// [`Self::declare_value_const`]).
    next_value_id: u32,
    /// Fingerprint table: maps fingerprint -> list of node indices with that fingerprint.
    /// Used as a fast pre-filter before full signature comparison in congruence checks.
    ///
    /// Invariant: every key of `sig_table` has its fingerprint present here, so
    /// "fingerprint absent" soundly implies "signature absent".
    fingerprint_table: FxHashMap<ENodeFingerprint, SmallVec<[u32; 4]>>,
    /// Context stack for push/pop
    context_stack: Vec<ContextState>,
    /// Proof forest: for each node, edges to explain equalities.
    /// SmallVec<[MergeEdge; 4]> avoids heap allocation for nodes with ≤4 proof edges,
    /// which covers the vast majority of E-graph nodes in practice.
    proof_forest: Vec<SmallVec<[MergeEdge; 4]>>,
    /// Function properties for dynamic arity support
    function_properties: FxHashMap<u32, FunctionProperties>,
    /// Reused queue for newly discovered propagations during congruence closure.
    propagation_buf: Vec<(u32, u32, MergeReason)>,
    /// Undo trail for sig_table and fingerprint_table insertions.
    sig_trail: Vec<SigTrailEntry>,
    /// Scope checkpoints into sig_trail, parallel to uf.trail_limits.
    sig_trail_limits: Vec<usize>,
    /// Undo trail for proof-forest edge insertions.
    ///
    /// Each entry is the node index onto whose `proof_forest` adjacency list an
    /// edge was pushed while a scope was active.  `pop()` replays these in LIFO
    /// order, popping exactly one edge off the recorded node's list, so that merge
    /// edges appended to *pre-existing* nodes during a popped scope are removed
    /// (truncation alone only reclaims edges belonging to nodes created in the
    /// scope, leaving stale edges on older nodes that would let `explain_equality`
    /// cite retracted assertions).
    proof_trail: Vec<u32>,
    /// Scope checkpoints into proof_trail, parallel to sig_trail_limits.
    proof_trail_limits: Vec<usize>,
    /// Undo trail for `use_list` appends.
    ///
    /// Each entry is the node index onto whose `use_list` an entry was pushed
    /// while a scope was active. `pop()` replays these in LIFO order, popping
    /// exactly one entry off the recorded node's list. This removes use-list
    /// entries appended to *pre-existing* nodes during a popped scope
    /// (truncation alone only reclaims the lists of nodes created in the scope,
    /// leaving stale entries on older nodes – which would corrupt congruence
    /// once a popped node index is reused by a later `intern`).
    use_list_trail: Vec<u32>,
    /// Scope checkpoints into use_list_trail, parallel to sig_trail_limits.
    use_list_trail_limits: Vec<usize>,
    /// Reusable settled markers for try_explain_equality's bottleneck search,
    /// stamped with `explain_generation` instead of cleared between searches.
    explain_visited: Vec<u32>,
    /// Generation stamps marking which `explain_dist`/`explain_parent` entries
    /// belong to the search currently running.
    explain_seen_gen: Vec<u32>,
    /// Monotonic generation counter for the stamped explain buffers.
    explain_generation: u32,
    /// Reusable distance table for try_explain_equality. Each entry packs the
    /// lexicographic cost `(max_edge_stamp << 32) | hop_count` of the best known
    /// path from the source, so ties on the bottleneck break by shortest path –
    /// an earliest *and* compact explanation.
    explain_dist: Vec<u64>,
    /// Reusable priority queue for try_explain_equality's search, ordered by
    /// `(packed_cost, node)` ascending.
    explain_heap: crate::prelude::BinaryHeap<core::cmp::Reverse<(u64, u32)>>,
    /// Reusable parent-pointer table for explain_equality – parallel to explain_visited.
    explain_parent: Vec<Option<(u32, usize)>>,
    /// Reusable worklist of node pairs whose equality still has to be explained.
    ///
    /// `explain_equality` discharges the argument sub-goals of a congruence edge
    /// through this list instead of recursing, so its stack consumption is
    /// constant no matter how deeply the terms nest.
    explain_todo: Vec<(u32, u32)>,
    /// Pairs already scheduled on `explain_todo` during the current explanation,
    /// normalized via `ordered_pair`. Expanding every pair at most once avoids
    /// redundant path searches and bounds the worklist loop by the number of
    /// distinct node pairs.
    explain_enqueued: FxHashSet<(u32, u32)>,
    /// Bounded LRU cache for explanation results.
    ///
    /// Maps `(a, b)` node-index pairs to the `Vec<TermId>` reason set returned by
    /// `try_explain_equality`.  Only *complete* explanations are stored.  The
    /// cache is valid as long as the proof forest is unchanged; it is cleared
    /// eagerly whenever an edge is added (`propagate`), removed (`pop`), or the
    /// whole solver is `reset`, so a stale entry can never be observed.
    expl_cache: crate::lru_cache::LruCache<(u32, u32), Vec<TermId>>,
    /// Monotonic counter handing out `MergeEdge::stamp` values in derivation
    /// order. Never rewound on `pop()`: edges re-added after a backtrack are
    /// genuinely derived later, so larger stamps keep the invariant intact.
    proof_stamp: u32,
}

/// State to save for push/pop
#[derive(Debug, Clone)]
struct ContextState {
    num_nodes: usize,
    num_diseqs: usize,
}

impl Default for EufSolver {
    fn default() -> Self {
        Self::new()
    }
}

impl EufSolver {
    /// Create a new EUF solver
    #[must_use]
    pub fn new() -> Self {
        Self {
            uf: UnionFind::new(0),
            nodes: Vec::new(),
            term_to_node: FxHashMap::default(),
            diseqs: Vec::new(),
            pending: Vec::new(),
            use_list: Vec::new(),
            sig_table: FxHashMap::default(),
            node_sig_key: Vec::new(),
            diseq_watch: Vec::new(),
            diseq_watch_trail: Vec::new(),
            diseq_watch_trail_limits: Vec::new(),
            diseq_pair_counts: FxHashMap::default(),
            diseq_pair_trail: Vec::new(),
            diseq_pair_trail_limits: Vec::new(),
            diseq_stamp: Vec::new(),
            diseq_stamp_gen: 0,
            atom_watch: Vec::new(),
            atom_watch_trail: Vec::new(),
            atom_watch_trail_limits: Vec::new(),
            forced_eq_queue: Vec::new(),
            atom_epoch: 1,
            atom_enqueued_epoch: Vec::new(),
            pending_diseq_conflict: None,
            pending_trail: Vec::new(),
            pending_trail_limits: Vec::new(),
            pending_value_conflict: None,
            value_conflict_trail: Vec::new(),
            value_conflict_trail_limits: Vec::new(),
            class_value: Vec::new(),
            value_summary_trail: Vec::new(),
            value_summary_trail_limits: Vec::new(),
            value_consts: FxHashMap::default(),
            next_value_id: 0,
            fingerprint_table: FxHashMap::default(),
            context_stack: Vec::new(),
            proof_forest: Vec::new(),
            function_properties: FxHashMap::default(),
            propagation_buf: Vec::new(),
            sig_trail: Vec::new(),
            sig_trail_limits: Vec::new(),
            proof_trail: Vec::new(),
            proof_trail_limits: Vec::new(),
            use_list_trail: Vec::new(),
            use_list_trail_limits: Vec::new(),
            explain_visited: Vec::new(),
            explain_seen_gen: Vec::new(),
            explain_generation: 0,
            explain_dist: Vec::new(),
            explain_heap: crate::prelude::BinaryHeap::new(),
            explain_parent: Vec::new(),
            explain_todo: Vec::new(),
            explain_enqueued: FxHashSet::default(),
            expl_cache: crate::lru_cache::LruCache::new(EUF_EXPL_CACHE_CAPACITY),
            proof_stamp: 0,
        }
    }

    /// Intern a term, returning its node index
    #[inline]
    pub fn intern(&mut self, term: TermId) -> u32 {
        if let Some(&idx) = self.term_to_node.get(&term) {
            return idx;
        }

        // A term the caller declared a distinguished value starts its class
        // summary at that id (see `class_value`); the node itself is an
        // ordinary leaf.  Reached only on a memo miss, so this costs nothing
        // once the term is interned – and, crucially, re-marking on every
        // rebuild after a `reset()`/backtrack is automatic: the registry is a
        // property of the *symbol*, not of any one node's lifetime.
        if let Some(&value) = self.value_consts.get(&term) {
            let idx = self.nodes.len() as u32;
            self.nodes.push(ENode::leaf(term));
            self.uf.add();
            self.use_list.push(SmallVec::new());
            self.proof_forest.push(SmallVec::new());
            self.node_sig_key.push(None);
            self.class_value.push(Some((value, idx)));
            self.term_to_node.insert(term, idx);
            return idx;
        }

        let idx = self.nodes.len() as u32;
        self.nodes.push(ENode::leaf(term));
        self.uf.add();
        self.use_list.push(SmallVec::new());
        self.proof_forest.push(SmallVec::new());
        self.node_sig_key.push(None);
        self.class_value.push(None);
        self.term_to_node.insert(term, idx);
        idx
    }

    /// Declare that `term` denotes one element of a family of pairwise-distinct
    /// distinguished values, identified by `value`.
    ///
    /// Two live nodes whose ids differ can never merge: the merge loop in the
    /// congruence-closure propagator turns the attempt into a conflict whose
    /// explanation is the (complete) justification of the equality it
    /// contradicts – the distinctness of the values themselves is a hard
    /// semantic fact contributing no literal.
    /// Equal ids mean the same element and merge freely.
    ///
    /// The caller owns id assignment (one fresh id per distinct constant).
    /// Registering the same term twice keeps the first id.  This is the nixie
    /// analogue of Z3's model values (`mk_model_value` + `mark_interpreted`,
    /// merged-distinct check in `euf_egraph.cpp`): it exists so the large-
    /// `distinct` injective-map encoding needs O(n) e-graph state instead of
    /// O(n²) pairwise disequality edges.  See `Solver::encode_distinct_*` in
    /// `nixie-solver/src/solver/encode.rs`.
    pub fn declare_value_const(&mut self, term: TermId, value: u32) {
        self.value_consts.entry(term).or_insert(value);
    }

    /// Mint a fresh distinctness id (monotone, never reused across rebuilds).
    pub fn fresh_value_id(&mut self) -> u32 {
        let id = self.next_value_id;
        self.next_value_id = id
            .checked_add(1)
            .expect("e-graph value-id space exhausted (2^32 constants)");
        id
    }

    /// Intern a function application.
    ///
    /// A new term **always** gets a node of its own.  When the signature table
    /// already holds a congruent application the two are joined by a *merge*, not
    /// by sharing a node index.
    ///
    /// Sharing the index was a backtracking bug: the congruence rests on the
    /// argument classes that hold right now, but `term_to_node` survives `pop()`
    /// (its entries are dropped by node index, and the borrowed index belongs to
    /// an older, still-live node).  After `a = 0` was retracted, `f(0)` therefore
    /// stayed pinned to `f(a)`'s node – so `f(0)` had no node, no use-list entry
    /// and no signature of its own, the congruence `f(f(a)) = f(0)` could never be
    /// discovered, and the solver answered `sat` for
    /// `a ∈ {0,1} ∧ f(0),f(1) ∈ {0,1} ∧ f(f(a)) > 1`, which has no model.
    /// Merging instead keeps the equality on the trail, where `pop()` retracts it
    /// with everything else.  Reference: Z3's `euf_egraph.cpp`, where
    /// `egraph::mk` calls `push_merge(n, n2)` on a congruence-table hit.
    #[inline]
    pub fn intern_app(
        &mut self,
        term: TermId,
        func: u32,
        args: impl IntoIterator<Item = u32>,
    ) -> u32 {
        if let Some(&idx) = self.term_to_node.get(&term) {
            return idx;
        }

        let args: SmallVec<[u32; 4]> = args.into_iter().collect();

        // Flatten for associative functions
        let flattened_args = self.flatten_args(func, &args);

        // Canonicalize arguments (handles commutativity and finds canonical reps)
        let canonical_args = self.canonicalize_args(func, &flattened_args);

        // Compute fingerprint for fast congruence pre-filtering
        let fp = ENodeFingerprint::compute(func, &canonical_args);

        let sig = (func, canonical_args);
        let congruent = self.lookup_valid_sig(&sig);

        let idx = self.nodes.len() as u32;
        self.nodes
            .push(ENode::app(func, flattened_args.clone(), fp, term));
        self.uf.add();
        self.use_list.push(SmallVec::new());
        self.proof_forest.push(SmallVec::new());
        // Applications are never distinguished values (only leaf constants are
        // registered via `declare_value_const`), so the class summary starts
        // empty; a value enters the class only by merging with a marked leaf.
        self.class_value.push(None);
        // Record the key under which this node is registered in sig_table (None
        // when it will merge into a congruent existing node and so never publish
        // its own signature), so a later signature change in `propagate` can
        // remove exactly this entry.
        self.node_sig_key.push(if congruent.is_some() {
            None
        } else {
            Some(sig.clone())
        });
        self.term_to_node.insert(term, idx);

        // Register the application on the *representative* of each argument, so a
        // later merge of that class re-canonicalizes this node.  Trailed so pop()
        // removes these appends from pre-existing argument nodes (idx itself is
        // truncated wholesale).
        for &arg in &flattened_args {
            let arg_root = self.uf.find(arg);
            self.use_list_push(arg_root, idx);
        }

        match congruent {
            Some(existing) => {
                // The signature is already published under `existing`; leave the
                // entry alone (its undo record is a plain `remove`, so overwriting
                // would lose the older mapping on pop) and record the congruence
                // as a retractable merge instead.
                self.merge_congruent(idx, existing);
            }
            None => {
                self.insert_signature(func, sig.1, idx, fp);
            }
        }

        idx
    }

    /// Merge two equivalence classes
    #[inline]
    pub fn merge(&mut self, a: u32, b: u32, reason: TermId) -> Result<()> {
        // Any pending merge invalidates previously cached explanations because the
        // proof forest will grow new edges that could shorten existing paths.
        self.expl_cache.clear();
        self.pending.push((a, b, MergeReason::Assertion(reason)));
        self.propagate();
        Ok(())
    }

    /// Assert a disequality
    pub fn assert_diseq(&mut self, a: u32, b: u32, reason: TermId) {
        let idx = self.diseqs.len() as u32;
        // Watch the disequality on each endpoint's current representative.
        // When either class later merges, `propagate` tests it for violation.
        // find_no_compress (read-only): the watch key is the current rep, and
        // migration on merge keeps it current, so we never need to mutate here.
        let ra = self.uf.find_no_compress(a);
        let rb = self.uf.find_no_compress(b);
        let cached_pair = ordered_pair(ra, rb);
        // Count the pair into the O(1) proven-disequality index (trailed).
        let e = self.diseq_pair_counts.entry(cached_pair).or_insert(0);
        *e = e.saturating_add(1);
        if !self.diseq_pair_trail_limits.is_empty() {
            self.diseq_pair_trail
                .push(DiseqPairTrailEntry::Asserted { idx });
        }
        self.diseqs.push(Diseq {
            lhs: a,
            rhs: b,
            reason,
            cached_pair,
        });
        self.diseq_stamp.push(0);
        self.diseq_watch_push(ra, idx);
        if ra != rb {
            self.diseq_watch_push(rb, idx);
        } else if self.pending_diseq_conflict.is_none() {
            // Already equal: the new disequality is violated right now.
            self.pending_diseq_conflict = Some(idx);
        }
        // The new disequality may make equality atoms between these two
        // classes *proven disequal* right away: wake the atoms watched on
        // either endpoint class so the manager can propagate them.
        if ra != rb {
            self.wake_atom_watch_on_diseq(ra, rb);
        }
    }

    /// Test every equality atom watched between the two freshly
    /// disequality-connected classes, enqueueing the forced ones.  An atom is
    /// forced exactly when its near endpoint sits in one class and its far
    /// endpoint in the other; such an atom is registered on **both** classes'
    /// lists (side-ordered), so walking the shorter list alone finds them all –
    /// entries whose far endpoint lies elsewhere cost one root lookup each and
    /// are dropped.  The near endpoint's root is the list owner by the
    /// side-ordering invariant of [`Self::watch_eq_atom`].
    fn wake_atom_watch_on_diseq(&mut self, r1: u32, r2: u32) {
        let (root, other) = {
            let l1 = self.atom_watch.get(r1 as usize).map_or(0, Vec::len);
            let l2 = self.atom_watch.get(r2 as usize).map_or(0, Vec::len);
            if l1 <= l2 { (r1, r2) } else { (r2, r1) }
        };
        let len = self.atom_watch.get(root as usize).map_or(0, Vec::len);
        for i in 0..len {
            let w = self.atom_watch[root as usize][i];
            if self.uf.find_no_compress(w.b) == other {
                self.enqueue_forced_atom(w);
            }
        }
    }

    /// Enqueue `w` for SAT-side propagation, deduplicated per epoch: within one
    /// epoch (between backtracks) an atom is delivered at most once, so
    /// re-triggering merges cannot churn the queue with copies of entries the
    /// manager has already consumed (or that are already assigned).
    fn enqueue_forced_atom(&mut self, w: EqAtomWatch) {
        if self.forced_eq_queue.len() >= FORCED_EQ_QUEUE_CAP {
            return;
        }
        let slot = w.var.index();
        if slot >= self.atom_enqueued_epoch.len() {
            self.atom_enqueued_epoch.resize(slot + 1, 0);
        }
        if self.atom_enqueued_epoch[slot] == self.atom_epoch {
            return;
        }
        self.atom_enqueued_epoch[slot] = self.atom_epoch;
        self.forced_eq_queue.push(w);
    }

    /// Register an equality-atom watch on the classes of `a` and `b`.
    ///
    /// See the `EqAtomWatch` payload type.  Registration does not enqueue an already-forced
    /// atom: triggers fire on the merges and disequality assertions that make
    /// atoms forced, mirroring the previous rescan-based propagation's
    /// behaviour (which likewise only observed state *changes*).
    ///
    /// Each list copy is stored *side-ordered*: the entry's `a` endpoint is the
    /// one whose class owns the list it sits on (`find(a) == list owner`), and
    /// `b` is the far endpoint.  The watch lists migrate with their classes on
    /// every merge (exactly like `use_list`/`diseq_watch`), so the invariant
    /// holds for as long as the entry lives.  It is what lets the trigger and
    /// wake walks find only the far endpoint's root – one union-find walk per
    /// entry instead of two.  A hypothetical invariant violation can only miss
    /// or add a queue entry, and every queued entry is re-validated against
    /// the live e-graph before it becomes a propagation, so trusting the
    /// invariant never affects the verdict.
    pub fn watch_eq_atom(&mut self, a: u32, b: u32, var: nixie_sat::Var, is_eq: bool) {
        let ra = self.uf.find_no_compress(a);
        let rb = self.uf.find_no_compress(b);
        self.atom_watch_push(ra, EqAtomWatch { a, b, var, is_eq });
        if ra != rb {
            self.atom_watch_push(
                rb,
                EqAtomWatch {
                    a: b,
                    b: a,
                    var,
                    is_eq,
                },
            );
        }
    }

    /// Drain the queue of atoms whose endpoints became equal or proven
    /// disequal.  The theory manager converts each into a SAT propagation with
    /// an explanation; anything it does not consume is simply dropped (the
    /// atoms stay registered, so a later merge of their classes re-triggers).
    pub fn drain_forced_eq_atoms(&mut self) -> Vec<EqAtomWatch> {
        core::mem::take(&mut self.forced_eq_queue)
    }

    /// Check if two terms are equivalent
    #[inline]
    pub fn are_equal(&mut self, a: u32, b: u32) -> bool {
        self.uf.same(a, b)
    }

    /// Get the representative of a term
    #[inline]
    pub fn find(&mut self, a: u32) -> u32 {
        self.uf.find(a)
    }

    /// Get the representative of a term without path compression (immutable)
    #[inline]
    pub fn find_immutable(&self, a: u32) -> u32 {
        self.uf.find_no_compress(a)
    }

    /// Check equivalence without mutation (immutable)
    #[inline]
    pub fn are_equal_immutable(&self, a: u32, b: u32) -> bool {
        self.uf.same_no_compress(a, b)
    }

    /// Whether an *asserted* disequality has both endpoints in the equivalence
    /// classes of `a` and `b` (i.e. `a` and `b` are PROVEN disequal, not merely
    /// "not currently known equal").
    ///
    /// O(1): two root lookups plus one probe of `diseq_pair_counts`, whose keys
    /// are exactly the `ordered_pair` of current roots of every live asserted
    /// disequality (maintained by `assert_diseq` and rewritten on merge – see
    /// `Diseq::cached_pair`).  The previous implementation walked the whole
    /// per-class `diseq_watch` list and re-found both endpoints of every entry
    /// per query, which dominated QF_UF runtime on all-different-heavy
    /// benchmarks (quasigroup existence problems).
    pub fn are_proven_disequal(&self, a: u32, b: u32) -> bool {
        let ra = self.uf.find_no_compress(a);
        let rb = self.uf.find_no_compress(b);
        ra != rb
            && (self.diseq_pair_counts.contains_key(&ordered_pair(ra, rb))
                || self.roots_value_apart(ra, rb))
    }

    /// Whether two *root* nodes carry different distinguished-value summaries
    /// – the mark-based form of proven disequality (two different ground
    /// constants can never merge).  Callers that also need a *reason* should
    /// treat a `None` from `try_explain_diseq` on a value-apart pair as an
    /// empty (tautological) justification, not as "not proven".
    fn roots_value_apart(&self, ra: u32, rb: u32) -> bool {
        let va = self.class_value.get(ra as usize).copied().flatten();
        let vb = self.class_value.get(rb as usize).copied().flatten();
        va.is_some_and(|x| vb.is_some_and(|y| x != y))
    }

    /// Whether two nodes' classes carry different distinguished-value
    /// summaries (the tautological ground-constant form of apartness).
    #[must_use]
    pub fn classes_value_apart(&self, a: u32, b: u32) -> bool {
        self.roots_value_apart(self.uf.find_no_compress(a), self.uf.find_no_compress(b))
    }

    /// Get the number of E-graph nodes
    pub fn node_count(&self) -> usize {
        self.nodes.len()
    }

    /// Whether the e-graph contains any function-application nodes (as opposed
    /// to only leaf constants). Used to gate the from-scratch rebuild backstop
    /// in the CDCL(T) final check: the incremental-state false-sat bug
    /// (live e-graph diverging from a fresh replay of the same equalities)
    /// manifests on function-bearing EUF, not on pure-equality (constants-only)
    /// problems.
    pub fn has_app_nodes(&self) -> bool {
        self.nodes.iter().any(|n| n.is_app())
    }

    /// Get the term associated with a node index
    pub fn node_term(&self, idx: u32) -> Option<TermId> {
        self.nodes.get(idx as usize).map(|n| n.term)
    }

    /// Every **live** (in-scope) disequality as a pair of terms.
    ///
    /// `diseqs` is scope-truncated on `pop`, so this is exactly the set of
    /// `a ≠ b` facts currently asserted.  Used by theory combination as a
    /// *care graph*: the only shared-term pairs whose equality could possibly
    /// conflict with EUF are these, so an arithmetic entailment probe need only
    /// run on them (and only when arithmetic's model already equates the two) –
    /// O(#disequalities) instead of O(n²) over the whole interface.
    pub fn live_diseq_pairs(&self) -> Vec<(TermId, TermId)> {
        self.diseqs
            .iter()
            .filter_map(|d| Some((self.node_term(d.lhs)?, self.node_term(d.rhs)?)))
            .collect()
    }

    /// Every term that appears as the argument of a function application in
    /// the e-graph – the structural EUF interface (congruence fires on these
    /// terms' equality).
    pub fn app_argument_terms(&self) -> rustc_hash::FxHashSet<TermId> {
        let mut out: rustc_hash::FxHashSet<TermId> = rustc_hash::FxHashSet::default();
        for n in &self.nodes {
            if n.is_app() {
                for &arg_node in &n.args {
                    if let Some(t) = self.node_term(arg_node) {
                        out.insert(t);
                    }
                }
            }
        }
        out
    }

    /// Get the function symbol of a node (if it is a function application)
    pub fn node_func(&self, idx: u32) -> Option<u32> {
        self.nodes
            .get(idx as usize)
            .and_then(|n| if n.is_app() { Some(n.func) } else { None })
    }

    /// Get the arguments of a node (if it is a function application)
    pub fn node_args(&self, idx: u32) -> Option<&SmallVec<[u32; 4]>> {
        let node = self.nodes.get(idx as usize)?;
        if node.is_app() {
            Some(&node.args)
        } else {
            None
        }
    }

    /// Debug-only (NIXIE_SCAN_VIOL): indices of every interned function
    /// application node, for congruence-gap diagnostics.
    #[cfg(debug_assertions)]
    pub fn debug_app_nodes(&self) -> Vec<u32> {
        self.nodes
            .iter()
            .enumerate()
            .filter(|(_, n)| n.is_app())
            .map(|(i, _)| i as u32)
            .collect()
    }

    /// Production accessor for the application-node indices (same set as
    /// [`Self::debug_app_nodes`], available in release builds — the
    /// congruence-gap repair walks it on the final candidate).
    pub fn app_nodes(&self) -> Vec<u32> {
        self.nodes
            .iter()
            .enumerate()
            .filter(|(_, n)| n.is_app())
            .map(|(i, _)| i as u32)
            .collect()
    }

    /// Look up the node index for a given TermId
    pub fn term_to_node(&self, term: TermId) -> Option<u32> {
        self.term_to_node.get(&term).copied()
    }

    /// Iterate over all node indices that are function applications of a given function symbol.
    /// Returns a Vec of node indices.
    pub fn apps_by_func(&self, func_id: u32) -> Vec<u32> {
        let mut result = Vec::new();
        for (idx, node) in self.nodes.iter().enumerate() {
            if node.is_app() && node.func == func_id {
                result.push(idx as u32);
            }
        }
        result
    }

    /// Collect, for every interned application of `func_id`, the congruence-closed
    /// data a model builder needs to assemble a function interpretation.
    ///
    /// For each application node `f(a1, …, an)` the returned [`FuncAppEntry`]
    /// records:
    /// - `arg_reps`: the canonical equivalence-class representative (node index,
    ///   obtained via [`find_immutable`](Self::find_immutable)) of each argument,
    /// - `arg_class_terms`: every `TermId` interned into each argument's class –
    ///   so the caller can pick whichever member carries a concrete model value,
    /// - `result_rep`: the canonical class representative of the application
    ///   itself,
    /// - `result_class_terms`: every `TermId` interned into the result's class.
    ///
    /// Because the argument and result classes are taken through `find`, two
    /// applications whose arguments are pairwise congruent (e.g. `f(a)` and
    /// `f(b)` when `a = b`) yield identical `arg_reps` and `result_rep`. The
    /// caller can therefore deduplicate on `arg_reps` and rely on congruence
    /// having already collapsed them onto the same value class.
    ///
    /// This is a read-only `O(nodes)` scan (it never mutates the union-find, so
    /// no path compression occurs) and is intended for the post-`Sat` model
    /// extraction path, not the hot solving loop.
    #[must_use]
    pub fn function_application_entries(&self, func_id: u32) -> Vec<FuncAppEntry> {
        // Single O(nodes) pass: bucket every node's TermId under its canonical
        // class representative.  This avoids the O(apps × nodes) blow-up of
        // calling `class_members` once per application.
        let mut class_to_terms: FxHashMap<u32, Vec<TermId>> = FxHashMap::default();
        for idx in 0..self.nodes.len() as u32 {
            let rep = self.uf.find_no_compress(idx);
            class_to_terms
                .entry(rep)
                .or_default()
                .push(self.nodes[idx as usize].term);
        }

        let mut entries = Vec::new();
        for (idx, node) in self.nodes.iter().enumerate() {
            if !node.is_app() || node.func != func_id {
                continue;
            }

            // Canonical class rep of each argument plus the member TermIds of
            // that class (for value resolution by the caller).
            let mut arg_reps: SmallVec<[u32; 4]> = SmallVec::with_capacity(node.args.len());
            let mut arg_class_terms: SmallVec<[Vec<TermId>; 4]> =
                SmallVec::with_capacity(node.args.len());
            for &arg in &node.args {
                let rep = self.uf.find_no_compress(arg);
                arg_reps.push(rep);
                arg_class_terms.push(class_to_terms.get(&rep).cloned().unwrap_or_default());
            }

            let result_rep = self.uf.find_no_compress(idx as u32);
            let result_class_terms = class_to_terms.get(&result_rep).cloned().unwrap_or_default();

            entries.push(FuncAppEntry {
                arg_reps,
                arg_class_terms,
                result_rep,
                result_class_terms,
            });
        }
        entries
    }

    /// Get all members of an equivalence class (all node indices with the same representative).
    /// This is an O(n) scan; for performance-critical paths, consider caching.
    pub fn class_members(&self, class_rep: u32) -> Vec<u32> {
        let rep = self.uf.find_no_compress(class_rep);
        let mut members = Vec::new();
        for idx in 0..self.nodes.len() {
            if self.uf.find_no_compress(idx as u32) == rep {
                members.push(idx as u32);
            }
        }
        members
    }

    /// Iterate over all node indices (0..node_count)
    pub fn all_node_indices(&self) -> std::ops::Range<u32> {
        0..self.nodes.len() as u32
    }

    /// Get all distinct function symbols present in the E-graph
    pub fn all_func_symbols(&self) -> Vec<u32> {
        use rustc_hash::FxHashSet;
        let mut funcs = FxHashSet::default();
        for node in &self.nodes {
            if node.is_app() {
                funcs.insert(node.func);
            }
        }
        funcs.into_iter().collect()
    }

    /// Get the fingerprint table size (for testing/debugging)
    #[cfg(test)]
    fn fingerprint_table_len(&self) -> usize {
        self.fingerprint_table.len()
    }

    /// Get the sig table size (for testing/debugging)
    #[cfg(test)]
    fn sig_table_len(&self) -> usize {
        self.sig_table.len()
    }
}

impl Theory for EufSolver {
    fn id(&self) -> TheoryId {
        TheoryId::EUF
    }

    fn name(&self) -> &str {
        "EUF"
    }

    fn can_handle(&self, _term: TermId) -> bool {
        // EUF can handle equality and function applications
        true
    }

    // Audit note (theories-euf): `EufSolver` (like `crate::simplify` and
    // the MBQI matcher) only ever sees opaque `TermId`s here -- it has no
    // AST/term-manager access, so it cannot parse an arbitrary boolean
    // `term` into the `(lhs, rhs)` pair a "term is a true/false equality"
    // assertion needs. The production integration
    // (`nixie-solver`'s theory manager) knows this and never calls these
    // two generic `Theory` methods: it always resolves `lhs`/`rhs` itself
    // and calls `merge`/`assert_diseq` directly with the correctly parsed
    // nodes. These two methods exist only to satisfy the `Theory` trait
    // for callers that go through the generic interface; interning `term`
    // is the only thing they can honestly do without term structure.
    fn assert_true(&mut self, term: TermId) -> Result<TheoryResult> {
        let _ = self.intern(term);
        Ok(TheoryResult::Sat)
    }

    fn assert_false(&mut self, term: TermId) -> Result<TheoryResult> {
        // Previously called `self.assert_diseq(node, node, term)` here --
        // asserting a node disequal to ITSELF, which is unconditionally
        // false in any congruence closure. That made every call to this
        // method (regardless of what `term` actually meant) an instant,
        // fabricated contradiction. Since this method cannot honestly
        // determine `term`'s actual negated meaning without term
        // structure (see the note above), the correct, non-fabricating
        // behavior is to record the term without asserting anything false
        // about it -- mirroring `assert_true`'s equally honest limitation
        // above -- rather than poison every subsequent `check()`.
        let _ = self.intern(term);
        Ok(TheoryResult::Sat)
    }

    fn check(&mut self) -> Result<TheoryResult> {
        if let Some(conflict) = self.check_conflicts() {
            Ok(TheoryResult::Unsat(conflict))
        } else {
            Ok(TheoryResult::Sat)
        }
    }

    fn push(&mut self) {
        self.context_stack.push(ContextState {
            num_nodes: self.nodes.len(),
            num_diseqs: self.diseqs.len(),
        });
        self.uf.push();
        // Record sig_trail checkpoint, mirroring uf.trail_limits.push(...)
        self.sig_trail_limits.push(self.sig_trail.len());
        // Record proof_trail checkpoint so pop() can rewind proof-forest edges
        // appended during this scope.
        self.proof_trail_limits.push(self.proof_trail.len());
        // Record use_list_trail checkpoint so pop() can rewind use-list appends
        // to pre-existing nodes made during this scope.
        self.use_list_trail_limits.push(self.use_list_trail.len());
        // Disequality watch-list + pending-conflict checkpoints for pop().
        self.diseq_watch_trail_limits
            .push(self.diseq_watch_trail.len());
        self.diseq_pair_trail_limits
            .push(self.diseq_pair_trail.len());
        self.atom_watch_trail_limits
            .push(self.atom_watch_trail.len());
        self.pending_trail_limits.push(self.pending_trail.len());
        self.pending_trail.push(self.pending_diseq_conflict);
        self.value_conflict_trail_limits
            .push(self.value_conflict_trail.len());
        self.value_conflict_trail.push(self.pending_value_conflict);
        self.value_summary_trail_limits
            .push(self.value_summary_trail.len());
    }

    fn pop(&mut self) {
        if let Some(state) = self.context_stack.pop() {
            let num_nodes = state.num_nodes;

            // A new epoch begins: every equality atom becomes eligible for
            // enqueue again (the SAT core may have unassigned it above the
            // rollback point).  Cleared rather than stamped so a pop never has
            // to touch the per-variable vector.
            self.atom_epoch = self.atom_epoch.wrapping_add(1);

            // Every merge is applied to a fixed point before control leaves the
            // e-graph, so this queue is normally empty; clearing it makes that a
            // guarantee rather than an assumption, so no merge scheduled inside
            // the popped scope can be applied after it is gone.
            self.pending.clear();

            // Rewind the proven-disequality index to the scope-entry state,
            // BEFORE the disequality vector itself is truncated: every undo
            // step reads `diseqs[idx].cached_pair`, including the
            // `Asserted` entries whose disequality is about to vanish.
            // LIFO replay of the rewrites restores both the pair counts and
            // each disequality's cached key exactly (a key rewritten twice in
            // the scope is unwound twice, ending at its scope-entry value).
            if let Some(pair_limit) = self.diseq_pair_trail_limits.pop() {
                while self.diseq_pair_trail.len() > pair_limit {
                    match self.diseq_pair_trail.pop() {
                        Some(DiseqPairTrailEntry::Asserted { idx }) => {
                            if let Some(d) = self.diseqs.get(idx as usize) {
                                let key = d.cached_pair;
                                self.dec_diseq_pair(key);
                            }
                        }
                        Some(DiseqPairTrailEntry::Rewrote { idx, old }) => {
                            let cur = self
                                .diseqs
                                .get_mut(idx as usize)
                                .map(|d| core::mem::replace(&mut d.cached_pair, old));
                            if let Some(cur) = cur {
                                self.dec_diseq_pair(cur);
                                self.inc_diseq_pair(old);
                            }
                        }
                        None => break,
                    }
                }
            }

            self.nodes.truncate(num_nodes);
            self.diseqs.truncate(state.num_diseqs);
            self.diseq_stamp.truncate(state.num_diseqs);
            self.uf.pop();

            // Also truncate related structures. Truncation removes the adjacency
            // lists of nodes created in the popped scope, but NOT edges appended to
            // pre-existing nodes' lists – those are undone via proof_trail below.
            self.use_list.truncate(num_nodes);
            self.proof_forest.truncate(num_nodes);
            self.node_sig_key.truncate(num_nodes);
            self.diseq_watch.truncate(num_nodes);
            self.atom_watch.truncate(num_nodes);
            self.class_value.truncate(num_nodes);

            // Rewind use_list_trail: for each append recorded during the popped
            // scope, pop exactly one entry off the recorded node's use-list.
            // Nodes created in this scope (index >= num_nodes) were already
            // dropped by the truncate above, so guard against them.
            if let Some(use_list_limit) = self.use_list_trail_limits.pop() {
                while self.use_list_trail.len() > use_list_limit {
                    let Some(node) = self.use_list_trail.pop() else {
                        break;
                    };
                    if (node as usize) < self.use_list.len() {
                        self.use_list[node as usize].pop();
                    }
                }
            }

            // Rewind proof_trail: for each edge recorded during the popped scope,
            // pop exactly one edge off the recorded node's adjacency list. Nodes
            // created in this scope (index >= num_nodes) were already dropped by
            // the truncate above, so guard against out-of-range indices.
            if let Some(proof_limit) = self.proof_trail_limits.pop() {
                while self.proof_trail.len() > proof_limit {
                    let Some(node) = self.proof_trail.pop() else {
                        break;
                    };
                    if (node as usize) < self.proof_forest.len() {
                        self.proof_forest[node as usize].pop();
                    }
                }
            }

            // Any cached explanation may reference edges just removed; drop them.
            self.expl_cache.clear();

            // Rewind diseq_watch_trail: for each watch-list append recorded
            // during the popped scope, pop one entry off the recorded rep's list
            // (mirror of use_list_trail above).
            if let Some(dw_limit) = self.diseq_watch_trail_limits.pop() {
                while self.diseq_watch_trail.len() > dw_limit {
                    let Some(rep) = self.diseq_watch_trail.pop() else {
                        break;
                    };
                    if (rep as usize) < self.diseq_watch.len() {
                        self.diseq_watch[rep as usize].pop();
                    }
                }
            }
            // Rewind atom_watch_trail: same LIFO one-append-one-pop discipline
            // for the equality-atom watch lists.
            if let Some(aw_limit) = self.atom_watch_trail_limits.pop() {
                while self.atom_watch_trail.len() > aw_limit {
                    let Some(node) = self.atom_watch_trail.pop() else {
                        break;
                    };
                    if (node as usize) < self.atom_watch.len() {
                        self.atom_watch[node as usize].pop();
                    }
                }
            }
            // Restore pending_diseq_conflict to its scope-entry value: the saved
            // value lives at index `pending_limit` (pushed at scope entry), then
            // the trail is rewound to that checkpoint.
            if let Some(pending_limit) = self.pending_trail_limits.pop() {
                self.pending_diseq_conflict = self
                    .pending_trail
                    .get(pending_limit)
                    .copied()
                    .unwrap_or(None);
                self.pending_trail.truncate(pending_limit);
            }

            // Restore pending_value_conflict the same way, then rewind the
            // class-value summary writes made by this scope's merges.  Each
            // entry names the surviving root whose slot was overwritten and the
            // value it held before; LIFO replay undoes them exactly (a slot
            // rewritten twice in the scope is restored twice, ending at its
            // scope-entry value).  Entries whose node was truncated away by this
            // same pop are skipped: their slots no longer exist, and a re-intern
            // of the term rebuilds the mark from `value_consts`.
            if let Some(value_limit) = self.value_conflict_trail_limits.pop() {
                self.pending_value_conflict = self
                    .value_conflict_trail
                    .get(value_limit)
                    .copied()
                    .unwrap_or(None);
                self.value_conflict_trail.truncate(value_limit);
            }
            if let Some(summary_limit) = self.value_summary_trail_limits.pop() {
                while self.value_summary_trail.len() > summary_limit {
                    let Some((root, old)) = self.value_summary_trail.pop() else {
                        break;
                    };
                    if (root as usize) < self.class_value.len() {
                        self.class_value[root as usize] = old;
                    }
                }
            }

            // Remove term_to_node mappings that point to removed nodes.  Every
            // term maps to the node created for it (never to a borrowed congruent
            // one), and nodes are truncated in LIFO order, so this drops exactly
            // the terms first interned inside the popped scope.
            self.term_to_node
                .retain(|_term, &mut idx| (idx as usize) < num_nodes);

            // Rewind sig_trail to the saved limit, undoing all sig/fp insertions
            // made since the matching push().  Mirrors UnionFind::pop() exactly.
            if let Some(sig_limit) = self.sig_trail_limits.pop() {
                while self.sig_trail.len() > sig_limit {
                    if let Some(entry) = self.sig_trail.pop() {
                        match entry {
                            SigTrailEntry::InsertedSig { key, node } => {
                                self.sig_table.remove(&key);
                                if let Some(slot) = self.node_sig_key.get_mut(node as usize) {
                                    *slot = None;
                                }
                            }
                            SigTrailEntry::RemovedSig { key, node } => {
                                self.sig_table.insert(key.clone(), node);
                                if let Some(slot) = self.node_sig_key.get_mut(node as usize) {
                                    *slot = Some(key);
                                }
                            }
                            SigTrailEntry::InsertedFingerprint { fp, node_idx } => {
                                if let Some(bucket) = self.fingerprint_table.get_mut(&fp) {
                                    // Remove in LIFO order: the last push is the first to undo.
                                    if let Some(pos) = bucket.iter().rposition(|&n| n == node_idx) {
                                        bucket.swap_remove(pos);
                                    }
                                    if bucket.is_empty() {
                                        self.fingerprint_table.remove(&fp);
                                    }
                                }
                            }
                        }
                    }
                }
            }
        }
    }

    fn reset(&mut self) {
        self.uf = UnionFind::new(0);
        self.nodes.clear();
        self.term_to_node.clear();
        self.diseqs.clear();
        self.pending.clear();
        self.use_list.clear();
        // Distinct-value state: the per-class summaries and any pending value
        // conflict are incremental (rebuilt by the replay that follows a
        // reset), but `value_consts` is a symbol-level registry and is
        // deliberately NOT cleared – a rebuilt node for a registered term must
        // reacquire its mark or the pairwise distinctness the caller declared
        // would silently vanish.
        self.class_value.clear();
        self.pending_value_conflict = None;
        self.value_conflict_trail.clear();
        self.value_conflict_trail_limits.clear();
        self.value_summary_trail.clear();
        self.value_summary_trail_limits.clear();
        self.sig_table.clear();
        self.node_sig_key.clear();
        self.diseq_watch.clear();
        self.diseq_watch_trail.clear();
        self.diseq_watch_trail_limits.clear();
        self.diseq_pair_counts.clear();
        self.diseq_pair_trail.clear();
        self.diseq_pair_trail_limits.clear();
        self.diseq_stamp.clear();
        self.diseq_stamp_gen = 0;
        self.atom_watch.clear();
        self.atom_watch_trail.clear();
        self.atom_watch_trail_limits.clear();
        self.forced_eq_queue.clear();
        self.atom_epoch = self.atom_epoch.wrapping_add(1);
        self.atom_enqueued_epoch.clear();
        self.pending_diseq_conflict = None;
        self.pending_trail.clear();
        self.pending_trail_limits.clear();
        self.fingerprint_table.clear();
        self.context_stack.clear();
        self.proof_forest.clear();
        self.function_properties.clear();
        self.propagation_buf.clear();
        self.sig_trail.clear();
        self.sig_trail_limits.clear();
        self.proof_trail.clear();
        self.proof_trail_limits.clear();
        self.use_list_trail.clear();
        self.use_list_trail_limits.clear();
        self.explain_todo.clear();
        self.explain_enqueued.clear();
        self.expl_cache.clear();
        // The proof forest is gone, so derivation order restarts from zero.
        self.proof_stamp = 0;
    }
}
