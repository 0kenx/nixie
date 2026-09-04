//! Dense difference-logic core — a faithful port of Z3's
//! `smt/theory_dense_diff_logic` (Leonardo de Moura, 2008).
//!
//! # What this is
//!
//! An **incremental all-pairs shortest-path closure** over the asserted
//! difference constraints, plus **occurrence-list theory propagation**.
//! Z3 installs this engine for dense difference-logic problems
//! (`smt/smt_setup.cpp`: `setup_QF_IDL(st)` / `setup_QF_UFIDL(st)` when
//! `st.is_dense()`); it is the engine that solves the SMT-LIB `queens_bench`
//! and `DTP` families in milliseconds.
//!
//! # Semantics (mirrors Z3 cell-for-cell)
//!
//! * A constraint `t − s ≤ k` is the edge `s → t` with weight `k`.
//! * `dist(s,t)` is the shortest known path distance `d(s, t)` over the
//!   edges asserted so far; `edge_of(s,t)` names the edge that last improved
//!   it ([`SELF_EDGE`] on the diagonal, [`NO_EDGE`] when unreachable).
//! * [`DenseDlCore::assert_edge`] `(s → t, k)`:
//!   * reports **conflict** iff the reverse distance is known and
//!     `−d(t, s) > k` (the cycle `s→t→s` weighs `k + d(t,s) < 0`), with the
//!     justifying atoms of the whole cycle as the reason;
//!   * otherwise, if the edge improves `d(s,t)`, runs
//!     [`DenseDlCore::update_cells`]: the incremental closure update
//!     `d(y, x) := min(d(y,x), d(y,s) + k + d(t,x))`, trailed cell by cell.
//!   * Every improved cell `(y,x)` with watching atoms fires
//!     [`DenseDlCore::propagate_using_cell`]: an atom `t′ − s′ ≤ k′` is
//!     entailed **true** when `d(s′,t′) ≤ k′`, and **false** when
//!     `−d(s′,t′) > k′` (its negation `t′ − s′ > k′` is `s′ − t′ < −k′`,
//!     i.e. `s′ − t′ ≤ −k′ − 1` over the integers, entailed exactly when
//!     `−d(s′,t′) ≥ −k′ − 1`).
//! * Explanations decompose a cell's supporting path through its supporting
//!   edge ([`DenseDlCore::antecedents`]) — Z3 `get_antecedents` exactly.
//!
//! # Exactness of the incremental closure
//!
//! `update_cells` computes the improving set `F` from row `t` first, then
//! relaxes cells `(y, x)` for `x ∈ F` using `d(y,s)` — and neither row `t`
//! (skipped: `y ≠ t`) nor column `s` (excluded: `s ∉ F`) is written while the
//! loop runs, so every read input is stable at its pre-round value. The
//! standard incremental-closure argument then applies: before the edge the
//! matrix was the exact closure, and any strictly shorter path afterwards
//! must pass through the new edge exactly once (a path using it twice
//! contains a cycle of weight `k + d(t,s) ≥ 0`, which can be cut), so
//! `min(d(y,x), d(y,s) + k + d(t,x))` over the *old* distances is the new
//! exact closure. All writes happen in one round over stable inputs, with
//! strict improvements only — the matrix stays exact after every assert.
//!
//! # Numeric exactness
//!
//! Integer-only, by design. Weights are `i64` and *rejected* by the caller
//! when any `|k|` exceeds [`DL_MAX_ABS_WEIGHT`]; distances live in the same
//! `i64` space with `INF = i64::MAX / 4` as the unreachable sentinel. A
//! shortest path is simple, so any live distance is a sum of at most *n*
//! weights with `n·max|k| ≤ DL_MAX_NODES·DL_MAX_ABS_WEIGHT ≤ 2¹¹·2⁴⁰ = 2⁵¹`,
//! far below `INF = 2⁶¹`: **no distance can overflow and `INF` can never be
//! mistaken for a real distance.** Strict inequalities are pre-tightened by
//! the caller (`x − y < c` ⇒ `x − y ≤ c − 1` over ℤ), so no infinitesimals
//! are needed. (Z3's engine handles reals with `mpq_inf`; nixie routes
//! real-sorted difference logic to the sparse `Rational64` engine instead —
//! see `solver.rs`.)

use rustc_hash::FxHashMap;

/// No supporting edge (Z3 `null_edge_id`).
pub const NO_EDGE: u32 = u32::MAX;
/// The diagonal's self edge (Z3 `self_edge_id`).
pub const SELF_EDGE: u32 = u32::MAX - 1;

/// Unreachable-distance sentinel. Real distances are bounded by
/// `DL_MAX_NODES * DL_MAX_ABS_WEIGHT < 2^51`, far below this.
const DL_INF: i64 = i64::MAX / 4;

/// Largest accepted `|weight|`; keeps every possible path sum `n·|k|` far
/// below `DL_INF` (see the module doc's exactness argument).
pub const DL_MAX_ABS_WEIGHT: i64 = 1 << 40;

/// Largest accepted node count. The closure matrix is `n²` cells of
/// `(i64, u32)`; 2048 nodes ≈ 34 MiB, matching Z3's dense-engine remit
/// (`is_dense()` implies fewer than 1000 uninterpreted constants).
pub const DL_MAX_NODES: usize = 2048;

/// One asserted edge: `src --offset--> dst`, justified by atom `key` being
/// assigned `pol` (Z3: `edge { m_source, m_target, m_offset, m_justification }`).
#[derive(Debug, Clone, Copy)]
struct DlEdge {
    src: u32,
    dst: u32,
    offset: i64,
    /// Caller identity of the justifying atom (the SAT variable index).
    key: u32,
    /// Polarity the justifying atom is asserted with.
    pol: bool,
}

/// One difference atom under observation: `t − s ≤ k` (Z3: `atom`).
/// `is_eq` atoms are equalities `t = s` (`k == 0`, both directions asserted
/// together by the caller); they are only ever propagated **true**.
#[derive(Debug, Clone, Copy)]
struct DlAtomEntry {
    /// Caller identity (SAT variable index).
    key: u32,
    /// Edge source: the subtrahend of `t − s ≤ k`.
    s: u32,
    /// Edge target: the minuend of `t − s ≤ k`.
    t: u32,
    /// The bound `k`.
    k: i64,
    /// Whether this atom is an equality `t = s`.
    is_eq: bool,
}

/// A theory propagation produced by the core: atom `key` is forced to `pol`
/// by the asserted atoms listed in `reason` (each as `(key, pol)`).
#[derive(Debug, Clone, PartialEq)]
pub struct DlPropagation {
    /// Caller identity of the propagated atom (the SAT variable index).
    pub key: u32,
    /// The polarity the atom is forced to.
    pub pol: bool,
    /// Justifying atoms with their asserted polarities.
    pub reason: Vec<(u32, bool)>,
}

/// Outcome of asserting one edge.
#[derive(Debug, Clone, PartialEq)]
pub enum DlAssert {
    /// Edge accepted (closure updated; propagations may be pending).
    Ok,
    /// The edge closes a negative cycle: `reason` lists the asserted atoms
    /// on a refuting cycle (including the new edge's own justification).
    Conflict(Vec<(u32, bool)>),
}

/// Dense difference-logic core (see the module documentation).
///
/// The matrix is a flat row-major `Vec` whose *capacity width* doubles as
/// nodes arrive (each row reserves `cap` slots), so growth re-layouts the
/// whole matrix only every power of two — `O(n²)` total copying, amortised
/// `O(n)` per node.
#[derive(Default, Debug)]
pub struct DenseDlCore {
    /// Number of nodes.
    n: usize,
    /// Row stride (a power of two ≥ `n`).
    cap: usize,
    /// Row-major distances, stride `cap`; `DL_INF` = unreachable.
    dist: Vec<i64>,
    /// Row-major supporting-edge ids, stride `cap`.
    edge_of: Vec<u32>,
    /// All edges ever added (append-only; popped by truncation).
    edges: Vec<DlEdge>,
    /// Atoms, indexed by atom id.
    atoms: Vec<DlAtomEntry>,
    /// Caller key → atom id.
    key_to_atom: FxHashMap<u32, u32>,
    /// `(s, t)` → atom ids watching that cell (Z3: `cell::m_occs`). Atoms on
    /// `(s,t)` and `(t,s)` share one list per cell pair; the disambiguation
    /// direction is recovered from the atom's own `(s,t)` orientation.
    occs: FxHashMap<(u32, u32), Vec<u32>>,
    /// Undo trail for closure cells: `(row, col, old edge, old dist)`.  The
    /// cell is stored as coordinates, not a flat index — the matrix stride
    /// changes on capacity re-layout, which would silently invalidate flat
    /// trail indices.
    cell_trail: Vec<(u32, u32, u32, i64)>,
    /// Scope marks: `(edges.len(), cell_trail.len())` at push time.
    scopes: Vec<(usize, usize)>,
    /// Propagations discovered by the last asserts, not yet drained.
    pending: Vec<DlPropagation>,
    /// Scratch for [`DenseDlCore::update_cells`]: the improving target list.
    f_targets: Vec<(u32, i64)>,
    /// Scratch for [`DenseDlCore::antecedents_scratch`]: the emitted
    /// justifications (copied out only when a propagation/conflict is kept).
    ant_scratch: Vec<(u32, bool)>,
    /// Scratch for [`DenseDlCore::antecedents_scratch`]: the decomposition
    /// worklist.
    ant_todo: Vec<(u32, u32)>,
    /// Scratch for [`DenseDlCore::propagate_using_cell`]: watcher snapshot.
    watch_scratch: SmallIds,
}

impl DenseDlCore {
    /// Create an empty core.
    pub fn new() -> Self {
        Self::default()
    }

    /// Number of nodes.
    pub fn num_nodes(&self) -> usize {
        self.n
    }

    /// Whether the core can still accept another node (matrix budget).
    pub fn has_node_budget(&self) -> bool {
        self.n < DL_MAX_NODES
    }

    /// Intern a fresh node, growing the matrix by one row and column.
    pub fn intern_node(&mut self) -> u32 {
        if self.n == self.cap {
            self.relayout();
        }
        let idx = self.n;
        // Ensure storage covers `idx + 1` rows at stride `cap` (relayout
        // only moves the existing `n` rows).
        let needed = (idx + 1) * self.cap;
        if self.dist.len() < needed {
            self.dist.resize(needed, DL_INF);
            self.edge_of.resize(needed, NO_EDGE);
        }
        self.n += 1;
        // Initialise the new row and the new column.
        let row = idx * self.cap;
        for c in 0..self.n {
            self.dist[row + c] = DL_INF;
            self.edge_of[row + c] = NO_EDGE;
        }
        for r in 0..idx {
            let cell = r * self.cap + idx;
            self.dist[cell] = DL_INF;
            self.edge_of[cell] = NO_EDGE;
        }
        self.dist[row + idx] = 0;
        self.edge_of[row + idx] = SELF_EDGE;
        idx as u32
    }

    /// Double the row stride, re-laying-out both matrices.
    fn relayout(&mut self) {
        let new_cap = if self.cap == 0 { 4 } else { self.cap * 2 };
        let mut dist = vec![DL_INF; self.n * new_cap];
        let mut edge_of = vec![NO_EDGE; self.n * new_cap];
        for r in 0..self.n {
            let (old_base, new_base) = (r * self.cap, r * new_cap);
            dist[new_base..new_base + self.n]
                .copy_from_slice(&self.dist[old_base..old_base + self.n]);
            edge_of[new_base..new_base + self.n]
                .copy_from_slice(&self.edge_of[old_base..old_base + self.n]);
        }
        self.dist = dist;
        self.edge_of = edge_of;
        self.cap = new_cap;
    }

    #[inline]
    fn cell(&self, s: u32, t: u32) -> usize {
        s as usize * self.cap + t as usize
    }

    #[inline]
    fn dist_of(&self, s: u32, t: u32) -> i64 {
        self.dist[self.cell(s, t)]
    }

    #[inline]
    fn edge_of(&self, s: u32, t: u32) -> u32 {
        self.edge_of[self.cell(s, t)]
    }

    /// Shortest known distance `d(s,t)`; `None` when unreachable.
    pub fn distance(&self, s: u32, t: u32) -> Option<i64> {
        let d = self.dist_of(s, t);
        if d != DL_INF && self.edge_of(s, t) != NO_EDGE {
            Some(d)
        } else {
            None
        }
    }

    /// Register the atom `t − s ≤ k` (or the equality `t = s` when `is_eq`)
    /// under caller key `key`, so closure improvements can propagate it.
    /// Idempotent per key: the first registration wins.
    pub fn intern_atom(&mut self, key: u32, s: u32, t: u32, k: i64, is_eq: bool) {
        if self.key_to_atom.contains_key(&key) {
            return;
        }
        let id = self.atoms.len() as u32;
        self.atoms.push(DlAtomEntry {
            key,
            s,
            t,
            k,
            is_eq,
        });
        self.key_to_atom.insert(key, id);
        self.occs.entry((s, t)).or_default().push(id);
        if s != t {
            self.occs.entry((t, s)).or_default().push(id);
        }
    }

    /// Whether `key` has an interned atom.
    pub fn has_atom(&self, key: u32) -> bool {
        self.key_to_atom.contains_key(&key)
    }

    /// Atom registered for `key`, if any: `(s, t, k, is_eq)`.
    pub fn atom_of(&self, key: u32) -> Option<(u32, u32, i64, bool)> {
        let id = *self.key_to_atom.get(&key)?;
        let a = self.atoms.get(id as usize).copied()?;
        Some((a.s, a.t, a.k, a.is_eq))
    }

    /// Assert the edge `src --offset--> dst` justified by atom `key = pol`.
    ///
    /// Returns [`DlAssert::Conflict`] when the edge closes a negative cycle
    /// (the reason lists the justifying atoms of the whole cycle), else
    /// [`DlAssert::Ok`] — in which case closure improvements may have queued
    /// propagations (drained via [`Self::take_propagations`]).
    pub fn assert_edge(
        &mut self,
        src: u32,
        dst: u32,
        offset: i64,
        key: u32,
        pol: bool,
    ) -> DlAssert {
        debug_assert!(offset.unsigned_abs() <= DL_MAX_ABS_WEIGHT as u64);

        // Z3 `add_edge`: conflict iff the reverse path is known and
        // `-d(dst,src) > offset` (cycle weight `offset + d(dst,src) < 0`).
        // `-DL_INF` is representable (i64::MIN/2), so the negation is safe.
        let inv = self.dist_of(dst, src);
        let inv_known = inv != DL_INF && self.edge_of(dst, src) != NO_EDGE;
        if inv_known && -inv > offset {
            let mut reason = self.antecedents_scratch(dst, src).to_vec();
            reason.push((key, pol));
            return DlAssert::Conflict(reason);
        }

        // Add the edge; update the closure only when it improves `d(src,dst)`.
        if offset < self.dist_of(src, dst) {
            let id = self.edges.len() as u32;
            self.edges.push(DlEdge {
                src,
                dst,
                offset,
                key,
                pol,
            });
            self.update_cells(id);
        }
        DlAssert::Ok
    }

    /// Incremental closure update after edge `id` (Z3 `update_cells`).
    ///
    /// See the module doc for why the inputs read here are stable and the
    /// result is the exact new closure.
    fn update_cells(&mut self, id: u32) {
        let e = self.edges[id as usize];
        let (s, t, k) = (e.src as usize, e.dst as usize, e.offset);

        // F set: nodes x whose distance from s improves through t.
        self.f_targets.clear();
        let t_row = t * self.cap;
        for x in 0..self.n {
            if x == s {
                continue;
            }
            let d_t_x = self.dist[t_row + x];
            if d_t_x == DL_INF {
                continue;
            }
            let new_dist = k + d_t_x; // bounded: see module doc exactness
            if new_dist < self.dist[s * self.cap + x] {
                self.f_targets.push((x as u32, new_dist));
            }
        }
        if self.f_targets.is_empty() {
            return;
        }

        // Snapshot the improving target list so `&mut self` is free while
        // writing cells and propagating.
        let f_targets = core::mem::take(&mut self.f_targets);

        // For each y with a known d(y,s): relax d(y,x) through the new edge.
        for y in 0..self.n {
            if y == t {
                continue;
            }
            let d_y_s = self.dist[y * self.cap + s];
            if d_y_s == DL_INF {
                continue;
            }
            for &(x, via) in &f_targets {
                let x = x as usize;
                if x == y {
                    continue;
                }
                let new_dist = d_y_s + via; // bounded: see module doc exactness
                let cell = y * self.cap + x;
                if new_dist < self.dist[cell] {
                    self.cell_trail
                        .push((y as u32, x as u32, self.edge_of[cell], self.dist[cell]));
                    self.dist[cell] = new_dist;
                    self.edge_of[cell] = id;
                    self.propagate_using_cell(y as u32, x as u32);
                }
            }
        }
        self.f_targets = f_targets;
    }

    /// Propagate atoms watching the improved cell `(y, x)` with `d(y,x)`
    /// already written to the matrix (Z3 `propagate_using_cell`).
    fn propagate_using_cell(&mut self, y: u32, x: u32) {
        let Some(watchers) = self.occs.get(&(y, x)) else {
            return;
        };
        self.watch_scratch.clear();
        self.watch_scratch.extend_from_slice(watchers);
        // Index-walk the snapshot: the body takes `&mut self` (explanations,
        // pending queue), which a `drain` iterator's borrow would forbid.
        // Nothing below mutates `watch_scratch` itself.
        let mut wi = 0usize;
        while wi < self.watch_scratch.len() {
            let wid = self.watch_scratch[wi];
            wi += 1;
            let Some(a) = self.atoms.get(wid as usize).copied() else {
                continue;
            };
            let d = self.dist_of(y, x);
            if a.s == y && a.t == x {
                // Atom reads `x − y ≤ a.k`; entailed when d(y,x) ≤ a.k.
                if d <= a.k {
                    let mut reason = self.antecedents_scratch(y, x).to_vec();
                    if a.is_eq {
                        // Equality `t − s = k` needs BOTH directions:
                        // `t − s ≤ k` (this cell) and `s − t ≤ −k` (the
                        // reverse cell).  Testing the reverse against 0
                        // instead of −k would propagate `x − y = 1` from a
                        // path pair with d(s,t) ≤ 1, d(t,s) ≤ 0 — a bound
                        // that does NOT entail the equality.
                        // The reverse edge is asserted only on assignment, so
                        // it may not be known yet — skip unless present.
                        let back = self.dist_of(x, y);
                        let back_known = back != DL_INF && self.edge_of(x, y) != NO_EDGE;
                        if back_known && back <= -a.k {
                            reason.extend_from_slice(self.antecedents_scratch(x, y));
                        } else {
                            continue;
                        }
                    }
                    self.push_prop(a.key, true, reason);
                }
            } else {
                // Atom reads `y − x ≤ a.k` (registered on the reversed pair),
                // so the improved cell (y,x) is its REVERSE direction.
                debug_assert!(a.s == x && a.t == y);
                if a.is_eq {
                    // An equality is entailed TRUE once BOTH directions are
                    // bounded: the reverse here (d(y,x) ≤ −k) and the forward
                    // cell (d(x,y) ≤ k).  The forward edge is asserted only
                    // on assignment, so it may not be known yet.
                    let fwd = self.dist_of(a.s, a.t);
                    let fwd_known = fwd != DL_INF && self.edge_of(a.s, a.t) != NO_EDGE;
                    if d <= -a.k && fwd_known && fwd <= a.k {
                        let mut reason = self.antecedents_scratch(y, x).to_vec();
                        reason.extend_from_slice(self.antecedents_scratch(a.s, a.t));
                        self.push_prop(a.key, true, reason);
                    }
                } else if -d > a.k {
                    // Its negation `y − x > a.k` is entailed when −d(y,x) > a.k.
                    let reason = self.antecedents_scratch(y, x).to_vec();
                    self.push_prop(a.key, false, reason);
                }
            }
        }
    }

    /// Queue one propagation, skipping duplicates (keep the first reason).
    fn push_prop(&mut self, key: u32, pol: bool, reason: Vec<(u32, bool)>) {
        if self.pending.iter().any(|p| p.key == key && p.pol == pol) {
            return;
        }
        self.pending.push(DlPropagation { key, pol, reason });
    }

    /// Drain queued propagations (empty when none).
    pub fn take_propagations(&mut self) -> Vec<DlPropagation> {
        core::mem::take(&mut self.pending)
    }

    /// Decompose the supporting path for `d(s,t)` into its justifying atoms
    /// (Z3 `get_antecedents`): iterative, splitting `(s,t)` at the cell's
    /// supporting edge into `(s, e.src)` and `(e.dst, t)`.  The result is
    /// written to scratch storage and returned as a slice borrowed from
    /// `self`; copy it out before the next call.
    fn antecedents_scratch(&mut self, s: u32, t: u32) -> &[(u32, bool)] {
        self.ant_scratch.clear();
        self.ant_todo.clear();
        if s != t {
            self.ant_todo.push((s, t));
            let mut steps = 0usize;
            while let Some((a, b)) = self.ant_todo.pop() {
                if a == b {
                    continue;
                }
                let eid = self.edge_of(a, b);
                if eid == NO_EDGE || eid == SELF_EDGE {
                    // Unreachable pair (should not happen when called on a
                    // cell with a known distance) — emit nothing further
                    // rather than fabricating an explanation.
                    continue;
                }
                let e = self.edges[eid as usize];
                self.ant_scratch.push((e.key, e.pol));
                if a != e.src {
                    self.ant_todo.push((a, e.src));
                }
                if e.dst != b {
                    self.ant_todo.push((e.dst, b));
                }
                // Every decomposition step strictly reduces the path it
                // explains (it removes one edge from it); the total is
                // bounded by the number of edges ever supporting any cell
                // decomposition, but as a belt against any future change
                // breaking that invariant, stop at a bound no real
                // explanation can reach.
                steps += 1;
                if steps > self.edges.len() * 2 + 8 {
                    break;
                }
            }
        }
        &self.ant_scratch
    }

    /// Push a decision scope.
    pub fn push(&mut self) {
        self.scopes.push((self.edges.len(), self.cell_trail.len()));
    }

    /// Pop one decision scope: restore trailed cells, drop scoped edges.
    pub fn pop(&mut self) {
        let Some((edges_lim, trail_lim)) = self.scopes.pop() else {
            // Unreachable while the core is created at level 0 and pushed in
            // lockstep (see `DiffLogicSolver::with_config`): a pop past the
            // last scope mark would strand every live edge as a phantom
            // constraint.
            debug_assert!(
                false,
                "dense DL core pop without a matching push (stranded edges!)"
            );
            return;
        };
        while self.cell_trail.len() > trail_lim {
            if let Some((row, col, edge, dist)) = self.cell_trail.pop() {
                let cell = row as usize * self.cap + col as usize;
                self.dist[cell] = dist;
                self.edge_of[cell] = edge;
            }
        }
        self.edges.truncate(edges_lim);
        // Any queued propagation may rest on just-popped edges.
        self.pending.clear();
    }

    /// Full reset.
    pub fn reset(&mut self) {
        *self = Self::default();
    }

    /// Model value of node `v`: `−min over w≠v of d(v, w)` (Z3 `init_model`,
    /// which negates the row minimum; 0 when no `w` improves on 0).
    ///
    /// With every asserted edge `src→dst` of weight `w` satisfying
    /// `value(dst) − value(src) ≤ d(src,dst) ≤ w`, this is a feasible
    /// integer assignment — the negated-row-minimum argument on the exact
    /// closure.
    pub fn value(&self, v: u32) -> i64 {
        let row = v as usize * self.cap;
        let mut d = 0_i64;
        for w in 0..self.n {
            if w == v as usize {
                continue;
            }
            let dw = self.dist[row + w];
            if dw != DL_INF && self.edge_of[row + w] != NO_EDGE && dw < d {
                d = dw;
            }
        }
        -d
    }

    /// Whether the current closure is consistent. Conflicts are reported at
    /// assert time, so this is an invariant probe for the final-check
    /// backstop: a negative diagonal would mean a negative cycle.
    pub fn is_consistent(&self) -> bool {
        for i in 0..self.n {
            if self.dist[i * self.cap + i] < 0 {
                return false;
            }
        }
        true
    }
}

/// Small alias for watcher id lists.
type SmallIds = Vec<u32>;

#[cfg(test)]
mod tests {
    use super::*;

    fn nodes(core: &mut DenseDlCore, count: usize) -> Vec<u32> {
        (0..count).map(|_| core.intern_node()).collect()
    }

    #[test]
    fn intern_node_lays_out_matrix() {
        let mut c = DenseDlCore::new();
        let v = nodes(&mut c, 5);
        assert_eq!(c.num_nodes(), 5);
        // Diagonal 0 with SELF_EDGE; everything else unreachable.
        for (i, &x) in v.iter().enumerate() {
            for (j, &y) in v.iter().enumerate() {
                assert_eq!(c.distance(x, y), if i == j { Some(0) } else { None });
            }
        }
    }

    #[test]
    fn intern_node_across_relayout() {
        // 17 nodes crosses the 4→8→16 capacity doublings.
        let mut c = DenseDlCore::new();
        let v = nodes(&mut c, 17);
        assert_eq!(c.num_nodes(), 17);
        for (i, &x) in v.iter().enumerate() {
            for (j, &y) in v.iter().enumerate() {
                assert_eq!(c.distance(x, y), if i == j { Some(0) } else { None });
            }
        }
        // A path over the relaid-out matrix still closes correctly.
        assert_eq!(c.assert_edge(0, 5, 3, 1, true), DlAssert::Ok);
        assert_eq!(c.assert_edge(5, 16, 2, 2, true), DlAssert::Ok);
        assert_eq!(c.distance(0, 16), Some(5));
    }

    #[test]
    fn closure_two_edge_path() {
        // b−a ≤ 3, c−b ≤ 2  ⟹  c−a ≤ 5.
        let mut c = DenseDlCore::new();
        let v = nodes(&mut c, 3);
        let (a, b, cc) = (v[0], v[1], v[2]);
        assert_eq!(c.assert_edge(a, b, 3, 10, true), DlAssert::Ok);
        assert_eq!(c.assert_edge(b, cc, 2, 11, true), DlAssert::Ok);
        assert_eq!(c.distance(a, cc), Some(5));
        // Antecedents of (a,c) name both edges' atoms.  (The accessor was
        // renamed to `antecedents_scratch` and now borrows internal scratch
        // storage, so copy the slice out before sorting.)
        let mut ants = c.antecedents_scratch(a, cc).to_vec();
        ants.sort_unstable();
        assert_eq!(ants, vec![(10, true), (11, true)]);
    }

    #[test]
    fn negative_cycle_conflict() {
        // x−y ≤ −1, y−z ≤ −1, z−x ≤ −1: cycle sum −3 < 0.
        let mut c = DenseDlCore::new();
        let v = nodes(&mut c, 3);
        let (x, y, z) = (v[0], v[1], v[2]);
        assert_eq!(c.assert_edge(y, x, -1, 1, true), DlAssert::Ok);
        assert_eq!(c.assert_edge(z, y, -1, 2, true), DlAssert::Ok);
        match c.assert_edge(x, z, -1, 3, true) {
            DlAssert::Conflict(reason) => {
                let mut keys: Vec<u32> = reason.iter().map(|r| r.0).collect();
                keys.sort_unstable();
                assert_eq!(keys, vec![1, 2, 3]);
            }
            r => panic!("expected conflict, got {r:?}"),
        }
        // After the conflict nothing was written; the state is as before.
        assert_eq!(c.distance(x, z), None);
    }

    #[test]
    fn immediate_self_conflict() {
        // x − x ≤ −1 asserted directly: reverse distance is the diagonal 0,
        // −0 > −1 holds → conflict naming the atom itself.
        let mut c = DenseDlCore::new();
        let v = nodes(&mut c, 1);
        let x = v[0];
        assert_eq!(
            c.assert_edge(x, x, -1, 7, true),
            DlAssert::Conflict(vec![(7, true)])
        );
        // x − x ≤ 0 is fine (does not improve the diagonal).
        assert_eq!(c.assert_edge(x, x, 0, 8, true), DlAssert::Ok);
    }

    #[test]
    fn propagation_entails_true_and_false() {
        // Chain a→b(3)→cc(2): the closure derives d(a,cc) = 5, entailing the
        // watching atom `cc − a ≤ 5` TRUE with both edges as its reason.
        let mut c = DenseDlCore::new();
        let v = nodes(&mut c, 3);
        let (a, b, cc) = (v[0], v[1], v[2]);
        c.intern_atom(100, a, cc, 5, false); // cc − a ≤ 5
        c.intern_atom(101, b, a, 0, false); // a − b ≤ 0
        assert_eq!(c.assert_edge(a, b, 3, 10, true), DlAssert::Ok);
        // The single edge does not yet reach cc: no propagation.
        assert!(c.take_propagations().is_empty());
        assert_eq!(c.assert_edge(b, cc, 2, 11, true), DlAssert::Ok);
        let props = c.take_propagations();
        // d(a,cc) = 5 ≤ 5 → atom 100 true, reason names both edges.
        assert!(props.iter().any(|p| p.key == 100 && p.pol), "{props:?}");
        let p100 = props
            .iter()
            .find(|p| p.key == 100)
            .unwrap_or(&props[0])
            .clone();
        let mut reason = p100.reason.clone();
        reason.sort_unstable();
        assert_eq!(reason, vec![(10, true), (11, true)]);

        // Now assert a→b(−1): a − b ≤ −1, so −d(a,b) = 1 > 0 and the
        // watching atom `a − b ≤ 0` is entailed FALSE.
        assert_eq!(c.assert_edge(a, b, -1, 12, true), DlAssert::Ok);
        let props = c.take_propagations();
        assert!(props.iter().any(|p| p.key == 101 && !p.pol), "{props:?}");
    }

    #[test]
    fn push_pop_restores_cells() {
        let mut c = DenseDlCore::new();
        let v = nodes(&mut c, 2);
        let (a, b) = (v[0], v[1]);
        assert_eq!(c.assert_edge(a, b, 3, 1, true), DlAssert::Ok);
        assert_eq!(c.distance(a, b), Some(3));
        c.push();
        assert_eq!(c.assert_edge(a, b, 1, 2, true), DlAssert::Ok);
        assert_eq!(c.distance(a, b), Some(1));
        c.pop();
        assert_eq!(c.distance(a, b), Some(3));
        // Re-assert the tighter edge after the pop: accepted again.
        assert_eq!(c.assert_edge(a, b, 1, 2, true), DlAssert::Ok);
        assert_eq!(c.distance(a, b), Some(1));
    }

    #[test]
    fn pop_clears_pending_propagations() {
        let mut c = DenseDlCore::new();
        let v = nodes(&mut c, 3);
        let (a, b, cc) = (v[0], v[1], v[2]);
        c.intern_atom(100, a, cc, 5, false);
        c.push();
        assert_eq!(c.assert_edge(a, b, 3, 10, true), DlAssert::Ok);
        assert_eq!(c.assert_edge(b, cc, 2, 11, true), DlAssert::Ok);
        assert!(!c.take_propagations().is_empty());
        c.pop();
        // Edges gone; re-asserting at base scope is accepted and the queue
        // starts empty.
        assert_eq!(c.assert_edge(a, b, 3, 10, true), DlAssert::Ok);
    }

    #[test]
    fn model_values_satisfy_edges() {
        // A chain a→b(3)→c(2), plus b→a(0).  value() must satisfy every
        // asserted edge: value(dst) − value(src) ≤ w.
        let mut c = DenseDlCore::new();
        let v = nodes(&mut c, 3);
        let (a, b, cc) = (v[0], v[1], v[2]);
        c.assert_edge(a, b, 3, 1, true);
        c.assert_edge(b, cc, 2, 2, true);
        c.assert_edge(b, a, 0, 3, true);
        let (va, vb, vc) = (c.value(a), c.value(b), c.value(cc));
        assert!(vb - va <= 3, "vb−va = {} ≤ 3", vb - va);
        assert!(vc - vb <= 2);
        assert!(va - vb <= 0);
    }

    #[test]
    fn equality_atom_propagates_only_when_both_directions() {
        // a − b ≤ 0 asserted; the eq atom `a = b` must NOT propagate yet
        // (the reverse bound b − a ≤ 0 is missing).
        let mut c = DenseDlCore::new();
        let v = nodes(&mut c, 2);
        let (a, b) = (v[0], v[1]);
        c.intern_atom(50, b, a, 0, true); // a = b, watch reads a − b ≤ 0
        assert_eq!(c.assert_edge(b, a, 0, 10, true), DlAssert::Ok);
        assert!(c.take_propagations().is_empty());
        // Reverse direction closes the equality: d(a,b) = 0 ≤ 0 too, so the
        // improved cell fires the watch with both bounds in reach.
        assert_eq!(c.assert_edge(a, b, 0, 11, true), DlAssert::Ok);
        let props = c.take_propagations();
        assert!(props.iter().any(|p| p.key == 50 && p.pol), "{props:?}");
    }

    #[test]
    fn zero_weight_cycle_is_consistent() {
        let mut c = DenseDlCore::new();
        let v = nodes(&mut c, 2);
        let (a, b) = (v[0], v[1]);
        assert_eq!(c.assert_edge(a, b, 0, 1, true), DlAssert::Ok);
        assert_eq!(c.assert_edge(b, a, 0, 2, true), DlAssert::Ok);
        assert_eq!(c.distance(a, b), Some(0));
        assert!(c.is_consistent());
    }

    /// Randomised differential test against a Floyd–Warshall reference:
    /// after every assert the closure must equal the reference closure, and
    /// conflicts must coincide.
    #[test]
    fn differential_against_floyd_warshall() {
        let mut seed = 0x5eed_1234_u64;
        let mut rng = || {
            seed = seed
                .wrapping_mul(6364136223846793005)
                .wrapping_add(1442695040888963407);
            seed
        };
        const INF: i64 = i64::MAX / 2;
        for trial in 0..60 {
            let n = 3 + (rng() % 5) as usize;
            let mut core = DenseDlCore::new();
            let v: Vec<u32> = (0..n).map(|_| core.intern_node()).collect();
            // Reference closure.
            let mut d = vec![vec![INF; n]; n];
            for (i, row) in d.iter_mut().enumerate() {
                row[i] = 0;
            }
            for step in 0..40 {
                let si = (rng() % n as u64) as usize;
                let ti = (rng() % n as u64) as usize;
                let w = (rng() % 21) as i64 - 10;
                let (s, t) = (v[si], v[ti]);
                // Reference: add edge si→ti, recompute closure exactly.
                let mut d2 = d.clone();
                for y in 0..n {
                    for x in 0..n {
                        // Skip unreachable endpoints: INF-saturated sums can
                        // land below INF and masquerade as real distances.
                        if d[y][si] >= INF || d[ti][x] >= INF {
                            continue;
                        }
                        let via = d[y][si].saturating_add(w).saturating_add(d[ti][x]);
                        if via < d2[y][x] {
                            d2[y][x] = via;
                        }
                    }
                }
                // Detect negative diagonal (cycle) the same way the core
                // must: the assert conflicts.
                let conflict = (0..n).any(|i| d2[i][i] < 0);
                let outcome = core.assert_edge(s, t, w, step as u32, true);
                if conflict {
                    assert!(
                        matches!(outcome, DlAssert::Conflict(_)),
                        "trial {trial} step {step}: expected conflict (w={w} {si}->{ti})"
                    );
                    break;
                }
                assert_eq!(outcome, DlAssert::Ok);
                d = d2;
                for y in 0..n {
                    for x in 0..n {
                        let got = core.distance(v[y], v[x]);
                        let want = d[y][x] < INF;
                        assert_eq!(
                            got,
                            want.then_some(d[y][x]),
                            "trial {trial} step {step}: d({y},{x})"
                        );
                    }
                }
            }
        }
    }
}
