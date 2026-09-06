//! Congruence closure: signature maintenance, use lists and merge propagation.
//!
//! Split out of `euf/solver.rs` along the "what mutates the e-graph" seam.  Every
//! function here either records a retractable change (a proof-forest edge, a
//! use-list append, a signature-table insertion) or consumes the pending-merge
//! queue; the explanation side lives in [`super::explain`] and the term/instance
//! bookkeeping in the parent module.

use super::{
    DiseqPairTrailEntry, ENode, ENodeFingerprint, EqAtomWatch, EufSolver, FunctionProperties,
    MergeEdge, MergeReason, SigTrailEntry, ordered_pair,
};
#[allow(unused_imports)]
use crate::prelude::*;
use core::mem;
use smallvec::SmallVec;

impl EufSolver {
    /// Register a function with specific properties (for dynamic arity support)
    pub fn register_function(&mut self, func: u32, props: FunctionProperties) {
        self.function_properties.insert(func, props);
    }

    /// Get the properties of a function
    pub(super) fn get_function_props(&self, func: u32) -> FunctionProperties {
        self.function_properties
            .get(&func)
            .copied()
            .unwrap_or_default()
    }

    /// Canonicalize arguments for commutative functions
    pub(super) fn canonicalize_args(&mut self, func: u32, args: &[u32]) -> SmallVec<[u32; 4]> {
        let props = self.get_function_props(func);
        self.canonicalize_args_with_props(&props, args)
    }

    /// Canonicalize arguments given pre-fetched function properties.
    /// Used in hot paths to hoist the `get_function_props` hashmap lookup out of inner loops.
    fn canonicalize_args_with_props(
        &mut self,
        props: &FunctionProperties,
        args: &[u32],
    ) -> SmallVec<[u32; 4]> {
        let mut canonical: SmallVec<[u32; 4]> = args.iter().map(|&a| self.uf.find(a)).collect();

        // For commutative functions, sort arguments by their canonical representative
        if props.commutative {
            canonical.sort_unstable();
        }

        canonical
    }

    /// Canonicalize arguments into a caller-owned buffer to avoid per-call allocation.
    /// Clears `buf` first, then pushes the canonical representative of each arg.
    /// For commutative functions the results are sorted in-place.
    ///
    /// This is the allocation-free variant used in the hot inner loop of `propagate`.
    fn canonicalize_args_with_props_into(
        &mut self,
        props: &FunctionProperties,
        args: &[u32],
        buf: &mut SmallVec<[u32; 4]>,
    ) {
        buf.clear();
        for &a in args {
            buf.push(self.uf.find(a));
        }
        if props.commutative {
            buf.sort_unstable();
        }
    }

    /// Flatten associative function applications
    /// For example: f(f(a, b), c) -> f(a, b, c)
    pub(super) fn flatten_args(&self, func: u32, args: &[u32]) -> SmallVec<[u32; 4]> {
        let props = self.get_function_props(func);

        if !props.associative {
            return args.iter().copied().collect();
        }

        let mut flattened = SmallVec::new();
        for &arg in args {
            let arg_node = &self.nodes[arg as usize];
            // If the argument is an application of the same function, flatten it
            if arg_node.is_app() && arg_node.func == func {
                flattened.extend(arg_node.args.iter().copied());
            } else {
                flattened.push(arg);
            }
        }

        flattened
    }

    /// Append a merge edge to `node`'s proof-forest adjacency list, recording the
    /// insertion on `proof_trail` when a scope is active so `pop()` can remove it.
    ///
    /// Trailing is gated on `proof_trail_limits` being non-empty (i.e. at least one
    /// `push` outstanding), mirroring the sig-trail discipline: at the base level
    /// edges are permanent and need no undo record.
    #[inline]
    fn add_proof_edge(&mut self, node: u32, edge: MergeEdge) {
        self.proof_forest[node as usize].push(edge);
        if !self.proof_trail_limits.is_empty() {
            self.proof_trail.push(node);
        }
    }

    /// Hand out the next derivation-order stamp. Both directed edges of a single
    /// merge must share one stamp, so callers take it once per merge. Saturates
    /// instead of wrapping: a wrap would make old edges look newer than recent
    /// ones and break the derivation order `try_explain_equality` depends on.
    /// Saturation only makes the last stamps compare equal, which costs
    /// explanation quality rather than soundness, and is unreachable in practice.
    #[inline]
    fn next_proof_stamp(&mut self) -> u32 {
        let s = self.proof_stamp;
        self.proof_stamp = self.proof_stamp.saturating_add(1);
        s
    }

    /// Append `entry` to `node`'s use-list, recording the append on
    /// `use_list_trail` when a scope is active so `pop()` can remove it.
    #[inline]
    pub(super) fn use_list_push(&mut self, node: u32, entry: u32) {
        self.use_list[node as usize].push(entry);
        if !self.use_list_trail_limits.is_empty() {
            self.use_list_trail.push(node);
        }
    }

    /// Append `diseq_idx` to `rep`'s disequality watch list, recording the append
    /// on `diseq_watch_trail` when a scope is active so `pop()` removes it.
    /// Auto-sizes `diseq_watch` to cover `rep` (reps are node ids, so the vector
    /// parallels `use_list`/`nodes`).
    #[inline]
    pub(super) fn diseq_watch_push(&mut self, rep: u32, diseq_idx: u32) {
        let r = rep as usize;
        if r >= self.diseq_watch.len() {
            self.diseq_watch.resize_with(r + 1, Vec::new);
        }
        self.diseq_watch[r].push(diseq_idx);
        if !self.diseq_watch_trail_limits.is_empty() {
            self.diseq_watch_trail.push(rep);
        }
    }

    /// Append `w` to `node`'s equality-atom watch list, recording the append on
    /// `atom_watch_trail` when a scope is active so `pop()` removes it.
    /// Auto-sizes `atom_watch` to cover `node` (the vector parallels `nodes`).
    #[inline]
    pub(super) fn atom_watch_push(&mut self, node: u32, w: EqAtomWatch) {
        let n = node as usize;
        if n >= self.atom_watch.len() {
            self.atom_watch.resize_with(n + 1, Vec::new);
        }
        self.atom_watch[n].push(w);
        if !self.atom_watch_trail_limits.is_empty() {
            self.atom_watch_trail.push(node);
        }
    }

    /// Count `key` into the proven-disequality index.
    #[inline]
    pub(super) fn inc_diseq_pair(&mut self, key: (u32, u32)) {
        let e = self.diseq_pair_counts.entry(key).or_insert(0);
        *e = e.saturating_add(1);
    }

    /// Drop one count of `key` from the proven-disequality index.
    #[inline]
    pub(super) fn dec_diseq_pair(&mut self, key: (u32, u32)) {
        if let Some(e) = self.diseq_pair_counts.get_mut(&key) {
            *e = e.saturating_sub(1);
            if *e == 0 {
                self.diseq_pair_counts.remove(&key);
            }
        }
    }

    /// Publish `node` under the signature `(func, args)` with fingerprint `fp`.
    ///
    /// The caller must have established that the key is **absent** – the undo
    /// record for a signature insertion is a plain `remove`, so overwriting an
    /// existing entry would make `pop()` delete the older, still-valid mapping and
    /// silently lose every congruence that depended on it.  Both call sites check
    /// first (and merge instead when the key is taken), so the `debug_assert`
    /// below states an invariant rather than a hope.
    pub(super) fn insert_signature(
        &mut self,
        func: u32,
        args: SmallVec<[u32; 4]>,
        node: u32,
        fp: ENodeFingerprint,
    ) {
        debug_assert!(
            !self.sig_table.contains_key(&(func, args.clone())),
            "insert_signature would overwrite the entry for ({func}, {args:?}); \
             pop() undoes an insertion by removing the key, so the previous \
             mapping could never be restored"
        );
        let in_scope = !self.sig_trail_limits.is_empty();
        if in_scope {
            // Clone before the key is moved into the insert below.
            self.sig_trail.push(SigTrailEntry::InsertedSig {
                key: (func, args.clone()),
                node,
            });
        }
        self.sig_table.insert((func, args), node);
        self.fingerprint_table.entry(fp).or_default().push(node);
        if in_scope {
            self.sig_trail
                .push(SigTrailEntry::InsertedFingerprint { fp, node_idx: node });
        }
    }

    /// Replace `user`'s entry in `sig_table` with `new_key`: remove its
    /// previously-recorded key (from `intern_app` or a prior signature change),
    /// insert `new_key -> user`, record both operations on `sig_trail` (when in
    /// scope) so `pop()` restores the prior state exactly, and update
    /// `node_sig_key[user]`.
    ///
    /// Root-cause fix for the stale sig-table-entry bug: without the removal,
    /// every signature change in `propagate` left a dead entry keyed by obsolete
    /// representatives, and under specific push/pop orderings those dead entries
    /// resurrect into a spurious (or missed) congruence that `pop` partially
    /// undoes – leaving the incremental closure in a state a from-scratch
    /// rebuild never reaches (missed congruence / spurious sat).
    ///
    /// Callers only invoke this when `new_key` is known absent (fingerprint /
    /// sig pre-checks), so the insert never overwrites a different live entry.
    #[inline]
    fn update_sig_entry(&mut self, user: u32, new_key: (u32, SmallVec<[u32; 4]>), in_scope: bool) {
        // Remove the node's prior key, if any (leaf/congruent-merged -> None).
        if let Some(Some(old_key)) = self.node_sig_key.get(user as usize) {
            self.sig_table.remove(old_key);
            if in_scope {
                self.sig_trail.push(SigTrailEntry::RemovedSig {
                    key: old_key.clone(),
                    node: user,
                });
            }
        }
        self.sig_table.insert(new_key.clone(), user);
        if in_scope {
            self.sig_trail.push(SigTrailEntry::InsertedSig {
                key: new_key.clone(),
                node: user,
            });
        }
        self.node_sig_key[user as usize] = Some(new_key);
    }

    /// Look up `sig` in `sig_table`, returning the registered node only if its
    /// *current* canonical signature still equals `sig` (per `node_sig_key`).
    /// A stale entry – left behind before `update_sig_entry` existed – is
    /// evicted so it can never dedup a freshly-interned term to a node it isn't
    /// actually congruent to.
    pub(super) fn lookup_valid_sig(&mut self, sig: &(u32, SmallVec<[u32; 4]>)) -> Option<u32> {
        let node = self.sig_table.get(sig).copied()?;
        let valid = self
            .node_sig_key
            .get(node as usize)
            .map(|k| k.as_ref() == Some(sig))
            .unwrap_or(false);
        if valid {
            Some(node)
        } else {
            self.sig_table.remove(sig);
            None
        }
    }

    /// Enqueue the congruence `node == other` and run it to a fixed point.
    ///
    /// Used by `intern_app` when the signature table already holds an application
    /// congruent to the one being interned.  The two applications are joined by a
    /// **merge**, never by sharing a node index: the congruence rests on the
    /// current argument classes, and a shared index would outlive the `pop()` that
    /// retracts them.
    pub(super) fn merge_congruent(&mut self, node: u32, other: u32) {
        self.expl_cache.clear();
        self.pending.push((
            node,
            other,
            MergeReason::Congruence {
                term1: node,
                term2: other,
            },
        ));
        self.propagate();
    }

    /// Propagate pending merges with optimized congruence closure:
    /// - Index-based use-list iteration (avoids cloning the use-list)
    /// - Fingerprint pre-filter (cheap u64 comparison before full signature match)
    ///
    /// Signature updates are applied **as they are discovered**, not batched to
    /// the end of the use-list scan.  Batching made two applications that acquire
    /// the *same* new signature within one merge event invisible to each other –
    /// neither found the other in `sig_table` (the inserts had not happened yet),
    /// so no congruence was enqueued and the two stayed in different classes.
    pub(super) fn propagate(&mut self) {
        let mut propagation_buf = mem::take(&mut self.propagation_buf);
        propagation_buf.clear();

        while let Some((a, b, reason)) = self.pending.pop() {
            let root_a = self.uf.find(a);
            let root_b = self.uf.find(b);

            if root_a == root_b {
                continue;
            }

            // Record the merge in the proof forest (for explanation generation).
            // Trailed so pop() removes these edges even when a and b pre-existed
            // the current scope.
            //
            // Both assertion *and* congruence edges are appended here – i.e. only
            // once the union below is actually going to happen. Adding an edge for
            // a merge that is subsequently skipped (because the two classes were
            // joined in the meantime by another propagation) would leave the proof
            // forest with two distinct paths between the same pair of nodes, and
            // `explain_equality`'s path search could then justify a congruence by a
            // route that runs through the very edge being explained.
            let stamp = self.next_proof_stamp();
            self.add_proof_edge(
                a,
                MergeEdge {
                    other: b,
                    reason: reason.clone(),
                    stamp,
                },
            );
            self.add_proof_edge(
                b,
                MergeEdge {
                    other: a,
                    reason,
                    stamp,
                },
            );
            // The forest just grew an edge, so every cached explanation may now be
            // longer than the shortest path.  Drop the cache rather than serve a
            // stale (still sound, but needlessly large) answer.
            self.expl_cache.clear();

            // Union the classes
            self.uf.union(root_a, root_b);
            let new_root = self.uf.find(root_a);

            // Congruence closure: check for new merges
            let other_root = if new_root == root_a { root_b } else { root_a };

            // ======== Distinct-value merge check (Z3 `are_distinct`) ========
            //
            // Both merged classes carry a distinguished-value summary and the
            // summaries differ -> the merge is impossible in every model.
            // Recorded AFTER the union and its proof-forest edges so
            // `check_conflicts` can explain root_a = root_b completely (same
            // shape as a disequality violation, which is also detected
            // post-union).  The value distinctness itself is a hard semantic
            // fact and names no literal, exactly like the tautological
            // `10 ≠ 20` reasons of intern-time constant disequalities.  First
            // conflict wins, as for disequalities.
            //
            // The surviving root then inherits the merged summary (at most one
            // id can survive a conflict-free merge), trailed so `pop()` can
            // restore it when the union rewinds.
            if self.pending_value_conflict.is_none() {
                let va = self.class_value[root_a as usize];
                let vb = self.class_value[root_b as usize];
                if let (Some((x, wa)), Some((y, wb))) = (va, vb)
                    && x != y
                {
                    // Record the witness nodes, not the roots: the explanation
                    // of `wa = wb` must cross this merge's own proof edge (the
                    // witnesses lived in different classes until now), which is
                    // what keeps the surfaced conflict core complete.
                    self.pending_value_conflict = Some((wa, wb));
                }
            }
            // The surviving root inherits the merged summary.  After a value
            // conflict this is arbitrary (both ids "exist" in the corrupted
            // class until the search unwinds); nothing reads it again before
            // the rewind because `pending_value_conflict` is already set and
            // first-wins.  Trailed so `pop()` restores it with the union.
            let merged = self.class_value[root_a as usize].or(self.class_value[root_b as usize]);
            if merged != self.class_value[new_root as usize] {
                if !self.value_summary_trail_limits.is_empty() {
                    self.value_summary_trail
                        .push((new_root, self.class_value[new_root as usize]));
                }
                self.class_value[new_root as usize] = merged;
            }

            // ======== O(1) proven-disequality index maintenance ========
            //
            // Every live disequality watched on *either* merged class has a
            // `cached_pair` naming `root_a` or `root_b`; rewrite those keys to
            // `new_root` so `are_proven_disequal` stays an exact O(1) map
            // probe.  A disequality can sit on both lists (one endpoint per
            // class), so stamp-dedupe the walk of the two lists.  Walking only
            // the loser's list (as the violation scan below does) would miss
            // `(winner, elsewhere)` pairs, whose key also just changed.
            self.diseq_stamp_gen = self.diseq_stamp_gen.wrapping_add(1);
            for list_root in [new_root, other_root] {
                let dw_len = self.diseq_watch.get(list_root as usize).map_or(0, Vec::len);
                for i in 0..dw_len {
                    let didx = self.diseq_watch[list_root as usize][i] as usize;
                    if self.diseq_stamp.get(didx).copied() == Some(self.diseq_stamp_gen)
                        || didx >= self.diseqs.len()
                    {
                        continue;
                    }
                    if let Some(s) = self.diseq_stamp.get_mut(didx) {
                        *s = self.diseq_stamp_gen;
                    }
                    let old = self.diseqs[didx].cached_pair;
                    let new = (
                        if old.0 == root_a || old.0 == root_b {
                            new_root
                        } else {
                            old.0
                        },
                        if old.1 == root_a || old.1 == root_b {
                            new_root
                        } else {
                            old.1
                        },
                    );
                    if new != old {
                        self.dec_diseq_pair(old);
                        self.inc_diseq_pair(new);
                        self.diseqs[didx].cached_pair = new;
                        if !self.diseq_pair_trail_limits.is_empty() {
                            self.diseq_pair_trail.push(DiseqPairTrailEntry::Rewrote {
                                idx: didx as u32,
                                old,
                            });
                        }
                    }
                }
            }

            // Eager disequality check: every disequality watched on the loser
            // class (`other_root`) has an endpoint whose class just merged into
            // `new_root`. Test each for violation (both endpoints now equal),
            // then copy it onto `new_root`'s watch list so future merges keep
            // testing it. This replaces check_conflicts' O(diseqs) full scan –
            // the dominant EUF cost – with O(watched-by-this-class) per merge.
            // Violation now reads the freshly-rewritten `cached_pair`: both
            // endpoints in one class ⟺ the pair collapsed to `(R, R)`.
            let dw_len = self
                .diseq_watch
                .get(other_root as usize)
                .map_or(0, Vec::len);
            for i in 0..dw_len {
                let didx = self.diseq_watch[other_root as usize][i];
                let d = &self.diseqs[didx as usize];
                if self.pending_diseq_conflict.is_none() && d.cached_pair.0 == d.cached_pair.1 {
                    self.pending_diseq_conflict = Some(didx);
                }
                self.diseq_watch_push(new_root, didx);
            }

            // ======== Equality-atom watch trigger + migration ========
            // Atoms watched on *either* merged class may have had an endpoint's
            // class change under it: re-test each for a forced value (equal or
            // proven disequal) and enqueue it for the theory manager.  Walking
            // only the loser's list would miss the atoms whose endpoint sits in
            // the surviving class but whose *other* endpoint just became its
            // disequality partner (the loser class carried a matching
            // disequality) – the old rescan observed those via its touch test,
            // so the walk covers both lists.  Duplicate delivery is suppressed
            // by the per-epoch stamp inside `enqueue_forced_atom`.
            //
            // Both lists' entries have their near endpoint in what is now the
            // merged class (root `new_root`) by the side-ordering invariant of
            // `watch_eq_atom`, so one root lookup of the far endpoint decides:
            // equal iff it also lands in `new_root`, proven-disequal iff the
            // pair index holds `(new_root, far)`, or value-apart iff the two
            // classes carry *different* distinguished-value summaries – the
            // mark-based analogue of the proven-disequal case, which keeps
            // equality atoms over ground constants (e.g. `(= x #x01)` once
            // `x` merges into `#x00`'s class) propagating false without a
            // decision, exactly as the old pairwise constant-disequality
            // edges did through the pair index.
            let new_value = self.class_value.get(new_root as usize).copied().flatten();
            for list_root in [new_root, other_root] {
                let aw_len = self.atom_watch.get(list_root as usize).map_or(0, Vec::len);
                for i in 0..aw_len {
                    let w = self.atom_watch[list_root as usize][i];
                    let far = self.uf.find_no_compress(w.b);
                    if far == new_root
                        || self
                            .diseq_pair_counts
                            .contains_key(&ordered_pair(new_root, far))
                        || (new_value.is_some()
                            && new_value != self.class_value.get(far as usize).copied().flatten())
                    {
                        self.enqueue_forced_atom(w);
                    }
                }
            }
            let aw_len = self.atom_watch.get(other_root as usize).map_or(0, Vec::len);
            for i in 0..aw_len {
                let w = self.atom_watch[other_root as usize][i];
                self.atom_watch_push(new_root, w);
            }

            // ======== Optimization 1: Index-based use-list iteration ========
            // Instead of cloning the entire use-list, iterate by index.
            // We snapshot the length so we only process existing entries.
            let use_len = self.use_list[other_root as usize].len();

            // Collect congruence merges to enqueue
            propagation_buf.clear();

            // ======== Change A: Reusable canonicalization buffer ========
            // Declared once outside the loop so the SmallVec's heap backing (if it
            // ever spills past the inline capacity of 4) is allocated at most once
            // per merge event rather than once per use-list entry.
            let mut canon_buf: SmallVec<[u32; 4]> = SmallVec::new();

            for i in 0..use_len {
                let user = self.use_list[other_root as usize][i];
                if (user as usize) >= self.nodes.len() {
                    continue; // stale use-list entry – node was not allocated
                }
                let node_func_val = self.nodes[user as usize].func;
                if node_func_val == ENode::NO_FUNC {
                    continue;
                }
                let func = node_func_val;

                // Read args by index to avoid cloning the SmallVec
                let args_len = self.nodes[user as usize].args.len();
                let mut args_copy: SmallVec<[u32; 4]> = SmallVec::with_capacity(args_len);
                for j in 0..args_len {
                    args_copy.push(self.nodes[user as usize].args[j]);
                }

                // Fetch function properties once per use-list entry (per unique func),
                // then pass to canonicalize_args_with_props_into to avoid repeated lookups.
                let props = self.get_function_props(func);

                // Canonicalize arguments into the reusable buffer (avoids per-iteration alloc).
                self.canonicalize_args_with_props_into(&props, &args_copy, &mut canon_buf);

                // ======== Optimization 2: Fingerprint pre-filter ========
                // Compute the new fingerprint for the updated canonical args and
                // keep the node's cached copy in step with it.
                let new_fp = ENodeFingerprint::compute(func, &canon_buf);
                self.nodes[user as usize].fingerprint = new_fp;

                // Fast-exit guard before the costly sig_table lookup: `sig_table.get`
                // hashes over (u32, SmallVec), which is expensive.  Every signature
                // insertion also pushes the node's fingerprint, so "fingerprint
                // absent" implies "signature absent" and the lookup can be skipped.
                if self.fingerprint_table.contains_key(&new_fp) {
                    let sig = (func, canon_buf.clone());
                    if let Some(&existing) = self.sig_table.get(&sig) {
                        if existing != user && !self.uf.same(user, existing) {
                            // Congruence detected. The proof-forest edge is *not*
                            // appended here – it is appended by the main loop when the
                            // merge is actually applied, so that a merge skipped as
                            // already-satisfied never leaves a redundant edge behind.
                            propagation_buf.push((
                                user,
                                existing,
                                MergeReason::Congruence {
                                    term1: user,
                                    term2: existing,
                                },
                            ));
                        }
                        // The signature is already represented by `existing`, which
                        // is (or is about to be) in `user`'s class.  Leave it alone:
                        // overwriting would break the pop-undo discipline.
                        continue;
                    }
                }

                // No congruence match; publish this node under its *new* signature,
                // first removing its now-stale old entry (keyed by the previous
                // argument representatives) so obsolete keys never accumulate and
                // resurrect into a spurious/missed congruence. The fingerprint
                // table is a prefilter only (sig_table is authoritative), so its
                // stale old bucket is left for the next scan to ignore.
                let in_scope = !self.sig_trail_limits.is_empty();
                self.update_sig_entry(user, (func, canon_buf.clone()), in_scope);
                self.fingerprint_table.entry(new_fp).or_default().push(user);
                if in_scope {
                    self.sig_trail.push(SigTrailEntry::InsertedFingerprint {
                        fp: new_fp,
                        node_idx: user,
                    });
                }
            }

            // Enqueue congruence merges
            for entry in propagation_buf.drain(..) {
                self.pending.push(entry);
            }

            // Merge use lists: extend new_root's use-list with other_root's
            // entries. Each append is trailed (via use_list_push) so pop() undoes
            // exactly these entries from new_root – a pre-existing node whose list
            // would otherwise not be reclaimed by truncation.
            for i in 0..use_len {
                let entry = self.use_list[other_root as usize][i];
                self.use_list_push(new_root, entry);
            }
        }

        propagation_buf.clear();
        self.propagation_buf = propagation_buf;
    }
}
