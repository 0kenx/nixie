//! Congruence closure: signature maintenance, use lists and merge propagation.
//!
//! Split out of `euf/solver.rs` along the "what mutates the e-graph" seam.  Every
//! function here either records a retractable change (a proof-forest edge, a
//! use-list append, a signature-table insertion) or consumes the pending-merge
//! queue; the explanation side lives in [`super::explain`] and the term/instance
//! bookkeeping in the parent module.

use super::{
    ENode, ENodeFingerprint, EufSolver, FunctionProperties, MergeEdge, MergeReason, SigTrailEntry,
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

    /// Append `entry` to `node`'s use-list, recording the append on
    /// `use_list_trail` when a scope is active so `pop()` can remove it.
    #[inline]
    pub(super) fn use_list_push(&mut self, node: u32, entry: u32) {
        self.use_list[node as usize].push(entry);
        if !self.use_list_trail_limits.is_empty() {
            self.use_list_trail.push(node);
        }
    }

    /// Publish `node` under the signature `(func, args)` with fingerprint `fp`.
    ///
    /// The caller must have established that the key is **absent** — the undo
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
            });
        }
        self.sig_table.insert((func, args), node);
        self.fingerprint_table.entry(fp).or_default().push(node);
        if in_scope {
            self.sig_trail
                .push(SigTrailEntry::InsertedFingerprint { fp, node_idx: node });
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
    /// the *same* new signature within one merge event invisible to each other —
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
            // Both assertion *and* congruence edges are appended here — i.e. only
            // once the union below is actually going to happen. Adding an edge for
            // a merge that is subsequently skipped (because the two classes were
            // joined in the meantime by another propagation) would leave the proof
            // forest with two distinct paths between the same pair of nodes, and
            // `explain_equality`'s path search could then justify a congruence by a
            // route that runs through the very edge being explained.
            self.add_proof_edge(
                a,
                MergeEdge {
                    other: b,
                    reason: reason.clone(),
                },
            );
            self.add_proof_edge(b, MergeEdge { other: a, reason });
            // The forest just grew an edge, so every cached explanation may now be
            // longer than the shortest path.  Drop the cache rather than serve a
            // stale (still sound, but needlessly large) answer.
            self.expl_cache.clear();

            // Union the classes
            self.uf.union(root_a, root_b);
            let new_root = self.uf.find(root_a);

            // Congruence closure: check for new merges
            let other_root = if new_root == root_a { root_b } else { root_a };

            // --- Optimization 1: Index-based use-list iteration ---
            // Instead of cloning the entire use-list, iterate by index.
            // We snapshot the length so we only process existing entries.
            let use_len = self.use_list[other_root as usize].len();

            // Collect congruence merges to enqueue
            propagation_buf.clear();

            // --- Change A: Reusable canonicalization buffer ---
            // Declared once outside the loop so the SmallVec's heap backing (if it
            // ever spills past the inline capacity of 4) is allocated at most once
            // per merge event rather than once per use-list entry.
            let mut canon_buf: SmallVec<[u32; 4]> = SmallVec::new();

            for i in 0..use_len {
                let user = self.use_list[other_root as usize][i];
                if (user as usize) >= self.nodes.len() {
                    continue; // stale use-list entry — node was not allocated
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

                // --- Optimization 2: Fingerprint pre-filter ---
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
                            // appended here — it is appended by the main loop when the
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

                // No congruence match; publish this node under its new signature so
                // the *next* use-list entry in this very scan can congruence-match
                // against it.
                self.insert_signature(func, canon_buf.clone(), user, new_fp);
            }

            // Enqueue congruence merges
            for entry in propagation_buf.drain(..) {
                self.pending.push(entry);
            }

            // Merge use lists: extend new_root's use-list with other_root's
            // entries. Each append is trailed (via use_list_push) so pop() undoes
            // exactly these entries from new_root — a pre-existing node whose list
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
