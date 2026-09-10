//! Two-watched literal scheme

use crate::clause::ClauseId;
use crate::literal::Lit;
use crate::memory::{ClauseArena, ClauseRef, CompactionPlan};
#[allow(unused_imports)]
use crate::prelude::*;
#[allow(unused_imports)]
use smallvec::SmallVec;

/// A watcher entry
///
/// Ordinary entries occupy eight bytes: a direct arena reference and a blocker.
/// A stable identity is fetched from the clause header only for a live reason.
/// Observers retain an identity word because they classify deleted blocker hits
/// even after garbage collection has coalesced deleted headers.
#[derive(Debug, Clone, Copy)]
pub struct Watcher {
    /// The clause being watched
    #[cfg(any(
        feature = "bcp-groups",
        feature = "bcp-regions",
        feature = "clause-traffic"
    ))]
    pub clause: ClauseId,
    /// The clause's arena slot (byte offset) – direct-addressing fast path.
    pub r: ClauseRef,
    /// The other watched literal (blocking literal)
    pub blocker: Lit,
}

impl Watcher {
    /// Create a new watcher for a clause whose arena slot is `r`.
    #[must_use]
    pub const fn new(clause: ClauseId, r: ClauseRef, blocker: Lit) -> Self {
        #[cfg(not(any(
            feature = "bcp-groups",
            feature = "bcp-regions",
            feature = "clause-traffic"
        )))]
        let _ = clause;
        Self {
            #[cfg(any(
                feature = "bcp-groups",
                feature = "bcp-regions",
                feature = "clause-traffic"
            ))]
            clause,
            r,
            blocker,
        }
    }
    /// Identity for a clause already established to be live by the scan.
    #[inline]
    pub(crate) fn reason(self, clauses: &crate::clause::ClauseDatabase) -> ClauseId {
        clauses.live_identity(self.r)
    }
}

#[cfg(not(any(
    feature = "bcp-groups",
    feature = "bcp-regions",
    feature = "clause-traffic"
)))]
const _: () = assert!(core::mem::size_of::<Watcher>() == 8);
#[cfg(any(
    feature = "bcp-groups",
    feature = "bcp-regions",
    feature = "clause-traffic"
))]
const _: () = assert!(core::mem::size_of::<Watcher>() == 12);

/// Watch lists for the two-watched literal scheme
///
/// Each literal's list is a `Vec<Watcher>` rather than a `SmallVec`. Propagation
/// takes ownership of the list for the literal being propagated (`mem::take`),
/// walks it with a read/write index, and moves it back. With `Vec` that take/put
/// is just a (ptr,len,cap) move; with `SmallVec` it copied the inline buffer
/// (up to 128 bytes) on every propagated literal and paid a heap spill once a
/// list exceeded the inline capacity – a measurable propagation hot spot.
///
/// # Binary clauses are NOT watched (2026-09, BIG-authoritative BCP)
///
/// A live clause of length 2 is propagated exclusively by the binary
/// implication graph (`Solver::binary_graph`), which `propagate()` scans
/// *before* these lists; its watch entries were pure redundancy (measured:
/// binary entries never reached their arena load – the BIG had already
/// assigned the blocker true). `bin_phantom` exists for **tick parity**: the
/// cadical-style tick counters are computed from watch-list sizes and drive
/// restart / stable-mode schedules, so the removed binary entries must still
/// be *counted* exactly as the old scheme counted them (including lingering
/// after a retire, until the next rebuild). See
/// `studies/2026-09-big-authoritative-bcp.md`.
#[derive(Debug, Clone)]
pub struct WatchLists {
    /// Watch list for each literal (length ≥ 3 clauses only).
    watches: Vec<Vec<Watcher>>,
    /// Per-literal count of binary clauses keyed here in the old scheme
    /// (tick parity bookkeeping – see the module-level note above).
    bin_phantom: Vec<u32>,
    /// Deleted long-watchers stripped at arena compact. Charged once on the
    /// next propagate of that literal, matching lazy ghost removal ticks.
    ghost_debt: Vec<u32>,
}

/// Packed snapshot of a [`WatchLists`] (see [`WatchLists::packed_snapshot`]):
/// every watcher concatenated into one buffer plus one end-offset per list.
/// Restores exactly the same contents as `WatchLists::clone` at a fraction
/// of the transient memory – a deep `clone()` duplicates every per-literal
/// `Vec` (headers *and* doubled capacity), which on clause-dense instances
/// (worker-class: millions of watchers) transiently doubles the watch
/// memory just to hold a rollback copy.
#[derive(Debug)]
pub struct WatchSnapshot {
    /// All watchers, concatenated in list order.
    packed: Vec<Watcher>,
    /// End offset (in watchers) of each list; list i spans
    /// `[ends[i-1], ends[i])` (0 for i = 0).
    ends: Vec<u32>,
    /// Copy of the phantom binary counters (small; cloned verbatim).
    bin_phantom: Vec<u32>,
    /// Copy of compact-time ghost tick debt.
    ghost_debt: Vec<u32>,
}

impl WatchLists {
    pub(crate) fn propagation_parts(&mut self) -> (&mut [Vec<Watcher>], &[u32], &mut [u32]) {
        (&mut self.watches, &self.bin_phantom, &mut self.ghost_debt)
    }

    pub(crate) fn move_capacity_bytes(&self) -> usize {
        0
    }

    /// Create new watch lists for n variables
    #[must_use]
    pub fn new(num_vars: usize) -> Self {
        Self {
            watches: vec![Vec::new(); num_vars * 2],
            bin_phantom: vec![0; num_vars * 2],
            ghost_debt: vec![0; num_vars * 2],
        }
    }

    /// Record one binary clause direction keyed under `lit` (tick parity;
    /// see the struct-level note). Idempotent across resets only via
    /// [`Self::phantom_reset`] – every attach of a binary calls this once per
    /// direction, exactly where the old scheme pushed one watch entry.
    pub fn phantom_bump(&mut self, lit: Lit) {
        let idx = lit.index();
        if idx >= self.bin_phantom.len() {
            self.bin_phantom.resize(idx + 1, 0);
        }
        self.bin_phantom[idx] = self.bin_phantom[idx].saturating_add(1);
    }

    /// Reset every phantom count (the full watch rebuild's bookkeeping:
    /// the old scheme's rebuild re-created entries for exactly the live
    /// binaries, so the refill that follows this must add one bump per live
    /// binary direction).
    pub fn phantom_reset(&mut self, num_lits: usize) {
        self.bin_phantom.clear();
        self.bin_phantom.resize(num_lits, 0);
        self.ghost_debt.clear();
        self.ghost_debt.resize(num_lits, 0);
    }

    /// Phantom binary count under `lit` (tick parity read; 0 when the
    /// table has not grown that far).
    #[must_use]
    pub fn phantom_len(&self, lit: Lit) -> usize {
        self.bin_phantom.get(lit.index()).map_or(0, |&c| c as usize)
    }

    /// Add a watcher for a literal
    pub fn add(&mut self, lit: Lit, watcher: Watcher) {
        let idx = lit.index();
        if idx >= self.watches.len() {
            self.watches.resize(idx + 1, Vec::new());
        }
        self.watches[idx].push(watcher);
    }

    /// Get the watch list for a literal
    #[must_use]
    #[allow(dead_code)]
    pub fn get(&self, lit: Lit) -> &[Watcher] {
        self.watches.get(lit.index()).map_or(&[], |w| w.as_slice())
    }

    /// Get mutable access to the watch list for a literal
    pub fn get_mut(&mut self, lit: Lit) -> &mut Vec<Watcher> {
        let idx = lit.index();
        if idx >= self.watches.len() {
            self.watches.resize(idx + 1, Vec::new());
        }
        &mut self.watches[idx]
    }

    /// Remove all watchers for a clause from a literal's watch list
    #[allow(dead_code)]
    pub fn remove_clause(&mut self, lit: Lit, r: ClauseRef) {
        let idx = lit.index();
        if idx < self.watches.len() {
            self.watches[idx].retain(|w| w.r != r);
        }
    }

    /// Resize to support more variables
    pub fn resize(&mut self, num_vars: usize) {
        let new_size = num_vars * 2;
        if new_size > self.watches.len() {
            self.watches.resize(new_size, Vec::new());
        }
        if new_size > self.bin_phantom.len() {
            self.bin_phantom.resize(new_size, 0);
        }
        if new_size > self.ghost_debt.len() {
            self.ghost_debt.resize(new_size, 0);
        }
    }

    /// Packed rollback snapshot: concatenates every list into one buffer
    /// (one allocation, exact-ish size) instead of deep-cloning every
    /// per-literal `Vec`. [`Self::restore`] rebuilds lists with identical
    /// contents; capacity/pointer identity is not observable.
    #[must_use]
    pub fn packed_snapshot(&self) -> WatchSnapshot {
        let total: usize = self.watches.iter().map(Vec::len).sum();
        let mut snap = WatchSnapshot {
            packed: Vec::with_capacity(total),
            ends: Vec::with_capacity(self.watches.len()),
            bin_phantom: self.bin_phantom.clone(),
            ghost_debt: self.ghost_debt.clone(),
        };
        for list in &self.watches {
            snap.packed.extend_from_slice(list);
            snap.ends.push(snap.packed.len() as u32);
        }
        snap
    }

    /// Restore the exact list contents captured by [`Self::packed_snapshot`]
    /// (the array length and every watcher, in order; empty lists included).
    pub fn restore(&mut self, snap: WatchSnapshot) {
        let WatchSnapshot {
            packed,
            ends,
            bin_phantom,
            ghost_debt,
        } = snap;
        self.watches.clear();
        self.watches.reserve(ends.len());
        let mut start = 0u32;
        for &end in &ends {
            let list: &[Watcher] = &packed[start as usize..end as usize];
            // Exact-capacity rebuild: no doubling churn, and the restored
            // list's future growth behaves as from a fresh `Vec`.
            let mut v = Vec::with_capacity(list.len());
            v.extend_from_slice(list);
            self.watches.push(v);
            start = end;
        }
        self.bin_phantom = bin_phantom;
        self.ghost_debt = ghost_debt;
    }

    /// Live watcher count and total capacity count across all lists
    /// (diagnostics: `NIXIE_MEM_STATS`).
    pub(crate) fn watcher_accounting(&self) -> (usize, usize) {
        self.watches
            .iter()
            .fold((0, 0), |(l, c), w| (l + w.len(), c + w.capacity()))
    }

    /// Clear all watch lists
    pub fn clear(&mut self) {
        for watches in &mut self.watches {
            watches.clear();
        }
        for c in &mut self.bin_phantom {
            *c = 0;
        }
        for c in &mut self.ghost_debt {
            *c = 0;
        }
    }

    /// Get the number of watchers for a literal
    #[must_use]
    #[allow(dead_code)]
    pub fn count(&self, lit: Lit) -> usize {
        self.watches.get(lit.index()).map_or(0, |w| w.len())
    }

    /// Tick debt for deleted long-watchers stripped at the last compact of
    /// `lit`'s list. Zeros the slot so later propagates match lazy removal.
    pub(crate) fn take_ghost_debt(&mut self, lit: Lit) -> usize {
        let idx = lit.index();
        if idx >= self.ghost_debt.len() {
            return 0;
        }
        let debt = self.ghost_debt[idx];
        self.ghost_debt[idx] = 0;
        debt as usize
    }

    /// Validate all references before either the arena or a watcher changes.
    /// Live watchers are rewritten in place. Deleted hits are dropped and
    /// recorded as [`Self::ghost_debt`] so the next propagate charges the
    /// same ticks as lazy ghost removal (Kissat `collect.c` watch flush).
    pub(crate) fn relocate_refs(
        &mut self,
        arena: &ClauseArena,
        refs: &[ClauseRef],
        plan: &CompactionPlan,
    ) {
        assert_eq!(refs.len(), plan.relocated().len());
        assert!(
            self.check_ref_consistency(refs, arena).is_ok(),
            "invalid watcher before relocation"
        );
        if self.ghost_debt.len() < self.watches.len() {
            self.ghost_debt.resize(self.watches.len(), 0);
        }
        for (idx, list) in self.watches.iter_mut().enumerate() {
            let mut write = 0;
            let mut dropped = 0u32;
            for read in 0..list.len() {
                let mut w = list[read];
                if w.r.is_null() {
                    list[write] = w;
                    write += 1;
                    continue;
                }
                if arena.is_deleted(w.r) {
                    dropped = dropped.saturating_add(1);
                    continue;
                }
                w.r = plan.relocated()[arena.live_identity(w.r).index()];
                list[write] = w;
                write += 1;
            }
            list.truncate(write);
            if dropped != 0 {
                self.ghost_debt[idx] = self.ghost_debt[idx].saturating_add(dropped);
            }
        }
    }

    pub(crate) fn check_ref_consistency(
        &self,
        refs: &[ClauseRef],
        arena: &ClauseArena,
    ) -> Result<(), String> {
        for (lit_idx, list) in self.watches.iter().enumerate() {
            for w in list {
                if w.r.is_null() {
                    continue;
                }
                let Some(clause) = arena.get(w.r) else {
                    return Err(format!("invalid watcher reference under literal {lit_idx}"));
                };
                #[cfg(any(
                    feature = "bcp-groups",
                    feature = "bcp-regions",
                    feature = "clause-traffic"
                ))]
                if refs.get(w.clause.index()).copied() != Some(w.r) {
                    return Err(format!(
                        "observer identity disagrees with watcher reference under literal {lit_idx}"
                    ));
                }
                if !clause.deleted {
                    let id = arena.live_identity(w.r);
                    if refs.get(id.index()).copied() != Some(w.r) {
                        return Err(format!(
                            "live identity disagrees with watcher reference under literal {lit_idx}"
                        ));
                    }
                }
            }
        }
        Ok(())
    }
}

/// SIMD-optimized utilities for watched literal processing
///
/// These functions are designed to be auto-vectorized by LLVM for better performance.
/// When compiled with appropriate flags (e.g., -C target-cpu=native), these operations
/// can use SIMD instructions (SSE, AVX, etc.) automatically.
pub mod simd_utils {
    use super::*;
    use crate::literal::LBool;

    /// Check multiple blockers in parallel (optimized for auto-vectorization)
    ///
    /// This function processes watchers in batches and is designed to be
    /// auto-vectorized by LLVM. The compiler can generate SIMD instructions
    /// for the blocker checking when optimization is enabled.
    ///
    /// # Arguments
    /// * `watchers` - Slice of watchers to check
    /// * `lit_values` - Function to get the value of a literal
    ///
    /// # Returns
    /// Indices of watchers that need propagation (blocker is not true)
    #[inline]
    #[allow(dead_code)]
    pub fn find_non_satisfied_watchers<F>(
        watchers: &[Watcher],
        mut lit_values: F,
    ) -> SmallVec<[usize; 16]>
    where
        F: FnMut(Lit) -> LBool,
    {
        let mut result = SmallVec::new();

        // Process in chunks to enable better vectorization
        const CHUNK_SIZE: usize = 8;

        let mut i = 0;
        while i + CHUNK_SIZE <= watchers.len() {
            // Check blockers in batch (LLVM can vectorize this)
            for j in 0..CHUNK_SIZE {
                let watcher = &watchers[i + j];
                if !lit_values(watcher.blocker).is_true() {
                    result.push(i + j);
                }
            }
            i += CHUNK_SIZE;
        }

        // Process remaining watchers
        while i < watchers.len() {
            let watcher = &watchers[i];
            if !lit_values(watcher.blocker).is_true() {
                result.push(i);
            }
            i += 1;
        }

        result
    }

    /// Batch check if literals are satisfied (optimized for auto-vectorization)
    ///
    /// This is optimized for SIMD by processing literals in aligned chunks.
    ///
    /// # Arguments
    /// * `lits` - Slice of literals to check
    /// * `lit_values` - Function to get the value of a literal
    ///
    /// # Returns
    /// true if any literal is satisfied (true)
    #[inline]
    #[allow(dead_code)]
    pub fn any_satisfied<F>(lits: &[Lit], mut lit_values: F) -> bool
    where
        F: FnMut(Lit) -> LBool,
    {
        // Process in chunks for better vectorization
        const CHUNK_SIZE: usize = 8;

        let chunks = lits.chunks(CHUNK_SIZE);
        for chunk in chunks {
            // Check chunk (can be vectorized)
            for &lit in chunk {
                if lit_values(lit).is_true() {
                    return true;
                }
            }
        }

        false
    }

    /// Count unsatisfied literals in a clause (optimized for auto-vectorization)
    ///
    /// # Arguments
    /// * `lits` - Slice of literals to check
    /// * `lit_values` - Function to get the value of a literal
    ///
    /// # Returns
    /// Number of literals that are not satisfied (not true)
    #[inline]
    #[allow(dead_code)]
    pub fn count_unsatisfied<F>(lits: &[Lit], mut lit_values: F) -> usize
    where
        F: FnMut(Lit) -> LBool,
    {
        let mut count = 0;

        // Process in chunks for vectorization
        const CHUNK_SIZE: usize = 8;

        for chunk in lits.chunks(CHUNK_SIZE) {
            for &lit in chunk {
                if !lit_values(lit).is_true() {
                    count += 1;
                }
            }
        }

        count
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::literal::Var;

    #[test]
    fn test_watch_lists() {
        let mut wl = WatchLists::new(5);

        let lit = Lit::pos(Var::new(0));
        let clause = ClauseId::new(0);
        let blocker = Lit::neg(Var::new(1));

        wl.add(lit, Watcher::new(clause, ClauseRef::null(), blocker));

        assert_eq!(wl.get(lit).len(), 1);
        #[cfg(any(
            feature = "bcp-groups",
            feature = "bcp-regions",
            feature = "clause-traffic"
        ))]
        assert_eq!(wl.get(lit)[0].clause, clause);
        assert_eq!(wl.get(lit)[0].blocker, blocker);
    }
}
