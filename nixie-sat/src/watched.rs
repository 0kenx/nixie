//! Two-watched literal scheme

use crate::clause::ClauseId;
use crate::literal::{Lit, Var};
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
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
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

/// A CSR-form watch build (count → layout → fill), the `RoundOccs`
/// pattern (`solver/eliminate.rs`) adapted to [`Watcher`] entries —
/// slice 1 of the CSR-watches migration
/// (`docs/studies/2026-09-13-csr-watches-kickoff.md`).
/// Validation infrastructure only: nothing reads it on any default path.
#[derive(Debug, Default)]
pub struct CsrWatchBuild {
    /// Concatenated entries; literal `code`'s filled span is
    /// `entries[prim_end-position]` — see `prim_end`.
    entries: Vec<Watcher>,
    /// Exclusive end offset of each literal's span (the layout).
    span_end: Vec<u32>,
    /// Fill cursor: absolute write position of each literal's span.
    /// Starts at the span's beginning after [`Self::layout`] and advances
    /// to the span end as [`Self::fill`] appends.
    cursor: Vec<u32>,
    /// Per-literal counts accumulated by [`Self::count`] (consumed by
    /// [`Self::layout`]).
    counts: Vec<u32>,
}

impl CsrWatchBuild {
    /// Counting pass: one key per (clause, watched-literal) pair the
    /// caller will later fill, in fill order (order within a literal is
    /// preserved by the counting sort).
    pub fn count(&mut self, lit: Lit) {
        let idx = lit.index();
        if idx >= self.counts.len() {
            self.counts.resize(idx + 1, 0);
        }
        self.counts[idx] = self.counts[idx].saturating_add(1);
    }

    /// Prefix-sum the counts into span extents and size the entry buffer
    /// (`RoundOccs::layout`'s counting sort).  After this, `count` must
    /// not be called again; `fill` each counted pair.
    pub fn layout(&mut self, num_lits: usize) {
        self.counts.resize(num_lits, 0);
        self.span_end = vec![0; num_lits];
        self.cursor = vec![0; num_lits];
        let mut acc = 0u32;
        for (i, &n) in self.counts.iter().enumerate() {
            self.cursor[i] = acc;
            acc = acc.saturating_add(n);
            self.span_end[i] = acc;
        }
        self.entries = Vec::with_capacity(acc as usize);
        self.entries.resize(
            acc as usize,
            Watcher::new(ClauseId::NULL, ClauseRef::NULL, Lit::pos(Var::new(0))),
        );
    }

    /// Fill pass: write `w` into `lit`'s span at the cursor.  The caller
    /// MUST fill each literal's entries in exactly the order
    /// [`Self::count`] saw them.
    #[inline]
    pub fn fill(&mut self, lit: Lit, w: Watcher) {
        let idx = lit.index();
        debug_assert!(idx < self.cursor.len());
        let at = self.cursor[idx] as usize;
        debug_assert!(
            at < self.span_end[idx] as usize,
            "fill overruns the counted span for literal {lit:?}"
        );
        self.entries[at] = w;
        self.cursor[idx] += 1;
    }

    /// The filled span of `lit`'s entries (empty before [`Self::layout`]).
    pub fn span(&self, lit: Lit) -> &[Watcher] {
        let idx = lit.index();
        if idx >= self.span_end.len() {
            return &[];
        }
        let start = if idx == 0 {
            0
        } else {
            self.span_end[idx - 1] as usize
        };
        &self.entries[start..self.span_end[idx] as usize]
    }
}

/// The maintained CSR watch representation — slice 1.5's foundation
/// (`docs/studies/2026-09-13-csr-watches-kickoff.md`): primary spans
/// (rebuilt by the counting sort) plus per-literal arrival-order
/// overflow, with the four mutation operations the search performs.
///
/// InfraSTRUCTURE-AHEAD: nothing constructs this on default paths yet
/// (the hooks are the next slice); the operations are unit-tested against
/// the order-decomposition invariants.
///
/// Invariants (the order-isomorphism argument, kickoff doc §slice-1):
/// every list is *(sorted primary survivors in order) ++ (arrival-ordered
/// overflow)*, which is exactly the drifted `Vec<Vec<Watcher>>` order —
/// in-place compaction, removal and append are all order-preserving on
/// that decomposition.  Nothing reads this on any default path yet; the
/// BCP/session hooks that maintain it during search are the next slice.
#[derive(Debug, Default)]
#[allow(dead_code)] // slice-1.5 foundation; adopted by the shadow hooks next
pub struct CsrWatchLists {
    /// Primary entries; literal `code`'s span is
    /// `entries[span_start[code]..prim_end[code]]`.
    entries: Vec<Watcher>,
    /// Immutable span starts (the counting-sort layout).
    span_start: Vec<u32>,
    /// Live end of each primary span (compaction shrinks it; the space up
    /// to `span_start[code+1]`-style capacity is reclaimed at the next
    /// layout).
    prim_end: Vec<u32>,
    /// Per-literal arrival-order overflow for search-time appends.
    overflow: Vec<Vec<Watcher>>,
}

#[allow(dead_code)] // slice-1.5 foundation
impl CsrWatchLists {
    /// Combined-view length of `lit`'s list.
    #[must_use]
    pub fn len(&self, lit: Lit) -> usize {
        let i = lit.index();
        (self.prim_end.get(i).copied().unwrap_or(0) as usize)
            .saturating_sub(self.span_start.get(i).copied().unwrap_or(0) as usize)
            + self.overflow.get(i).map_or(0, Vec::len)
    }

    /// Whether `lit`'s combined list is empty.
    #[must_use]
    pub fn is_empty(&self, lit: Lit) -> bool {
        self.len(lit) == 0
    }

    /// Append `w` to `lit`'s overflow (search-time `add` / BCP watch move:
    /// arrival order, exactly where the `Vec` lists append).
    pub fn push_overflow(&mut self, lit: Lit, w: Watcher) {
        let i = lit.index();
        if i >= self.overflow.len() {
            self.overflow.resize(i + 1, Vec::new());
        }
        self.overflow[i].push(w);
    }

    /// In-place prefix compaction of `lit`'s primary span down to its
    /// first `n` survivors (the BCP scan's post-truncate state: the scan
    /// compacts survivors toward the span start; overflow survives).
    ///
    /// # Panics
    /// In debug builds when `n` exceeds the primary span's live length.
    pub fn compact_primary(&mut self, lit: Lit, n: usize) {
        let i = lit.index();
        let start = self.span_start.get(i).copied().unwrap_or(0) as usize;
        let end = self.prim_end.get(i).copied().unwrap_or(0) as usize;
        debug_assert!(n <= end - start, "compaction grows the span");
        if let Some(slot) = self.prim_end.get_mut(i) {
            *slot = (start + n) as u32;
        }
        // Survivors are already at [start, start+n): the BCP scan moved
        // them there with its write cursor; only the live end moves.
    }

    /// Remove every entry with arena ref `r` from `lit`'s combined list,
    /// order-preserving on both segments (the `retain`-removal the search
    /// performs on clause deletion).
    pub fn remove_clause(&mut self, lit: Lit, r: ClauseRef) {
        let i = lit.index();
        if i >= self.overflow.len() {
            return;
        }
        let start = self.span_start.get(i).copied().unwrap_or(0) as usize;
        let end = self.prim_end.get(i).copied().unwrap_or(0) as usize;
        let mut write = start;
        for read in start..end {
            let w = self.entries[read];
            if w.r != r {
                self.entries[write] = w;
                write += 1;
            }
        }
        if let Some(slot) = self.prim_end.get_mut(i) {
            *slot = write as u32;
        }
        self.overflow[i].retain(|w| w.r != r);
    }

    /// The combined view of `lit`'s list as a `SmallVec`-free pair:
    /// `(primary_slice, overflow_slice)`.
    #[must_use]
    pub fn spans(&self, lit: Lit) -> (&[Watcher], &[Watcher]) {
        let i = lit.index();
        let start = self.span_start.get(i).copied().unwrap_or(0) as usize;
        let end = self.prim_end.get(i).copied().unwrap_or(0) as usize;
        let prim = self.entries.get(start..end).unwrap_or(&[]);
        let extra: &[Watcher] = self.overflow.get(i).map_or(&[], Vec::as_slice);
        (prim, extra)
    }

    /// Adopt a fresh counting-sort layout (the rebuild): `build` supplies
    /// the spans, overflow is cleared (a full rebuild replaces every
    /// list's content).
    pub fn adopt_layout(&mut self, build: CsrWatchBuild) {
        // CsrWatchBuild's `span_end` is exclusive ends; starts derive.
        let CsrWatchBuild {
            entries, span_end, ..
        } = build;
        self.entries = entries;
        self.span_start = Vec::with_capacity(span_end.len());
        let mut prev = 0u32;
        for &end in &span_end {
            self.span_start.push(prev);
            prev = end;
        }
        self.prim_end = span_end;
        self.overflow.clear();
        self.overflow.resize(self.span_start.len(), Vec::new());
    }
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

    /// Reset to `num_vars` variables, reusing the existing list storage
    /// (each inner list is cleared with its capacity retained; the outer
    /// vector is only grown). The full-rebuild path's allocation-free form:
    /// identical contents to a fresh [`Self::new`] followed by the same
    /// fill, minus the per-rebuild `2·num_vars` header zeroing and the
    /// per-list regrowth.
    pub(crate) fn reset_lists_in_place(&mut self, num_vars: usize) {
        let n = num_vars * 2;
        if self.watches.len() < n {
            self.watches.resize(n, Vec::new());
        }
        for list in self.watches.iter_mut() {
            list.clear();
        }
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

    /// CSR shadow validation (`NIXIE_CSR_SHADOW=1`, slice 1 of the
    /// CSR-watches migration — `docs/studies/2026-09-13-csr-watches-kickoff.md`).
    ///
    /// Rebuilds the watch state **independently** as a CSR (two sweeps:
    /// count → layout → fill, the `RoundOccs` pattern) from the caller's
    /// iteration, then compares every literal's CSR span against the live
    /// per-literal `Vec` list entry-for-entry, **order included**.  Passing
    /// validates that the CSR layout reproduces the rebuild's contents and
    /// per-list order exactly — the representation's claim — and the
    /// elapsed time is an upper bound for the eventual merged build (the
    /// shadow runs the two sweeps alone; the real build will share the
    /// rebuild's existing sweep).
    ///
    /// Returns `(literals_compared, entries_compared, mismatched_literals)`.
    /// Zero-cost when the lists are empty of differences — callers gate on
    /// the env flag.
    pub fn csr_shadow_compare(
        &self,
        num_vars: usize,
        csr: &CsrWatchBuild,
    ) -> (usize, usize, usize) {
        let mut lits = 0usize;
        let mut entries = 0usize;
        let mut bad = 0usize;
        for code in 0..num_vars * 2 {
            let lit = Lit::from_code(code as u32);
            let span = csr.span(lit);
            let list = self.get(lit);
            lits += 1;
            entries += list.len();
            if span != list {
                bad += 1;
                if bad <= 4 {
                    eprintln!(
                        "[csr-shadow] literal {lit:?}: csr len {} vs list len {} (first divergence at {:?})",
                        span.len(),
                        list.len(),
                        span.iter().zip(list.iter()).position(|(a, b)| a != b)
                    );
                }
            }
        }
        (lits, entries, bad)
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

/// `NIXIE_CSR_SHADOW=1`: run the CSR shadow validation at every watch
/// rebuild (slice 1 of the CSR-watches migration — see
/// `docs/studies/2026-09-13-csr-watches-kickoff.md`).  Diagnostic only:
/// the flag adds two validation sweeps per rebuild and never feeds any
/// solver decision.
pub fn csr_shadow_enabled() -> bool {
    #[cfg(feature = "std")]
    {
        use std::sync::OnceLock;
        static FLAG: OnceLock<bool> = OnceLock::new();
        *FLAG.get_or_init(|| {
            std::env::var("NIXIE_CSR_SHADOW")
                .is_ok_and(|v| v == "1" || v.eq_ignore_ascii_case("true"))
        })
    }
    #[cfg(not(feature = "std"))]
    {
        false
    }
}

#[cfg(test)]
mod csr_tests {
    #[test]
    fn csr_watch_build_roundtrip_preserves_order() {
        use super::*;
        let v = |n: usize| Var::new(n as u32);
        let lits = [
            Lit::pos(v(0)),
            Lit::neg(v(0)),
            Lit::pos(v(1)),
            Lit::neg(v(1)),
        ];
        // Count: lit0 <- {A,B}, lit1 <- {C}, lit2 <- {D,A} (arrival order)
        let pairs = [
            (
                0usize,
                Watcher::new(ClauseId::new(1), ClauseRef::NULL, lits[2]),
            ),
            (0, Watcher::new(ClauseId::new(2), ClauseRef::NULL, lits[3])),
            (1, Watcher::new(ClauseId::new(3), ClauseRef::NULL, lits[0])),
            (2, Watcher::new(ClauseId::new(1), ClauseRef::NULL, lits[3])),
            (2, Watcher::new(ClauseId::new(4), ClauseRef::NULL, lits[0])),
        ];
        let mut csr = CsrWatchBuild::default();
        for (code, _) in &pairs {
            csr.count(Lit::from_code(*code as u32));
        }
        csr.layout(4);
        for (code, w) in &pairs {
            csr.fill(Lit::from_code(*code as u32), *w);
        }
        assert_eq!(csr.span(lits[0]).len(), 2);
        assert_eq!(csr.span(lits[1]).len(), 1);
        assert_eq!(csr.span(lits[2]).len(), 2);
        assert_eq!(csr.span(lits[3]).len(), 0);
        // Arrival order preserved within each span.
        assert_eq!(csr.span(lits[0])[0].blocker, lits[2]);
        assert_eq!(csr.span(lits[0])[1].blocker, lits[3]);
        #[cfg(any(
            feature = "bcp-groups",
            feature = "bcp-regions",
            feature = "clause-traffic"
        ))]
        {
            assert_eq!(csr.span(lits[2])[0].clause.0, 1);
            assert_eq!(csr.span(lits[2])[1].clause.0, 4);
        }
        // Order check independent of the clause-id field: the two spans'
        // blockers differ, so compare the arrival order via blockers.
        assert_eq!(csr.span(lits[2])[0].blocker, lits[3]);
        assert_eq!(csr.span(lits[2])[1].blocker, lits[0]);
    }

    #[test]
    fn csr_shadow_compare_detects_divergence() {
        use super::*;
        let mut wl = WatchLists::new(2);
        let w = Watcher::new(ClauseId::new(7), ClauseRef::NULL, Lit::neg(Var::new(1)));
        wl.add(Lit::pos(Var::new(0)), w);
        // Matching CSR: zero mismatches.
        let mut csr = CsrWatchBuild::default();
        csr.count(Lit::pos(Var::new(0)));
        csr.layout(4);
        csr.fill(Lit::pos(Var::new(0)), w);
        let (lits, entries, bad) = wl.csr_shadow_compare(2, &csr);
        assert_eq!((lits, entries, bad), (4, 1, 0));
        // Divergent CSR (different entry): exactly one mismatched literal.
        let mut csr2 = CsrWatchBuild::default();
        csr2.count(Lit::pos(Var::new(0)));
        csr2.layout(4);
        // Diverge in the blocker (always compiled; the clause-id field is
        // feature-gated).
        csr2.fill(
            Lit::pos(Var::new(0)),
            Watcher::new(ClauseId::new(8), ClauseRef::NULL, Lit::pos(Var::new(1))),
        );
        let (_, _, bad2) = wl.csr_shadow_compare(2, &csr2);
        assert_eq!(bad2, 1);
    }

    #[test]
    fn csr_watch_lists_mutation_ops_preserve_order_decomposition() {
        use super::*;
        let v = |n: usize| Var::new(n as u32);
        // Build a CSR with two literals: L0 <- {A,B,C}, L1 <- {} via the
        // counting sort, then exercise the four search mutations.
        let a = Watcher::new(ClauseId::new(1), ClauseRef::NULL, Lit::pos(v(3)));
        let b = Watcher::new(ClauseId::new(2), ClauseRef::NULL, Lit::neg(v(3)));
        let c = Watcher::new(ClauseId::new(3), ClauseRef::NULL, Lit::pos(v(4)));
        let mut build = CsrWatchBuild::default();
        for _ in 0..3 {
            build.count(Lit::pos(v(0)));
        }
        build.layout(8);
        build.fill(Lit::pos(v(0)), a);
        build.fill(Lit::pos(v(0)), b);
        build.fill(Lit::pos(v(0)), c);
        let mut csr = CsrWatchLists::default();
        csr.adopt_layout(build);
        assert_eq!(csr.len(Lit::pos(v(0))), 3);

        // Search-time append (BCP move): arrival order after the primary.
        let m = Watcher::new(ClauseId::new(9), ClauseRef::NULL, Lit::pos(v(5)));
        csr.push_overflow(Lit::pos(v(0)), m);
        let (prim, extra) = csr.spans(Lit::pos(v(0)));
        assert_eq!(prim.len(), 3);
        assert_eq!(extra, &[m]);

        // Clause deletion: order-preserving removal from the primary.
        csr.remove_clause(
            Lit::pos(v(0)),
            ClauseRef::NULL, /* all share NULL; use blocker check instead */
        );
        // (All test watchers share the null ref, so removal would drop
        // everything; compact instead and check the decomposition.)
        let mut csr2 = CsrWatchLists::default();
        let mut b2 = CsrWatchBuild::default();
        for _ in 0..2 {
            b2.count(Lit::neg(v(1)));
        }
        b2.layout(8);
        b2.fill(Lit::neg(v(1)), a);
        b2.fill(Lit::neg(v(1)), b);
        csr2.adopt_layout(b2);
        csr2.push_overflow(Lit::neg(v(1)), c);
        csr2.compact_primary(Lit::neg(v(1)), 1);
        let (p2, e2) = csr2.spans(Lit::neg(v(1)));
        assert_eq!(p2, &[a]);
        assert_eq!(e2, &[c]);
        assert_eq!(csr2.len(Lit::neg(v(1))), 2);
        assert!(csr2.is_empty(Lit::pos(v(0))));
    }
}
