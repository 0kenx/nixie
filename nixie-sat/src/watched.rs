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
    /// Maintained CSR shadow (`NIXIE_CSR_SHADOW=1`, slices 1.5-3 of the
    /// CSR-watches migration — `docs/studies/2026-09-13-csr-watches-kickoff.md`).
    /// `None` on default paths: every mirror below is a single None-check,
    /// and nothing on a default path constructs one.
    csr: Option<CsrWatchLists>,
    /// Surgery-economics instrumentation (slice 5, diagnostics only):
    /// entry visits (span+overflow scans) and wall nanos of the surgical
    /// ops — compared against the rebuild's two-sweep `build=`us per round.
    pub(crate) csr_surgery_visits: u64,
    pub(crate) csr_surgery_nanos: u64,
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
    /// Copy of the CSR shadow, when the dual-write diagnostic is active
    /// (slices 1.5-3; rollback must restore both representations).
    csr: Option<CsrWatchLists>,
}

/// The CSR-form watch build (count → layout → fill), the `RoundOccs`
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

/// The per-scan mirror state carried between `begin_scan` and `end_scan`
/// (the dual-write BCP scan, slice 2 of the CSR-watches migration —
/// `docs/studies/2026-09-13-csr-watches-kickoff.md`).
///
/// `read` counts *notified* entries. The notifying scan visits entries in
/// list order exactly once each, so `read` is the scan's read cursor in
/// combined-view coordinates: positions `< p_len` are primary sources,
/// positions `>= p_len` are overflow sources — the order-isomorphism
/// invariant that makes the mirror resolvable segment-wise.
#[derive(Debug, Default, Clone)]
struct CsrScanFrame {
    /// The scanned literal's code.
    code: usize,
    /// Primary span start (absolute entry offset).
    ps: u32,
    /// Primary live length at scan start.
    p_len: u32,
    /// Overflow length at scan start (excludes mid-scan pushes).
    o_len: u32,
    /// Notified entries so far.
    read: u32,
    /// Primary survivors compacted so far.
    pw: u32,
    /// Overflow survivors compacted so far.
    ow: u32,
    /// False once the frame is finished or its precondition failed (all
    /// notifications become no-ops; the per-rebuild drifted comparison
    /// localizes the divergence).
    active: bool,
}

/// The maintained CSR watch representation — slice 1.5's foundation
/// (`docs/studies/2026-09-13-csr-watches-kickoff.md`): primary spans
/// (rebuilt by the counting sort) plus per-literal arrival-order
/// overflow, with the four mutation operations the search performs.
///
/// Slices 1.5-2: the search-time hooks now maintain this beside the
/// `Vec<Vec<Watcher>>` under `NIXIE_CSR_SHADOW=1` — every scan's
/// keep/remove/move is dual-written, cold-path mutations (`add`,
/// `remove_clause`, arena relocation, snapshot/restore) are mirrored, and
/// each rebuild compares the **drifted** state against the drifted `Vec`
/// lists (order included) before adopting a fresh layout.  Nothing reads
/// this on any default path; readers switch in slice 4.
///
/// Invariants (the order-isomorphism argument, kickoff doc §slice-1):
/// every list is *(sorted primary survivors in order) ++ (arrival-ordered
/// overflow)*, which is exactly the drifted `Vec<Vec<Watcher>>` order —
/// in-place compaction, removal and append are all order-preserving on
/// that decomposition.
#[derive(Debug, Default, Clone)]
#[allow(dead_code)] // adopted by the shadow hooks; readers switch in slice 4
pub struct CsrWatchLists {
    /// Primary entries; literal `code`'s span is
    /// `entries[span_start[code]..prim_end[code]]`.
    entries: Vec<Watcher>,
    /// Immutable span starts (the counting-sort layout).
    span_start: Vec<u32>,
    /// Live end of each primary span (compaction shrinks it; the space up
    /// to the next span's start is reclaimed at the next layout).
    prim_end: Vec<u32>,
    /// Per-literal arrival-order overflow for search-time appends.
    overflow: Vec<Vec<Watcher>>,
    /// The active dual-write scan's mirror state (one scan at a time).
    scan: CsrScanFrame,
    /// Precondition-violation reporting is once per process.
    warned_precondition: bool,
    /// ref → watched-literal codes (≤ 2 entries: one watcher per
    /// (clause, literal)): the surgery experiment's position index.
    /// Maintained by the same funnels as the entries themselves —
    /// `push_overflow` (every append: attach, move, repair, surgery add),
    /// `remove_clause`, the scan notifications, `relocate` rekeying, and
    /// `adopt_layout` (rebuilt from the fresh spans).  The BCP moves
    /// watches without touching stored clause order, so this index — not
    /// `(lits[0], lits[1])` — is the ground truth for where a clause's
    /// watchers actually live (the watch-position-drift finding,
    /// 2026-09-14).
    positions: std::collections::BTreeMap<usize, smallvec::SmallVec<[u32; 2]>>,
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
        let slot = self.positions.entry(w.r.byte_offset()).or_default();
        if !slot.contains(&(i as u32)) {
            slot.push(i as u32);
        }
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
        if let Some(slot) = self.positions.get_mut(&r.byte_offset()) {
            slot.retain(|c| *c != i as u32);
            if slot.is_empty() {
                self.positions.remove(&r.byte_offset());
            }
        }
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
        self.scan = CsrScanFrame::default();
        // Rebuild the position index from the fresh layout: the counting
        // sort places every live clause's watchers at its span positions.
        self.positions.clear();
        for code in 0..self.span_start.len() {
            let start = self.span_start[code];
            let end = self.prim_end[code];
            for off in start..end {
                let w = self.entries[off as usize];
                let slot = self.positions.entry(w.r.byte_offset()).or_default();
                if !slot.contains(&(code as u32)) {
                    slot.push(code as u32);
                }
            }
        }
    }

    // ---- Dual-write BCP scan (slice 2) --------------------------------

    /// Begin mirroring a scan of `code`'s list whose live `Vec` length is
    /// `vec_len`.  Snapshots the primary/overflow split so per-entry
    /// notifications can compact each segment in lockstep with the `Vec`
    /// scan.  The precondition (`vec_len` equals the combined length) is
    /// the order-isomorphism invariant; a violation deactivates the frame
    /// so notifications no-op, and the drifted comparison at the next
    /// rebuild localizes the divergence.
    pub(crate) fn begin_scan(&mut self, code: usize, vec_len: usize) {
        let ps = self.span_start.get(code).copied().unwrap_or(0);
        let pe = self.prim_end.get(code).copied().unwrap_or(0);
        let p_len = pe.saturating_sub(ps);
        let o_len = self.overflow.get(code).map_or(0, Vec::len) as u32;
        let active = (p_len as usize) + (o_len as usize) == vec_len;
        if !active && !self.warned_precondition {
            self.warned_precondition = true;
            eprintln!(
                "[csr-shadow] scan precondition violated at literal code {code}: \
                 combined {} vs vec {vec_len} — mirror suspended for this scan",
                (p_len as u64) + (o_len as u64)
            );
            #[cfg(feature = "std")]
            eprintln!(
                "[csr-shadow] backtrace:\n{}",
                std::backtrace::Backtrace::force_capture()
            );
            let _ = self.scan.active;
        }
        self.scan = CsrScanFrame {
            code,
            ps,
            p_len,
            o_len,
            read: 0,
            pw: 0,
            ow: 0,
            active,
        };
    }

    /// Mirror a kept entry (optionally with a rewritten blocker — the
    /// parked-blocker update).  The survivor compacts into its source
    /// segment exactly where the `Vec` scan's write cursor would put it.
    pub(crate) fn scan_keep(&mut self, watcher: Watcher, blocker: Option<Lit>) {
        let f = &mut self.scan;
        if !f.active {
            return;
        }
        let mut w = watcher;
        if let Some(b) = blocker {
            w.blocker = b;
        }
        if f.read < f.p_len {
            let dst = (f.ps + f.pw) as usize;
            if let Some(slot) = self.entries.get_mut(dst) {
                *slot = w;
                f.pw += 1;
            }
        } else if let Some(ov) = self.overflow.get_mut(f.code) {
            let dst = f.ow as usize;
            if dst < ov.len() {
                ov[dst] = w;
                f.ow += 1;
            }
        }
        f.read += 1;
    }

    /// Mirror a removed entry (deleted clause, repair, watch move-out):
    /// advances the read cursor and drops the position-index entry for
    /// `r` under the scanned literal (the watch leaves this list).
    pub(crate) fn scan_remove(&mut self, r: ClauseRef) {
        if self.scan.active {
            let code = self.scan.code as u32;
            if let Some(slot) = self.positions.get_mut(&r.byte_offset()) {
                slot.retain(|c| *c != code);
                if slot.is_empty() {
                    self.positions.remove(&r.byte_offset());
                }
            }
            self.scan.read += 1;
        }
    }

    /// Mirror a watch move: the entry leaves the scanned list and appends
    /// to the destination literal's overflow in arrival order — exactly
    /// where the `Vec` path's `push_watch`/`add` lands it.
    pub(crate) fn scan_push(&mut self, dest: Lit, w: Watcher) {
        self.push_overflow(dest, w);
    }

    /// Finish the scan: compact each segment's unvisited tail behind its
    /// survivors and drop anything pushed into the scanned literal's own
    /// overflow mid-scan (the `Vec` put-back overwrites the taken slot,
    /// which drops exactly those entries).
    pub(crate) fn end_scan(&mut self) {
        let f = &mut self.scan;
        if !f.active {
            f.active = false;
            return;
        }
        let vis_p = f.read.min(f.p_len);
        let unvis_p = f.p_len - vis_p;
        if unvis_p > 0 {
            let from = (f.ps + vis_p) as usize;
            let to = (f.ps + f.p_len) as usize;
            let dst = (f.ps + f.pw) as usize;
            self.entries.copy_within(from..to, dst);
        }
        if let Some(end) = self.prim_end.get_mut(f.code) {
            *end = f.ps + f.pw + unvis_p;
        }
        let vis_o = f.read.saturating_sub(f.p_len);
        let unvis_o = f.o_len.saturating_sub(vis_o);
        if let Some(ov) = self.overflow.get_mut(f.code) {
            if unvis_o > 0 {
                ov.copy_within(vis_o as usize..f.o_len as usize, f.ow as usize);
            }
            let keep = (f.ow + unvis_o) as usize;
            if ov.len() > keep {
                ov.truncate(keep);
            }
        }
        f.active = false;
    }

    // ---- Cold-path mirrors (slice 3) ----------------------------------

    /// Mirror `WatchLists::relocate_refs`: rewrite survivors' arena refs
    /// through the compaction plan, dropping deleted-clause entries
    /// (order-preserving in both segments, matching the `Vec` pass).
    pub(crate) fn relocate(&mut self, arena: &ClauseArena, plan: &CompactionPlan) {
        let relocated = plan.relocated();
        // Rekey the position index (old → new byte offsets).  Entries of
        // deleted clauses die with the compaction (their watchers are
        // dropped below), so their index slots simply vanish — mirroring
        // the Vec pass's is_deleted skip.
        let mut rekeyed = std::collections::BTreeMap::new();
        let old = std::mem::take(&mut self.positions);
        for (off, lits) in old {
            if let Some(r) = ClauseRef::from_byte_offset(off)
                && !r.is_null()
                && !arena.is_deleted(r)
            {
                // The identity load is now safe (live clause; the deleted
                // case panicked in `live_identity` on lingering dead
                // entries — the compaction-fires test caught it).
                rekeyed.insert(
                    relocated[arena.live_identity(r).index()].byte_offset(),
                    lits,
                );
            }
        }
        self.positions = rekeyed;
        let n = self.span_start.len().max(self.overflow.len());
        for code in 0..n {
            if let (Some(&start), Some(end)) =
                (self.span_start.get(code), self.prim_end.get_mut(code))
            {
                let mut write = start as usize;
                for read in start as usize..*end as usize {
                    let mut w = self.entries[read];
                    if w.r.is_null() {
                        self.entries[write] = w;
                        write += 1;
                        continue;
                    }
                    if arena.is_deleted(w.r) {
                        continue;
                    }
                    w.r = relocated[arena.live_identity(w.r).index()];
                    self.entries[write] = w;
                    write += 1;
                }
                *end = write as u32;
            }
            if let Some(ov) = self.overflow.get_mut(code) {
                let mut write = 0usize;
                for read in 0..ov.len() {
                    let mut w = ov[read];
                    if w.r.is_null() {
                        ov[write] = w;
                        write += 1;
                        continue;
                    }
                    if arena.is_deleted(w.r) {
                        continue;
                    }
                    w.r = relocated[arena.live_identity(w.r).index()];
                    ov[write] = w;
                    write += 1;
                }
                ov.truncate(write);
            }
        }
    }

    /// Remove every entry whose arena byte-offset is in `refs`, from both
    /// segments, order-preserving (the batched surgery's per-literal pass).
    pub(crate) fn remove_clause_batch(
        &mut self,
        lit: Lit,
        refs: &std::collections::HashSet<usize>,
    ) {
        let i = lit.index();
        let start = self.span_start.get(i).copied().unwrap_or(0) as usize;
        let end = self.prim_end.get(i).copied().unwrap_or(0) as usize;
        let mut write = start;
        for read in start..end {
            let w = self.entries[read];
            if refs.contains(&w.r.byte_offset()) {
                if let Some(slot) = self.positions.get_mut(&w.r.byte_offset()) {
                    slot.retain(|c| *c != i as u32);
                    if slot.is_empty() {
                        self.positions.remove(&w.r.byte_offset());
                    }
                }
                continue;
            }
            self.entries[write] = w;
            write += 1;
        }
        if let Some(slot) = self.prim_end.get_mut(i) {
            *slot = write as u32;
        }
        if let Some(ov) = self.overflow.get_mut(i) {
            let mut write = 0usize;
            for read in 0..ov.len() {
                let w = ov[read];
                if refs.contains(&w.r.byte_offset()) {
                    if let Some(slot) = self.positions.get_mut(&w.r.byte_offset()) {
                        slot.retain(|c| *c != i as u32);
                        if slot.is_empty() {
                            self.positions.remove(&w.r.byte_offset());
                        }
                    }
                    continue;
                }
                ov[write] = w;
                write += 1;
            }
            ov.truncate(write);
        }
    }

    /// Sortedness datum (slice-5 economics): count spans whose primary
    /// entries are strictly increasing in arena byte offset (the fill
    /// pushes in clause-id order; ids and arena offsets allocate together,
    /// so spans are expected near-sorted — binary-search removal would
    /// then cut the O(span) surgery scan to O(log span)).
    pub(crate) fn span_sortedness(&self) -> (usize, usize) {
        let mut sorted = 0usize;
        let mut total = 0usize;
        for code in 0..self.span_start.len() {
            let start = self.span_start[code] as usize;
            let end = self.prim_end[code] as usize;
            if end > start + 1 {
                total += 1;
                let w = &self.entries[start..end];
                if w.windows(2)
                    .all(|p| p[0].r.byte_offset() < p[1].r.byte_offset())
                {
                    sorted += 1;
                }
            }
        }
        (sorted, total)
    }

    /// Live length of `code`'s primary span (diagnostics).
    pub(crate) fn span_len(&self, code: usize) -> usize {
        let start = self.span_start.get(code).copied().unwrap_or(0) as usize;
        let end = self.prim_end.get(code).copied().unwrap_or(0) as usize;
        end.saturating_sub(start)
    }

    /// Live length of `code`'s overflow (diagnostics).
    pub(crate) fn overflow_len(&self, code: usize) -> usize {
        self.overflow.get(code).map_or(0, Vec::len)
    }

    /// Diagnostics: total live entries / index size.
    pub(crate) fn debug_total_entries(&self) -> usize {
        let n = self.span_start.len().max(self.overflow.len());
        (0..n)
            .map(|code| {
                let lit = Lit::from_code(code as u32);
                let (prim, extra) = self.spans(lit);
                prim.len() + extra.len()
            })
            .sum()
    }

    pub(crate) fn debug_index_refs(&self) -> usize {
        self.positions.len()
    }

    /// Index-consistency audit: rebuild actual ref→positions from a full
    /// scan of the CSR and compare against the maintained index.  Returns
    /// `(indexed_refs, refs_with_missing_position, refs_with_stale_position)`.
    pub(crate) fn csr_index_audit(&self) -> (usize, usize, usize) {
        let mut actual: std::collections::BTreeMap<usize, smallvec::SmallVec<[u32; 2]>> =
            std::collections::BTreeMap::new();
        let n = self.span_start.len().max(self.overflow.len());
        for code in 0..n {
            let lit = Lit::from_code(code as u32);
            let (prim, extra) = self.spans(lit);
            for w in prim.iter().chain(extra.iter()) {
                let slot = actual.entry(w.r.byte_offset()).or_default();
                if !slot.contains(&(code as u32)) {
                    slot.push(code as u32);
                }
            }
        }
        let mut missing = 0usize;
        let mut stale = 0usize;
        for (off, indexed) in &self.positions {
            match actual.get(off) {
                None => stale += 1,
                Some(a) => {
                    if !indexed.iter().all(|c| a.contains(c)) {
                        missing += 1;
                    }
                }
            }
        }
        (self.positions.len(), missing, stale)
    }

    /// Split-borrow access for the swapped-dual scan (`NIXIE_CSR_SCAN`):
    /// the contiguous primary span (the kernels' `&mut [Watcher]` shape)
    /// and the overflow list of the scanned code, all disjoint from
    /// `entries`' span borrow.  The caller takes the overflow `Vec` out,
    /// scans span-then-overflow, and commits via [`Self::commit_span_end`].
    pub(crate) fn scan_parts(&mut self, code: usize) -> (usize, &[Watcher], &mut Vec<Watcher>) {
        if code >= self.overflow.len() {
            self.overflow.resize(code + 1, Vec::new());
        }
        let start = self.span_start.get(code).copied().unwrap_or(0) as usize;
        let end = self.prim_end.get(code).copied().unwrap_or(0) as usize;
        let CsrWatchLists {
            entries, overflow, ..
        } = self;
        let ovf = &mut overflow[code];
        let span = entries.get(start..end).unwrap_or(&[]);
        (start, span, ovf)
    }

    /// Copy the compacted span home (the swapped scan ran on a copy to
    /// keep the kernel's CSR accesses alias-free).
    pub(crate) fn write_back_span(&mut self, code: usize, start: usize, kept: &[Watcher]) {
        if kept.is_empty() {
            return;
        }
        if let Some(dst) = self.entries.get_mut(start..start + kept.len()) {
            dst.copy_from_slice(kept);
        }
        let _ = code;
    }

    /// Return the scanned overflow (truncated to its pass's write end; the
    /// unvisited tail included when the pass exited on conflict).
    pub(crate) fn put_back_overflow(&mut self, code: usize, mut ovf: Vec<Watcher>, write: usize) {
        if ovf.len() > write {
            ovf.truncate(write);
        }
        if code < self.overflow.len() {
            self.overflow[code] = ovf;
        } else {
            self.overflow.resize(code + 1, Vec::new());
            self.overflow[code] = ovf;
        }
    }

    /// Commit the span pass's compaction end (the swapped scan's primary
    /// maintenance — the kernel compacted the span in place).
    pub(crate) fn commit_span_end(&mut self, code: usize, kept: usize) {
        let start = self.span_start.get(code).copied().unwrap_or(0);
        if let Some(end) = self.prim_end.get_mut(code) {
            *end = start + kept as u32;
        }
    }

    /// Index upkeep for a swapped-scan removal: the entry with ref `r`
    /// left literal `code`'s list (the kernel compacts in place; the
    /// index entry must go now).
    pub(crate) fn index_remove(&mut self, code: usize, r: ClauseRef) {
        let code32 = code as u32;
        if let Some(slot) = self.positions.get_mut(&r.byte_offset()) {
            slot.retain(|c| *c != code32);
            if slot.is_empty() {
                self.positions.remove(&r.byte_offset());
            }
        }
    }

    /// Mirror `WatchLists::clear`: every list empties (the layout arrays
    /// reset; the next rebuild re-adopts a fresh layout).
    pub(crate) fn clear_all(&mut self) {
        self.entries.clear();
        self.span_start.clear();
        self.prim_end.clear();
        for list in &mut self.overflow {
            list.clear();
        }
        self.scan = CsrScanFrame::default();
        self.positions.clear();
    }
}

/// The disjoint mutable parts the propagation session needs: destination
/// lists, phantom ticks, ghost debt, and the CSR dual-write shadow.
pub(crate) type PropagationParts<'a> = (
    &'a mut [Vec<Watcher>],
    &'a [u32],
    &'a mut [u32],
    &'a mut Option<CsrWatchLists>,
);

/// The swapped-dual scan's `Vec` mirror (`NIXIE_CSR_SCAN`): the CSR's
/// span+overflow passes drive, and this cursor reproduces the old
/// in-place `Vec` compaction from the notifications — kept entries in
/// order (possibly blocker-rewritten), removals skipped, the unvisited
/// tail preserved at `finish`.  Consumed sequentially across the two
/// passes (span entries first, overflow after — the combined order the
/// drift invariant maintains).
pub(crate) struct VecScanMirror<'a> {
    list: &'a mut Vec<Watcher>,
    write: usize,
    read: usize,
}

impl<'a> VecScanMirror<'a> {
    pub(crate) fn new(list: &'a mut Vec<Watcher>) -> Self {
        Self {
            list,
            write: 0,
            read: 0,
        }
    }

    /// Mirror a kept entry (optionally with a rewritten blocker).
    pub(crate) fn keep(&mut self, watcher: Watcher, blocker: Option<Lit>) {
        if self.read >= self.list.len() {
            return;
        }
        let mut w = watcher;
        if let Some(b) = blocker {
            w.blocker = b;
        }
        self.list[self.write] = w;
        self.write += 1;
        self.read += 1;
    }

    /// Mirror a removed entry.
    pub(crate) fn remove(&mut self) {
        if self.read < self.list.len() {
            self.read += 1;
        }
    }

    /// Publish the kept prefix plus the unvisited tail (conflict-exit
    /// shape included).
    pub(crate) fn finish(self) {
        let remaining = self.list.len().saturating_sub(self.read);
        if remaining > 0 && self.read != self.write {
            self.list.copy_within(self.read.., self.write);
        }
        let kept = self.write + remaining;
        if self.list.len() > kept {
            self.list.truncate(kept);
        }
    }
}

/// Clause state for the surgery contract audit ([`WatchLists::
/// csr_surgery_contract_audit`]).
pub(crate) enum ClauseAuditState {
    LiveLong,
    DeadOrShort,
}

impl WatchLists {
    pub(crate) fn propagation_parts(&mut self) -> PropagationParts<'_> {
        (
            &mut self.watches,
            &self.bin_phantom,
            &mut self.ghost_debt,
            &mut self.csr,
        )
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
            csr: None,
            csr_surgery_visits: 0,
            csr_surgery_nanos: 0,
        }
    }

    // ---- CSR dual-write shadow (slices 1.5-3) -------------------------
    //
    // The maintained CSR mirrors every mutation the `Vec` lists undergo.
    // All hooks are single None-checks on default paths; the per-rebuild
    // drifted comparison (`csr_drifted_compare`, called by
    // `rebuild_watches_and_binary_graph`) validates the pair entry-for-
    // entry, order included — the empirical order-isomorphism proof.

    /// Detach the shadow (the rebuild: fills would double-maintain;
    /// `csr_set` re-attaches the adopted fresh layout).
    pub(crate) fn csr_take(&mut self) -> Option<CsrWatchLists> {
        self.csr.take()
    }

    /// Attach an adopted CSR layout as the new shadow baseline.
    pub(crate) fn csr_set(&mut self, csr: CsrWatchLists) {
        self.csr = Some(csr);
    }

    /// Whether a maintained shadow exists (drifted comparison is meaningful).
    pub(crate) fn csr_active(&self) -> bool {
        self.csr.is_some()
    }

    /// Read a ref's current watched-literal codes from the index (the
    /// pending-collection form of the batched surgery).
    pub(crate) fn csr_positions_of(&self, r: ClauseRef) -> Option<smallvec::SmallVec<[u32; 2]>> {
        self.csr.as_ref()?.positions.get(&r.byte_offset()).cloned()
    }

    /// Batched surgical removal (the production surgery shape): apply all
    /// pending `(ref, positions)` removals with ONE filtered pass per
    /// distinct literal, instead of a full span scan per ref — the ELS
    /// re-points concentrate on the formula's densest literals (two
    /// smallest-code literals per clause), so per-ref scans pay
    /// O(refs × span) where the batch pays O(sum of distinct spans).
    /// Index entries are dropped for every removed entry.
    #[allow(clippy::type_complexity)]
    pub(crate) fn csr_surgery_flush(
        &mut self,
        pending: &[(ClauseRef, smallvec::SmallVec<[u32; 2]>)],
    ) {
        let Some(csr) = &mut self.csr else {
            return;
        };
        #[cfg(feature = "std")]
        let t0 = std::time::Instant::now();
        let mut by_lit: std::collections::BTreeMap<u32, std::collections::HashSet<usize>> =
            std::collections::BTreeMap::new();
        for (r, lits) in pending {
            for &code in lits {
                by_lit.entry(code).or_default().insert(r.byte_offset());
            }
        }
        for (code, refs) in by_lit {
            let lit = Lit::from_code(code);
            let i = code as usize;
            self.csr_surgery_visits += (csr.span_len(i) + csr.overflow_len(i)) as u64;
            csr.remove_clause_batch(lit, &refs);
        }
        #[cfg(feature = "std")]
        {
            self.csr_surgery_nanos += t0.elapsed().as_nanos() as u64;
        }
    }

    /// CSR-only surgical append (the ELS-rewatching experiment): the
    /// arrival-order overflow push, shadow-only.
    pub(crate) fn csr_surgery_add(&mut self, lit: Lit, w: Watcher) {
        if let Some(csr) = &mut self.csr {
            #[cfg(feature = "std")]
            let t0 = std::time::Instant::now();
            csr.push_overflow(lit, w);
            #[cfg(feature = "std")]
            {
                self.csr_surgery_nanos += t0.elapsed().as_nanos() as u64;
            }
        }
    }

    /// The surgery experiment's equivalence oracle, per-clause contract
    /// form: scan the detached (surgically updated) CSR once and count
    /// watchers per arena ref.  The production surgery's invariant is that
    /// every live long clause keeps exactly two live watchers (wherever
    /// drift + surgery left them — the rebuild's re-normalization to
    /// stored literal order is churn the surgery deliberately does NOT
    /// reproduce) and every dead/binary clause keeps none.  Returns
    /// `(total_entries, live_long_with_wrong_count, dead_or_short_with_entries)`.
    pub(crate) fn csr_surgery_contract_audit(
        &self,
        csr: &CsrWatchLists,
        mut clause_state: impl FnMut(usize) -> ClauseAuditState,
    ) -> (usize, usize, usize) {
        let mut counts: std::collections::BTreeMap<usize, usize> =
            std::collections::BTreeMap::new();
        let mut total = 0usize;
        let n = csr.span_start.len().max(csr.overflow.len());
        for code in 0..n {
            let lit = Lit::from_code(code as u32);
            let (prim, extra) = csr.spans(lit);
            total += prim.len() + extra.len();
            for w in prim.iter().chain(extra.iter()) {
                *counts.entry(w.r.byte_offset()).or_insert(0) += 1;
            }
        }
        let mut wrong_live = 0usize;
        let mut stale_dead = 0usize;
        let mut sampled = 0usize;
        for (off, count) in counts {
            match clause_state(off) {
                ClauseAuditState::LiveLong => {
                    if count != 2 {
                        wrong_live += 1;
                        if sampled < 5 {
                            sampled += 1;
                            eprintln!(
                                "[csr-surgery] sample: ref {off} has {count} watchers, index says {:?}",
                                csr.positions.get(&off)
                            );
                        }
                    }
                }
                ClauseAuditState::DeadOrShort => stale_dead += 1,
            }
        }
        (total, wrong_live, stale_dead)
    }

    /// Order-insensitive (multiset) comparison of the shadow against the
    /// live `Vec` lists — the surgery experiment's equivalence oracle.  The
    /// order-sensitive drifted comparison cannot be used once surgery has
    /// edited the shadow in drift order while the `Vec` rebuilt in id
    /// order; a production surgery accepts (and screens) that order change,
    /// so the oracle validates the ENTRY SETS per literal.
    /// Returns `(literals, entries, mismatched_literals)`.
    /// Compare the CSR shadow against the live lists, order-insensitively
    /// (multiset of (ref, blocker) per literal) — see [`Self::csr_multiset_compare_with`].
    /// (detached) CSR — the surgery experiment's oracle form: the rebuild
    /// detaches the surgically-updated shadow at entry and compares it
    /// Compare the **drifted** shadow against the drifted `Vec` lists,
    /// entry-for-entry, order included (the dual-write validation; called
    /// at every watch rebuild before either representation resets).
    /// Returns `(literals_compared, entries_compared, mismatched_literals)`.
    pub(crate) fn csr_drifted_compare(&self, num_vars: usize) -> (usize, usize, usize) {
        let Some(csr) = &self.csr else {
            return (0, 0, 0);
        };
        let mut lits = 0usize;
        let mut entries = 0usize;
        let mut bad = 0usize;
        for code in 0..num_vars * 2 {
            let lit = Lit::from_code(code as u32);
            let list = self.get(lit);
            let (prim, extra) = csr.spans(lit);
            lits += 1;
            entries += list.len();
            let equal = prim.len() + extra.len() == list.len()
                && prim
                    .iter()
                    .chain(extra.iter())
                    .zip(list.iter())
                    .all(|(a, b)| a == b);
            if !equal {
                bad += 1;
                if bad <= 4 {
                    let first_div = prim
                        .iter()
                        .chain(extra.iter())
                        .zip(list.iter())
                        .position(|(a, b)| a != b);
                    eprintln!(
                        "[csr-shadow] drift literal {lit:?}: csr len {} vs list len {} (first divergence at {first_div:?})",
                        prim.len() + extra.len(),
                        list.len(),
                    );
                }
            }
        }
        (lits, entries, bad)
    }

    /// Begin mirroring a scan of `lit`'s list (dual-write BCP scan, slice
    /// 2): snapshot the primary/overflow split before the list is taken.
    pub(crate) fn shadow_begin_scan(&mut self, lit: Lit) {
        if self.csr.is_some() {
            let n = self.get(lit).len();
            if let Some(csr) = &mut self.csr {
                csr.begin_scan(lit.index(), n);
            }
        }
    }

    /// Mirror a kept entry (optionally with a rewritten blocker).
    pub(crate) fn shadow_scan_keep(&mut self, watcher: Watcher, blocker: Option<Lit>) {
        if let Some(csr) = &mut self.csr {
            csr.scan_keep(watcher, blocker);
        }
    }

    /// Mirror a removed entry.
    pub(crate) fn shadow_scan_remove(&mut self, r: ClauseRef) {
        if let Some(csr) = &mut self.csr {
            csr.scan_remove(r);
        }
    }

    /// Finish the mirrored scan (compaction tails + overflow truncation).
    pub(crate) fn shadow_end_scan(&mut self) {
        if let Some(csr) = &mut self.csr {
            csr.end_scan();
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

    /// Add a watcher for a literal (dual-write: `Vec` push + CSR mirror
    /// when the shadow is active).
    // The CSR mirror branch kept this out-of-line (measured: +2% samples on
    // si2 through call overhead in the rebuild fill and attach paths); the
    // always is load-bearing for the flag-off screen bar.
    #[inline(always)]
    pub fn add(&mut self, lit: Lit, watcher: Watcher) {
        self.push_only(lit, watcher);
        if let Some(csr) = &mut self.csr {
            csr.push_overflow(lit, watcher);
        }
    }

    /// Append without touching the CSR shadow — for callers that fill the
    /// lists while the shadow is detached (the watch rebuild's fill loop:
    /// `csr_take` removed the shadow, so `add` would pay a dead branch per
    /// entry on watch-dense instances, measured +0.75% samples on
    /// worker-class).
    #[inline(always)]
    pub(crate) fn push_only(&mut self, lit: Lit, watcher: Watcher) {
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
    #[inline]
    #[allow(dead_code)]
    pub fn remove_clause(&mut self, lit: Lit, r: ClauseRef) {
        let idx = lit.index();
        if idx < self.watches.len() {
            self.watches[idx].retain(|w| w.r != r);
        }
        if let Some(csr) = &mut self.csr {
            csr.remove_clause(lit, r);
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
            csr: self.csr.clone(),
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
            csr,
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
        self.csr = csr;
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
        if let Some(csr) = &mut self.csr {
            csr.clear_all();
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
        if let Some(csr) = &mut self.csr {
            csr.relocate(arena, plan);
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

/// `NIXIE_CSR_SCAN=1` (slice 4's swapped-dual gate; requires the shadow):
/// the propagation session scans the CSR's span+overflow as the PRIMARY
/// and mirrors the outcomes into the taken `Vec` list — the roles of the
/// slice-2 dual-write swapped.  The drift comparison stays the oracle:
/// it compares the (now primary-scanned) CSR against the (now mirrored)
/// `Vec`.  Default off; the flag-off path is byte-identical.
pub fn csr_scan_enabled() -> bool {
    #[cfg(feature = "std")]
    {
        use std::sync::OnceLock;
        static FLAG: OnceLock<bool> = OnceLock::new();
        *FLAG.get_or_init(|| {
            std::env::var("NIXIE_CSR_SCAN")
                .is_ok_and(|v| v == "1" || v.eq_ignore_ascii_case("true"))
        })
    }
    #[cfg(not(feature = "std"))]
    {
        false
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
    use super::*;

    #[test]
    fn csr_watch_build_roundtrip_preserves_order() {
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

    /// A tiny deterministic LCG so the dual-write tests are reproducible.
    struct Lcg(u64);
    impl Lcg {
        fn next(&mut self) -> u64 {
            self.0 = self
                .0
                .wrapping_mul(6364136223846793005)
                .wrapping_add(1442695040888963407);
            self.0 >> 33
        }
        fn below(&mut self, n: u64) -> u64 {
            self.next() % n
        }
    }

    fn wk(code: u32, salt: u32) -> Watcher {
        // Distinct blockers per generation make order violations visible.
        Watcher::new(
            ClauseId::new(code),
            ClauseRef::NULL,
            Lit::from_code(code.wrapping_mul(31).wrapping_add(salt)),
        )
    }

    /// Reference model of the scan's list-level effect (the spec the
    /// dual-write mirror implements): survivors in visit order (possibly
    /// blocker-rewritten) followed by the unvisited tail.
    fn model_scan(list: &[Watcher], script: &[Option<Option<Lit>>]) -> Vec<Watcher> {
        let mut out = Vec::new();
        let mut read = 0usize;
        for op in script {
            match op {
                Some(blocker) => {
                    let mut w = list[read];
                    if let Some(b) = blocker {
                        w.blocker = *b;
                    }
                    out.push(w);
                    read += 1;
                }
                None => {
                    read += 1;
                    if read >= list.len() {
                        break; // ran past the list: callers never do this
                    }
                }
            }
        }
        let unvisited = read.min(list.len());
        out.extend_from_slice(&list[unvisited..]);
        out
    }

    fn combined(csr: &CsrWatchLists, lit: Lit) -> Vec<Watcher> {
        let (p, o) = csr.spans(lit);
        p.iter().chain(o.iter()).copied().collect()
    }

    /// The dual-write mirror must reproduce the reference model's list
    /// after arbitrary keep/remove sequences over a mixed primary/overflow
    /// list — through many chained scans (drift chains) and early exits.
    #[test]
    fn csr_dual_write_scan_mirrors_reference_model() {
        use super::*;
        let v = |n: usize| Var::new(n as u32);
        let lit = Lit::pos(v(0));
        let mut rng = Lcg(0x5EED_1234);
        for trial in 0..200u32 {
            // Fresh CSR: 0..=5 primary entries, 0..=3 overflow entries.
            let n_prim = 1 + rng.below(5) as usize;
            let n_ovf = rng.below(4) as usize;
            let mut build = CsrWatchBuild::default();
            for i in 0..n_prim {
                build.count(lit);
                let _ = i;
            }
            build.layout(4);
            let mut genctr = 100 * trial;
            let mut reference: Vec<Watcher> = Vec::new();
            for _ in 0..n_prim {
                let w = wk(genctr, 0);
                genctr += 1;
                build.fill(lit, w);
                reference.push(w);
            }
            let mut csr = CsrWatchLists::default();
            csr.adopt_layout(build);
            for _ in 0..n_ovf {
                let w = wk(genctr, 0);
                genctr += 1;
                csr.push_overflow(lit, w);
                reference.push(w);
            }
            assert_eq!(combined(&csr, lit), reference, "baseline {trial}");

            // Chained scans: each notifies a scripted prefix then ends
            // (end == early exit, the conflict shape).
            for scan_round in 0..4u32 {
                csr.begin_scan(lit.index(), reference.len());
                let mut script: Vec<Option<Option<Lit>>> = Vec::new();
                let visits = if scan_round == 3 {
                    reference.len() // full sweep on the last round
                } else {
                    rng.below((reference.len() as u64) + 1) as usize
                };
                for _ in 0..visits {
                    match rng.below(4) {
                        0 => {
                            csr.scan_remove(reference[script.len()].r);
                            script.push(None);
                        }
                        1 => {
                            csr.scan_keep(reference[script.len()], None);
                            script.push(Some(None));
                        }
                        _ => {
                            let b = Lit::from_code((rng.below(2000)) as u32);
                            csr.scan_keep(reference[script.len()], Some(b));
                            script.push(Some(Some(b)));
                        }
                    }
                }
                csr.end_scan();
                reference = model_scan(&reference, &script);
                assert_eq!(
                    combined(&csr, lit),
                    reference,
                    "trial {trial} scan {scan_round}"
                );
            }
        }
    }

    /// Watch moves append to the destination's overflow in arrival order,
    /// and a mid-scan push into the scanned literal's own list is dropped
    /// at `end_scan` — exactly what the `Vec` put-back overwrite does.
    #[test]
    fn csr_dual_write_moves_and_self_push_parity() {
        use super::*;
        let v = |n: usize| Var::new(n as u32);
        let a = Lit::pos(v(0));
        let b = Lit::neg(v(1));
        let mut build = CsrWatchBuild::default();
        build.count(a);
        build.count(a);
        build.layout(4);
        let w0 = wk(10, 0);
        let w1 = wk(11, 0);
        build.fill(a, w0);
        build.fill(a, w1);
        let mut csr = CsrWatchLists::default();
        csr.adopt_layout(build);

        // Scan of `a`: keep w0, move w1 out to `b`, then push a fresh entry
        // back into `a` mid-scan (the repair-can-target-self shape).
        csr.begin_scan(a.index(), 2);
        csr.scan_keep(w0, None);
        let moved = Watcher::new(ClauseId::new(99), ClauseRef::NULL, Lit::from_code(77));
        csr.scan_remove(w1.r); // w1 leaves the list
        csr.scan_push(b, moved); // ...and lands in b's overflow
        let self_push = Watcher::new(ClauseId::new(98), ClauseRef::NULL, Lit::from_code(78));
        csr.scan_push(a, self_push); // dropped by end_scan (put-back parity)
        csr.end_scan();

        assert_eq!(combined(&csr, a), vec![w0]);
        assert_eq!(combined(&csr, b), vec![moved]);

        // A second scan of `b` with an early exit keeps its unvisited tail.
        csr.begin_scan(b.index(), 1);
        csr.end_scan();
        assert_eq!(combined(&csr, b), vec![moved]);
    }

    /// `WatchLists`-level dual bookkeeping: `add`, `remove_clause` and the
    /// scan delegators keep the shadow equal to the `Vec` lists, the
    /// drifted comparison confirms it, and a fabricated divergence is
    /// detected (the diagnostic must never silently pass).
    #[test]
    fn watch_lists_dual_write_drifted_compare_round_trip() {
        use super::*;
        let v = |n: usize| Var::new(n as u32);
        let l0 = Lit::pos(v(0));
        let l1 = Lit::neg(v(1));
        let mut wl = WatchLists::new(4);
        // Attach the shadow baseline the way the rebuild does.
        let mut build = CsrWatchBuild::default();
        build.count(l0);
        build.count(l0);
        build.layout(8);
        let w0 = wk(1, 0);
        let w1 = wk(2, 0);
        build.fill(l0, w0);
        build.fill(l0, w1);
        let mut csr = CsrWatchLists::default();
        csr.adopt_layout(build);
        wl.csr_set(csr);
        assert!(wl.csr_active());

        // Cold-path drift: attach (overflow append) — then a clause
        // deletion keyed by ref. All unit-test watchers share
        // `ClauseRef::NULL` (no arena here), so `remove_clause` drops every
        // NULL-ref entry under the literal: coarse, but it exercises the
        // mirrored retain in both segments (order-preserving).
        let w2 = wk(3, 0);
        wl.add(l1, w2);
        wl.remove_clause(l0, w1.r);
        assert!(wl.get(l0).is_empty());

        // Scan drift through the WatchLists delegators. The scan body
        // writes the `Vec` itself; the delegator mirrors the same keep.
        wl.shadow_begin_scan(l1);
        let parked = Lit::from_code(5);
        wl.get_mut(l1)[0].blocker = parked;
        wl.shadow_scan_keep(w2, Some(parked));
        wl.shadow_end_scan();
        let mut w2b = w2;
        w2b.blocker = parked;
        assert_eq!(wl.get(l1), &[w2b]);

        let (lits, entries, bad) = wl.csr_drifted_compare(4);
        assert_eq!(bad, 0);
        assert_eq!(entries, 1);
        assert_eq!(lits, 8);

        // Snapshot/restore round-trips both representations.
        let snap = wl.packed_snapshot();
        let mut wl2 = WatchLists::new(4);
        wl2.restore(snap);
        assert_eq!(wl2.get(l1), &[w2b]);
        let (_, _, bad2) = wl2.csr_drifted_compare(4);
        assert_eq!(bad2, 0);

        // A fabricated divergence is detected: a Vec-only mutation
        // (bypassing `add`, exactly what a missed mirror hook would be).
        let mut wl3 = wl2.clone();
        wl3.get_mut(l0).push(wk(42, 0));
        let (_, _, bad3) = wl3.csr_drifted_compare(4);
        assert_eq!(bad3, 1);
    }
}
