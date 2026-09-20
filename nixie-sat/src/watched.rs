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
/// `#[repr(C)]` is load-bearing: the AVX2 block filter extracts the
/// four blocker codes of a 4-watcher block as dwords 1,3,5,7 of one
/// `vmovdqu` — a field reorder would silently read refs instead (the
/// randomized differential test catches it as wild codes).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
#[repr(C)]
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
    /// Copy of the CSR, when one is active (rollback must restore it).
    /// Stored PACKED — the overflow as one buffer plus per-literal ends —
    /// because a derived `Vec<Vec<Watcher>>` clone duplicates every
    /// per-literal header (18.7M empty headers ≈ 450 MB on the
    /// 9.4M-variable class; measured 3% of the whole run inside lucky's
    /// entry snapshot in commit-B mode).
    csr: Option<PackedCsrSnapshot>,
}

/// The CSR's packed rollback form: the three contiguous arrays cloned
/// verbatim (unavoidable — they ARE the state) plus the overflow packed
/// into one buffer with per-literal end offsets (empty lists cost nothing,
/// matching the `Vec` side's `WatchSnapshot` economics).
#[derive(Debug, Clone)]
pub(crate) struct PackedCsrSnapshot {
    entries: Vec<Watcher>,
    span_start: Vec<u32>,
    prim_end: Vec<u32>,
    ovf_packed: Vec<Watcher>,
    /// (literal code, packed end offset) per nonempty spill tail.
    ovf_ends: Vec<(u32, u32)>,
    maintain_index: bool,
    positions: std::collections::BTreeMap<usize, smallvec::SmallVec<[u32; 2]>>,
}

impl From<&CsrWatchLists> for PackedCsrSnapshot {
    fn from(c: &CsrWatchLists) -> Self {
        // The spill tails pack into one buffer keyed by literal (sparse —
        // the common run has none at all); the three contiguous arrays
        // are the state and clone verbatim.
        let mut ovf_packed = Vec::new();
        let mut ovf_ends = Vec::new();
        for (code, tail) in c.spill.iter().enumerate() {
            if let Some(t) = tail.as_ref() {
                ovf_packed.extend_from_slice(t);
                ovf_ends.push((code as u32, ovf_packed.len() as u32));
            }
        }
        Self {
            entries: c.entries.clone(),
            span_start: c.span_start.clone(),
            prim_end: c.prim_end.clone(),
            ovf_packed,
            ovf_ends,
            maintain_index: c.maintain_index,
            positions: c.positions.clone(),
        }
    }
}

impl From<&PackedCsrSnapshot> for CsrWatchLists {
    fn from(p: &PackedCsrSnapshot) -> Self {
        let mut spill: Vec<Option<Box<Vec<Watcher>>>> = Vec::new();
        let mut start = 0usize;
        for &(code, end) in &p.ovf_ends {
            let v = p.ovf_packed[start..end as usize].to_vec();
            if (code as usize) >= spill.len() {
                spill.resize(code as usize + 1, None);
            }
            spill[code as usize] = Some(Box::new(v));
            start = end as usize;
        }
        Self {
            entries: p.entries.clone(),
            span_start: p.span_start.clone(),
            prim_end: p.prim_end.clone(),
            spill,
            arrivals: Vec::new(),
            scan: CsrScanFrame::default(),
            warned_precondition: false,
            positions: p.positions.clone(),
            maintain_index: p.maintain_index,
        }
    }
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

/// The maintained CSR watch representation — the **slack-CSR** form
/// (2026-09-20 redesign): one contiguous allocation per literal with
/// embedded slack, replacing the earlier span+per-literal-overflow pair.
///
/// * `entries[span_start[c]..cap(c)]` is literal `c`'s allocation
///   (`cap(c) = span_start[c+1]`; the array carries one sentinel at the
///   end); `[span_start[c]..prim_end[c])` is live, `[prim_end[c]..cap(c))`
///   is slack.
/// * A search-time append (`push_overflow`) writes `entries[prim_end[c]]`
///   and bumps — O(1), zero per-literal structure, zero allocation while
///   slack remains.  A literal whose slack fills **spills**: its appends
///   go to `fallback` from then on (sticky, so arrival order across the
///   two segments stays chronological) until the next rebuild.
/// * A scan compacts its span in place (the cursor's write stays behind
///   its read) and commits `prim_end` — mid-scan self-pushes land beyond
///   the snapshotted live end and die at the commit, exactly the old
///   taken-`Vec` put-back-overwrite semantics.
/// * The scan's visit order — *(rebuilt span in id order) compacted by
///   survivors, then arrival-ordered appends* — is the same
///   survivors-then-appends decomposition the span+overflow form
///   maintained, so trajectories are unchanged (bit-identity verified
///   per landing).
///
/// Pre-layout (before the first rebuild/deferred materialization) there
/// is no layout: `span_start`/`prim_end` are empty and every push goes
/// to `fallback`.
#[derive(Debug, Default, Clone)]
pub struct CsrWatchLists {
    /// Per-literal allocations with embedded slack; literal `c`'s live
    /// span is `entries[span_start[c]..prim_end[c]]`.
    entries: Vec<Watcher>,
    /// Allocation starts; `span_start[c+1]` is `c`'s cap (sentinel at the
    /// end: `span_start[num_lits] == entries.len()`).
    span_start: Vec<u32>,
    /// Live end of each span (a push bumps it; a scan commits it; the
    /// space up to the cap is slack, reclaimed at the next layout).
    prim_end: Vec<u32>,
    /// Sticky-spill tails: literals whose slack filled — a dense array of
    /// optional boxed lists (8 B per literal, heap only where actually
    /// spilled; O(1) take/put/push per scan).  Stickiness: once `Some`,
    /// the slot is that literal's append target until the next layout.
    #[allow(clippy::box_collection)] // Option<Box<Vec>>'s null IS the 8B spill marker
    spill: Vec<Option<Box<Vec<Watcher>>>>,
    /// Per-literal spill DEMAND for the next layout's slack sizing
    /// (saturating u16): at adopt time, each spilled literal's surviving
    /// tail length raises its slot, and the next layout gives it
    /// `1 + demand` free appends.  Derived at adopt time only — the hot
    /// push path pays nothing.  ~37 MB on the 9.4M-variable class.
    arrivals: Vec<u16>,
    /// The active dual-write scan's mirror state (one scan at a time).
    scan: CsrScanFrame,
    /// Precondition-violation reporting is once per process.
    warned_precondition: bool,
    /// ref → watched-literal codes (≤ 2 entries: one watcher per
    /// (clause, literal)): the surgery experiment's position index.
    /// Surgery/diagnostic machinery only — see `maintain_index`.
    positions: std::collections::BTreeMap<usize, smallvec::SmallVec<[u32; 2]>>,
    /// Whether `positions` is maintained at all (a BTreeMap write per
    /// watcher-add measured +24% whole-run instructions when left on
    /// unconditionally — the f5796de0 cost class).
    pub(crate) maintain_index: bool,
}

impl CsrWatchLists {
    /// Allocation cap of `code`'s span (its successor's start; the
    /// sentinel covers the last literal).
    fn cap(&self, code: usize) -> usize {
        self.span_start.get(code + 1).copied().unwrap_or(0) as usize
    }

    /// Combined-view length of `lit`'s list.
    #[must_use]
    #[inline]
    pub fn len(&self, lit: Lit) -> usize {
        let i = lit.index();
        let span = (self.prim_end.get(i).copied().unwrap_or(0) as usize)
            .saturating_sub(self.span_start.get(i).copied().unwrap_or(0) as usize);
        span + self.spill_slot_len(i)
    }

    /// Spill-tail length at `code` (0 when no slot / empty).
    fn spill_slot_len(&self, code: usize) -> usize {
        self.spill
            .get(code)
            .and_then(|s| s.as_ref())
            .map_or(0, |v| v.len())
    }

    /// Whether `lit`'s combined list is empty.
    #[must_use]
    #[allow(dead_code)] // diagnostics/tests
    pub fn is_empty(&self, lit: Lit) -> bool {
        self.len(lit) == 0
    }

    /// Number of literals the layout covers.
    pub(crate) fn num_lits(&self) -> usize {
        self.span_start.len().saturating_sub(1)
    }

    /// The combined view of `lit`'s list as a pair: `(live span, spill
    /// tail)` — the second is empty unless the literal spilled.
    #[must_use]
    pub fn spans(&self, lit: Lit) -> (&[Watcher], &[Watcher]) {
        let i = lit.index();
        let start = self.span_start.get(i).copied().unwrap_or(0) as usize;
        let end = self.prim_end.get(i).copied().unwrap_or(0) as usize;
        let prim = self.entries.get(start..end).unwrap_or(&[]);
        let extra: &[Watcher] = self.spill_extra(i);
        (prim, extra)
    }

    /// Spill-tail slice at `code` (empty when none).
    fn spill_extra(&self, code: usize) -> &[Watcher] {
        self.spill
            .get(code)
            .and_then(|s| s.as_ref())
            .map_or(&[], |v| v.as_slice())
    }

    /// Append `w` to `lit`'s list in arrival order: slack-append while
    /// the literal has room and has not spilled; the spill tail once it
    /// has (sticky — appends never interleave across the two segments,
    /// which would reorder the visit sequence).
    pub fn push_overflow(&mut self, lit: Lit, w: Watcher) {
        let code = lit.index();
        if let Some(tail) = self.spill.get_mut(code).and_then(|s| s.as_mut()) {
            tail.push(w);
            return;
        }
        let live = self.prim_end.get(code).copied().unwrap_or(0) as usize;
        let cap = self.cap(code);
        if code < self.prim_end.len() && live < cap {
            self.entries[live] = w;
            self.prim_end[code] = (live + 1) as u32;
        } else {
            if code >= self.spill.len() {
                self.spill.resize(code + 1, None);
            }
            self.spill[code] = Some(Box::default());
            if let Some(t) = self.spill[code].as_mut() {
                t.push(w);
            }
        }
        if self.maintain_index {
            let slot = self.positions.entry(w.r.byte_offset()).or_default();
            if !slot.contains(&(code as u32)) {
                slot.push(code as u32);
            }
        }
    }

    /// Remove every entry with arena ref `r` from `lit`'s list,
    /// order-preserving on both segments.
    pub fn remove_clause(&mut self, lit: Lit, r: ClauseRef) {
        let i = lit.index();
        let start = self.span_start.get(i).copied().unwrap_or(0) as usize;
        let end = self.prim_end.get(i).copied().unwrap_or(0) as usize;
        if end > start {
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
        }
        if let Some(tail) = self.spill.get_mut(i).and_then(|s| s.as_mut()) {
            tail.retain(|w| w.r != r);
            if tail.is_empty() {
                self.spill[i] = None;
            }
        }
        if self.maintain_index
            && let Some(slot) = self.positions.get_mut(&r.byte_offset())
        {
            slot.retain(|c| *c != i as u32);
            if slot.is_empty() {
                self.positions.remove(&r.byte_offset());
            }
        }
    }

    /// Adopt a fresh counting-sort layout (the rebuild): the build's
    /// packed spans are re-spaced with embedded slack, every literal
    /// restarts live, and the spill tails clear.
    ///
    /// Slack policy: `min(4, 1 + count/32)` per nonempty literal — the
    /// modal literal (2-3 watchers) gets one free append (the common
    /// inter-rebuild arrival), dense literals get proportionally more.
    /// A push beyond slack spills.
    pub fn adopt_layout(&mut self, build: CsrWatchBuild) {
        let CsrWatchBuild {
            entries, span_end, ..
        } = build;
        let num_lits = span_end.len();
        // Adaptive slack from OBSERVED SPILL DEMAND: a literal only needs
        // more than base slack if it actually spilled last interval, and
        // its surviving tail length is a lower bound on what it needed.
        // Derived entirely at adopt time (zero per-push cost — the hot
        // push path never touches the counter), so the sizing sees every
        // push source, including the session kernel's watch moves.
        if self.arrivals.len() < num_lits {
            self.arrivals.resize(num_lits, 0);
        }
        for (code, tail) in self.spill.iter().enumerate() {
            if let Some(t) = tail.as_ref() {
                let demand = t.len().min(usize::from(u16::MAX));
                let slot = &mut self.arrivals[code];
                *slot = (*slot).max(demand as u16);
            }
        }
        let mut starts = Vec::with_capacity(num_lits + 1);
        let mut total = 0u32;
        starts.push(0u32);
        let mut prev = 0u32;
        for (code, &end) in span_end.iter().enumerate() {
            let count = end - prev;
            prev = end;
            // Uncapped: the total equals what the old per-literal-overflow
            // design held anyway (demand-bounded), but contiguous and
            // allocation-free; hot literals stop spilling after one
            // learning interval.
            let slack = if count == 0 {
                u32::from(self.arrivals[code])
            } else {
                1 + u32::from(self.arrivals[code])
            };
            total = total.saturating_add(count + slack);
            starts.push(total);
        }
        for a in self.arrivals.iter_mut() {
            *a = 0;
        }
        let mut spaced = vec![
            Watcher::new(ClauseId::NULL, ClauseRef::NULL, Lit::pos(Var::new(0)));
            total as usize
        ];
        let mut cursor = 0usize;
        let mut live = Vec::with_capacity(num_lits);
        prev = 0;
        for (code, &end) in span_end.iter().enumerate() {
            let count = (end - prev) as usize;
            prev = end;
            let dst = starts[code] as usize;
            if count > 0 {
                spaced[dst..dst + count].copy_from_slice(&entries[cursor..cursor + count]);
            }
            cursor += count;
            live.push((dst + count) as u32);
        }
        self.entries = spaced;
        self.span_start = starts;
        self.prim_end = live;
        self.spill.clear();
        self.scan = CsrScanFrame::default();
        // Rebuild the position index from the fresh layout (surgery /
        // diagnostic machinery only).
        self.positions.clear();
        if self.maintain_index {
            for code in 0..num_lits {
                let s = self.span_start[code] as usize;
                let e = self.prim_end[code] as usize;
                for off in s..e {
                    let w = self.entries[off];
                    let slot = self.positions.entry(w.r.byte_offset()).or_default();
                    if !slot.contains(&(code as u32)) {
                        slot.push(code as u32);
                    }
                }
            }
        }
    }

    // ---- Dual-write BCP scan (the legacy frame mirror) ---------------

    /// Begin mirroring a scan of `code`'s list whose scanned length is
    /// `scanned_len` (the materialized scratch).  Precondition: the
    /// combined length equals it; a violation deactivates the frame.
    pub(crate) fn begin_scan(&mut self, code: usize, scanned_len: usize) {
        let ps = self.span_start.get(code).copied().unwrap_or(0);
        let pe = self.prim_end.get(code).copied().unwrap_or(0);
        let p_len = pe.saturating_sub(ps);
        let o_len = self.spill_slot_len(code) as u32;
        let active = (p_len as usize) + (o_len as usize) == scanned_len;
        if !active && !self.warned_precondition {
            self.warned_precondition = true;
            eprintln!(
                "[csr-shadow] scan precondition violated at literal code {code}: \
                 combined {} vs scanned {scanned_len} — mirror suspended for this scan",
                (p_len as u64) + (o_len as u64)
            );
            #[cfg(feature = "std")]
            eprintln!(
                "[csr-shadow] backtrace:\n{}",
                std::backtrace::Backtrace::force_capture()
            );
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

    /// Mirror a kept entry (optionally with a rewritten blocker).
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
        } else if let Some(tail) = self.spill.get_mut(f.code).and_then(|s| s.as_mut()) {
            let dst = f.ow as usize;
            if dst < tail.len() {
                tail[dst] = w;
                f.ow += 1;
            }
        }
        f.read += 1;
    }

    /// Mirror a removed entry: advance the read cursor and drop the
    /// position-index entry for `r` under the scanned literal.
    pub(crate) fn scan_remove(&mut self, r: ClauseRef) {
        if self.scan.active {
            let code = self.scan.code;
            if self.maintain_index
                && let Some(slot) = self.positions.get_mut(&r.byte_offset())
            {
                slot.retain(|c| *c != code as u32);
                if slot.is_empty() {
                    self.positions.remove(&r.byte_offset());
                }
            }
            self.scan.read += 1;
        }
    }

    /// Mirror a watch move: append to the destination literal (arrival
    /// order — exactly where the `Vec` path's push lands).
    pub(crate) fn scan_push(&mut self, dest: Lit, w: Watcher) {
        self.push_overflow(dest, w);
    }

    /// Finish the scan: compact the unvisited span tail behind its
    /// survivors, compact/truncate the spill tail, and commit the live
    /// end — mid-scan self-pushes (beyond the snapshotted lengths) die
    /// here, exactly as the `Vec` put-back overwrite dropped them.
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
        if let Some(tail) = self.spill.get_mut(f.code).and_then(|s| s.as_mut()) {
            if unvis_o > 0 {
                tail.copy_within(vis_o as usize..f.o_len as usize, f.ow as usize);
            }
            let keep = (f.ow + unvis_o) as usize;
            if tail.len() > keep {
                tail.truncate(keep);
            }
            if tail.is_empty() {
                self.spill[f.code] = None;
            }
        }
        f.active = false;
        f.read = 0;
        f.o_len = 0;
        f.p_len = 0;
        f.pw = 0;
        f.ow = 0;
        f.code = 0;
        f.ps = 0;
    }

    // ---- Cold paths ---------------------------------------------------

    /// Relocation through the compaction plan (see `relocate_with_debt`).
    pub(crate) fn relocate(&mut self, arena: &ClauseArena, plan: &CompactionPlan) {
        self.relocate_impl(arena, plan, None::<&mut [u32]>);
    }

    /// [`Self::relocate`] with tick-debt charging (commit-B mode).
    pub(crate) fn relocate_with_debt(
        &mut self,
        arena: &ClauseArena,
        plan: &CompactionPlan,
        ghost_debt: &mut [u32],
    ) {
        self.relocate_impl(arena, plan, Some(ghost_debt));
    }

    fn relocate_impl(
        &mut self,
        arena: &ClauseArena,
        plan: &CompactionPlan,
        mut ghost_debt: Option<&mut [u32]>,
    ) {
        let relocated = plan.relocated();
        if self.maintain_index {
            let mut rekeyed = std::collections::BTreeMap::new();
            let old = std::mem::take(&mut self.positions);
            for (off, lits) in old {
                if let Some(r) = ClauseRef::from_byte_offset(off)
                    && !r.is_null()
                    && !arena.is_deleted(r)
                {
                    rekeyed.insert(
                        relocated[arena.live_identity(r).index()].byte_offset(),
                        lits,
                    );
                }
            }
            self.positions = rekeyed;
        }
        let n = self.num_lits();
        for code in 0..n {
            let mut dropped = self.relocate_span(code, arena, relocated);
            if let Some(tail) = self.spill.get_mut(code).and_then(|s| s.as_mut()) {
                dropped = dropped.saturating_add(Self::relocate_tail(tail, arena, relocated));
                if tail.is_empty() {
                    self.spill[code] = None;
                }
            }
            if dropped != 0
                && let Some(debt) = ghost_debt.as_mut()
                && let Some(slot) = debt.get_mut(code)
            {
                *slot = slot.saturating_add(dropped);
            }
        }
        // Spill tails BEYOND the layout (the pre-first-materialize window,
        // where every push lived in the tails — the old code's overflow
        // array covered them; missing this left stale refs and dead
        // entries un-relocated and desynced the mirror from the first
        // compaction on).
        for code in n..self.spill.len() {
            let mut dropped = 0u32;
            if let Some(tail) = self.spill.get_mut(code).and_then(|s| s.as_mut()) {
                dropped = Self::relocate_tail(tail, arena, relocated);
                if tail.is_empty() {
                    self.spill[code] = None;
                }
            }
            if dropped != 0
                && let Some(debt) = ghost_debt.as_mut()
                && let Some(slot) = debt.get_mut(code)
            {
                *slot = slot.saturating_add(dropped);
            }
        }
    }

    /// Relocate one literal's live span in place; returns the dropped count.
    fn relocate_span(&mut self, code: usize, arena: &ClauseArena, relocated: &[ClauseRef]) -> u32 {
        let mut dropped = 0u32;
        if let (Some(&start), Some(end)) = (self.span_start.get(code), self.prim_end.get_mut(code))
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
                    dropped = dropped.saturating_add(1);
                    continue;
                }
                w.r = relocated[arena.live_identity(w.r).index()];
                self.entries[write] = w;
                write += 1;
            }
            *end = write as u32;
        }
        dropped
    }

    /// Relocate one spill tail in place; returns the dropped count.
    fn relocate_tail(tail: &mut Vec<Watcher>, arena: &ClauseArena, relocated: &[ClauseRef]) -> u32 {
        let mut dropped = 0u32;
        let mut write = 0usize;
        for read in 0..tail.len() {
            let mut w = tail[read];
            if w.r.is_null() {
                tail[write] = w;
                write += 1;
                continue;
            }
            if arena.is_deleted(w.r) {
                dropped = dropped.saturating_add(1);
                continue;
            }
            w.r = relocated[arena.live_identity(w.r).index()];
            tail[write] = w;
            write += 1;
        }
        tail.truncate(write);
        dropped
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
                if self.maintain_index
                    && let Some(slot) = self.positions.get_mut(&w.r.byte_offset())
                {
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
        if let Some(tail) = self.spill.get_mut(i).and_then(|s| s.as_mut()) {
            let mut write = 0usize;
            for read in 0..tail.len() {
                let w = tail[read];
                if refs.contains(&w.r.byte_offset()) {
                    if self.maintain_index
                        && let Some(slot) = self.positions.get_mut(&w.r.byte_offset())
                    {
                        slot.retain(|c| *c != i as u32);
                        if slot.is_empty() {
                            self.positions.remove(&w.r.byte_offset());
                        }
                    }
                    continue;
                }
                tail[write] = w;
                write += 1;
            }
            tail.truncate(write);
            if tail.is_empty() {
                self.spill[i] = None;
            }
        }
    }

    /// Sortedness datum (slice-5 economics).
    pub(crate) fn span_sortedness(&self) -> (usize, usize) {
        let mut sorted = 0usize;
        let mut total = 0usize;
        for code in 0..self.num_lits() {
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

    /// Live length of `code`'s span (diagnostics).
    pub(crate) fn span_len(&self, code: usize) -> usize {
        let start = self.span_start.get(code).copied().unwrap_or(0) as usize;
        let end = self.prim_end.get(code).copied().unwrap_or(0) as usize;
        end.saturating_sub(start)
    }

    /// Spill-tail length of `code` (diagnostics).
    pub(crate) fn overflow_len(&self, code: usize) -> usize {
        self.spill_slot_len(code)
    }

    /// Spill census (diagnostics: literals spilled / total spill entries).
    #[allow(dead_code)] // diagnostics
    pub(crate) fn spill_census(&self) -> (usize, usize) {
        (
            self.spill.iter().flatten().count(),
            self.spill.iter().flatten().map(|v| v.len()).sum(),
        )
    }

    /// Diagnostics: total live entries / index size.
    pub(crate) fn debug_total_entries(&self) -> usize {
        let n = self.num_lits();
        let in_layout: usize = (0..n)
            .map(|code| {
                let lit = Lit::from_code(code as u32);
                let (prim, extra) = self.spans(lit);
                prim.len() + extra.len()
            })
            .sum();
        in_layout + self.spill_slot_total(n)
    }

    /// Total spill entries at codes >= from.
    fn spill_slot_total(&self, from: usize) -> usize {
        self.spill[from.min(self.spill.len())..]
            .iter()
            .flatten()
            .map(|v| v.len())
            .sum()
    }

    pub(crate) fn debug_index_refs(&self) -> usize {
        self.positions.len()
    }

    /// Index-consistency audit (diagnostics).
    pub(crate) fn csr_index_audit(&self) -> (usize, usize, usize) {
        let mut actual: std::collections::BTreeMap<usize, smallvec::SmallVec<[u32; 2]>> =
            std::collections::BTreeMap::new();
        let n = self.num_lits();
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

    /// Index upkeep for a swapped-scan removal.
    pub(crate) fn index_remove(&mut self, code: usize, r: ClauseRef) {
        if !self.maintain_index {
            return;
        }
        if let Some(slot) = self.positions.get_mut(&r.byte_offset()) {
            slot.retain(|c| *c != code as u32);
            if slot.is_empty() {
                self.positions.remove(&r.byte_offset());
            }
        }
    }

    /// Mirror `WatchLists::clear`.
    pub(crate) fn clear_all(&mut self) {
        self.entries.clear();
        self.span_start.clear();
        self.prim_end.clear();
        self.spill.clear();
        self.arrivals.clear();
        self.scan = CsrScanFrame::default();
        self.positions.clear();
    }
}

/// In-place scan support for the slack-CSR: the entries buffer split
/// around the scanned literal's live span.  The cursor scans the span
/// (a clean `&mut [Watcher]`, returned separately so it and the context
/// borrow disjointly); pushes append into `head` or `tail` at the
/// destination literal's live end — region-disjoint from the scan by
/// construction (each literal's allocation is disjoint from every
/// other's), which the split makes borrow-checkable with no unsafe
/// code.
pub(crate) struct ScanCtx<'a> {
    /// Entries strictly before the scanned span (absolute-indexed).
    pub(crate) head: &'a mut [Watcher],
    /// Entries from the scanned span's end on (index 0 == absolute
    /// `scan_end`).
    pub(crate) tail: &'a mut [Watcher],
    /// Absolute index of the span's first entry.
    pub(crate) span_off: usize,
    /// The pre-scan live end (absolute); mid-scan self-pushes land beyond
    /// it and the commit discards them.
    pub(crate) scan_end: usize,
    /// Allocation starts (reads; the sentinel closes the array).
    span_start: &'a [u32],
    /// Live ends (a push bumps its destination's).
    prim_end: &'a mut [u32],
    /// Sticky-spill tails.
    #[allow(clippy::box_collection)] // see CsrWatchLists::spill
    spill: &'a mut Vec<Option<Box<Vec<Watcher>>>>,
    /// The position index (surgery machinery; `maintain_index` gates).
    positions: &'a mut std::collections::BTreeMap<usize, smallvec::SmallVec<[u32; 2]>>,
    /// The scanned literal's code.
    code: usize,
    maintain_index: bool,
}

impl CsrWatchLists {
    /// Split the entries buffer around `code`'s live span for an
    /// in-place scan: the cursor's buffer plus the push context.
    /// Pre-layout (no materialization yet) the split is degenerate —
    /// empty span, pushes land in the spill tails — so the caller never
    /// special-cases.
    #[inline]
    pub(crate) fn scan_split(&mut self, code: usize) -> (&mut [Watcher], ScanCtx<'_>) {
        let start = self.span_start.get(code).copied().unwrap_or(0) as usize;
        // A MISSING `prim_end` entry means the code has no live primary
        // span (the pre-layout contract: pushes land in the spill tails)
        // — its degenerate span is EMPTY, i.e. `start` itself.  Defaulting
        // to 0 independently of `start` made a code present in
        // `span_start` but absent from `prim_end` (the two tables resize
        // at different times) compute `end - start` UNDERFLOW — a hard
        // panic on the standing pete_5s fixture, release included (the
        // wrapped length then trips `split_at_mut`).  Found the day the
        // CSR flip landed; this is the documented-degenerate repair, with
        // the both-present invariant (`span_start <= prim_end <= cap`)
        // now asserted loudly rather than wrapped.
        let end = self.prim_end.get(code).copied().unwrap_or(start as u32) as usize;
        debug_assert!(
            end >= start,
            "csr scan_split: prim_end {end} < span_start {start} for code {code} \
             (both entries present — a layout invariant violation, not the \
             missing-entry degenerate case)"
        );
        let maintain = self.maintain_index;
        let CsrWatchLists {
            entries,
            span_start,
            prim_end,
            spill,
            positions,
            ..
        } = self;
        let (head, rest) = entries.split_at_mut(start);
        let (span, tail) = rest.split_at_mut(end - start);
        (
            span,
            ScanCtx {
                head,
                tail,
                span_off: start,
                scan_end: end,
                span_start,
                prim_end,
                spill,
                positions,
                code,
                maintain_index: maintain,
            },
        )
    }

    /// Detach `code`'s spill tail for a second scan pass (arrival order
    /// after the span — the same visit sequence the span+overflow form
    /// maintained).
    #[allow(clippy::box_collection)]
    pub(crate) fn take_fallback(&mut self, code: usize) -> Option<Box<Vec<Watcher>>> {
        self.spill.get_mut(code).and_then(|s| s.take())
    }
}

impl ScanCtx<'_> {
    /// Absolute allocation start of `key`'s span.
    fn start_of(&self, key: usize) -> usize {
        self.span_start.get(key).copied().unwrap_or(0) as usize
    }

    /// Absolute live end of `key`'s span.
    fn end_of(&self, key: usize) -> usize {
        self.prim_end.get(key).copied().unwrap_or(0) as usize
    }

    /// Cap of `key`'s allocation.
    fn cap_of(&self, key: usize) -> usize {
        self.span_start.get(key + 1).copied().unwrap_or(0) as usize
    }

    /// Read `entries[abs]` through the head/tail split (the caller
    /// guarantees `abs` is outside the scanned span).
    fn read_abs(&self, abs: usize) -> Option<Watcher> {
        if abs < self.span_off {
            self.head.get(abs).copied()
        } else {
            self.tail.get(abs - self.scan_end).copied()
        }
    }

    /// Write `entries[abs]` through the head/tail split.
    fn write_abs(&mut self, abs: usize, w: Watcher) {
        if abs < self.span_off {
            if let Some(slot) = self.head.get_mut(abs) {
                *slot = w;
            }
        } else if let Some(slot) = self.tail.get_mut(abs - self.scan_end) {
            *slot = w;
        }
    }

    /// Whether `key`'s live list already holds an entry with ref `r`
    /// (the dedup read; the scanned literal sees only its self-pushes).
    #[inline]
    pub(crate) fn contains_ref(&self, scanned_code: usize, key: Lit, r: ClauseRef) -> bool {
        let k = key.index();
        let (s, e) = if k == scanned_code {
            (self.scan_end, self.end_of(k))
        } else {
            (self.start_of(k), self.end_of(k))
        };
        for abs in s..e {
            if let Some(w) = self.read_abs(abs)
                && w.r == r
            {
                return true;
            }
        }
        if let Some(tail) = self.spill.get(k).and_then(|s| s.as_ref()) {
            return tail.iter().any(|w| w.r == r);
        }
        false
    }

    /// Append `w` to `key`'s list in arrival order (slack append while
    /// room remains and the literal has not spilled; the sticky spill
    /// tail once it has).
    #[inline(always)]
    pub(crate) fn push_entry(&mut self, key: Lit, w: Watcher) {
        let k = key.index();
        // Hot path (the whole reason this is inline): no spill slot and
        // slack available — one bounds test, one write, one bump.  The
        // out-of-line form (a call per watch move, ~1.4% of the run)
        // measured before this split.
        let live = self.prim_end.get(k).copied().unwrap_or(0) as usize;
        let cap = self.cap_of(k);
        let no_spill = self.spill.get(k).is_none_or(|s| s.is_none());
        if no_spill && !self.maintain_index && k < self.prim_end.len() && live < cap {
            self.write_abs(live, w);
            self.prim_end[k] = (live + 1) as u32;
            return;
        }
        self.push_entry_cold(key, w);
    }

    /// The spilled / layout-miss / spill-creation paths — cold by
    /// construction (a literal reaches here only after its slack filled).
    #[cold]
    #[inline(never)]
    fn push_entry_cold(&mut self, key: Lit, w: Watcher) {
        let k = key.index();
        if let Some(tail) = self.spill.get_mut(k).and_then(|s| s.as_mut()) {
            tail.push(w);
            self.index_note(k, w);
            return;
        }
        let live = self.end_of(k);
        let cap = self.cap_of(k);
        if k < self.prim_end.len() && live < cap {
            self.write_abs(live, w);
            self.prim_end[k] = (live + 1) as u32;
        } else {
            if k >= self.spill.len() {
                self.spill.resize(k + 1, None);
            }
            let slot = self.spill[k].get_or_insert_with(Box::default);
            slot.push(w);
        }
        self.index_note(k, w);
    }

    /// Position-index note for an append under `k` (surgery machinery).
    fn index_note(&mut self, k: usize, w: Watcher) {
        if self.maintain_index {
            let slot = self.positions.entry(w.r.byte_offset()).or_default();
            if !slot.contains(&(k as u32)) {
                slot.push(k as u32);
            }
        }
    }

    /// Position-index upkeep for a scan removal (the entry with ref `r`
    /// left the scanned literal).
    pub(crate) fn on_remove(&mut self, code: usize, r: ClauseRef) {
        if !self.maintain_index {
            return;
        }
        if let Some(slot) = self.positions.get_mut(&r.byte_offset()) {
            slot.retain(|c| *c != code as u32);
            if slot.is_empty() {
                self.positions.remove(&r.byte_offset());
            }
        }
    }

    /// Commit the in-place scan: the cursor compacted `kept` live entries
    /// at the span start; everything beyond (removals, holes, mid-scan
    /// self-pushes) dies.
    pub(crate) fn commit(&mut self, kept: usize) {
        if let Some(end) = self.prim_end.get_mut(self.code) {
            *end = (self.span_off + kept) as u32;
        }
    }

    /// Return a scanned spill tail (truncated — or untruncated on the
    /// conflict path — by its owning pass).
    #[allow(clippy::box_collection)]
    pub(crate) fn put_fallback(&mut self, tail: Box<Vec<Watcher>>) {
        if !tail.is_empty() {
            if self.code >= self.spill.len() {
                self.spill.resize(self.code + 1, None);
            }
            self.spill[self.code] = Some(tail);
        }
    }
}

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

/// The disjoint mutable parts the propagation session needs: destination
/// lists, phantom ticks, ghost debt, and the CSR (commit-B: the sole
/// watch representation).
pub(crate) type PropagationParts<'a> = (
    &'a mut [Vec<Watcher>],
    &'a [u32],
    &'a mut [u32],
    &'a mut Option<CsrWatchLists>,
);

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
            // The flip: the Vec side is dead in CSR-primary mode — its
            // 2·num_vars headers (~450 MB on the 9.4M-var class) are not
            // allocated at all.
            watches: if csr_b_enabled() {
                Vec::new()
            } else {
                vec![Vec::new(); num_vars * 2]
            },
            bin_phantom: vec![0; num_vars * 2],
            ghost_debt: vec![0; num_vars * 2],
            // The CSR shadow is a diagnostic/experimental mirror, documented
            // "Default off; the flag-off path is byte-identical" — but it was
            // attached unconditionally, so every `add` paid `push_overflow`
            // (a `positions` HashMap write per watcher!) and every scan paid
            // `scan_remove` mirroring.  Measured on SCPC-500-13 (seed study,
            // 2026-09-16): 65 % of runtime in mirror maintenance at
            // bit-identical conflict counts — a 3-6x wall inflation on
            // watch-dense instances with zero semantic effect.  Attach only
            // when one of the CSR knobs actually asks for it.
            csr: if csr_shadow_enabled()
                || csr_scan_enabled()
                || csr_read_enabled()
                || csr_b_enabled()
            {
                Some(CsrWatchLists {
                    maintain_index: csr_shadow_enabled()
                        || csr_index_enabled()
                        || crate::solver::equiv::equiv_surgery_enabled(),
                    ..CsrWatchLists::default()
                })
            } else {
                None
            },
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

    /// Whether any literal's overflow holds entries (the deferred-load
    /// materialization's safety guard: an empty-overflow CSR can be
    /// replaced wholesale by the counting-sort build; anything else needs
    /// the full rebuild).
    pub(crate) fn csr_has_overflow_content(&self) -> bool {
        self.csr
            .as_ref()
            .is_some_and(|c| c.spill.iter().any(|s| s.is_some()))
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
        let n = csr.num_lits();
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
    pub(crate) fn shadow_begin_scan(&mut self, lit: Lit, scanned_len: usize) {
        if self.csr.is_some() {
            // The scan target's length is the CALLER's scratch — in flip-A
            // the CSR materialized into it, in commit-B the Vec side is dead
            // and the CSR's own view is what the caller scanned.  Reading
            // `self.get(lit)` here compares against the dead Vec (0) and
            // wrongly suspends the mirror.
            if let Some(csr) = &mut self.csr {
                csr.begin_scan(lit.index(), scanned_len);
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
        crate::mut_trace!(
            lit.index(),
            "side=vec act=push ref={} blk={} path=add",
            watcher.r.byte_offset(),
            watcher.blocker.code()
        );
        // Commit-B mode: the CSR overflow is the only representation — the
        // Vec side is dead weight (its lists must stay empty so any read
        // surfaces as a bug, not a silent divergence).
        if !csr_b_enabled() {
            self.push_only(lit, watcher);
        }
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

    /// The CSR combined view (`NIXIE_CSR_READ=1`): primary span then
    /// overflow — the reader-side API for the flip.  Empty pair when no
    /// shadow exists (readers fall back to identical content).
    #[must_use]
    pub fn get_combined(&self, lit: Lit) -> (&[Watcher], &[Watcher]) {
        self.csr.as_ref().map_or((&[], &[]), |c| c.spans(lit))
    }

    /// Dump the CSR's combined view per literal (the commit-B divergence
    /// tool: run under flip-A — whose CSR provably equals its scanned Vec —
    /// and under the roundtrip build, diff at the phase boundary).  One
    /// line per nonempty literal: `code: ref:blocker ref:blocker ...`.
    #[cfg(feature = "std")]
    pub(crate) fn dump_watches(&self, num_vars: usize, path: &str) {
        use std::fmt::Write as _;
        let mut out = String::new();
        let mut total = 0usize;
        for code in 0..num_vars * 2 {
            let lit = Lit::from_code(code as u32);
            let (p, x) = self.get_combined(lit);
            if p.is_empty() && x.is_empty() {
                continue;
            }
            total += p.len() + x.len();
            let _ = write!(out, "{code}:");
            for w in p.iter().chain(x.iter()) {
                let _ = write!(out, " {}:{}", w.r.byte_offset(), w.blocker.code());
            }
            let _ = writeln!(out);
        }
        let _ = std::fs::write(path, out);
        eprintln!("[watch-dump] {path}: {total} entries");
    }

    /// Test scaffolding: overwrite the last entry's blocker in BOTH
    /// representations (tests position blockers directly; post-flip the
    /// CSR is authoritative and a `get_mut`-only write would desync it).
    /// Post-rebuild dump (the Vec lists after the fill).
    #[cfg(feature = "std")]
    pub(crate) fn dump_watches_post(&self, num_vars: usize, path: &str) {
        use std::fmt::Write as _;
        let mut out = String::new();
        let mut total = 0usize;
        for code in 0..num_vars * 2 {
            let lit = Lit::from_code(code as u32);
            let list = self.get(lit);
            if list.is_empty() {
                continue;
            }
            total += list.len();
            let _ = write!(out, "{code}:");
            for w in list {
                let _ = write!(out, " {}:{}", w.r.byte_offset(), w.blocker.code());
            }
            let _ = writeln!(out);
        }
        let _ = std::fs::write(path, out);
        eprintln!("[watch-dump-post] {path}: {total} entries");
    }
    #[cfg(test)]
    pub(crate) fn set_last_blocker(&mut self, lit: Lit, blocker: Lit) {
        if let Some(w) = self
            .watches
            .get_mut(lit.index())
            .and_then(|list| list.last_mut())
        {
            w.blocker = blocker;
        }
        if let Some(c) = self.csr.as_mut() {
            let (p, x) = c.spans(lit);
            let _ = p;
            let code = lit.index();
            let idx = if x.is_empty() {
                let end = c.prim_end.get(code).copied().unwrap_or(0) as usize;
                end.checked_sub(1).map(|e| (e, true))
            } else {
                x.len().checked_sub(1).map(|e| (e, false))
            };
            if let Some((idx, in_primary)) = idx {
                if in_primary {
                    let start = c.span_start.get(code).copied().unwrap_or(0) as usize;
                    if let Some(w) = c.entries.get_mut(start + idx) {
                        w.blocker = blocker;
                    }
                } else if let Some(w) = c
                    .spill
                    .get_mut(code)
                    .and_then(|s| s.as_mut())
                    .and_then(|v| v.get_mut(idx))
                {
                    w.blocker = blocker;
                }
            }
        }
    }

    /// Test scaffolding: overwrite every entry's blocker in BOTH
    /// representations (see [`Self::set_last_blocker`]).
    #[cfg(test)]
    pub(crate) fn set_all_blockers(&mut self, lit: Lit, blocker: Lit) {
        if let Some(list) = self.watches.get_mut(lit.index()) {
            for w in list.iter_mut() {
                w.blocker = blocker;
            }
        }
        if let Some(c) = self.csr.as_mut() {
            let code = lit.index();
            let start = c.span_start.get(code).copied().unwrap_or(0) as usize;
            let end = c.prim_end.get(code).copied().unwrap_or(0) as usize;
            for w in &mut c.entries[start..end] {
                w.blocker = blocker;
            }
            if let Some(v) = c.spill.get_mut(code).and_then(|s| s.as_mut()) {
                for w in v.iter_mut() {
                    w.blocker = blocker;
                }
            }
        }
    }

    /// Materialize `lit`'s combined view into an owned `Vec` (the
    /// non-session scan path's flip-A form: the `Vec` list becomes a
    /// per-scan scratch buffer copied from the CSR — the authoritative
    /// state — with the frame mirror maintaining the CSR through the scan
    /// exactly as before).
    pub(crate) fn take_combined_vec(&mut self, lit: Lit) -> Vec<Watcher> {
        match self.csr.as_ref() {
            Some(c) => {
                let (p, x) = c.spans(lit);
                let mut v = Vec::with_capacity(p.len() + x.len());
                v.extend_from_slice(p);
                v.extend_from_slice(x);
                v
            }
            None => core::mem::take(self.get_mut(lit)),
        }
    }

    /// Whether CSR reads are live (the flag AND an adopted shadow —
    /// before the first rebuild there is no CSR to read).
    #[must_use]
    pub fn csr_read_active(&self) -> bool {
        self.csr.is_some()
    }

    /// Combined iteration with NO env gate: the CSR's view whenever a CSR
    /// is attached, the `Vec` list otherwise.  For structural audits that
    /// must see the authoritative representation in every mode.
    pub(crate) fn iter_combined_always(&self, lit: Lit) -> Box<dyn Iterator<Item = &Watcher> + '_> {
        if let Some(c) = self.csr.as_ref() {
            let (p, x) = c.spans(lit);
            return Box::new(p.iter().chain(x.iter()));
        }
        Box::new(self.get(lit).iter())
    }

    /// Flag-aware combined iteration for reader sites: the CSR view under
    /// `NIXIE_CSR_READ=1`, the `Vec` list otherwise (identical content by
    /// the drift invariant).
    pub fn iter_combined(&self, lit: Lit) -> Box<dyn Iterator<Item = &Watcher> + '_> {
        #[cfg(feature = "std")]
        if (crate::watched::csr_read_enabled() || crate::watched::csr_b_enabled())
            && let Some(c) = self.csr.as_ref()
        {
            let (p, x) = c.spans(lit);
            return Box::new(p.iter().chain(x.iter()));
        }
        Box::new(self.get(lit).iter())
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
            crate::mut_trace!(
                idx,
                "side=vec act=drop ref={} path=remove_clause",
                r.byte_offset()
            );
        }
        if let Some(csr) = &mut self.csr {
            csr.remove_clause(lit, r);
        }
    }

    /// Resize to support more variables
    pub fn resize(&mut self, num_vars: usize) {
        let new_size = num_vars * 2;
        if !csr_b_enabled() && new_size > self.watches.len() {
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
            csr: self.csr.as_ref().map(PackedCsrSnapshot::from),
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
        self.csr = csr.as_ref().map(CsrWatchLists::from);
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
                    crate::mut_trace!(
                        idx,
                        "side=vec act=drop ref={} path=relocate_dead",
                        w.r.byte_offset()
                    );
                    continue;
                }
                let new_r = plan.relocated()[arena.live_identity(w.r).index()];
                if new_r != w.r {
                    crate::mut_trace!(
                        idx,
                        "side=vec act=rewrite ref={} new={} path=relocate",
                        w.r.byte_offset(),
                        new_r.byte_offset()
                    );
                }
                w.r = new_r;
                list[write] = w;
                write += 1;
            }
            list.truncate(write);
            if dropped != 0 {
                self.ghost_debt[idx] = self.ghost_debt[idx].saturating_add(dropped);
            }
        }
        if csr_b_enabled() {
            // Commit-B: the Vec side is dead — the CSR charges the debt.
            let WatchLists {
                csr, ghost_debt, ..
            } = self;
            if let Some(c) = csr.as_mut() {
                c.relocate_with_debt(arena, plan, ghost_debt);
            }
        } else if let Some(csr) = &mut self.csr {
            csr.relocate(arena, plan);
        }
    }

    pub(crate) fn check_ref_consistency(
        &self,
        refs: &[ClauseRef],
        arena: &ClauseArena,
    ) -> Result<(), String> {
        // Combined-view iteration: the CSR's entries when one is attached
        // (commit-B: the only representation), the Vec lists otherwise —
        // identical content by the drift invariant.
        for lit_idx in 0..self
            .watches
            .len()
            .max(self.csr.as_ref().map_or(0, |c| c.num_lits()))
        {
            let lit = Lit::from_code(lit_idx as u32);
            for w in self.iter_combined_always(lit) {
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
        crate::watched::pin_legacy_watch_world();
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
#[allow(dead_code)] // retained as a bisection knob (SHADOW alone now arms the swapped scan)
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

/// `NIXIE_CSR_READ=1` (slice 4's reader gate; requires the shadow):
/// production readers iterate the CSR's combined view instead of the
/// `Vec` lists.  Content-identical by the drift invariant — the gate
/// proves the reader-side API, the last pre-flip surface.
pub fn csr_read_enabled() -> bool {
    #[cfg(feature = "std")]
    {
        use std::sync::OnceLock;
        static FLAG: OnceLock<bool> = OnceLock::new();
        *FLAG.get_or_init(|| {
            std::env::var("NIXIE_CSR_READ")
                .is_ok_and(|v| v == "1" || v.eq_ignore_ascii_case("true"))
        })
    }
    #[cfg(not(feature = "std"))]
    {
        false
    }
}

/// `NIXIE_CSR_CHARGE_TRACE=1`: log every session tick charge (the
/// commit-B divergence probe — see the CSR study's commit-B sections).
pub fn csr_charge_trace_enabled() -> bool {
    #[cfg(feature = "std")]
    {
        use std::sync::OnceLock;
        static FLAG: OnceLock<bool> = OnceLock::new();
        *FLAG.get_or_init(|| std::env::var("NIXIE_CSR_CHARGE_TRACE").is_ok())
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

/// Whether the CSR position index is maintained (`NIXIE_CSR_INDEX=1`):
/// surgery/diagnostic machinery — a BTreeMap write per watcher-add
/// measured +24% whole-run instructions when left on unconditionally.
pub fn csr_index_enabled() -> bool {
    #[cfg(feature = "std")]
    {
        use std::sync::OnceLock;
        static FLAG: OnceLock<bool> = OnceLock::new();
        *FLAG.get_or_init(|| {
            std::env::var("NIXIE_CSR_INDEX")
                .is_ok_and(|v| v == "1" || v.eq_ignore_ascii_case("true"))
        })
    }
    #[cfg(not(feature = "std"))]
    {
        false
    }
}

/// Whether commit-B mode is active (`NIXIE_CSR_B=1`): the CSR is the
/// ONLY live watch representation — the session kernel scans it as
/// primary (span-copy + overflow-take roundtrip), pushes and dedups go
/// straight to the CSR, and the `Vec<Vec<Watcher>>` side is dead (its
/// lists stay empty; any read of them in this mode is a bug to flush
/// out).  The divergence-hunt vehicle for the CSR-watches flip: A and B
/// are the same binary, differing only in this env.
pub fn csr_b_enabled() -> bool {
    #[cfg(feature = "std")]
    {
        use std::sync::OnceLock;
        static FLAG: OnceLock<bool> = OnceLock::new();
        // The flip REVERTED (2026-09-20, the corpus ledger): the slack-CSR
        // as the DEFAULT measured geomean +16% instructions over the
        // standing corpus (search-heavy cells +15-32%; the load-heavy
        // spot instances that motivated it were its best case at +3-6%)
        // with a wash on memory and the surgery payback measured
        // negative — a net cost with no compensating win.  The machinery
        // stays landed at zero default cost; `NIXIE_CSR_B=1` opts into
        // the CSR-primary world (all its driver optimizations intact).
        *FLAG.get_or_init(|| {
            std::env::var("NIXIE_CSR_B").is_ok_and(|v| v == "1" || v.eq_ignore_ascii_case("true"))
        })
    }
    #[cfg(not(feature = "std"))]
    {
        false
    }
}

#[cfg(test)]
pub(crate) fn pin_legacy_watch_world() {
    // The legacy `Vec<Vec<Watcher>>` world this test asserts against is
    // now the `NIXIE_CSR_B=0` opt-out (the slack-CSR is the default).
    // nextest isolates each test in its own process, so setting the env
    // here pins the world before the first `csr_b_enabled()` read —
    // single-threaded test main, nothing observes the race window.
    #[allow(unsafe_code)]
    unsafe {
        std::env::set_var("NIXIE_CSR_B", "0");
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
        crate::watched::pin_legacy_watch_world();
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
        // The slack-CSR appends into the span's slack — the combined view
        // is [primary survivors][arrivals] exactly as the span+overflow
        // form maintained; the spill tail stays empty until slack runs out.
        let m = Watcher::new(ClauseId::new(9), ClauseRef::NULL, Lit::pos(v(5)));
        csr.push_overflow(Lit::pos(v(0)), m);
        let (prim, extra) = csr.spans(Lit::pos(v(0)));
        assert_eq!(prim.len(), 4);
        assert_eq!(prim[3], m);
        assert_eq!(extra, &[] as &[Watcher]);

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
        // Shrink the live span to its first entry (the slack-CSR's scan
        // commit shape): the appended entry dies with the commit — the
        // same take-semantics the scan guarantees.
        let code = Lit::neg(v(1)).index();
        let start = csr2.span_start[code] as usize;
        csr2.prim_end[code] = (start + 1) as u32;
        let (p2, e2) = csr2.spans(Lit::neg(v(1)));
        assert_eq!(p2, &[a]);
        assert_eq!(e2, &[] as &[Watcher]);
        assert_eq!(csr2.len(Lit::neg(v(1))), 1);
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
        crate::watched::pin_legacy_watch_world();
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
        wl.shadow_begin_scan(l1, 1);
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

#[cfg(test)]
mod slack_debug_tests {
    use super::*;

    #[test]
    fn pre_layout_pushes_land_in_fallback_and_len_counts_them() {
        let w =
            |r: usize| Watcher::new(ClauseId::new(r as u32), ClauseRef::NULL, Lit::from_code(7));
        let mut c = CsrWatchLists::default();
        let lit = Lit::from_code(30);
        c.push_overflow(lit, w(1));
        c.push_overflow(lit, w(2));
        c.push_overflow(lit, w(3));
        assert_eq!(c.len(lit), 3, "len must count pre-layout fallbacks");
        let (p, x) = c.spans(lit);
        assert_eq!((p.len(), x.len()), (0, 3));
    }
}
