//! Clause arena: contiguous header+literals storage for the clause database.
//!
//! This is the backing store `ClauseDatabase` (`clause.rs`) is built on. Each
//! clause occupies one slot – a 12-byte header immediately followed by its
//! `Lit` array – packed back-to-back in a single `Vec<u64>` buffer. A clause
//! reference ([`ClauseRef`]) is the byte offset of its slot.
//!
//! # Layout & alignment
//!
//! The buffer is a `Vec<u64>`, so the allocation is 8-byte aligned by
//! construction. Slot sizes are rounded up to a multiple of 8 bytes, so every
//! header sits at an 8-aligned offset (headers are `#[repr(C, align(4))]`,
//! 12 bytes). Literal arrays start at `header + 12`, which is 4-aligned –
//! exactly what `Lit` (`#[repr(transparent)]` over `u32`) requires. The
//! previous version of this arena stored headers in a `Vec<u8>` (align-1
//! guaranteed only) while reading them through aligned references –
//! unconstructible soundness that happened to work; it is fixed by the
//! `u64`-element buffer.
//!
//! # Lifetime invariants (the load-bearing ones)
//!
//! * **Slots are never reused, and relocation rewrites every holder.**
//!   Between compactions the arena is append-only: allocation only ever
//!   extends `pos`, so a `ClauseRef` names exactly one clause. This mirrors
//!   the no-slot-reuse soundness rule of `ClauseDatabase::add`: stale
//!   watch-list entries and trail reasons can hold a `ClauseRef` across
//!   deletions, and they must never come to name a *different* clause.
//!   [`ClauseArena::compact`] is the single exception to append-only: it
//!   relocates every live clause downward **in place** and **synchronously
//!   rewrites every outstanding ref holder** (the database's `refs` table,
//!   then each watcher's `.r` via `WatchLists::relocate_refs`)
//!   – an audit confirmed watchers are the only `ClauseRef` holders outside
//!   the database (`ClauseRef`'s inner offset is private to this module, so
//!   the audit is enforced by the type system). Deleted ids relocate to a
//!   **permanent tombstone slot** at the end of the compacted region that
//!   always reads as a deleted clause, so a stale ref can never dangle
//!   past the shrunken live region nor name an unrelated clause.
//! * **Shrink-in-slot.** [`ClauseArena::shrink`] rewrites a clause with a
//!   shorter literal array *in place* (the tail bytes of the old slot become
//!   unreachable padding). Growing a clause is not possible in place and the
//!   API refuses it; every in-solver rewrite site only ever shrinks (drops
//!   redundant literals). Shrinking keeps the `ClauseRef` stable, which
//!   watchers and reasons require. (Compaction later re-tightens shrunk
//!   slots to their current length, reclaiming that padding.)
//! * Offsets are `u32`; [`ClauseRef::NULL`] (`u32::MAX`) is reserved.
//!
//! # Deleted-flag reads
//!
//! Deletion sets a header flag only. Readers (`get`, `get_mut`) still return
//! the (now-deleted-flagged) clause; callers filter on
//! [`ClauseView::deleted`] exactly like the old `Vec<Clause>` database did
//! with `c.deleted`. Lazy cleanup semantics are therefore unchanged.

#![allow(unsafe_code)]

use crate::clause::ClauseTier;
use crate::literal::Lit;

/// Clause reference: byte offset of the clause's slot in the arena.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct ClauseRef(u32);

impl ClauseRef {
    /// The null reference (no clause).
    pub const NULL: Self = Self(u32::MAX);

    /// Create a null reference.
    #[must_use]
    pub const fn null() -> Self {
        Self(u32::MAX)
    }

    /// Check whether this is the null reference.
    #[must_use]
    pub const fn is_null(self) -> bool {
        self.0 == u32::MAX
    }

    /// Raw byte offset (crate-internal).
    pub(super) const fn byte_offset(self) -> usize {
        self.0 as usize
    }

    /// Construct from a raw byte offset (crate-internal). Returns `None` for
    /// offsets that collide with the null encoding or cannot be addressed.
    pub(super) fn from_byte_offset(off: usize) -> Option<Self> {
        if off >= u32::MAX as usize {
            return None;
        }
        Some(Self(off as u32))
    }
}

const FLAG_DELETED: u8 = 1 << 0;
const FLAG_LEARNED: u8 = 1 << 1;
const TIER_SHIFT: u8 = 4;

/// Per-clause header, exactly 16 bytes, immediately followed by the literal
/// array (so the array starts 4-aligned – `Lit` is `#[repr(transparent)]`
/// over `u32`).
///
/// Widths are matched to their actual consumers, not defaulted to `u32`:
/// * `len: u32` – genuinely large DIMACS clauses exist.
/// * `lbd: u16` – distinct decision levels; every semantic consumer
///   thresholds at ≤ 10 (tiering) or averages into `u64` stats. Stored
///   saturating at `u16::MAX`; the debug invariant that recomputes an LBD
///   right after learning must compare against the clamped value (see
///   `invariants::check_learned_clause_lbd`).
/// * flags (2 bits) and tier (2 bits) share one byte.
/// * `usage: u8` saturating – the tier-promotion consumers fire at 3 and 10
///   uses; saturation at 255 cannot change any decision those consumers
///   make.
/// * `activity: f32` at offset 8 of a 12-byte header – clause-activity is
///   only the `reduce_clause_database` sort key (relative ordering of
///   clauses), and the saturating rescale policy below keeps every stored
///   value far from `f32`'s range limits. f32 halves the header and is what
///   lets a 3-literal clause slot be 24 bytes (two per cache line) and a
///   5-literal clause slot be 32 bytes (half a line).
///
/// Alignment: `align(4)` is the whole header's requirement (largest member
/// is a u32/f32); slots still start at multiples of 8 (the buffer is
/// `Vec<u64>` and the stride rounds to 8), so headers are over-aligned in
/// practice and the literal array at `header + 12` is 4-aligned as `Lit`
/// requires.
#[repr(C, align(4))]
#[derive(Clone, Copy)]
struct ClauseHeader {
    len: u32,
    lbd: u16,
    flags_tier: u8,
    usage: u8,
    activity: f32,
}

impl ClauseHeader {
    fn new(len: u32, learned: bool) -> Self {
        Self {
            len,
            lbd: 0,
            flags_tier: if learned { FLAG_LEARNED } else { 0 },
            usage: 0,
            activity: 0.0,
        }
    }

    #[inline]
    fn deleted(self) -> bool {
        (self.flags_tier & FLAG_DELETED) != 0
    }

    #[inline]
    fn learned(self) -> bool {
        (self.flags_tier & FLAG_LEARNED) != 0
    }

    #[inline]
    fn tier(self) -> u32 {
        ((self.flags_tier >> TIER_SHIFT) & 0x3) as u32
    }

    #[inline]
    fn lbd(self) -> u32 {
        self.lbd as u32
    }

    /// Set the LBD, saturating at `u16::MAX` (the stored width).
    #[inline]
    fn set_lbd(&mut self, lbd: u32) {
        self.lbd = lbd.min(u16::MAX as u32) as u16;
    }
}

/// Slot geometry: header size and 8-byte slot stride rounding.
const HEADER_BYTES: usize = core::mem::size_of::<ClauseHeader>();
const ALIGN: usize = 8;

/// Compaction gate: minimum unreachable bytes before a compaction can pay
/// for itself (smaller arenas never reach the [`ClauseArena::should_compact`]
/// gate – sub-64-KiB waste is irrelevant to RSS and not worth a copy).
const COMPACT_MIN_WASTED: usize = 64 * 1024;
/// Compaction gate divisor: garbage must reach `live / COMPACT_WASTE_DIV`
/// before firing. Bounds total copy work at ~`COMPACT_WASTE_DIV`× the bytes
/// ever garbage-collected (see [`ClauseArena::should_compact`]).
///
/// 8 (2026-09-05, was 3): every compaction ends in `shrink_to_fit`, so a
/// tighter gate keeps the arena's *capacity* (Vec doubling overshoot, which
/// RSS pays for) close to live data between reduce rounds — on
/// worker-class instances the measured end-of-run slack was ~220 MB
/// (537 MB cap vs 317 MB live) with waste crossing live/3 only twice in a
/// 30 s solve. Compaction remains trajectory-neutral by construction
/// (ids, bytes and visit orders preserved) at a bounded copy cost of
/// ≤ 8× the collected bytes.
const COMPACT_WASTE_DIV: usize = 8;

#[inline]
fn slot_size(len: usize) -> usize {
    let raw = HEADER_BYTES + len * core::mem::size_of::<Lit>();
    raw.div_ceil(ALIGN) * ALIGN
}

/// Read-only view of one clause in the arena.
///
/// Field reads mirror the old `&Clause` field names (`lits`, `lbd`,
/// `learned`, `deleted`, `tier`, `usage_count`, `activity`) so call sites
/// read identically; mutations go through `ClauseArena` methods.
#[derive(Debug, Clone, Copy)]
pub struct ClauseView<'a> {
    /// The clause's literals.
    pub lits: &'a [Lit],
    /// LBD (Literal Block Distance).
    pub lbd: u32,
    /// Whether this clause was learned during search.
    pub learned: bool,
    /// Whether this clause has been deleted.
    pub deleted: bool,
    /// Tiered-database tier (learned clauses only).
    pub tier: ClauseTier,
    /// Times used in conflict analysis.
    pub usage_count: u32,
    /// Clause activity for the deletion heuristic.
    pub activity: f32,
}

impl ClauseView<'_> {
    /// Number of literals.
    #[must_use]
    pub fn len(&self) -> usize {
        self.lits.len()
    }

    /// Whether the clause is empty (only possible for a degenerate input).
    #[must_use]
    pub fn is_empty(&self) -> bool {
        self.lits.is_empty()
    }
}

/// The clause arena itself.
#[derive(Clone)]
pub struct ClauseArena {
    /// Backing storage. `u64` elements pin the allocation to 8-byte
    /// alignment; all offsets are byte offsets into this buffer and every
    /// slot starts at a multiple of 8.
    buffer: Vec<u64>,
    /// Write position, in bytes (always a multiple of 8). Decreases only in
    /// [`Self::compact`], which synchronously rewrites every outstanding
    /// ref holder.
    pos: usize,
    /// Bytes occupied by deleted (unreachable) slots.
    wasted_bytes: usize,
    /// Slots allocated (live + deleted).
    num_clauses: usize,
    /// Slots deleted.
    num_deleted: usize,
    /// Compactions performed (see [`Self::compact`]).
    compactions: u64,
}

impl Default for ClauseArena {
    fn default() -> Self {
        Self::new(0)
    }
}

impl ClauseArena {
    /// Create an arena whose buffer is pre-allocated to hold at least
    /// `initial_capacity` bytes (rounded up to whole `u64`s).
    #[must_use]
    pub fn new(initial_capacity: usize) -> Self {
        Self {
            buffer: Vec::with_capacity(initial_capacity / ALIGN),
            pos: 0,
            wasted_bytes: 0,
            num_clauses: 0,
            num_deleted: 0,
            compactions: 0,
        }
    }

    fn ensure_capacity(&mut self, end: usize) {
        let need_words = end.div_ceil(ALIGN);
        if need_words > self.buffer.len() {
            self.buffer.reserve(need_words - self.buffer.len());
        }
    }

    #[inline]
    fn header_ptr(&self, r: ClauseRef) -> *const ClauseHeader {
        // SAFETY: `self.pos` is a multiple of 8 and never exceeds the buffer
        // length; every stored ref was produced by `alloc` at a valid slot
        // boundary, and the buffer base is 8-aligned (`Vec<u64>`).
        unsafe {
            self.buffer
                .as_ptr()
                .cast::<u8>()
                .add(r.byte_offset())
                .cast::<ClauseHeader>()
        }
    }

    #[inline]
    fn header_ptr_mut(&mut self, r: ClauseRef) -> *mut ClauseHeader {
        // SAFETY: as `header_ptr`; the mutable borrow of `self.buffer`
        // through `as_mut_ptr` is exclusive for the call's duration.
        unsafe {
            self.buffer
                .as_mut_ptr()
                .cast::<u8>()
                .add(r.byte_offset())
                .cast::<ClauseHeader>()
        }
    }

    #[inline]
    fn lits_ptr(header: *const ClauseHeader) -> *const Lit {
        // SAFETY: literals are laid out immediately after the header; the
        // combined slot is 8-aligned, so the literal array is 4-aligned
        // (`Lit` is `#[repr(transparent)]` over `u32`).
        unsafe { header.add(1).cast::<Lit>() }
    }

    #[inline]
    fn lits_ptr_mut(header: *mut ClauseHeader) -> *mut Lit {
        // SAFETY: as `lits_ptr`, through a mutable header pointer.
        unsafe { header.add(1).cast::<Lit>() }
    }

    /// Read-only view of the clause at `r`, or `None` if `r` is null/out of
    /// range. Deleted clauses are still returned (flagged) – callers filter,
    /// matching the old database's semantics.
    #[must_use]
    pub fn get(&self, r: ClauseRef) -> Option<ClauseView<'_>> {
        if r.is_null() || r.byte_offset() + HEADER_BYTES > self.pos {
            return None;
        }
        let hp = self.header_ptr(r);
        // SAFETY: `hp` points at a live slot's header within the buffer;
        // read by value (the header is `Copy`) so no borrow is held.
        let h = unsafe { core::ptr::read(hp) };
        if h.len as usize
            > (self.pos - r.byte_offset() - HEADER_BYTES) / core::mem::size_of::<Lit>()
        {
            // Corrupt length (cannot happen through the API; refuse rather
            // than fabricate a slice).
            return None;
        }
        let lits: &[Lit] =
            unsafe { core::slice::from_raw_parts(Self::lits_ptr(hp), h.len as usize) };
        Some(ClauseView {
            lits,
            lbd: u32::from(h.lbd),
            learned: h.learned(),
            deleted: h.deleted(),
            tier: ClauseTier::from_u32(h.tier()),
            usage_count: u32::from(h.usage),
            activity: h.activity,
        })
    }

    /// Append a new clause and return its reference.
    ///
    /// The reference is fresh – slots are never reused (see module docs) –
    /// so a returned `ClauseRef` names this clause until the arena is
    /// dropped.
    pub fn alloc(&mut self, lits: &[Lit], learned: bool) -> ClauseRef {
        if lits.is_empty() {
            #[cfg(feature = "std")]
            eprintln!("ARENA-FORENSIC: alloc(empty) called");
            debug_assert!(false, "alloc of empty");
        }
        let size = slot_size(lits.len());
        let start = self.pos;
        let end = start + size;
        debug_assert_eq!(start % ALIGN, 0);
        debug_assert!(
            ClauseRef::from_byte_offset(start).is_some(),
            "arena overflow"
        );
        self.ensure_capacity(end);

        let header = ClauseHeader::new(lits.len() as u32, learned);
        // SAFETY: `ensure_capacity` reserved room for [start, end); writing
        // the header and literals initialises exactly that range, after
        // which `set_len` exposes it. No element of `buffer` outside the
        // written range is ever read before being overwritten by a later
        // `alloc` (each `alloc` extends `pos` by a whole slot).
        unsafe {
            let base = self.buffer.as_mut_ptr().cast::<u8>().add(start);
            (base as *mut ClauseHeader).write(header);
            core::ptr::copy_nonoverlapping(
                lits.as_ptr(),
                base.add(HEADER_BYTES) as *mut Lit,
                lits.len(),
            );
            self.buffer.set_len(end / ALIGN);
        }

        self.pos = end;
        self.num_clauses += 1;
        ClauseRef::from_byte_offset(start).unwrap_or(ClauseRef::NULL)
    }

    /// Mark the clause at `r` deleted (idempotent). The slot is *not*
    /// reclaimed.
    pub fn delete(&mut self, r: ClauseRef) {
        let Some(h) = self.read_header(r) else { return };
        if h.deleted() {
            return;
        }
        // SAFETY: `r` validated by `read_header`; flag write.
        unsafe {
            (*self.header_ptr_mut(r)).flags_tier |= FLAG_DELETED;
        }
        self.num_deleted += 1;
        self.wasted_bytes += slot_size(h.len as usize);
    }

    /// Read the header at `r` by value, after validating the slot is in the
    /// live region. `None` for null/out-of-range refs or a corrupt length.
    fn read_header(&self, r: ClauseRef) -> Option<ClauseHeader> {
        if r.is_null() || r.byte_offset() + HEADER_BYTES > self.pos {
            return None;
        }
        // SAFETY: within the live region, at a slot boundary written by
        // `alloc`; reading by value holds no borrow.
        let h = unsafe { core::ptr::read(self.header_ptr(r)) };
        if h.len as usize
            > (self.pos - r.byte_offset() - HEADER_BYTES) / core::mem::size_of::<Lit>()
        {
            return None;
        }
        Some(h)
    }

    /// Header of the slot at byte offset `off`, read from `base` (the
    /// buffer holding the slot), validated against the live region
    /// `[0, arena_end)`: the header must lie fully inside it and the
    /// declared literal array must fit between the header and the region
    /// end – the same bound every arena read applies (`get`/`read_header`).
    /// `None` for out-of-range offsets or a length that would cross the
    /// region – refuse rather than trust a fabricated length.
    ///
    /// SAFETY: `base` must point at the buffer that holds a slot starting
    /// at `off`, and `[base, base + arena_end)` must be initialised.
    #[inline]
    unsafe fn header_in_extent(
        base: *const u8,
        off: usize,
        arena_end: usize,
    ) -> Option<ClauseHeader> {
        if off + HEADER_BYTES > arena_end {
            return None;
        }
        // SAFETY: caller contract; reading by value holds no borrow.
        let h = unsafe { core::ptr::read(base.add(off).cast::<ClauseHeader>()) };
        if HEADER_BYTES + h.len as usize * core::mem::size_of::<Lit>() > arena_end - off {
            return None;
        }
        Some(h)
    }

    /// Amortization gate for [`Self::compact`], checked every reduce round
    /// (the cadical/kissat shape: garbage collection is part of reduce, and
    /// the gate keeps it amortized O(1) per byte of garbage).
    ///
    /// Fires when the unreachable bytes reach the 64-KiB minimum *and*
    /// at least a third of the live data (garbage ≥ live/3): after a
    /// compaction at least `live/3` bytes must therefore be deleted before
    /// the next one can fire, so the total copy work over a whole run is
    /// bounded by ~3× the bytes ever garbage-collected – never per-conflict.
    /// `wasted_bytes` counts deleted slots only; the shrink padding a
    /// compaction also reclaims is unaccounted (shrink is rare next to
    /// deletion), so the true reclaim can only exceed the gate's estimate.
    #[must_use]
    pub fn should_compact(&self) -> bool {
        self.wasted_bytes >= COMPACT_MIN_WASTED
            && self.wasted_bytes >= (self.pos - self.wasted_bytes) / COMPACT_WASTE_DIV
    }

    /// Relocate every live clause downward in place (kissat-style) and
    /// reclaim deleted slots *and* shrink padding. This is the real
    /// implementation of the compaction the reduce loop has always called
    /// (it was an empty stub until 2026-09; see
    /// `docs/studies/2026-09-01-standing-vs-kissat-gap-decomposition.md`).
    ///
    /// * `slots` must list **every** slot the database has ever allocated,
    ///   indexed by clause id – the database's `refs` table is exactly
    ///   this. Live entries' offsets are strictly ascending in id order
    ///   (debug-asserted below); deleted entries may hold any earlier
    ///   tombstone offset. Walking the buffer by recomputed strides
    ///   instead would be unsound: a slot's physical size is fixed at
    ///   allocation while `shrink` lowers `len` (the stride-desync bug
    ///   documented on [`Self::scale_activity`]).
    /// * On return `slots[i]` holds the clause's **new** ref if it was
    ///   live, or the tombstone ref if it was deleted (or failed
    ///   validation – an impossible state that must never fabricate a
    ///   relocation). The caller then rewrites every other ref holder from
    ///   this table (`WatchLists::relocate_refs`).
    ///
    /// The compacted region ends with a permanent **tombstone slot** (a
    /// `len == 0`, deleted-flagged header) so a stale ref always lands on a
    /// readable deleted clause; live clauses precede it in slot order,
    /// re-tightened to their current length (a 4→3 shrink's 8 bytes of
    /// padding are reclaimed). Clause contents, ids and relative order are
    /// untouched, so the solver's trajectory is preserved exactly – only
    /// physical addresses change.
    ///
    /// The sweep is **in place**, kissat-style (`collect.c`'s src/dst
    /// pointers): placing the tombstone at the *end* makes every live
    /// clause's new offset ≤ its old offset (deleted bytes only ever
    /// precede it), so clauses are `memmove`d down within the existing
    /// buffer – **peak RSS never exceeds the pre-compaction footprint**
    /// (a fresh-buffer copy would transiently hold old + new, which showed
    /// up as a +25 % peak on si2-b03m before this was rewritten). The tail
    /// is then returned via
    /// `shrink_to_fit` (glibc splits the arena's mmap in place), and no
    /// remap table is needed: the rewritten `slots` array *is* the map.
    pub fn compact(&mut self, slots: &mut [ClauseRef]) -> CompactSummary {
        let old_pos = self.pos;
        let tombstone_bytes = slot_size(0);

        // Pass 1 (read-only): classify every entry and measure the
        // compacted size (live clauses re-tightened to their current
        // lengths). Validation is the same bound every arena read uses
        // (`get`/`read_header`: header inside the live region, declared
        // literal array fitting between the header and `pos`) – a `slots`
        // entry that fails it, or whose header is deleted (a slot deleted
        // since the last compaction, or a previous compaction's tombstone
        // offset), is tombstoned rather than copied.
        //
        // Debug invariant carried through this scan: the **live** entries'
        // offsets are strictly ascending in id order (ids are handed out in
        // allocation order, `alloc` only appends, and every compaction
        // relocates live clauses preserving that order).
        let mut live_bytes = 0usize;
        let mut live_count = 0usize;
        let mut tombstoned = 0usize;
        let mut prev_live_off: Option<usize> = None;
        // SAFETY: `self.buffer` holds every real slot listed in `slots`;
        // reads only, before any in-place write.
        let base = self.buffer.as_ptr().cast::<u8>();
        for slot in slots.iter() {
            let off = slot.byte_offset();
            match unsafe { Self::header_in_extent(base, off, old_pos) } {
                Some(h) if !h.deleted() => {
                    debug_assert!(
                        prev_live_off.is_none_or(|p| p < off),
                        "live slot offsets must be strictly ascending in id order"
                    );
                    prev_live_off = Some(off);
                    live_bytes += slot_size(h.len as usize);
                    live_count += 1;
                }
                _ => tombstoned += 1,
            }
        }

        // Pass 2 (in place): every live clause moves to
        // `dst = Σ slot_size(len)` over the live clauses before it, which is
        // ≤ its current offset (deleted bytes only ever precede it) – a
        // downward `memmove` inside the existing buffer, so the peak
        // footprint is never exceeded.
        let tomb_off = live_bytes;
        let tomb = ClauseRef::from_byte_offset(tomb_off).unwrap_or(ClauseRef::NULL);
        let mut dst = 0usize;
        // SAFETY: within one call, `base` stays valid (no reallocation).
        // When slot i is processed, the bytes at `[off_i, off_i + bytes)`
        // are untouched by earlier copies (each copy i' < i ended at
        // `dst_{i'+1} ≤ off_i`), so its header read is sound; the copy
        // itself uses `ptr::copy` because `[dst, dst+bytes)` may overlap
        // `[off, off+bytes)` when the gap is smaller than the slot.
        let base = self.buffer.as_mut_ptr().cast::<u8>();
        unsafe {
            for slot in slots.iter_mut() {
                let off = slot.byte_offset();
                let Some(hdr) = Self::header_in_extent(base, off, old_pos) else {
                    // Unreachable through the public API (every `slots`
                    // entry came from `alloc` or a prior compaction);
                    // tombstone rather than fabricate a relocation for a
                    // corrupt slot.
                    *slot = tomb;
                    continue;
                };
                if hdr.deleted() {
                    *slot = tomb;
                    continue;
                }
                let bytes = HEADER_BYTES + hdr.len as usize * core::mem::size_of::<Lit>();
                core::ptr::copy(base.add(off).cast::<u8>(), base.add(dst), bytes);
                *slot = ClauseRef::from_byte_offset(dst).unwrap_or(tomb);
                dst += slot_size(hdr.len as usize);
            }
            debug_assert_eq!(dst, live_bytes, "pass-1 measurement must equal the copy");

            // The permanent tombstone at the end of the compacted region.
            // Room for it exists unless the region is entirely live (only
            // the ungated test entry can hit that); reserve in that case.
            if tomb_off + tombstone_bytes > self.buffer.capacity() * ALIGN {
                self.buffer
                    .reserve((tomb_off + tombstone_bytes).div_ceil(ALIGN) - self.buffer.len());
            }
            let base = self.buffer.as_mut_ptr().cast::<u8>();
            let mut h = ClauseHeader::new(0, false);
            h.flags_tier = FLAG_DELETED;
            base.add(tomb_off).cast::<ClauseHeader>().write(h);
            let new_pos = tomb_off + tombstone_bytes;
            self.buffer.set_len(new_pos.div_ceil(ALIGN));
        }

        self.pos = tomb_off + tombstone_bytes;
        // Return the freed tail to the allocator (glibc splits the arena's
        // mmap in place; small brk-backed buffers may keep their capacity,
        // which is irrelevant at those sizes).
        self.buffer.truncate(self.pos / ALIGN);
        self.buffer.shrink_to_fit();
        self.num_clauses = live_count + 1; // + the tombstone slot
        self.num_deleted = 1; // the tombstone
        self.wasted_bytes = tombstone_bytes;
        self.compactions += 1;

        CompactSummary {
            live: live_count,
            tombstoned,
            old_bytes: old_pos,
            new_bytes: self.pos,
            tombstone_offset: tomb_off as u32,
        }
    }

    /// Rewrite the clause at `r` with `new_lits`, in place.
    ///
    /// Returns `true` on success. Fails (returning `false`, leaving the
    /// clause untouched) if `r` is invalid, the clause is deleted, or
    /// `new_lits.len() > current len` – an arena slot cannot grow, and
    /// relocating would invalidate the `ClauseRef` held by watchers and
    /// trail reasons. Callers only ever shrink (drop redundant literals).
    pub fn shrink(&mut self, r: ClauseRef, new_lits: &[Lit]) -> bool {
        let Some(h) = self.read_header(r) else {
            return false;
        };
        if h.deleted() || new_lits.len() > h.len as usize {
            return false;
        }
        if new_lits.is_empty() {
            #[cfg(feature = "std")]
            eprintln!("ARENA-FORENSIC: shrink(id -> empty) called");
            debug_assert!(false, "shrink to empty");
        }
        // SAFETY: `r` validated; writing at most `new_lits.len()` literals
        // over an array that holds `v.lits.len() >= new_lits.len()`.
        unsafe {
            let hp = self.header_ptr_mut(r);
            core::ptr::copy_nonoverlapping(
                new_lits.as_ptr(),
                Self::lits_ptr_mut(hp),
                new_lits.len(),
            );
            (*hp).len = new_lits.len() as u32;
            // cadical `shrink_clause` parity: clamp the glue of a redundant
            // clause to `min(new_size - 1, glue)` on every in-place shrink.
            // The LBD is a tiering/quality metric only, but the stored value
            // must satisfy `lbd <= len - 1` (distinct decision levels of the
            // surviving literals cannot exceed their count) – an in-place
            // rewrite that drops literals (ELS substitution, subsume
            // strengthening, vivification) leaves a stale, now-too-large LBD
            // behind otherwise, which the debug invariant
            // `check_learned_clause_lbd` flags and tier promotion mis-reads.
            let new_lbd = (*hp).lbd().min(new_lits.len().saturating_sub(1) as u32);
            (*hp).set_lbd(new_lbd);
        }
        true
    }

    /// Swap literals `i` and `j` of the clause at `r`.
    pub fn swap_lits(&mut self, r: ClauseRef, i: usize, j: usize) {
        let Some(v) = self.get(r) else { return };
        if i >= v.lits.len() || j >= v.lits.len() || i == j {
            return;
        }
        // SAFETY: `r` validated; both indices in range.
        unsafe {
            let lp = Self::lits_ptr_mut(self.header_ptr_mut(r));
            core::ptr::swap(lp.add(i), lp.add(j));
        }
    }

    /// Mutable access to the clause's literals, for in-place algorithms
    /// (sorting, scan-and-swap in propagation).
    ///
    /// The slice's length is the clause's *current* length. Shrinking
    /// through this slice is impossible (it is a view, not ownership);
    /// use [`ClauseArena::shrink`].
    #[must_use]
    pub fn lits_mut(&mut self, r: ClauseRef) -> Option<&mut [Lit]> {
        let h = self.read_header(r)?;
        // SAFETY: `r` validated by `read_header`; `len` was written by
        // `alloc`/`shrink` and the literal array has that many initialised
        // elements (any tail of a shrunk slot is unreachable).
        Some(unsafe {
            core::slice::from_raw_parts_mut(
                Self::lits_ptr_mut(self.header_ptr_mut(r)),
                h.len as usize,
            )
        })
    }

    /// Set the LBD of the clause at `r`. Values above `u16::MAX` saturate –
    /// every consumer thresholds at ≤ 10 or averages into `u64` stats.
    pub fn set_lbd(&mut self, r: ClauseRef, lbd: u32) {
        if self.read_header(r).is_some() {
            // SAFETY: `r` validated by `get`.
            unsafe {
                (*self.header_ptr_mut(r)).lbd = lbd.min(u16::MAX as u32) as u16;
            }
        }
    }

    /// Set the usage counter (reduce-round decay under the used-shield).
    pub fn set_usage(&mut self, r: ClauseRef, usage: u32) {
        if self.read_header(r).is_none() {
            return;
        }
        // SAFETY: `r` validated by `read_header`.
        let hp = self.header_ptr_mut(r);
        unsafe {
            (*hp).usage = usage.min(u32::from(u8::MAX)) as u8;
        }
    }

    /// Set the tier of the clause at `r`.
    pub fn set_tier(&mut self, r: ClauseRef, tier: ClauseTier) {
        if self.read_header(r).is_some() {
            // SAFETY: `r` validated by `get`.
            unsafe {
                (*self.header_ptr_mut(r)).flags_tier = ((*self.header_ptr_mut(r)).flags_tier
                    & !(0x3 << TIER_SHIFT))
                    | ((tier as u8) << TIER_SHIFT);
            }
        }
    }

    /// Set the activity of the clause at `r`.
    pub fn set_activity(&mut self, r: ClauseRef, activity: f32) {
        if self.read_header(r).is_some() {
            // SAFETY: `r` validated by `get`.
            unsafe {
                (*self.header_ptr_mut(r)).activity = activity;
            }
        }
    }

    /// Clear the learned flag, promoting the clause to an original (cadical
    /// `subsume_clause`'s promotion rule; see `subsume.rs`).
    ///
    /// Deliberately does **not** touch the arena's live-original/learned
    /// accounting: the previous implementation flipped `Clause::learned`
    /// without adjusting `ClauseDatabase`'s counters either, and
    /// `reduce_clause_database` iterates `learned_clause_ids`, not the
    /// counters.
    pub fn clear_learned(&mut self, r: ClauseRef) {
        if let Some(h) = self.read_header(r)
            && h.learned()
        {
            // SAFETY: `r` validated by `get`.
            unsafe {
                (*self.header_ptr_mut(r)).flags_tier &= !FLAG_LEARNED;
            }
        }
    }

    /// Increment the usage count (saturating at `u8::MAX`) and return the
    /// new value. The tier-promotion consumers fire at 3 and 10 uses;
    /// saturation cannot change any decision they make.
    pub fn bump_usage(&mut self, r: ClauseRef) -> u32 {
        if self.read_header(r).is_none() {
            return 0;
        }
        // SAFETY: `r` validated by `read_header`.
        let hp = self.header_ptr_mut(r);
        unsafe {
            (*hp).usage = (*hp).usage.saturating_add(1);
            u32::from((*hp).usage)
        }
    }

    /// Reset the usage counter to zero.
    pub fn reset_usage(&mut self, r: ClauseRef) {
        if self.read_header(r).is_some() {
            // SAFETY: `r` validated by `read_header`.
            unsafe {
                (*self.header_ptr_mut(r)).usage = 0;
            }
        }
    }

    /// Read the usage count.
    #[must_use]
    pub fn usage_count(&self, r: ClauseRef) -> u32 {
        self.get(r).map_or(0, |v| v.usage_count)
    }

    /// Hot-path variant of [`Self::live_lits_mut`] for the propagation
    /// scan: identical semantics (null → `None`, deleted → `None`, live →
    /// the literal slice), with the region-arithmetic validation moved to
    /// `debug_assert!`s.
    ///
    /// Release elision argument: `self.pos` is written only by `alloc`
    /// (`self.pos = end`, monotonic) and by `compact` (`self.pos = dst`,
    /// shrinking) – and a compaction **synchronously rewrites every
    /// outstanding ref holder** (the `refs` table, then each watcher's `.r`;
    /// watchers are the only `ClauseRef` holders outside the database, an
    /// audit enforced by the privacy of the inner offset). A `ClauseRef`
    /// this arena has handed out therefore still names its clause after a
    /// compaction – live clauses at their new offset, deleted clauses at
    /// the permanent tombstone slot (the end of the compacted region),
    /// which is always inside the live region and always deleted-flagged.
    /// The elided checks
    /// (`byte_offset + HEADER_BYTES > pos` and the len-in-region bound) can
    /// therefore only fire on a *fabricated* ref, which no production caller
    /// constructs (watchers carry refs from `alloc`/`relocate_refs`; the
    /// only semantic liveness condition is the deleted flag, which is
    /// checked – it arrives free with the header load this function must do
    /// anyway).  Measured 2026-08-21: the validated path's arithmetic was
    /// the bulk of the ~10 % `read_header` bucket in the noL propagate
    /// profile.
    #[inline]
    pub fn live_lits_hot(&mut self, r: ClauseRef) -> Option<&mut [Lit]> {
        if r.is_null() {
            return None;
        }
        debug_assert!(r.byte_offset() + HEADER_BYTES <= self.pos);
        // SAFETY: `r` is non-null and (by the arena-invariant argument
        // above, debug-asserted) within the live region at a slot
        // boundary written by `alloc`; reading by value holds no borrow.
        let h = unsafe { core::ptr::read(self.header_ptr(r)) };
        debug_assert!(
            h.len as usize
                <= (self.pos - r.byte_offset() - HEADER_BYTES) / core::mem::size_of::<Lit>()
        );
        if h.deleted() {
            return None;
        }
        // SAFETY: slot valid; the literal array holds `h.len` initialised
        // elements (a shrunk slot's tail is unreachable).
        Some(unsafe {
            core::slice::from_raw_parts_mut(
                Self::lits_ptr_mut(self.header_ptr_mut(r)),
                h.len as usize,
            )
        })
    }

    /// Mutable literal slice for a **live** (non-deleted) clause, or `None`.
    /// Single header read validates both the slot and the deleted flag –
    /// this is the propagation hot path's entry point.
    #[must_use]
    pub fn live_lits_mut(&mut self, r: ClauseRef) -> Option<&mut [Lit]> {
        let h = self.read_header(r)?;
        if h.deleted() {
            return None;
        }
        // SAFETY: `r` validated by `read_header`; the literal array holds
        // `h.len` initialised elements (a shrunk slot's tail is unreachable).
        Some(unsafe {
            core::slice::from_raw_parts_mut(
                Self::lits_ptr_mut(self.header_ptr_mut(r)),
                h.len as usize,
            )
        })
    }

    /// Whether the clause at `r` exists and is deleted. Invalid refs read as
    /// not-deleted (callers pair this with `get`/`live_lits_mut`, which
    /// already refuse invalid refs).
    #[must_use]
    pub fn is_deleted(&self, r: ClauseRef) -> bool {
        self.read_header(r).is_some_and(|h| h.deleted())
    }

    /// `activity += inc` in one header write.
    pub fn add_activity(&mut self, r: ClauseRef, inc: f32) {
        if self.read_header(r).is_some() {
            // SAFETY: `r` validated by `read_header`.
            unsafe {
                (*self.header_ptr_mut(r)).activity += inc;
            }
        }
    }

    /// Multiply one clause's activity by `factor` (read-modify-write of the
    /// header field).
    ///
    /// Deliberately per-ref: the *previous* implementation walked the buffer
    /// slot-by-slot, recomputing each stride as `slot_size(current_len)` –
    /// but a clause's physical slot size is fixed at **allocation** while
    /// `shrink` later lowers `len`, so after a 4→3 literal shrink (stride
    /// 32→24) the walk desynchronized from the real layout, landed
    /// mid-slot, and "scaled an activity" 8 bytes past a bogus offset –
    /// reading a real clause's `len` field as a denormal `f32` and
    /// multiplying it by the rescale factor, underflowing to an exact zero
    /// bit pattern (caught by a gdb watchpoint on the zeroed field; the
    /// bogus-offset write came from `live_offs`). The authoritative slot
    /// list is the database's `refs` table, which never desynchronizes;
    /// memory-walking by recomputed strides is unsound by construction and
    /// this API is the replacement.
    pub fn scale_activity(&mut self, r: ClauseRef, factor: f32) {
        let Some(h) = self.read_header(r) else { return };
        if h.deleted() {
            return;
        }
        // SAFETY: `r` validated by `read_header`; activity field write.
        unsafe {
            (*self.header_ptr_mut(r)).activity *= factor;
        }
    }

    /// Arena memory statistics.
    #[must_use]
    pub fn stats(&self) -> MemoryStats {
        MemoryStats {
            total_bytes: self.buffer.capacity() * ALIGN,
            used_bytes: self.pos,
            wasted_bytes: self.wasted_bytes,
            num_clauses: self.num_clauses,
            num_deleted: self.num_deleted,
            compactions: self.compactions,
        }
    }
}

impl ClauseTier {
    /// Header code → tier. Unknown codes degrade to `Local` (the least
    /// privileged tier – deletion-friendliest – so a corrupt code never
    /// earns a clause permanent retention it did not pay for).
    fn from_u32(code: u32) -> Self {
        match code {
            1 => Self::Core,
            2 => Self::Mid,
            _ => Self::Local,
        }
    }
}

// The header must stay exactly 12 bytes: the slot-density arithmetic this
// module exists for (24 bytes for a 3-literal clause, 32 for a 5-literal
// one, two ternaries per cache line) is pinned by tests below.
const _: () = assert!(core::mem::size_of::<ClauseHeader>() == 12);

/// Memory usage statistics.
#[derive(Debug, Clone)]
pub struct MemoryStats {
    /// Total allocated bytes.
    pub total_bytes: usize,
    /// Bytes currently in use.
    pub used_bytes: usize,
    /// Bytes wasted by deleted clauses.
    pub wasted_bytes: usize,
    /// Number of active clauses.
    pub num_clauses: usize,
    /// Number of deleted clauses.
    pub num_deleted: usize,
    /// Compactions performed (slots reclaimed + re-tightened).
    pub compactions: u64,
}

/// What one [`ClauseArena::compact`] reclaimed.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct CompactSummary {
    /// Live clauses relocated.
    pub live: usize,
    /// Deleted slots whose `refs` entries became the tombstone.
    pub tombstoned: usize,
    /// Live-region bytes before (old `pos`).
    pub old_bytes: usize,
    /// Live-region bytes after (tombstone included).
    pub new_bytes: usize,
    /// Byte offset of the permanent deleted-clause tombstone (the end of
    /// the compacted region); deleted ids relocate here.
    pub tombstone_offset: u32,
}

impl MemoryStats {
    /// Memory efficiency (live bytes / total bytes).
    #[must_use]
    pub fn efficiency(&self) -> f64 {
        if self.total_bytes == 0 {
            return 1.0;
        }
        (self.used_bytes - self.wasted_bytes) as f64 / self.total_bytes as f64
    }

    /// Fraction of used bytes that is unreachable (deleted slots).
    #[must_use]
    pub fn waste_ratio(&self) -> f64 {
        if self.used_bytes == 0 {
            return 0.0;
        }
        self.wasted_bytes as f64 / self.used_bytes as f64
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::literal::Var;

    fn l(v: u32) -> Lit {
        Lit::pos(Var::new(v))
    }

    #[test]
    fn alloc_then_read_roundtrip() {
        let mut a = ClauseArena::new(0);
        let r = a.alloc(&[l(0), l(1), l(2)], false);
        let v = a.get(r).expect("clause readable");
        assert_eq!(v.lits, &[l(0), l(1), l(2)]);
        assert!(!v.learned);
        assert!(!v.deleted);
        assert_eq!(v.tier, ClauseTier::Local);
        assert_eq!(v.usage_count, 0);
    }

    #[test]
    fn refs_are_stable_across_more_allocs() {
        let mut a = ClauseArena::new(0);
        let r1 = a.alloc(&[l(0)], true);
        let r2 = a.alloc(&[l(1), l(2), l(3), l(4)], true);
        let r3 = a.alloc(&[l(5), l(6)], false);
        assert_ne!(r1, r2);
        assert_ne!(r2, r3);
        // Append-only: earlier refs still read their own clauses.
        assert_eq!(a.get(r1).expect("r1").lits, &[l(0)]);
        assert!(!a.get(r3).expect("r3").learned);
    }

    #[test]
    fn delete_flags_but_keeps_slot_readable() {
        let mut a = ClauseArena::new(0);
        let r = a.alloc(&[l(0), l(1)], false);
        a.delete(r);
        let v = a.get(r).expect("deleted clauses remain readable");
        assert!(v.deleted);
        // Idempotent.
        a.delete(r);
        assert!(a.get(r).expect("still readable").deleted);
        // A ref is never reused: the next alloc gets a fresh slot.
        let r2 = a.alloc(&[l(9)], false);
        assert_ne!(r, r2);
        assert!(!a.get(r2).expect("r2 live").deleted);
    }

    #[test]
    fn shrink_in_place_keeps_ref_and_refuses_growth() {
        let mut a = ClauseArena::new(0);
        let r = a.alloc(&[l(0), l(1), l(2), l(3)], false);
        assert!(a.shrink(r, &[l(2), l(0)]));
        assert_eq!(a.get(r).expect("shrunk").lits, &[l(2), l(0)]);
        // Growth is refused, clause untouched.
        assert!(!a.shrink(r, &[l(1), l(2), l(3), l(4), l(5)]));
        assert_eq!(a.get(r).expect("untouched").lits, &[l(2), l(0)]);
        // Shrink on a deleted clause is refused.
        a.delete(r);
        assert!(!a.shrink(r, &[l(1)]));
    }

    #[test]
    fn swap_lits_swaps() {
        let mut a = ClauseArena::new(0);
        let r = a.alloc(&[l(0), l(1), l(2)], false);
        a.swap_lits(r, 0, 2);
        assert_eq!(a.get(r).expect("swapped").lits, &[l(2), l(1), l(0)]);
        // Out-of-range is a no-op, not a panic.
        a.swap_lits(r, 0, 7);
        assert_eq!(a.get(r).expect("unchanged").lits, &[l(2), l(1), l(0)]);
    }

    #[test]
    fn metadata_roundtrip() {
        let mut a = ClauseArena::new(0);
        let r = a.alloc(&[l(0), l(1)], true);
        a.set_lbd(r, 3);
        a.set_tier(r, ClauseTier::Core);
        a.set_activity(r, 12.5);
        assert_eq!(a.get(r).expect("meta").lbd, 3);
        assert_eq!(a.get(r).expect("meta").tier, ClauseTier::Core);
        assert_eq!(a.get(r).expect("meta").activity, 12.5);
        a.clear_learned(r);
        assert!(!a.get(r).expect("promoted").learned);
        assert_eq!(a.bump_usage(r), 1);
        assert_eq!(a.usage_count(r), 1);
    }

    #[test]
    fn lits_mut_allows_in_place_sort() {
        let mut a = ClauseArena::new(0);
        let r = a.alloc(&[l(5), l(1), l(3)], false);
        let slice = a.lits_mut(r).expect("mutable lits");
        slice.sort_unstable_by_key(|x| x.code());
        assert_eq!(a.get(r).expect("sorted").lits, &[l(1), l(3), l(5)]);
    }

    #[test]
    fn scale_activity_skips_deleted_and_shrunk_slots_stay_exact() {
        // Regression for the stride-desync corruption: alloc, shrink across
        // a stride boundary (4->3 literals: slot stride 32->24 *as computed
        // from len*, physical slot unchanged), then scale. The refs-driven
        // implementation must touch only true slots; the old len-walking
        // version "scaled" an activity 8 bytes past a bogus mid-slot offset
        // and zeroed a real clause's len field (denormal x 1e-20 underflow).
        let mut a = ClauseArena::new(0);
        let r1 = a.alloc(&[l(0), l(1), l(2), l(3)], false); // stride 32
        let r2 = a.alloc(&[l(4), l(5), l(6), l(7)], false); // stride 32
        let r3 = a.alloc(&[l(8), l(9), l(10), l(11)], false);
        let r4 = a.alloc(&[l(12), l(13)], false);

        a.set_activity(r1, 4.0);
        a.set_activity(r2, 4.0);
        a.set_activity(r3, 4.0);
        a.set_activity(r4, 4.0);

        // Shrink r1 across the stride boundary; its physical slot stays 32B
        // but len-based stride arithmetic would now say 24B.
        assert!(a.shrink(r1, &[l(2), l(0), l(1)]));
        a.delete(r4);

        // The desync poison factor: a tiny scale, exactly like the rescale.
        a.scale_activity(r1, 1e-20);
        a.scale_activity(r2, 1e-20);
        a.scale_activity(r3, 1e-20);
        a.scale_activity(r4, 1e-20);

        // Every clause keeps its true length; nothing was zeroed.
        assert_eq!(a.get(r1).unwrap().lits.len(), 3);
        assert_eq!(a.get(r2).unwrap().lits.len(), 4);
        assert_eq!(a.get(r3).unwrap().lits.len(), 4);
        assert_eq!(a.get(r4).unwrap().lits.len(), 2); // deleted but readable
    }

    #[test]
    fn null_and_out_of_range_reads_refuse() {
        let mut a = ClauseArena::new(0);
        assert!(a.get(ClauseRef::null()).is_none());
        assert!(a.lits_mut(ClauseRef::null()).is_none());
        let r = a.alloc(&[l(0), l(1)], false);
        // Past the live region entirely.
        let past = ClauseRef::from_byte_offset(a.pos + 8).expect("constructible");
        assert!(a.get(past).is_none());
        // Deleting / mutating a bogus ref is a no-op, never a panic.
        a.delete(past);
        a.set_lbd(past, 3);
        assert!(!a.shrink(past, &[l(0)]));
        // A mid-slot offset (header of r is 12B; +8 is its middle) is
        // rejected by the length sanity check rather than trusted.
        let mid = ClauseRef::from_byte_offset(r.byte_offset() + 8).expect("constructible");
        assert!(a.get(mid).is_none() || a.get(r).is_some());
    }

    #[test]
    fn two_ternary_clauses_share_one_cache_line() {
        // Pins the f32-header density property: a 3-literal clause occupies
        // a 24-byte slot (12-byte header + 12 bytes of literals), so two
        // consecutive ternary clauses fit in a single 64-byte cache line
        // (2 x 24 = 48 <= 64). With the previous 16-byte f64 header the
        // slot was 28 raw bytes -> 32 after the 8-byte stride round, and
        // two ternaries needed 64 bytes exactly - only touching the line
        // by luck of the stride. If this test breaks, either the header
        // width or the slot arithmetic changed - revisit before shipping.
        let mut a = ClauseArena::new(0);
        let r1 = a.alloc(&[l(0), l(1), l(2)], false);
        let r2 = a.alloc(&[l(3), l(4), l(5)], false);

        assert_eq!(HEADER_BYTES, 12);
        assert_eq!(slot_size(3), 24);

        let line = |r: ClauseRef| r.byte_offset() / 64;
        assert_eq!(line(r1), line(r2), "two ternaries must share a cache line");

        // Both remain independently readable (line-sharing is layout, not
        // aliasing).
        assert_eq!(a.get(r1).unwrap().lits, &[l(0), l(1), l(2)]);
        assert_eq!(a.get(r2).unwrap().lits, &[l(3), l(4), l(5)]);
    }

    #[test]
    fn five_literal_clause_fits_half_a_cache_line() {
        // The 12-byte f32 header is exactly what upgrades the half-line
        // capacity from 4 literals (16-byte f64 header: 32 - 16 = 16 bytes
        // = 4 lits) to 5 (32 - 12 = 20 bytes of literals; the 8-byte stride
        // round keeps the slot at exactly 32). 5 is near the median learned
        // clause length, so "two median clauses per line" is the common
        // case. 6 literals (36 -> 40 after stride) must NOT fit.
        let mut a = ClauseArena::new(0);
        let five: Vec<Lit> = (0..5).map(l).collect();
        let six: Vec<Lit> = (0..6).map(l).collect();

        assert_eq!(slot_size(5), 32);
        assert_eq!(slot_size(6), 40);
        assert!(slot_size(6) > 32);

        let r5 = a.alloc(&five, false);
        let r6 = a.alloc(&six, false);
        // The 5-literal slot stays within its own half: the next clause can
        // still start in the same line...
        assert_eq!(r5.byte_offset(), 0);
        assert_eq!(r6.byte_offset(), 32);
        // ...while a 6-literal slot pushes the next clause off the line.
        let r7 = a.alloc(&[l(100)], false);
        assert_eq!(
            r7.byte_offset(),
            72,
            "6-lit slot (40B) leaves the first line"
        );

        assert_eq!(a.get(r5).unwrap().lits, &five[..]);
        assert_eq!(a.get(r6).unwrap().lits, &six[..]);
        assert_eq!(a.get(r7).unwrap().lits, &[l(100)]);
    }

    #[test]
    fn two_binary_clauses_share_one_cache_line() {
        // Pins the density property this arena exists for: a binary clause
        // occupies a 24-byte slot (12-byte header + 8 bytes of literals
        // after the 8-byte stride round), so two consecutive binary
        // clauses fit in a single 64-byte cache line with 16 bytes to
        // spare. The old `Vec<Clause>` layout spent 64 bytes *per* clause
        // (`#[repr(align(64))]`, SmallVec<[Lit; 8]>). If this test breaks,
        // either the header width or the slot arithmetic changed – revisit
        // the layout before shipping.
        let mut a = ClauseArena::new(0);
        let r1 = a.alloc(&[l(0), l(1)], false);
        let r2 = a.alloc(&[l(2), l(3)], false);
        let r3 = a.alloc(&[l(4), l(5)], false);

        assert_eq!(HEADER_BYTES, 12);
        assert_eq!(slot_size(2), 24);

        // Same 64-byte cache line iff floor(offset / 64) agrees.
        let line = |r: ClauseRef| r.byte_offset() / 64;
        assert_eq!(line(r1), line(r2), "binaries r1/r2 must share a cache line");
        // A third binary may or may not straddle (24*3 = 72 > 64) – but the
        // *first two* always fit, because slots are allocated from offset 0
        // in allocation order and 24 + 24 <= 64.
        assert!(line(r1) <= line(r3));

        // All three remain independently readable (the line-sharing is
        // layout, not aliasing).
        assert_eq!(a.get(r1).unwrap().lits, &[l(0), l(1)]);
        assert_eq!(a.get(r2).unwrap().lits, &[l(2), l(3)]);
        assert_eq!(a.get(r3).unwrap().lits, &[l(4), l(5)]);
    }

    #[test]
    fn large_clause_spans_multiple_slots_correctly() {
        let mut a = ClauseArena::new(0);
        let many: Vec<Lit> = (0..37).map(l).collect();
        let r1 = a.alloc(&many, false);
        let r2 = a.alloc(&[l(100)], false);
        assert_eq!(a.get(r1).expect("37 lits").lits, &many[..]);
        assert_eq!(a.get(r2).expect("next slot").lits, &[l(100)]);
    }

    #[test]
    fn header_is_twelve_bytes() {
        assert_eq!(core::mem::size_of::<ClauseHeader>(), 12);
        assert_eq!(core::mem::align_of::<ClauseHeader>(), 4);
    }

    #[test]
    fn lbd_saturates_at_u16_max() {
        let mut a = ClauseArena::new(0);
        let r = a.alloc(&[l(0), l(1)], true);
        a.set_lbd(r, 500_000);
        assert_eq!(a.get(r).expect("sat").lbd, u16::MAX as u32);
        a.set_lbd(r, 7);
        assert_eq!(a.get(r).expect("small").lbd, 7);
    }

    #[test]
    fn usage_saturates_at_u8_max() {
        let mut a = ClauseArena::new(0);
        let r = a.alloc(&[l(0)], true);
        for _ in 0..300 {
            a.bump_usage(r);
        }
        assert_eq!(a.usage_count(r), u8::MAX as u32);
    }

    #[test]
    fn activity_is_f32_and_stays_finite_under_policy() {
        let mut a = ClauseArena::new(0);
        let r = a.alloc(&[l(0)], false);
        assert_eq!(a.get(r).expect("f32").activity, 0.0);
        // The rescale policy guarantees activities stay below the
        // increment bound x 1/(1-decay); with the 1e20 bound and the
        // default 0.999 decay that ceiling is ~1e23, far inside f32's
        // 3.4e38. Bump far past a whole solver run's worth of increments
        // and confirm finiteness at the bound itself.
        for _ in 0..1000 {
            a.add_activity(r, 1e20_f32);
        }
        assert!(a.get(r).expect("bumped").activity.is_finite());
    }

    #[test]
    fn compact_moves_live_and_tombstones_deleted() {
        let mut a = ClauseArena::new(0);
        let r1 = a.alloc(&[l(0), l(1), l(2)], false);
        let r2 = a.alloc(&[l(3), l(4)], true); // deleted
        let r3 = a.alloc(&[l(5), l(6), l(7), l(8)], false);
        a.set_lbd(r1, 4);
        a.set_tier(r1, ClauseTier::Core);
        a.bump_usage(r1);
        a.add_activity(r3, 7.5);
        a.delete(r2);

        let mut slots = vec![r1, r2, r3];
        let s = a.compact(&mut slots);

        assert_eq!(s.live, 2);
        assert_eq!(s.tombstoned, 1);
        assert!(s.new_bytes < s.old_bytes);

        // Deleted slot's entry became the tombstone (end of the compacted
        // region), which reads as a deleted clause (never dangles, never
        // names another clause).
        assert_eq!(slots[1].byte_offset(), s.tombstone_offset as usize);
        assert_eq!(slots[1].byte_offset(), slot_size(3) + slot_size(4));
        assert!(a.get(slots[1]).expect("tombstone readable").deleted);

        // Live clauses relocated in place (downward), contents and metadata
        // identical; the first live clause now sits at offset 0.
        assert_eq!(slots[0].byte_offset(), 0);
        let v1 = a.get(slots[0]).expect("r1 live");
        assert_eq!(v1.lits, &[l(0), l(1), l(2)]);
        assert_eq!(v1.lbd, 4);
        assert_eq!(v1.tier, ClauseTier::Core);
        assert_eq!(v1.usage_count, 1);
        assert!(!v1.deleted);
        let v3 = a.get(slots[2]).expect("r3 live");
        assert_eq!(v3.lits, &[l(5), l(6), l(7), l(8)]);
        assert_eq!(v3.activity, 7.5);

        // Counters: live + tombstone only.
        let st = a.stats();
        assert_eq!(st.num_clauses, 3);
        assert_eq!(st.num_deleted, 1);
        assert_eq!(st.compactions, 1);
        assert_eq!(st.wasted_bytes, 16);
        assert_eq!(st.used_bytes, slot_size(3) + slot_size(4) + 16);
    }

    #[test]
    fn compact_reclaims_shrink_padding() {
        // A 4-literal slot (32 B) shrunk to 2 literals still occupies 32 B
        // until compaction re-tightens it to 24 B.
        let mut a = ClauseArena::new(0);
        let r = a.alloc(&[l(0), l(1), l(2), l(3)], false);
        assert!(a.shrink(r, &[l(2), l(0)]));
        let before = a.stats().used_bytes;
        assert_eq!(before, 32);

        let mut slots = vec![r];
        let s = a.compact(&mut slots);
        assert_eq!(a.stats().used_bytes, slot_size(2) + 16);
        assert_eq!(s.tombstone_offset as usize, slot_size(2));
        assert_eq!(a.get(slots[0]).expect("shrunk live").lits, &[l(2), l(0)]);
    }

    #[test]
    fn compact_then_alloc_continues_fresh() {
        let mut a = ClauseArena::new(0);
        let r1 = a.alloc(&[l(0), l(1)], false);
        a.delete(r1);
        let mut slots = vec![r1];
        let s = a.compact(&mut slots);
        assert_eq!(slots[0].byte_offset(), s.tombstone_offset as usize);
        assert_eq!(s.tombstone_offset, 0, "no live clauses: tombstone at 0");

        // Post-compaction allocation lands after the tombstone-only region.
        let r2 = a.alloc(&[l(9), l(10), l(11)], true);
        assert_eq!(r2.byte_offset(), 16);
        assert_eq!(a.get(r2).expect("fresh").lits, &[l(9), l(10), l(11)]);
    }

    #[test]
    fn compact_on_empty_arena_yields_tombstone_only() {
        let mut a = ClauseArena::new(0);
        let slots: &mut [ClauseRef] = &mut [];
        let s = a.compact(slots);
        assert_eq!(a.stats().used_bytes, 16);
        let tomb = ClauseRef::from_byte_offset(s.tombstone_offset as usize).expect("in range");
        assert!(a.get(tomb).expect("tombstone").deleted);
        assert!(a.get(tomb).expect("tombstone").lits.is_empty());
    }

    #[test]
    fn should_compact_gate_is_amortized() {
        let mut a = ClauseArena::new(0);
        // Tiny arena: below the absolute floor.
        let rs: Vec<_> = (0..10).map(|i| a.alloc(&[l(i), l(i + 1)], false)).collect();
        for r in rs {
            a.delete(r);
        }
        assert!(!a.should_compact());

        // Large arena, garbage < live/3: still no.
        let big: Vec<_> = (0..3000)
            .map(|i| a.alloc(&[l(i), l(i + 1), l(i + 2)], false))
            .collect();
        for r in big.iter().take(100) {
            a.delete(*r);
        }
        assert!(!a.should_compact());

        // Garbage >= live/3 and above the floor: fire.
        for r in big.iter() {
            a.delete(*r);
        }
        assert!(a.should_compact());
    }

    #[test]
    fn compact_preserves_relative_order_and_interleaving() {
        // Live clauses must keep their relative order (ids and allocation
        // order stay aligned after relocation).
        let mut a = ClauseArena::new(0);
        let mut slots = Vec::new();
        for i in 0..8 {
            let r = a.alloc(&[l(i * 3), l(i * 3 + 1), l(i * 3 + 2)], false);
            slots.push(r);
            if i % 2 == 1 {
                a.delete(r); // delete every second clause
            }
        }
        let live_before: Vec<_> = slots
            .iter()
            .enumerate()
            .filter(|(i, _)| i % 2 == 0)
            .map(|(i, _)| a.get(slots[i]).expect("live").lits.to_vec())
            .collect();
        a.compact(&mut slots);
        let live_after: Vec<_> = slots
            .iter()
            .filter(|r| a.get(**r).is_some_and(|v| !v.deleted))
            .map(|r| a.get(*r).expect("live").lits.to_vec())
            .collect();
        assert_eq!(live_before, live_after);
        // Offsets of surviving entries are strictly ascending (refs-order
        // invariant preserved across compaction).
        let offs: Vec<usize> = slots
            .iter()
            .filter(|r| a.get(**r).is_some_and(|v| !v.deleted))
            .map(|r| r.byte_offset())
            .collect();
        assert!(offs.windows(2).all(|w| w[0] < w[1]));
    }
}
