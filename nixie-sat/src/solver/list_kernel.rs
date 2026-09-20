//! One long-watch list inside a fixed-domain propagation session.
//! Both compaction phases retain a narrow call boundary; no BIG state or outer
//! propagation-head cursor is live inside this kernel. Units never yield.
use super::{ClauseId, Lit, Watcher};
use crate::memory::ClauseRef;
#[allow(unused_imports)]
use crate::prelude::*;
use crate::trail::{PropagationQueue, assign_undefined, prefetch_watch_payload, propagation_value};
use crate::watched::{CsrWatchLists, VecScanMirror};

#[path = "watch_cursor.rs"]
mod watch_cursor;
use watch_cursor::WatchCursor;

/// The kept-run block filter: how many of the next 4 entries have
/// satisfied blockers — a leading run whose scalar action (`keep(None)`)
/// is semantically inert, so the cursor may skip them in bulk.
///
/// AVX2 shape (where it pays — dense lists): one `vmovdqu` loads 4
/// watchers ({ref, blocker} pairs, 8 B each); `vpermd` extracts the 4
/// blocker codes; the VALUE loads stay scalar (std::arch's gather family
/// addresses through typed pointers — byte-indexed gathers do not exist
/// there, and the 4-byte-scaled form reads wild addresses: the fault
/// storm the unit test caught); 4 branchless compares + a prefix mask
/// give the run.  The win over the scalar loop is skipping its per-entry
/// machinery (the Entry token, the write-cursor dance), not the loads.
#[cfg(all(target_arch = "x86_64", feature = "std"))]
mod block_filter {
    use super::Watcher;

    /// Leading run (0..=4) of entries whose blocker is TRUE.
    /// Leading run (0..=len) of entries whose blocker is TRUE — safe,
    /// slice-based: the caller shortens the scan's input by this prefix,
    /// which `keep(None)` would leave untouched in place anyway.
    #[inline]
    pub(super) fn kept_run(watches: &[Watcher], values: &[i8]) -> usize {
        watches
            .iter()
            .take_while(|w| values[w.blocker.index()] > 0)
            .count()
    }

    /// Runtime gate, cached once; `NIXIE_NO_SIMD=1` opts out.
    #[inline]
    pub(super) fn enabled() -> bool {
        use std::sync::OnceLock;
        static ON: OnceLock<bool> = OnceLock::new();
        *ON.get_or_init(|| {
            std::arch::is_x86_feature_detected!("avx2")
                && !std::env::var("NIXIE_NO_SIMD").is_ok_and(|v| v == "1")
        })
    }
}

/// The scan's push/notification funnel, monomorphized per driver mode:
/// the `Vec`-primary world (plain, CSR-mirror, swapped-dual) pushes the
/// destination `Vec` and mirrors into the CSR; the CSR-primary world
/// (commit-B / the unified in-place arm) pushes the slack-CSR through
/// its split context.  One body, zero dynamic dispatch.
pub(super) trait ScanDest {
    /// A watch move's push to `key`.
    fn push(&mut self, scanned_code: usize, key: Lit, watcher: Watcher);
    /// A repair's dedup'd push to `key`.
    fn push_unique(&mut self, scanned_code: usize, key: Lit, watcher: Watcher);
    /// A kept-entry notification (the CSR-mirror modes; structural modes
    /// no-op — their write-backs are commit-time).
    fn keep(&mut self, watcher: Watcher, blocker: Option<Lit>);
    /// A removed-entry notification (mirror / index maintenance).
    fn remove(&mut self, scanned_code: usize, r: ClauseRef);
    /// Prefetch a destination list (the `Vec` world's payload hint).
    fn prefetch(&mut self, key: usize);
}

/// The `Vec`-primary funnel: pushes land in the destination `Vec` (and
/// mirror into the CSR when one is attached).
pub(super) struct VecDest<'a, const MIRROR: bool> {
    pub(super) destinations: &'a mut [Vec<Watcher>],
    pub(super) csr: &'a mut Option<CsrWatchLists>,
    /// Whether a swapped-dual `VecScanMirror` rides this scan (its CSR
    /// side is mirrored, not authoritative).
    pub(super) swapped: bool,
}

impl<const MIRROR: bool> ScanDest for VecDest<'_, MIRROR> {
    #[inline]
    fn push(&mut self, _scanned_code: usize, key: Lit, watcher: Watcher) {
        crate::mut_trace!(
            key.index(),
            "side=vec act=push ref={} blk={} path=push_watch",
            watcher.r.byte_offset(),
            watcher.blocker.code()
        );
        self.destinations[key.index()].push(watcher);
        if MIRROR && let Some(c) = self.csr.as_mut() {
            c.scan_push(key, watcher);
        } else if self.swapped
            && let Some(c) = self.csr.as_mut()
        {
            c.scan_push(key, watcher);
        }
    }

    #[inline]
    fn push_unique(&mut self, _scanned_code: usize, key: Lit, watcher: Watcher) {
        let list = &mut self.destinations[key.index()];
        if list.iter().any(|w| w.r == watcher.r) {
            crate::mut_trace!(
                key.index(),
                "side=vec act=suppress ref={} path=push_watch_unique",
                watcher.r.byte_offset()
            );
            return;
        }
        crate::mut_trace!(
            key.index(),
            "side=vec act=push ref={} blk={} path=push_watch_unique",
            watcher.r.byte_offset(),
            watcher.blocker.code()
        );
        list.push(watcher);
        if MIRROR && let Some(c) = self.csr.as_mut() {
            c.scan_push(key, watcher);
        } else if self.swapped
            && let Some(c) = self.csr.as_mut()
        {
            c.scan_push(key, watcher);
        }
    }

    #[inline]
    fn keep(&mut self, watcher: Watcher, blocker: Option<Lit>) {
        if MIRROR && let Some(c) = self.csr.as_mut() {
            c.scan_keep(watcher, blocker);
        }
    }

    #[inline]
    fn remove(&mut self, scanned_code: usize, r: ClauseRef) {
        if MIRROR && let Some(c) = self.csr.as_mut() {
            c.scan_remove(r);
        } else if self.swapped
            && let Some(c) = self.csr.as_mut()
        {
            c.index_remove(scanned_code, r);
        }
    }

    #[inline]
    fn prefetch(&mut self, key: usize) {
        if let Some(list) = self.destinations.get(key) {
            prefetch_watch_payload(list);
        }
    }
}

/// The CSR-primary funnel (commit-B and the unified in-place arm): pushes
/// append into the slack-CSR through the split context; the swapped-dual
/// validation mode additionally pushes the `Vec` side (whose lists the
/// drift oracle compares at rebuilds — including its dedup reader, kept
/// on the `Vec` so the validated world stays exactly the validated one).
pub(super) struct CsrPartsDest<'a, 'c> {
    pub(super) ctx: &'c mut crate::watched::ScanCtx<'a>,
    pub(super) vec_dest: Option<&'c mut [Vec<Watcher>]>,
}

impl ScanDest for CsrPartsDest<'_, '_> {
    #[inline]
    fn push(&mut self, _scanned_code: usize, key: Lit, watcher: Watcher) {
        crate::mut_trace!(
            key.index(),
            "side=csr act=push ref={} blk={} path=push_watch",
            watcher.r.byte_offset(),
            watcher.blocker.code()
        );
        self.ctx.push_entry(key, watcher);
        if let Some(d) = self.vec_dest.as_deref_mut() {
            d[key.index()].push(watcher);
        }
    }

    #[inline]
    fn push_unique(&mut self, scanned_code: usize, key: Lit, watcher: Watcher) {
        if let Some(d) = self.vec_dest.as_deref_mut() {
            // Swapped-dual: the dedup reads the `Vec` (the validated
            // reader); the CSR side is content-equal by the drift
            // invariant the oracle checks at every rebuild.
            let list = &mut d[key.index()];
            if list.iter().any(|w| w.r == watcher.r) {
                crate::mut_trace!(
                    key.index(),
                    "side=vec act=suppress ref={} path=push_watch_unique",
                    watcher.r.byte_offset()
                );
                return;
            }
            crate::mut_trace!(
                key.index(),
                "side=vec act=push ref={} blk={} path=push_watch_unique",
                watcher.r.byte_offset(),
                watcher.blocker.code()
            );
            list.push(watcher);
            self.ctx.push_entry(key, watcher);
            return;
        }
        if self.ctx.contains_ref(scanned_code, key, watcher.r) {
            crate::mut_trace!(
                key.index(),
                "side=vec act=suppress ref={} path=push_watch_unique",
                watcher.r.byte_offset()
            );
            return;
        }
        crate::mut_trace!(
            key.index(),
            "side=vec act=push ref={} blk={} path=push_watch_unique",
            watcher.r.byte_offset(),
            watcher.blocker.code()
        );
        self.ctx.push_entry(key, watcher);
    }

    #[inline]
    fn keep(&mut self, _watcher: Watcher, _blocker: Option<Lit>) {
        // Structural: the commit publishes the compacted span.
    }

    #[inline]
    fn remove(&mut self, scanned_code: usize, r: ClauseRef) {
        self.ctx.on_remove(scanned_code, r);
    }

    #[inline]
    fn prefetch(&mut self, _key: usize) {}
}

pub(super) struct ScanResult {
    #[cfg(feature = "bcp-work")]
    pub(super) work: super::super::PropagationWork,
    pub(super) write: usize,
    pub(super) conflict: ClauseId,
}

impl Default for ScanResult {
    fn default() -> Self {
        Self {
            write: 0,
            conflict: ClauseId::NULL,
            #[cfg(feature = "bcp-work")]
            work: super::super::PropagationWork::default(),
        }
    }
}

#[inline]
#[allow(clippy::too_many_arguments)]
pub(super) fn scan_list<D: ScanDest>(
    watches: &mut [Watcher],
    false_lit: Lit,
    values: &mut [i8],
    queue: &mut PropagationQueue<'_>,
    clauses: crate::memory::PropagationArena<'_>,
    dest: &mut D,
    vec_mirror: Option<&mut VecScanMirror<'_>>,
) -> ScanResult {
    // Kept-run prefilter (the safe form): the leading run of satisfied
    // blockers needs no scalar work — keep(None) leaves those entries in
    // place — so the scan starts after them and the write count carries
    // the prefix.  The pre-read of blockers is monotone-safe: values only
    // go undefined -> true/false within a scan, so a blocker already true
    // cannot become false before the scan would have reached it.
    let prefix = if use_simd_prefilter() && watches.len() >= 8 {
        block_filter::kept_run(watches, values)
    } else {
        0
    };
    #[cfg(feature = "bcp-work")]
    let pre_visits = prefix as u64;
    #[cfg(not(feature = "bcp-work"))]
    let _ = prefix;
    let cut = prefix.min(watches.len());
    let watches = &mut watches[cut..];
    let begin = watches.as_mut_ptr();
    // The destination trait carries the driver's mode (Vec-primary plain
    // / CSR-mirror / swapped-dual, or CSR-primary in-place); the flag-off
    // VecDest instantiation compiles without a single CSR check.
    let mut result = scan(
        WatchCursor::new(watches),
        false_lit,
        values,
        queue,
        clauses,
        dest,
        vec_mirror,
        #[cfg(feature = "bcp-work")]
        super::super::PropagationWork::default(),
    );
    // SAFETY: the cursor only returns an initialized-prefix endpoint within
    // this same borrowed slice (possibly its beginning/end for an empty list).
    #[allow(unsafe_code)]
    let write = unsafe { result.end.offset_from(begin) as usize } + prefix;
    #[cfg(feature = "bcp-work")]
    {
        result.work.long_visits += pre_visits;
    }
    ScanResult {
        write,
        conflict: result.conflict,
        #[cfg(feature = "bcp-work")]
        work: result.work,
    }
}

/// Whether the leading-run prefilter runs (AVX2 present, 8-byte
/// watchers, `NIXIE_NO_SIMD` unset).
#[inline]
fn use_simd_prefilter() -> bool {
    #[cfg(all(target_arch = "x86_64", feature = "std"))]
    {
        block_filter::enabled() && core::mem::size_of::<Watcher>() == 8
    }
    #[cfg(not(all(target_arch = "x86_64", feature = "std")))]
    {
        false
    }
}

struct ScanEnd {
    end: *mut Watcher,
    conflict: ClauseId,
    #[cfg(feature = "bcp-work")]
    work: super::super::PropagationWork,
}

#[inline(never)]
#[allow(clippy::too_many_arguments)]
fn scan<const COMPACT: bool, D: ScanDest>(
    watches: WatchCursor<'_, COMPACT>,
    false_lit: Lit,
    values: &mut [i8],
    queue: &mut PropagationQueue<'_>,
    mut clauses: crate::memory::PropagationArena<'_>,
    dest: &mut D,
    mut vec_mirror: Option<&mut VecScanMirror<'_>>,
    #[cfg(feature = "bcp-work")] mut work: super::super::PropagationWork,
) -> ScanEnd {
    let scanned_code = (!false_lit).index();
    // Hoisted per-scan invariants (process-wide `OnceLock`s): the per-visit
    // calls below cost two Acquire loads + branches per watcher visit —
    // measurable in line-level profiles (mut_trace.rs / option.rs entries).
    #[cfg(feature = "std")]
    let cwrite_probe = crate::mut_trace::cwrite_target();
    #[cfg(not(feature = "std"))]
    let cwrite_probe: Option<usize> = None;
    let mut watches = watches.into_local();
    while let Some(entry) = watches.next() {
        let watcher = entry.watcher();
        #[cfg(feature = "bcp-work")]
        {
            work.long_visits += 1;
        }
        if propagation_value(values, watcher.blocker) > 0 {
            entry.keep(None);
            dest.keep(watcher, None);
            if let Some(vm) = vec_mirror.as_deref_mut() {
                vm.keep(watcher, None);
            }
            continue;
        }
        #[cfg(feature = "bcp-work")]
        {
            work.clause_reads += 1;
        }
        let Some(mut live) = clauses.live_clause(watcher.r) else {
            #[cfg(feature = "bcp-work")]
            {
                work.deleted += 1;
            }
            entry.remove();
            crate::mut_trace!(
                scanned_code,
                "side=scan act=drop ref={} path=scan_dead_clause",
                watcher.r.byte_offset()
            );
            dest.remove(scanned_code, watcher.r);
            if let Some(vm) = vec_mirror.as_deref_mut() {
                vm.remove();
            }
            if COMPACT {
                continue;
            }
            return scan::<true, _>(
                watches.compacting(),
                false_lit,
                values,
                queue,
                clauses,
                dest,
                vec_mirror.as_deref_mut(),
                #[cfg(feature = "bcp-work")]
                work,
            );
        };
        let searched = live.searched();
        #[cfg(feature = "std")]
        let cid_visit = cwrite_probe.map(|_| live.reason());
        #[cfg(feature = "std")]
        if let Some(want) = cwrite_probe
            && cid_visit.is_some_and(|c| c.index() == want)
        {
            use std::fmt::Write as _;
            let mut tv = String::new();
            for &tl in live.lits().iter().skip(2) {
                let _ = write!(tv, "{}:{},", tl.code(), propagation_value(values, tl));
            }
            eprintln!(
                "[cvisit op={}] id={} searched={} blk={} tail={}",
                crate::mut_trace::next_op(),
                want,
                searched,
                watcher.blocker.code(),
                tv
            );
        }
        let mut found = None;
        let mut new_searched = searched;
        let mut repair = None;
        let first;
        {
            #[cfg(feature = "std")]
            let cid_watch = cwrite_probe.map(|_| live.reason());
            #[cfg(not(feature = "std"))]
            let cid_watch: Option<ClauseId> = None;
            let lits = live.lits();
            if lits.len() < 2 {
                repair = Some(None);
                first = false_lit;
            } else {
                let (pair, tail) = lits.split_at_mut(2);
                if pair[0] != false_lit && pair[1] != false_lit {
                    repair = Some(Some((pair[0], pair[1])));
                    first = false_lit;
                } else {
                    debug_assert!(pair[0] == false_lit || pair[1] == false_lit);
                    first = Lit::from_code(pair[0].code() ^ pair[1].code() ^ false_lit.code());
                    pair[0] = first;
                    pair[1] = false_lit;
                    if propagation_value(values, first) > 0 {
                        #[cfg(feature = "bcp-work")]
                        {
                            work.first_satisfied += 1;
                        }
                        found = Some(Some(first));
                    } else {
                        let hit = crate::memory::find_saved_pos_hit(
                            tail,
                            searched,
                            |lit| propagation_value(values, lit),
                            || {
                                #[cfg(feature = "bcp-work")]
                                {
                                    work.tail_probes += 1;
                                }
                            },
                        );
                        if let Some((i, literal, value)) = hit {
                            new_searched = crate::memory::saved_pos_store(i);
                            if value > 0 {
                                #[cfg(feature = "bcp-work")]
                                {
                                    work.tail_satisfied += 1;
                                }
                                found = Some(Some(literal));
                            } else {
                                #[cfg(feature = "std")]
                                if let Some(want) = cwrite_probe
                                    && cid_watch.is_some_and(|c| c.index() == want)
                                {
                                    eprintln!(
                                        "[cwrite op={}] kernel-swap id={} i={} moved={} old1={}",
                                        crate::mut_trace::next_op(),
                                        want,
                                        i,
                                        tail[i].code(),
                                        pair[1].code()
                                    );
                                }
                                core::mem::swap(&mut pair[1], &mut tail[i]);
                                #[cfg(feature = "bcp-work")]
                                {
                                    work.watch_moves += 1;
                                }
                                dest.push(
                                    scanned_code,
                                    pair[1].negate(),
                                    Watcher {
                                        blocker: first,
                                        ..watcher
                                    },
                                );
                                found = Some(None);
                            }
                        }
                    }
                }
            }
        }
        if let Some(pair) = repair {
            if let Some((a, b)) = pair {
                let cid = live.reason();
                dest.push_unique(scanned_code, a.negate(), Watcher::new(cid, watcher.r, b));
                dest.push_unique(scanned_code, b.negate(), Watcher::new(cid, watcher.r, a));
            }
            entry.remove();
            crate::mut_trace!(
                scanned_code,
                "side=scan act=drop ref={} path=scan_repair",
                watcher.r.byte_offset()
            );
            dest.remove(scanned_code, watcher.r);
            if let Some(vm) = vec_mirror.as_deref_mut() {
                vm.remove();
            }
            if COMPACT {
                continue;
            }
            return scan::<true, _>(
                watches.compacting(),
                false_lit,
                values,
                queue,
                clauses,
                dest,
                vec_mirror.as_deref_mut(),
                #[cfg(feature = "bcp-work")]
                work,
            );
        }
        if new_searched != searched {
            live.set_searched(new_searched);
        }
        if let Some(parked) = found {
            if let Some(blocker) = parked {
                entry.keep(Some(blocker));
                dest.keep(watcher, Some(blocker));
                if let Some(vm) = vec_mirror.as_deref_mut() {
                    vm.keep(watcher, Some(blocker));
                }
            } else {
                entry.remove();
                crate::mut_trace!(
                    scanned_code,
                    "side=scan act=drop ref={} path=scan_watch_move",
                    watcher.r.byte_offset()
                );
                dest.remove(scanned_code, watcher.r);
                if let Some(vm) = vec_mirror.as_deref_mut() {
                    vm.remove();
                }
                if !COMPACT {
                    return scan::<true, _>(
                        watches.compacting(),
                        false_lit,
                        values,
                        queue,
                        clauses,
                        dest,
                        vec_mirror.as_deref_mut(),
                        #[cfg(feature = "bcp-work")]
                        work,
                    );
                }
            }
            continue;
        }
        entry.keep(Some(first));
        dest.keep(watcher, Some(first));
        if let Some(vm) = vec_mirror.as_deref_mut() {
            vm.keep(watcher, Some(first));
        }
        if propagation_value(values, first) < 0 {
            #[cfg(feature = "bcp-work")]
            {
                work.long_conflicts += 1;
            }
            return ScanEnd {
                end: watches.finish(),
                conflict: live.reason(),
                #[cfg(feature = "bcp-work")]
                work,
            };
        }
        // SAFETY: first is an in-domain clause literal. Its true exit
        // precedes the tail scan and its false exit is above. No assignment
        // occurred between these checks, so it is still undefined. The
        // exclusive view prevents resize, unassignment and queue growth.
        #[allow(unsafe_code)]
        unsafe {
            assign_undefined(values, queue, first, live.reason())
        };
        dest.prefetch(first.index());
        #[cfg(feature = "bcp-work")]
        {
            work.long_assignments += 1;
        }
    }
    ScanEnd {
        end: watches.finish(),
        conflict: ClauseId::NULL,
        #[cfg(feature = "bcp-work")]
        work,
    }
}
