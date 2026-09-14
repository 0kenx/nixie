//! One long-watch list inside a fixed-domain propagation session.
//! Both compaction phases retain a narrow call boundary; no BIG state or outer
//! propagation-head cursor is live inside this kernel. Units never yield.
use super::{ClauseId, Lit, Watcher};
#[allow(unused_imports)]
use crate::prelude::*;
use crate::trail::{PropagationQueue, assign_undefined, prefetch_watch_payload, propagation_value};
use crate::watched::{CsrWatchLists, VecScanMirror};

#[path = "watch_cursor.rs"]
mod watch_cursor;
use watch_cursor::WatchCursor;

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
pub(super) fn scan_list<const MIRROR: bool>(
    watches: &mut [Watcher],
    false_lit: Lit,
    values: &mut [i8],
    queue: &mut PropagationQueue<'_>,
    clauses: crate::memory::PropagationArena<'_>,
    destinations: &mut [Vec<Watcher>],
    csr: &mut Option<CsrWatchLists>,
    vec_mirror: Option<&mut VecScanMirror<'_>>,
    swapped_code: Option<usize>,
) -> ScanResult {
    let begin = watches.as_mut_ptr();
    // MIRROR comes from the driver's specialization: the flag-off
    // instantiation compiles without a single CSR check (the screen bar).
    let result = scan::<false, MIRROR>(
        WatchCursor::new(watches),
        false_lit,
        values,
        queue,
        clauses,
        destinations,
        csr,
        vec_mirror,
        swapped_code,
        #[cfg(feature = "bcp-work")]
        super::super::PropagationWork::default(),
    );
    // SAFETY: the cursor only returns an initialized-prefix endpoint within
    // this same borrowed slice (possibly its beginning/end for an empty list).
    #[allow(unsafe_code)]
    let write = unsafe { result.end.offset_from(begin) as usize };
    ScanResult {
        write,
        conflict: result.conflict,
        #[cfg(feature = "bcp-work")]
        work: result.work,
    }
}

struct ScanEnd {
    end: *mut Watcher,
    conflict: ClauseId,
    #[cfg(feature = "bcp-work")]
    work: super::super::PropagationWork,
}

/// Only the prefix can call the suffix, once at its first removal. The suffix
/// never recurses; no input can increase native call depth beyond these two.
/// A phase returns its final state; no caller-owned cursor stays live in it.
#[allow(clippy::too_many_arguments)]
fn push_watch<const MIRROR: bool>(
    csr: &mut Option<CsrWatchLists>,
    vec_present: bool,
    destinations: &mut [Vec<Watcher>],
    key: Lit,
    watcher: Watcher,
) {
    crate::mut_trace!(
        key.index(),
        "side=vec act=push ref={} blk={} path=push_watch",
        watcher.r.byte_offset(),
        watcher.blocker.code()
    );
    destinations[key.index()].push(watcher);
    if MIRROR && let Some(c) = csr.as_mut() {
        c.scan_push(key, watcher);
    } else if vec_present && let Some(c) = csr.as_mut() {
        // Swapped-dual: the CSR overflow is the primary's mirror here.
        c.scan_push(key, watcher);
    }
}

#[allow(clippy::too_many_arguments)]
fn push_watch_unique<const MIRROR: bool>(
    csr: &mut Option<CsrWatchLists>,
    vec_present: bool,
    destinations: &mut [Vec<Watcher>],
    key: Lit,
    watcher: Watcher,
) {
    let list = &mut destinations[key.index()];
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
    if MIRROR && let Some(c) = csr.as_mut() {
        c.scan_push(key, watcher);
    } else if vec_present && let Some(c) = csr.as_mut() {
        c.scan_push(key, watcher);
    }
}

#[inline(never)]
#[allow(clippy::too_many_arguments)]
fn scan<const COMPACT: bool, const MIRROR: bool>(
    watches: WatchCursor<'_, COMPACT>,
    false_lit: Lit,
    values: &mut [i8],
    queue: &mut PropagationQueue<'_>,
    mut clauses: crate::memory::PropagationArena<'_>,
    destinations: &mut [Vec<Watcher>],
    csr: &mut Option<CsrWatchLists>,
    mut vec_mirror: Option<&mut VecScanMirror<'_>>,
    swapped_code: Option<usize>,
    #[cfg(feature = "bcp-work")] mut work: super::super::PropagationWork,
) -> ScanEnd {
    let scanned_code = (!false_lit).index();
    let mut watches = watches.into_local();
    while let Some(entry) = watches.next() {
        let watcher = entry.watcher();
        #[cfg(feature = "bcp-work")]
        {
            work.long_visits += 1;
        }
        if propagation_value(values, watcher.blocker) > 0 {
            entry.keep(None);
            if MIRROR && let Some(c) = csr.as_mut() {
                c.scan_keep(watcher, None);
            } else if let Some(vm) = vec_mirror.as_deref_mut() {
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
            if MIRROR && let Some(c) = csr.as_mut() {
                c.scan_remove(watcher.r);
            } else if let (Some(vm), Some(code)) = (vec_mirror.as_deref_mut(), swapped_code) {
                vm.remove();
                if let Some(c) = csr.as_mut() {
                    c.index_remove(code, watcher.r);
                }
            }
            if COMPACT {
                continue;
            }
            return scan::<true, MIRROR>(
                watches.compacting(),
                false_lit,
                values,
                queue,
                clauses,
                destinations,
                csr,
                vec_mirror.as_deref_mut(),
                swapped_code,
                #[cfg(feature = "bcp-work")]
                work,
            );
        };
        let searched = live.searched();
        #[cfg(feature = "std")]
        let cid_visit = crate::mut_trace::cwrite_target().map(|_| live.reason());
        #[cfg(feature = "std")]
        if let Some(want) = crate::mut_trace::cwrite_target()
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
            let cid_watch = crate::mut_trace::cwrite_target().map(|_| live.reason());
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
                                if let Some(want) = crate::mut_trace::cwrite_target()
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
                                push_watch::<MIRROR>(
                                    csr,
                                    vec_mirror.is_some(),
                                    destinations,
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
                push_watch_unique::<MIRROR>(
                    csr,
                    vec_mirror.is_some(),
                    destinations,
                    a.negate(),
                    Watcher::new(cid, watcher.r, b),
                );
                push_watch_unique::<MIRROR>(
                    csr,
                    vec_mirror.is_some(),
                    destinations,
                    b.negate(),
                    Watcher::new(cid, watcher.r, a),
                );
            }
            entry.remove();
            crate::mut_trace!(
                scanned_code,
                "side=scan act=drop ref={} path=scan_repair",
                watcher.r.byte_offset()
            );
            if MIRROR && let Some(c) = csr.as_mut() {
                c.scan_remove(watcher.r);
            } else if let (Some(vm), Some(code)) = (vec_mirror.as_deref_mut(), swapped_code) {
                vm.remove();
                if let Some(c) = csr.as_mut() {
                    c.index_remove(code, watcher.r);
                }
            }
            if COMPACT {
                continue;
            }
            return scan::<true, MIRROR>(
                watches.compacting(),
                false_lit,
                values,
                queue,
                clauses,
                destinations,
                csr,
                vec_mirror.as_deref_mut(),
                swapped_code,
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
                if MIRROR && let Some(c) = csr.as_mut() {
                    c.scan_keep(watcher, Some(blocker));
                } else if let Some(vm) = vec_mirror.as_deref_mut() {
                    vm.keep(watcher, Some(blocker));
                }
            } else {
                entry.remove();
                crate::mut_trace!(
                    scanned_code,
                    "side=scan act=drop ref={} path=scan_watch_move",
                    watcher.r.byte_offset()
                );
                if MIRROR && let Some(c) = csr.as_mut() {
                    c.scan_remove(watcher.r);
                } else if let (Some(vm), Some(code)) = (vec_mirror.as_deref_mut(), swapped_code) {
                    vm.remove();
                    if let Some(c) = csr.as_mut() {
                        c.index_remove(code, watcher.r);
                    }
                }
                if !COMPACT {
                    return scan::<true, MIRROR>(
                        watches.compacting(),
                        false_lit,
                        values,
                        queue,
                        clauses,
                        destinations,
                        csr,
                        vec_mirror.as_deref_mut(),
                        swapped_code,
                        #[cfg(feature = "bcp-work")]
                        work,
                    );
                }
            }
            continue;
        }
        entry.keep(Some(first));
        if MIRROR && let Some(c) = csr.as_mut() {
            c.scan_keep(watcher, Some(first));
        } else if let Some(vm) = vec_mirror.as_deref_mut() {
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
        if let Some(list) = destinations.get(first.index()) {
            prefetch_watch_payload(list);
        }
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
