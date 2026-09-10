//! One long-watch list inside a fixed-domain propagation session.
//! Both compaction phases retain a narrow call boundary; no BIG state or outer
//! propagation-head cursor is live inside this kernel. Units never yield.
use super::{ClauseId, Lit, Watcher};
#[allow(unused_imports)]
use crate::prelude::*;
use crate::trail::{PropagationQueue, assign_undefined, propagation_value};
use crate::watched::{MoveBuffer, MoveWriter, Moves};

#[path = "watch_cursor.rs"]
mod watch_cursor;
use watch_cursor::WatchCursor;

pub(super) struct ScanResult {
    #[cfg(feature = "bcp-work")]
    pub(super) work: super::super::PropagationWork,
    pub(super) write: usize,
    // Live arena identities exclude NULL. Keeping this result to two
    // scalars keeps the driver-facing result compact. Internal scans also
    // return their initialized move slice.
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
pub(super) fn scan_list(
    watches: &mut [Watcher],
    false_lit: Lit,
    values: &mut [i8],
    queue: &mut PropagationQueue<'_>,
    clauses: crate::memory::PropagationArena<'_>,
    destinations: &mut [Vec<Watcher>],
    delayed: &mut MoveBuffer,
) -> ScanResult {
    let begin = watches.as_mut_ptr();
    let moves = delayed.prepare(watches.len());
    let result = scan::<false>(
        WatchCursor::new(watches),
        false_lit,
        values,
        queue,
        clauses,
        moves,
        #[cfg(feature = "bcp-work")]
        super::super::PropagationWork::default(),
    );
    // SAFETY: the cursor only returns an initialized-prefix endpoint within
    // this same borrowed slice (possibly its beginning/end for an empty list).
    #[allow(unsafe_code)]
    let write = unsafe { result.end.offset_from(begin) as usize };
    if !result.moves.is_empty() {
        result.moves.flush(destinations);
    }
    ScanResult {
        write,
        conflict: result.conflict,
        #[cfg(feature = "bcp-work")]
        work: result.work,
    }
}

struct ScanEnd<'a> {
    end: *mut Watcher,
    conflict: ClauseId,
    moves: Moves<'a>,
    #[cfg(feature = "bcp-work")]
    work: super::super::PropagationWork,
}

/// Only the prefix can call the suffix, once at its first removal. The suffix
/// never recurses; no input can increase native call depth beyond these two.
/// A phase returns its final state; no caller-owned cursor stays live in it.
#[inline(never)]
#[allow(clippy::too_many_arguments)] // Disjoint fixed stores are explicit borrows.
fn scan<'a, const COMPACT: bool>(
    watches: WatchCursor<'_, COMPACT>,
    false_lit: Lit,
    values: &mut [i8],
    queue: &mut PropagationQueue<'_>,
    mut clauses: crate::memory::PropagationArena<'_>,
    mut moves: MoveWriter<'a>,
    #[cfg(feature = "bcp-work")] mut work: super::super::PropagationWork,
) -> ScanEnd<'a> {
    let mut watches = watches.into_local();
    while let Some(entry) = watches.next() {
        let watcher = entry.watcher();
        #[cfg(feature = "bcp-work")]
        {
            work.long_visits += 1;
        }
        if propagation_value(values, watcher.blocker) > 0 {
            entry.keep(None);
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
            if COMPACT {
                continue;
            }
            return scan::<true>(
                watches.compacting(),
                false_lit,
                values,
                queue,
                clauses,
                moves,
                #[cfg(feature = "bcp-work")]
                work,
            );
        };
        let (pair, tail) = live.lits().split_at_mut(2);
        debug_assert!(pair[0] == false_lit || pair[1] == false_lit);
        let first = Lit::from_code(pair[0].code() ^ pair[1].code() ^ false_lit.code());
        // Even satisfied exits keep the original eager normalization:
        // subsequent inprocessing observes literal order.
        pair[0] = first;
        pair[1] = false_lit;
        if propagation_value(values, first) > 0 {
            #[cfg(feature = "bcp-work")]
            {
                work.first_satisfied += 1;
            }
            entry.keep(Some(first));
            continue;
        }
        // A disjoint mutable iterator needs only the current slot and end;
        // no tail index or derived arena-plus-tail base survives the loop.
        let mut found = None;
        for slot in tail {
            #[cfg(feature = "bcp-work")]
            {
                work.tail_probes += 1;
            }
            let literal = *slot;
            let value = propagation_value(values, literal);
            if value > 0 {
                #[cfg(feature = "bcp-work")]
                {
                    work.tail_satisfied += 1;
                }
                found = Some(Some(literal));
                break;
            }
            if value == 0 {
                core::mem::swap(&mut pair[1], slot);
                #[cfg(feature = "bcp-work")]
                {
                    work.watch_moves += 1;
                }
                // SAFETY: the buffer reserves one slot per input watcher;
                // each entry can reach this branch at most once, then breaks
                // and is removed. A suffix inherits the same writer. Since
                // the replacement is undefined and false_lit is false, the
                // queued destination cannot be the active watch list.
                #[allow(unsafe_code)]
                unsafe {
                    moves.push(
                        pair[1].negate(),
                        Watcher {
                            blocker: first,
                            ..watcher
                        },
                    )
                };
                found = Some(None);
                break;
            }
        }
        if let Some(parked) = found {
            if let Some(blocker) = parked {
                entry.keep(Some(blocker));
            } else {
                entry.remove();
                if !COMPACT {
                    return scan::<true>(
                        watches.compacting(),
                        false_lit,
                        values,
                        queue,
                        clauses,
                        moves,
                        #[cfg(feature = "bcp-work")]
                        work,
                    );
                }
            }
            continue;
        }
        entry.keep(Some(first));
        if propagation_value(values, first) < 0 {
            #[cfg(feature = "bcp-work")]
            {
                work.long_conflicts += 1;
            }
            return ScanEnd {
                end: watches.finish(),
                conflict: live.reason(),
                moves: moves.finish(),
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
        #[cfg(feature = "bcp-work")]
        {
            work.long_assignments += 1;
        }
    }
    ScanEnd {
        end: watches.finish(),
        conflict: ClauseId::NULL,
        moves: moves.finish(),
        #[cfg(feature = "bcp-work")]
        work,
    }
}
