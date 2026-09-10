//! Long-watch scan between assignment events. The immutable trail view is
//! confined to a non-inlined phase, with no Solver borrow. Stable compaction
//! has a no-removal prefix and a suffix whose write cursor is strictly behind
//! its read cursor, just as in `Vec::retain_mut`. Unit yields preserve the phase.
use super::{ClauseDatabase, ClauseId, Lit, Trail, WatchLists, Watcher};

pub(super) enum Step {
    Done,
    Conflict(ClauseId),
    Unit { literal: Lit, reason: ClauseId },
}

#[derive(Default)]
pub(super) struct Cursor {
    #[cfg(feature = "bcp-work")]
    pub(super) work: super::super::PropagationWork,
    pub(super) read: usize,
    pub(super) write: usize,
}

impl Cursor {
    #[inline]
    pub(super) fn advance(
        &mut self,
        watches: &mut [Watcher],
        false_lit: Lit,
        trail: &Trail,
        clauses: &mut ClauseDatabase,
        destinations: &mut WatchLists,
    ) -> Step {
        debug_assert!(self.write <= self.read && self.read <= watches.len());
        if self.write == self.read {
            self.scan::<false>(watches, false_lit, trail, clauses, destinations)
        } else {
            self.scan::<true>(watches, false_lit, trail, clauses, destinations)
        }
    }

    /// The prefix transfers to the suffix exactly once, at the first removal.
    /// The suffix never calls either phase, so call depth is bounded by two,
    /// independently of the input or the number of removals. Const specialization
    /// removes the compaction-state test from every kept entry in both loops.
    #[inline(never)]
    fn scan<const COMPACT: bool>(
        &mut self,
        watches: &mut [Watcher],
        false_lit: Lit,
        trail: &Trail,
        clauses: &mut ClauseDatabase,
        destinations: &mut WatchLists,
    ) -> Step {
        debug_assert_eq!(self.write < self.read, COMPACT);
        let mut write = self.write;
        for read in self.read..watches.len() {
            let watcher = watches[read];
            #[cfg(feature = "bcp-work")]
            {
                self.work.long_visits += 1;
            }
            if trail.lit_val_hot(watcher.blocker) > 0 {
                if COMPACT {
                    watches[write] = watcher;
                    write += 1;
                }
                continue;
            }
            #[cfg(feature = "bcp-work")]
            {
                self.work.clause_reads += 1;
            }
            let Some(mut live) = clauses.live_clause_by_ref(watcher.r) else {
                #[cfg(feature = "bcp-work")]
                {
                    self.work.deleted += 1;
                }
                if COMPACT {
                    continue;
                }
                self.read = read + 1;
                self.write = read;
                return self.scan::<true>(watches, false_lit, trail, clauses, destinations);
            };
            let searched = live.searched();
            let mut found = false;
            let mut new_searched = searched;
            let first;
            {
                let clause = live.lits();
                debug_assert!(clause[0] == false_lit || clause[1] == false_lit);
                first = Lit::from_code(clause[0].code() ^ clause[1].code() ^ false_lit.code());
                // Even satisfied exits keep the original eager normalization:
                // subsequent inprocessing observes literal order.
                clause[0] = first;
                clause[1] = false_lit;
                if trail.lit_val_hot(first) > 0 {
                    #[cfg(feature = "bcp-work")]
                    {
                        self.work.first_satisfied += 1;
                    }
                    let kept = if COMPACT { write } else { read };
                    if COMPACT {
                        watches[kept] = watcher;
                        write += 1;
                    }
                    watches[kept].blocker = first;
                    found = true;
                } else {
                    let (pair, tail) = clause.split_at_mut(2);
                    let hit = crate::memory::find_saved_pos_hit(
                        tail,
                        searched,
                        |lit| trail.lit_val_hot(lit),
                        || {
                            #[cfg(feature = "bcp-work")]
                            {
                                self.work.tail_probes += 1;
                            }
                        },
                    );
                    if let Some((i, literal, value)) = hit {
                        new_searched = crate::memory::saved_pos_store(i);
                        if value > 0 {
                            #[cfg(feature = "bcp-work")]
                            {
                                self.work.tail_satisfied += 1;
                            }
                            let kept = if COMPACT { write } else { read };
                            if COMPACT {
                                watches[kept] = watcher;
                                write += 1;
                            }
                            watches[kept].blocker = literal;
                            found = true;
                        } else {
                            core::mem::swap(&mut pair[1], &mut tail[i]);
                            #[cfg(feature = "bcp-work")]
                            {
                                self.work.watch_moves += 1;
                            }
                            destinations.add(
                                pair[1].negate(),
                                Watcher {
                                    blocker: first,
                                    ..watcher
                                },
                            );
                            if !COMPACT {
                                live.set_searched(new_searched);
                                self.read = read + 1;
                                self.write = read;
                                return self.scan::<true>(
                                    watches,
                                    false_lit,
                                    trail,
                                    clauses,
                                    destinations,
                                );
                            }
                            found = true;
                        }
                    }
                }
            }
            if new_searched != searched {
                live.set_searched(new_searched);
            }
            if found {
                continue;
            }
            let kept = if COMPACT { write } else { read };
            if COMPACT {
                watches[kept] = watcher;
            }
            watches[kept].blocker = first;
            let next_write = kept + 1;
            if trail.lit_val_hot(first) < 0 {
                #[cfg(feature = "bcp-work")]
                {
                    self.work.long_conflicts += 1;
                }
                // Preserve the unvisited tail without examining its blockers.
                // In the prefix it is already in its final position.
                if COMPACT {
                    watches.copy_within(read + 1.., next_write);
                }
                self.read = watches.len();
                self.write = next_write + watches.len() - read - 1;
                return Step::Conflict(watcher.reason(clauses));
            }
            // Resume only after the caller assigns this literal. No pointer
            // into the trail or clause arena survives this return.
            self.read = read + 1;
            self.write = next_write;
            return Step::Unit {
                literal: first,
                reason: watcher.reason(clauses),
            };
        }
        self.read = watches.len();
        self.write = if COMPACT { write } else { watches.len() };
        Step::Done
    }
}
