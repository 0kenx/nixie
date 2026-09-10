//! Ordinary propagation driver. Fixed-domain borrows live across all lists;
//! the narrow long-list call keeps BIG/driver state out of its scanning loops.
use super::*;
use crate::trail::{assign_undefined, prefetch_watch_payload, propagation_value};

impl Solver {
    pub(super) fn propagate_session(&mut self) -> Option<ClauseId> {
        if !self.trail.has_pending_propagation() {
            return None;
        }
        let session = self.trail.propagation_session();
        let values = session.values;
        let mut queue = session.queue;
        let mut arena = self.clauses.propagation();
        let (destinations, phantom, ghost_debt) = self.watches.propagation_parts();
        let graph = &self.binary_graph;
        let ticks = if self.stable {
            &mut self.ticks_stable
        } else {
            &mut self.ticks_focused
        };
        while let Some(lit) = queue.next() {
            self.stats.propagations += 1;
            #[cfg(feature = "bcp-work")]
            {
                self.stats.propagation_work.dequeued += 1;
            }
            if let Some(limit) = &mut self.propagate_step_limit {
                if *limit == 0 {
                    self.propagate_aborted = true;
                    return None;
                }
                *limit -= 1;
            }
            let code = lit.index();
            let (start, plen) = graph.span_of(code);
            let primary = &graph.edges[start..start + plen];
            let extra = &graph.extra[code];
            #[cfg(feature = "bcp-work")]
            {
                use super::super::propagation_work::list_lines;
                let work = &mut self.stats.propagation_work;
                work.started += 1;
                work.binary_lists += u64::from(!primary.is_empty() || !extra.is_empty());
                work.binary_list_lines += list_lines::<(Lit, ClauseId)>(primary.len())
                    + list_lines::<(Lit, ClauseId)>(extra.len());
            }
            // No graph mutation is possible in this callback-free session.
            // Preserve primary-before-overflow and binary-before-long order.
            for (is_primary, span) in [(true, primary), (false, extra)] {
                #[cfg(not(feature = "bcp-work"))]
                let _ = is_primary;
                for &(implied, reason) in span {
                    #[cfg(feature = "bcp-work")]
                    {
                        if is_primary {
                            self.stats.propagation_work.binary_primary_visits += 1;
                        } else {
                            self.stats.propagation_work.binary_overflow_visits += 1;
                        }
                    }
                    let value = propagation_value(values, implied);
                    if value < 0 {
                        #[cfg(feature = "bcp-work")]
                        {
                            self.stats.propagation_work.binary_conflicts += 1;
                        }
                        queue.requeue();
                        return Some(reason);
                    }
                    if value == 0 {
                        // SAFETY: graph literals belong to this session's
                        // fixed domain. The immediately preceding read proves
                        // undefined; no callback/unassignment can intervene.
                        #[allow(unsafe_code)]
                        unsafe {
                            assign_undefined(values, &mut queue, implied, reason)
                        };
                        let implied_code = implied.index();
                        if let Some(list) = destinations.get(implied_code) {
                            prefetch_watch_payload(list);
                        }
                        let (istart, ilen) = graph.span_of(implied_code);
                        prefetch_watch_payload(&graph.edges[istart..istart + ilen]);
                        if let Some(overflow) = graph.extra.get(implied_code) {
                            prefetch_watch_payload(overflow);
                        }
                        #[cfg(feature = "bcp-work")]
                        {
                            self.stats.propagation_work.binary_assignments += 1;
                        }
                    }
                }
            }
            let mut watches = core::mem::take(&mut destinations[code]);
            #[cfg(feature = "bcp-work")]
            {
                let work = &mut self.stats.propagation_work;
                work.long_lists += u64::from(!watches.is_empty());
                work.long_list_lines +=
                    super::super::propagation_work::list_lines::<Watcher>(watches.len());
            }
            // Preserve the old scheduling formula, including phantom binaries.
            let bins = phantom.get(code).map_or(0, |&n| n as usize);
            let ghosts = ghost_debt.get(code).map_or(0, |&n| n as usize);
            let charge = 1 + (((watches.len() + bins + ghosts) as u64) * 8).div_ceil(128);
            if ghosts != 0 {
                ghost_debt[code] = 0;
            }
            *ticks = ticks.saturating_add(charge);
            #[allow(unused_mut)]
            let mut result = if watches.is_empty() {
                list_kernel::ScanResult::default()
            } else {
                list_kernel::scan_list(
                    &mut watches,
                    !lit,
                    values,
                    &mut queue,
                    arena.reborrow(),
                    destinations,
                )
            };
            #[cfg(feature = "bcp-work")]
            self.stats
                .propagation_work
                .take_watch_scan(&mut result.work);
            watches.truncate(result.write);
            destinations[code] = watches;
            if !result.conflict.is_null() {
                queue.requeue();
                return Some(result.conflict);
            }
        }
        None
    }
}
