//! Ordinary propagation driver. Fixed-domain borrows live across all lists;
//! the narrow long-list call keeps BIG/driver state out of its scanning loops.
use super::*;
use crate::trail::{assign_undefined, prefetch_watch_payload, propagation_value};

impl Solver {
    #[inline]
    pub(super) fn propagate_session(&mut self) -> Option<ClauseId> {
        // Const-generic MIRROR specialization: the whole driver (and the
        // list kernel it calls) compiles without a single CSR check when
        // the dual-write shadow is off — the flag-off binary must be
        // instruction-identical to the pre-mirror code (measured: the
        // per-literal Option checks alone cost 1.2% instructions on
        // 6s167-class instances).
        if self.watches.csr_active() {
            self.propagate_session_inner::<true>()
        } else {
            self.propagate_session_inner::<false>()
        }
    }

    fn propagate_session_inner<const MIRROR: bool>(&mut self) -> Option<ClauseId> {
        if !self.trail.has_pending_propagation() {
            return None;
        }
        let session = self.trail.propagation_session();
        let values = session.values;
        let mut queue = session.queue;
        let mut arena = self.clauses.propagation();
        let (destinations, phantom, ghost_debt, csr, scratch) = self.watches.propagation_parts();
        let stable_mode = self.stable;
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
                if span.is_empty() {
                    continue;
                }
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
                        #[cfg(feature = "std")]
                        if crate::env_flags::conflict_trace() {
                            eprintln!("[bconf] code={} cid={}", code, reason.index());
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
            // The swapped-dual scan (`NIXIE_CSR_SCAN=1`, slice 4's gate):
            // the CSR's span+overflow are the PRIMARY scan target and the
            // taken `Vec` list is the mirror — the roles of slice 2
            // exchanged, validated by the same drift comparison.  The span
            // is copied out so the kernel's CSR pushes (index upkeep,
            // overflow mirrors) never alias the scanned slice.
            #[cfg(feature = "std")]
            let b_mode = MIRROR && crate::watched::csr_b_enabled() && csr.is_some();
            #[cfg(not(feature = "std"))]
            let b_mode = false;
            #[cfg(feature = "std")]
            let swapped = MIRROR && !b_mode && crate::watched::csr_scan_enabled() && csr.is_some();
            #[cfg(not(feature = "std"))]
            let swapped = false;
            // Commit-B (`NIXIE_CSR_B=1`): the CSR's span+overflow ARE the
            // scan target — take semantics (the span's live end drops to
            // its start and the overflow leaves the CSR), so mid-scan
            // self-dedups read an empty combined view exactly as the old
            // taken-Vec slot did.  Pushes/dedups target the CSR directly
            // (the kernel's const-B instantiation); the Vec side is dead.
            // Commit-B scan scratch: reused across scans (clear + copy —
            // the lists average ~3 entries, so the copy is L1 traffic and
            // the per-scan `Vec::with_capacity` it replaces was the
            // dominant commit-B cost).
            let b_prepared: Option<(usize, &mut Vec<Watcher>, Vec<Watcher>)> =
                if b_mode && let Some(c) = csr.as_mut() {
                    let (start, span, ovf_slot) = c.scan_parts(code);
                    scratch.clear();
                    scratch.extend_from_slice(span);
                    Some((start, &mut *scratch, core::mem::take(ovf_slot)))
                } else {
                    None
                };
            let mut watches = if b_mode {
                Vec::new()
            } else {
                core::mem::take(&mut destinations[code])
            };
            let watches_len = if let Some((_, span_copy, ovf)) = b_prepared.as_ref() {
                span_copy.len() + ovf.len()
            } else {
                watches.len()
            };
            crate::mut_trace!(
                code,
                "side=vec act=begin_scan len={} path=session_take",
                watches_len
            );
            // Dual-write BCP scan (CSR slice 2): snapshot the primary/
            // overflow split before the list is scanned; the per-entry
            // notifications below mirror keep/remove/move into the CSR.
            if MIRROR
                && !swapped
                && !b_mode
                && let Some(c) = csr.as_mut()
            {
                c.begin_scan(code, watches.len());
            }
            #[cfg(feature = "bcp-work")]
            {
                let work = &mut self.stats.propagation_work;
                work.long_lists += u64::from(watches_len != 0);
                work.long_list_lines +=
                    super::super::propagation_work::list_lines::<Watcher>(watches_len);
            }
            // Preserve the old scheduling formula, including phantom binaries.
            let bins = phantom.get(code).map_or(0, |&n| n as usize);
            let ghosts = ghost_debt.get(code).map_or(0, |&n| n as usize);
            let charge = 1 + (((watches_len + bins + ghosts) as u64) * 8).div_ceil(128);
            if ghosts != 0 {
                ghost_debt[code] = 0;
            }
            *ticks = ticks.saturating_add(charge);
            #[cfg(feature = "std")]
            if crate::watched::csr_charge_trace_enabled() {
                eprintln!(
                    "[charge] c={} stable={} len={} bins={} ghosts={} code={}",
                    charge,
                    stable_mode,
                    watches.len(),
                    bins,
                    ghosts,
                    code
                );
                if let Ok(t) = std::env::var("NIXIE_CSR_CONTENT_TRACE")
                    && t == code.to_string()
                {
                    let refs: Vec<String> = if let Some((_, sc, ov)) = b_prepared.as_ref() {
                        sc.iter()
                            .chain(ov.iter())
                            .map(|w| format!("{}:{}", w.r.byte_offset(), w.blocker.code()))
                            .collect()
                    } else {
                        watches
                            .iter()
                            .map(|w| format!("{}:{}", w.r.byte_offset(), w.blocker.code()))
                            .collect()
                    };
                    eprintln!("[content] code={} refs={:?}", code, refs);
                }
            }
            // Swapped-state preparation (fallible, unwrap-free): copy the
            // span out and take the overflow so the kernel's CSR access
            // never aliases the scanned segments.
            let swapped_prepared: Option<(usize, Vec<Watcher>, Vec<Watcher>)> = if swapped {
                csr.as_mut().map(|c| {
                    let (start, span, ovf_slot) = c.scan_parts(code);
                    (start, span.to_vec(), std::mem::take(ovf_slot))
                })
            } else {
                None
            };
            #[allow(unused_mut)]
            let mut result = if let Some((span_start, span_copy, mut ovf)) = b_prepared {
                // Commit-B arm: the CSR is the sole representation — no
                // Vec mirror, pushes/dedups land in the CSR (the kernel's
                // const-B instantiation), and the kept prefixes (unvisited
                // tails on conflict included) are written back structurally.
                let r1 = list_kernel::scan_list::<false, true>(
                    &mut span_copy[..],
                    !lit,
                    values,
                    &mut queue,
                    arena.reborrow(),
                    destinations,
                    csr,
                    None,
                    None,
                );
                if let Some(c) = csr.as_mut() {
                    c.write_back_span(code, span_start, &span_copy[..r1.write]);
                    c.commit_span_end(code, r1.write);
                }
                let mut r2 = list_kernel::ScanResult::default();
                let ovf_write = if r1.conflict.is_null() {
                    r2 = list_kernel::scan_list::<false, true>(
                        &mut ovf,
                        !lit,
                        values,
                        &mut queue,
                        arena.reborrow(),
                        destinations,
                        csr,
                        None,
                        None,
                    );
                    r2.write
                } else {
                    // Conflict in the span pass: the overflow was never
                    // visited — it returns UNTRUNCATED (the unvisited
                    // tail), exactly as the Vec side's finish() did.
                    ovf.len()
                };
                if let Some(c) = csr.as_mut() {
                    c.put_back_overflow(code, ovf, ovf_write);
                }
                let mut merged = r1;
                if merged.conflict.is_null() {
                    merged.conflict = r2.conflict;
                    #[cfg(feature = "bcp-work")]
                    {
                        merged.work.take_watch_scan(&mut r2.work);
                    }
                }
                merged.write = watches_len;
                merged
            } else if let Some((span_start, mut span_copy, mut ovf)) = swapped_prepared {
                let mut vm = crate::watched::VecScanMirror::new(&mut watches);
                let r1 = list_kernel::scan_list::<false, false>(
                    &mut span_copy,
                    !lit,
                    values,
                    &mut queue,
                    arena.reborrow(),
                    destinations,
                    csr,
                    Some(&mut vm),
                    Some(code),
                );
                // Copy the compacted span home and commit its live end.
                if let Some(c) = csr.as_mut() {
                    c.write_back_span(code, span_start, &span_copy[..r1.write]);
                    c.commit_span_end(code, r1.write);
                }
                let mut r2 = list_kernel::ScanResult::default();
                let ovf_write = if r1.conflict.is_null() {
                    r2 = list_kernel::scan_list::<false, false>(
                        &mut ovf,
                        !lit,
                        values,
                        &mut queue,
                        arena.reborrow(),
                        destinations,
                        csr,
                        Some(&mut vm),
                        Some(code),
                    );
                    r2.write
                } else {
                    // Conflict in the span pass: the overflow was never
                    // visited — it returns UNTRUNCATED (the unvisited
                    // tail), exactly as the Vec side does via the mirror.
                    ovf.len()
                };
                if let Some(c) = csr.as_mut() {
                    c.put_back_overflow(code, ovf, ovf_write);
                }
                vm.finish();
                let mut merged = r1;
                if merged.conflict.is_null() {
                    merged.conflict = r2.conflict;
                    // Both passes' work counters accumulate (the old
                    // single-pass scan would have counted them together).
                    #[cfg(feature = "bcp-work")]
                    {
                        merged.work.take_watch_scan(&mut r2.work);
                    }
                }
                merged.write = watches.len();
                merged
            } else if watches.is_empty() {
                list_kernel::ScanResult::default()
            } else {
                list_kernel::scan_list::<MIRROR, false>(
                    &mut watches,
                    !lit,
                    values,
                    &mut queue,
                    arena.reborrow(),
                    destinations,
                    csr,
                    None,
                    None,
                )
            };
            #[cfg(feature = "bcp-work")]
            self.stats
                .propagation_work
                .take_watch_scan(&mut result.work);
            if b_mode {
                crate::mut_trace!(
                    code,
                    "side=vec act=end_scan kept={} path=session_putback",
                    result.write
                );
            } else {
                watches.truncate(result.write);
                crate::mut_trace!(
                    code,
                    "side=vec act=end_scan kept={} path=session_putback",
                    watches.len()
                );
                destinations[code] = watches;
                if MIRROR
                    && !swapped
                    && let Some(c) = csr.as_mut()
                {
                    c.end_scan();
                }
            }
            if !result.conflict.is_null() {
                #[cfg(feature = "std")]
                if crate::env_flags::conflict_trace() {
                    eprintln!("[conf] code={} cid={}", code, result.conflict.index());
                }
                queue.requeue();
                return Some(result.conflict);
            }
        }
        None
    }
}
