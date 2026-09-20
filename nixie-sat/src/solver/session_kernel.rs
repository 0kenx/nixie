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
        let (destinations, phantom, ghost_debt, csr) = self.watches.propagation_parts();
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
            // THE FLIP: the slack-CSR is the primary on the default path.
            // The swapped-dual validation mode and the Vec-primary arm run
            // only under the `NIXIE_CSR_B=0` legacy opt-out, so the hot
            // path carries none of their branches.
            #[cfg(feature = "std")]
            let csr_arm = crate::watched::csr_b_enabled() && csr.is_some();
            #[cfg(not(feature = "std"))]
            let csr_arm = false;
            // Unified CSR-primary in-place scan (commit-B and swapped-dual
            // share it): the entries buffer splits around the scanned
            // literal's live span — the cursor scans the span in place
            // (no copy), pushes append into the head/tail halves at their
            // destination's live end, and the commit publishes the
            // compacted span.  A spilled literal's tail (if any) is
            // scanned second, on its detached Vec.
            let mut watches = if csr_arm {
                // CSR-primary: the CSR is the sole representation; the Vec
                // side stays dead (its lists empty).
                Vec::new()
            } else {
                core::mem::take(&mut destinations[code])
            };
            // The pre-scan combined length — computed BEFORE the spill
            // tail detaches (the charge drives restart/stable schedules;
            // an undercount here diverges the whole trajectory).
            let watches_len = if csr_arm {
                csr.as_ref()
                    .map_or(0, |c| c.len(Lit::from_code(code as u32)))
            } else {
                watches.len()
            };
            let mut fbv = if csr_arm {
                csr.as_mut().and_then(|c| c.take_fallback(code))
            } else {
                None
            };
            crate::mut_trace!(
                code,
                "side=vec act=begin_scan len={} path=session_take",
                watches_len
            );
            // Dual-write BCP scan (CSR slice 2): the Vec-primary mirror
            // path snapshots the split before the list is scanned.
            if MIRROR
                && !csr_arm
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
                    charge, stable_mode, watches_len, bins, ghosts, code
                );
                if let Ok(t) = std::env::var("NIXIE_CSR_CONTENT_TRACE")
                    && t == code.to_string()
                {
                    let refs: Vec<String> = if csr_arm {
                        let (p, x) = csr
                            .as_ref()
                            .map_or((&[] as &[Watcher], &[] as &[Watcher]), |c| {
                                c.spans(Lit::from_code(code as u32))
                            });
                        p.iter()
                            .chain(x.iter())
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
            let mut result = if csr_arm && let Some(c) = csr.as_mut() {
                let (span, mut ctx) = c.scan_split(code);
                // Primary mode: no Vec mirror, no Vec destinations — the
                // dest struct carries CSR only (the swapped-dual shape
                // survives behind the legacy opt-out for A/B validation).
                let swapped_dual = crate::watched::csr_scan_enabled();
                let mut vm = if swapped_dual {
                    Some(crate::watched::VecScanMirror::new(&mut watches))
                } else {
                    None
                };
                let mut vm_ref = vm.as_mut();
                let mut dest = list_kernel::CsrPartsDest {
                    ctx: &mut ctx,
                    vec_dest: if swapped_dual {
                        Some(&mut *destinations)
                    } else {
                        None
                    },
                };
                let r1 = list_kernel::scan_list(
                    span,
                    !lit,
                    values,
                    &mut queue,
                    arena.reborrow(),
                    &mut dest,
                    vm_ref.as_deref_mut(),
                );
                let mut r2 = list_kernel::ScanResult::default();
                if r1.conflict.is_null() {
                    if let Some(v) = fbv.as_deref_mut() {
                        r2 = list_kernel::scan_list(
                            v,
                            !lit,
                            values,
                            &mut queue,
                            arena.reborrow(),
                            &mut dest,
                            vm_ref,
                        );
                        v.truncate(r2.write);
                    }
                    if let Some(v) = fbv.take() {
                        dest.ctx.put_fallback(v);
                    }
                } else if let Some(fb) = fbv.take() {
                    // Conflict in the span pass: the spill tail was never
                    // visited — it returns UNTRUNCATED.
                    dest.ctx.put_fallback(fb);
                }
                dest.ctx.commit(r1.write);
                if let Some(vm) = vm {
                    vm.finish();
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
            } else if watches.is_empty() {
                list_kernel::ScanResult::default()
            } else {
                let mut dest = list_kernel::VecDest::<MIRROR> {
                    destinations: &mut *destinations,
                    csr: &mut *csr,
                    swapped: false,
                };
                list_kernel::scan_list(
                    &mut watches,
                    !lit,
                    values,
                    &mut queue,
                    arena.reborrow(),
                    &mut dest,
                    None,
                )
            };
            #[cfg(feature = "bcp-work")]
            self.stats
                .propagation_work
                .take_watch_scan(&mut result.work);
            if !csr_arm {
                // Legacy Vec world: the scanned list goes home.
                watches.truncate(result.write);
                destinations[code] = watches;
                if MIRROR && let Some(c) = csr.as_mut() {
                    c.end_scan();
                }
            } else if crate::watched::csr_scan_enabled() {
                // Swapped-dual validation: the mirror's reconstruction.
                watches.truncate(result.write);
                destinations[code] = watches;
            } else {
                crate::mut_trace!(
                    code,
                    "side=vec act=end_scan kept={} path=session_putback",
                    result.write
                );
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
