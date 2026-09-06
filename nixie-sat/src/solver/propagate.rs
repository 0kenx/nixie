//! Unit propagation (BCP) and binary implication graph

use super::*;
#[cfg(feature = "profiling")]
use crate::profiling::{ProfilingCategory, ScopedTimer};

impl Solver {
    /// Unit propagation using two-watched literals
    ///
    /// Updates the current watch list in place so propagation does not rebuild
    /// the list through repeated pushes into a freshly emptied buffer.
    pub(super) fn propagate(&mut self) -> Option<ClauseId> {
        #[cfg(feature = "profiling")]
        let _timer = ScopedTimer::new(ProfilingCategory::SatPropagation);
        // Hoist the bounded check out of the hot loop: a single predictable
        // branch at loop entry instead of an Option pattern match per
        // propagation step (the limit is always None during search).
        let bounded = self.propagate_step_limit.is_some();
        while let Some(lit) = self.trail.next_to_propagate() {
            self.stats.propagations += 1;

            if bounded && let Some(ref mut limit) = self.propagate_step_limit {
                if *limit == 0 {
                    self.propagate_aborted = true;
                    return None;
                }
                *limit -= 1;
            }

            // First, propagate binary implications (faster).
            //
            // The trigger's edges live in the BIG's CSR primary span plus
            // its post-build overflow; both are iterated by index (one
            // copied edge per step) so no borrow is held across the `&mut
            // self` calls below. Span layout and overflow length are
            // snapshotted up front — nothing can move or append under
            // `lit` while it propagates (the single-threaded invariant the
            // old take/put-back version documented: the only mid-
            // propagation append source is hyper-binary resolution, which
            // keys its new edges under negations of literals *other than*
            // `lit`), and deletions never run inside propagation.
            //
            // Most propagated literals have no binary implications at all –
            // the `is_empty` probe keeps the common case down to two
            // length loads instead of the full loop setup.
            if !self.binary_graph.get(lit).is_empty() {
                let code = lit.code() as usize;
                let (span_start, plen) = self.binary_graph.span_of(code);
                let xlen = self.binary_graph.extra_len(code);
                for i in 0..plen + xlen {
                    let (implied_lit, clause_id) = if i < plen {
                        self.binary_graph.edge_at(span_start + i)
                    } else {
                        self.binary_graph.extra_at(code, i - plen)
                    };
                    // Binary clauses are never deleted during search
                    // (reduce_clause_database skips len<=2 clauses), so edges in
                    // the binary implication graph are always valid. The previous
                    // per-edge validation (clauses.get + 2x contains) was a major
                    // BCP bottleneck – ~5 ops per binary edge per propagation.
                    // In incremental mode (pop/forget), edges could go stale; that
                    // path would need edge invalidation, not per-propagation checks.

                    let value = self.trail.lit_val(implied_lit);
                    if value < 0 {
                        // Conflict in binary clause. `lit`'s remaining implication
                        // edges (and its whole watch list) have not been examined,
                        // so requeue the literal (see
                        // `Trail::requeue_last_propagated`; preserves the
                        // propagation-queue contract so a later solve() re-visits
                        // it and rescans those edges).
                        self.note_conflict_prefix();
                        self.trail.requeue_last_propagated();
                        return Some(clause_id);
                    } else if value == 0 {
                        // Propagate.
                        //
                        // No lazy hyper-binary resolution here: the reason is
                        // a binary clause (the BIG edge being traversed), and
                        // `check_hyper_binary_resolution` provably cannot
                        // learn anything from one — the resolvent of a binary
                        // clause against the conflicting clause is what the
                        // ordinary conflict path already learns.  Skipping the
                        // call removes 6-31% of all scans on BIG-heavy
                        // instances with bit-identical search trajectories;
                        // the same filter *inside* the function was measured
                        // (upstream v0.3.3) to change *which* clauses get
                        // learned, because a binary clause can also propagate
                        // from the watch lists where the BIG edge may not
                        // exist.
                        self.trail.assign_propagation(implied_lit, clause_id);
                        // LRAT: flush level-0 propagations to explicit derived units
                        // so every level-0 literal carries a unit id.
                        if self.lrat && self.trail.decision_level() == 0 {
                            self.flush_level0_unit(implied_lit, clause_id);
                        }
                    }
                }
            }

            // Take the current watch list, mutate it in place, then move it
            // back once propagation for this literal is finished.
            let mut watches = core::mem::take(self.watches.get_mut(lit));
            // cadical tick formula: ticks += 1 + cache_lines(ws.size, sizeof(Watcher)).
            //
            // NOTE: deliberately counts 8 bytes/watcher even though our
            // `Watcher` is 12 (id + arena slot + blocker). The tick counters
            // drive restart/mode-switch schedules – changing the accounting
            // changes the search trajectory, which makes every before/after
            // measurement a different-search comparison. Any correction here
            // must go through the matched-null methodology in
            // docs/BENCHMARKING.md first.
            //
            // Binary clauses left the watch lists (BIG-authoritative BCP,
            // 2026-09) but MUST still be counted here: the phantom counter
            // models exactly the binary entries the old scheme scanned
            // (attach/rebuild bump it; retirement leaves it lingering, as the
            // old entries lingered) so the schedules stay bit-identical.
            let phantom_bins = self.watches.phantom_len(lit);
            let ticks = 1u64 + (((watches.len() + phantom_bins) as u64) * 8).div_ceil(128);
            if self.stable {
                self.ticks_stable = self.ticks_stable.saturating_add(ticks);
            } else {
                self.ticks_focused = self.ticks_focused.saturating_add(ticks);
            }
            let mut conflict_found: Option<ClauseId> = None;

            // Two-pointer in-place compaction (cadical-style): read pointer
            // scans all watchers; write pointer only advances for kept ones.
            // Eliminates swap_remove (2 writes per removal → 0) and enables
            // bounds-check elision on the read index (0..len range).
            let mut write = 0usize;

            for read in 0..watches.len() {
                let watcher = watches[read];

                if self.trail.lit_val_hot(watcher.blocker) > 0 {
                    // Kept watcher. While `write == read` (no watcher dropped
                    // yet in this scan) the write-back would be a pure
                    // self-write — skip it; the compaction copy is only
                    // needed once the pointers have split.
                    if write != read {
                        watches[write] = watcher;
                    }
                    write += 1;
                    continue;
                }

                // Direct arena addressing: the watcher carries the clause's
                // slot (`Watcher::r`), so a visit costs one dependent load
                // (the clause itself) instead of two (refs table, then
                // clause). Validation is unchanged: bounds + deleted flag,
                // with deleted/invalid slots reading as "no clause" exactly
                // like the id-based path.
                let clause = match self.clauses.live_lits_by_ref(watcher.r) {
                    Some(lits) => lits,
                    None => {
                        // Deleted clause – drop (don't advance write).
                        continue;
                    }
                };

                // Make sure the false literal is at position 1. The
                // normalization is kept UNCONDITIONAL (not on-demand): a
                // pilot that left the watched pair in visit order on the
                // satisfied/satrepl paths diverged 34/54 corpus trajectories
                // — stored order is observable beyond direct `lits[0]`
                // readers (watch-rank tie-breaks, first-wins scans in
                // vivify/probe/els), so the two arena stores stay on every
                // miss visit. See
                // `studies/2026-09-propagate-write-elision.md` (slice a,
                // reverted).
                if clause[0] == lit.negate() {
                    clause.swap(0, 1);
                }

                // If first watch is true, clause is satisfied
                let first = clause[0];
                if self.trail.lit_val_hot(first) > 0 {
                    if write != read {
                        watches[write] = watcher;
                    }
                    // Refresh only the blocker word (the other two words are
                    // unchanged; while `write == read` a full write-back
                    // would be a pure self-write).
                    watches[write].blocker = first;
                    write += 1;
                    continue;
                }

                // Look for a replacement watch, separating the satisfied
                // case from the unassigned case (cadical `propagate.cpp`'s
                // `if (v > 0) j[-1].blit = r` / `else if (!v) ...` pair):
                //
                // * a **satisfied** replacement literal means the clause
                //   cannot become unit or conflict before a backtrack —
                //   the watcher STAYS on this list and only its blocker is
                //   refreshed. No clause write, no watch-list move; the
                //   next visit short-circuits on the blocker byte instead
                //   of re-scanning the clause.
                // * only an **unassigned** replacement moves the watch to
                //   the new literal's list (the watch must track a
                //   non-false literal to preserve the two-watch
                //   invariant).
                //
                // The previous `>= 0` branch moved the watch in both cases,
                // paying a clause swap plus a cross-list push for every
                // satisfied replacement — the larger half of the blocker
                // gap measured against cadical (55% hit rate: watchers
                // parked on satisfied literals kept stale blockers).
                let mut found = false;
                for j in 2..clause.len() {
                    let l = clause[j];
                    let v = self.trail.lit_val_hot(l);
                    if v > 0 {
                        // Satisfied replacement: keep the watcher here,
                        // refresh the blocker to the satisfied literal
                        // (blocker word only).
                        if write != read {
                            watches[write] = watcher;
                        }
                        watches[write].blocker = l;
                        write += 1;
                        found = true;
                        break;
                    }
                    if v == 0 {
                        // Unassigned replacement: move the watch (the
                        // conditional swap above already normalized
                        // `lits[0]` to the non-false watch).
                        clause.swap(1, j);
                        self.watches.add(
                            clause[1].negate(),
                            Watcher {
                                blocker: first,
                                ..watcher
                            },
                        );
                        found = true;
                        break;
                    }
                }

                if found {
                    continue; // handled: parked-with-fresh-blocker or moved
                }

                // No new watch found - clause is unit or conflicting
                if write != read {
                    watches[write] = watcher;
                }
                watches[write].blocker = first;

                if self.trail.lit_val_hot(first) < 0 {
                    conflict_found = Some(watcher.clause);
                    write += 1; // keep the conflicting watcher
                    // Copy remaining watchers to preserve them
                    for rest in read + 1..watches.len() {
                        watches[write] = watches[rest];
                        write += 1;
                    }
                    break;
                } else {
                    // Unit propagation
                    self.trail.assign_propagation(first, watcher.clause);
                    // Diagnostic (`NIXIE_REASON_STATS`): classify each BCP
                    // propagation by whether its reason clause was learned.
                    // Cold: one extra clause-header read per assignment, only
                    // when the env gate is set (search-shape studies).
                    if Self::reason_stats_enabled() && !watcher.clause.is_null() {
                        self.count_reason_origin(watcher.clause);
                    }
                    // LRAT: flush level-0 propagations to explicit derived units.
                    if self.lrat && self.trail.decision_level() == 0 {
                        self.flush_level0_unit(first, watcher.clause);
                    }

                    // Lazy hyper-binary resolution
                    if self.config.enable_lazy_hyper_binary {
                        self.check_hyper_binary_resolution(lit, first, watcher.clause);
                    }

                    write += 1;
                }
            }

            watches.truncate(write);

            *self.watches.get_mut(lit) = watches;

            if let Some(conflict) = conflict_found {
                // The watch list was abandoned mid-scan, so `lit` is only
                // partially propagated. Re-queue it so the invariant "everything
                // before the head is fully propagated" survives the abort – see
                // `Trail::requeue_last_propagated`.
                self.note_conflict_prefix();
                self.trail.requeue_last_propagated();
                return Some(conflict);
            }
        }

        // Clean fixpoint: the entire trail propagated without conflict
        // (cadical `no_conflict_until = propagated`). Not recorded when a
        // step-limit abort stopped propagation early – the trail is *not*
        // known to be conflict-free past the head.
        if !self.propagate_aborted {
            self.no_conflict_until = self.trail.size();
        }

        None
    }

    /// cadical's conflict-side update of `no_conflict_until`: the trail
    /// *before the current decision level* propagated without conflict, so
    /// that prefix is the material `update_target_and_best` snapshots into
    /// the target/best phase arrays at the next backtrack
    /// (`no_conflict_until = control[level].trail`). Also counts
    /// `stats.stable_conflicts` exactly where cadical counts
    /// `stats.stabconflicts` (propagate.cpp).
    fn note_conflict_prefix(&mut self) {
        if self.stable {
            self.stats.stable_conflicts += 1;
        }
        self.no_conflict_until = self.trail.level_start(self.trail.decision_level());
    }

    /// Check for hyper-binary resolution opportunity
    /// When propagating `implied` due to `lit` being assigned, check if we can
    /// learn a binary clause by resolving the reason clauses
    pub(super) fn check_hyper_binary_resolution(
        &mut self,
        _lit: Lit,
        implied: Lit,
        reason_id: ClauseId,
    ) {
        // Only check at higher decision levels to avoid overhead
        if self.trail.decision_level() < 2 {
            return;
        }

        // Get the reason clause
        let reason_clause = match self.clauses.get(reason_id) {
            Some(c) if c.lits.len() >= 2 && c.lits.len() <= 4 => c.lits.to_vec(),
            _ => return,
        };

        // Check if we can derive a binary clause
        // Look for literals in the reason clause that are assigned at the current level
        let current_level = self.trail.decision_level();
        let mut current_level_lits = SmallVec::<[Lit; 4]>::new();
        let mut has_non_zero_level_other = false;

        for &reason_lit in reason_clause.iter() {
            if reason_lit != implied {
                // Only a literal that is *assigned false* may be resolved away:
                // the derivation below drops every other literal on the grounds
                // that the clause already forces `implied` once they are false.
                //
                // Checking the level alone is not enough, because `Trail` leaves
                // `VarInfo.level` stale when a variable is unassigned (the same
                // trap documented in `analyze_theory_conflict`).  An unassigned
                // literal whose stale level happens to be 0 was silently read as
                // "false at level 0" and resolved away, so the learned binary
                // dropped a literal that was not false at all.  That clause is
                // not implied by the formula, and since it goes straight into the
                // binary implication graph – where it both propagates and serves
                // as a conflict reason – it yields a wrong top-level UNSAT on
                // satisfiable input (QF_UF quasigroup `iso_brn*`).
                if !self.trail.lit_value(reason_lit).is_false() {
                    return;
                }
                let var = reason_lit.var();
                let level = self.trail.level(var);
                if level == current_level {
                    current_level_lits.push(reason_lit);
                } else if level > 0 {
                    // There's a literal at a non-zero level other than current
                    // This means the learned clause would depend on that assignment
                    // which is not safe for incremental solving
                    has_non_zero_level_other = true;
                }
            }
        }

        // If there's exactly one literal from the current level besides the implied one,
        // and all others are at level 0, we can safely learn a binary clause.
        // IMPORTANT: We must ensure ALL other literals are at level 0 for the learned
        // clause to be valid when new constraints are added incrementally.
        if current_level_lits.len() == 1 && !has_non_zero_level_other {
            let other_lit = current_level_lits[0];

            // Check if we can create a useful binary clause
            // The reason clause had other_lit FALSE and implied it. So we learn:
            // other_lit | implied (if other_lit is false, implied must be true)
            let binary_clause_lits = [other_lit, implied];

            // Check if this binary clause is new and useful
            // The binary clause is: other_lit | implied
            // This means: ~other_lit -> implied, and ~implied -> other_lit
            if !self.has_binary_implication(other_lit.negate(), implied) {
                // Learn this binary clause on-the-fly
                let clause_id = self.clauses.add_learned(binary_clause_lits.iter().copied());

                // Register the clause in the two ledgers that make a learned
                // clause retractable, exactly as the main CDCL loop's 1-UIP
                // learning step does – see `Solver::solve` in `solver/mod.rs`,
                // which pushes to `learned_clause_ids` *and* to the current
                // assertion level's list in both its unit and its general
                // branch.  (`Solver::learn_clause` in `solver/learn.rs`, used
                // by the alternative search drivers in `search_ext.rs`, records
                // only the first of the two; the two-ledger form is the one
                // that keeps `pop` able to take the clause back, so it is the
                // one copied here.)
                //
                // This site used to write to neither ledger, and an
                // unregistered learned clause is invisible to every mechanism
                // that is supposed to be able to take a learned clause back:
                //
                // * `learned_clause_count()` reports `learned_clause_ids.len()`,
                //   so callers computing "originals" as
                //   `num_clauses() - learned_clause_count()` counted these as
                //   *original* clauses – the whole reported symptom of task #28
                //   ("repeated check-sat grows the original clause database").
                // * `forget_learned_since` splits `learned_clause_ids`, so the
                //   bit-vector theory's incremental safety net (see its doc
                //   comment) could not forget them.
                // * `pop` removes only the ids listed for the popped assertion
                //   level, so they outlived the assertion scope they were
                //   derived in.  That last one is not merely accounting: the
                //   resolution that produces `other_lit | implied` discharges
                //   the reason clause's remaining literals because they are
                //   false *at level 0*, and level-0 facts here are only
                //   level-0 for the current assertion scope – `add_clause`
                //   installs a unit as a level-0 trail assignment and `pop`
                //   rolls the trail back.  A surviving hyper-binary clause
                //   whose level-0 premises have just been retracted is no
                //   longer implied by the remaining constraints.
                self.learned_clause_ids.push(clause_id);
                if let Some(current_level_clauses) = self.assertion_clause_ids.last_mut() {
                    current_level_clauses.push(clause_id);
                }

                // Add correct implications: ~A -> B and ~B -> A for clause (A | B)
                self.binary_graph
                    .add(other_lit.negate(), implied, clause_id);
                self.binary_graph
                    .add(implied.negate(), other_lit, clause_id);
                self.stats.learned_clauses += 1;

                // Every other `add_learned` call site computes and stores an LBD
                // (see `Solver::compute_lbd`'s call sites in `solve` and
                // `learn_clause`); this on-the-fly path used to be an exception,
                // leaving `clause.lbd` at `Clause::learned`'s default of 0
                // forever. `Clause::record_usage` promotes a clause straight to
                // the rarely-deleted `Core` tier once `lbd <= 2`, so a stuck LBD
                // of 0 gave every hyper-binary-resolution clause an artificially
                // easy path into permanent retention regardless of its actual
                // quality.
                let lbd = self.compute_lbd(&binary_clause_lits);
                self.clauses.set_lbd(clause_id, lbd);
                self.debug_check_learned_clause_lbd(clause_id);
            }
        }
    }

    /// Check if a binary implication already exists
    pub(super) fn has_binary_implication(&self, from_lit: Lit, to_lit: Lit) -> bool {
        self.binary_graph
            .get(from_lit)
            .iter()
            .any(|(lit, _)| *lit == to_lit)
    }

    /// `NIXIE_REASON_STATS` gate (search-shape diagnostics only).
    #[cfg(feature = "std")]
    pub(super) fn reason_stats_enabled() -> bool {
        use std::sync::OnceLock;
        static FLAG: OnceLock<bool> = OnceLock::new();
        *FLAG.get_or_init(|| {
            std::env::var("NIXIE_REASON_STATS").is_ok_and(|v| !v.is_empty() && v != "0")
        })
    }
    #[cfg(not(feature = "std"))]
    pub(super) fn reason_stats_enabled() -> bool {
        false
    }

    /// Classify one BCP propagation by the origin of its reason clause
    /// (`NIXIE_REASON_STATS`). Counters live in `lib.rs` so the stats harness
    /// can read them at exit.
    #[cfg(feature = "std")]
    pub(super) fn count_reason_origin(&mut self, cid: crate::clause::ClauseId) {
        let learned = self.clauses.get(cid).map(|v| v.learned).unwrap_or(false);
        if learned {
            crate::DIAG_REASON_LEARNED.fetch_add(1, core::sync::atomic::Ordering::Relaxed);
        } else {
            crate::DIAG_REASON_ORIGINAL.fetch_add(1, core::sync::atomic::Ordering::Relaxed);
        }
    }
    #[cfg(not(feature = "std"))]
    pub(super) fn count_reason_origin(&mut self, _cid: crate::clause::ClauseId) {}
}
