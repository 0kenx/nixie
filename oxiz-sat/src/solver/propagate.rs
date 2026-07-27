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
        while let Some(lit) = self.trail.next_to_propagate() {
            self.stats.propagations += 1;

            // Bounded propagation for preprocessing: bail (as "no conflict, but
            // incomplete") once the step budget is exhausted, so a single doomed
            // cascade can't run unbounded. The real search leaves this `None`.
            if let Some(ref mut limit) = self.propagate_step_limit {
                if *limit == 0 {
                    self.propagate_aborted = true;
                    return None;
                }
                *limit -= 1;
            }

            // First, propagate binary implications (faster)
            let binary_len = self.binary_graph.get(lit).len();
            for idx in 0..binary_len {
                let (implied_lit, clause_id) = self.binary_graph.get(lit)[idx];

                // The binary implication graph is a fast-path index over binary
                // clauses, but its edges are never removed when a clause is
                // retracted by pop()/forget_learned_since()/subsumption, and
                // freed clause slots are reused for new clauses. A stale edge
                // would keep propagating (or reporting conflicts from) a clause
                // that no longer exists — or, after slot reuse, from an unrelated
                // live clause — yielding false UNSAT in incremental solving.
                // Only trust an edge still backed by a live binary clause
                // {~lit, implied_lit}; skip (and thereby ignore) any other edge.
                let backed = match self.clauses.get(clause_id) {
                    Some(c) => {
                        !c.deleted
                            && c.lits.len() == 2
                            && c.lits.contains(&lit.negate())
                            && c.lits.contains(&implied_lit)
                    }
                    None => false,
                };
                if !backed {
                    continue;
                }

                let value = self.trail.lit_value(implied_lit);
                if value.is_false() {
                    // Conflict in binary clause. `lit`'s remaining implication
                    // edges (and its whole watch list) have not been examined,
                    // so put it back on the queue before bailing out — see
                    // `Trail::requeue_last_propagated`.
                    self.trail.requeue_last_propagated();
                    return Some(clause_id);
                } else if !value.is_defined() {
                    // Propagate
                    self.trail.assign_propagation(implied_lit, clause_id);

                    // Lazy hyper-binary resolution: check if we can learn a binary clause
                    if self.config.enable_lazy_hyper_binary {
                        self.check_hyper_binary_resolution(lit, implied_lit, clause_id);
                    }
                }
            }

            // Take the current watch list, mutate it in place, then move it
            // back once propagation for this literal is finished.
            let mut watches = core::mem::take(self.watches.get_mut(lit));
            // cadical tick formula: ticks += 1 + cache_lines(ws.size, sizeof(Watcher)).
            // sizeof(Watcher) = 8; cache_lines(n, 8) = (n*8 + 127) / 128.
            let ticks = 1u64 + (watches.len() as u64 * 8 + 127) / 128;
            if self.stable {
                self.ticks_stable = self.ticks_stable.saturating_add(ticks);
            } else {
                self.ticks_focused = self.ticks_focused.saturating_add(ticks);
            }
            let mut conflict_found: Option<ClauseId> = None;
            let mut watch_idx = 0;

            while watch_idx < watches.len() {
                let watcher = watches[watch_idx];

                if self.trail.lit_value(watcher.blocker).is_true() {
                    watch_idx += 1;
                    continue;
                }

                let clause = match self.clauses.get_mut(watcher.clause) {
                    Some(c) if !c.deleted => c,
                    _ => {
                        // Deleted clause - remove its watcher in place.
                        watches.swap_remove(watch_idx);
                        continue;
                    }
                };

                // Make sure the false literal is at position 1
                if clause.lits[0] == lit.negate() {
                    clause.swap(0, 1);
                }

                // If first watch is true, clause is satisfied
                let first = clause.lits[0];
                if self.trail.lit_value(first).is_true() {
                    watches[watch_idx] = Watcher::new(watcher.clause, first);
                    watch_idx += 1;
                    continue;
                }

                // Look for a new watch
                let mut found = false;
                for j in 2..clause.lits.len() {
                    let l = clause.lits[j];
                    if !self.trail.lit_value(l).is_false() {
                        clause.swap(1, j);
                        self.watches
                            .add(clause.lits[1].negate(), Watcher::new(watcher.clause, first));
                        watches.swap_remove(watch_idx);
                        found = true;
                        break;
                    }
                }

                if found {
                    continue;
                }

                // No new watch found - clause is unit or conflicting
                watches[watch_idx] = Watcher::new(watcher.clause, first);

                if self.trail.lit_value(first).is_false() {
                    conflict_found = Some(watcher.clause);
                    break;
                } else {
                    // Unit propagation
                    self.trail.assign_propagation(first, watcher.clause);

                    // Lazy hyper-binary resolution
                    if self.config.enable_lazy_hyper_binary {
                        self.check_hyper_binary_resolution(lit, first, watcher.clause);
                    }

                    watch_idx += 1;
                }
            }

            *self.watches.get_mut(lit) = watches;

            if let Some(conflict) = conflict_found {
                // The watch list was abandoned mid-scan, so `lit` is only
                // partially propagated. Re-queue it so the invariant "everything
                // before the head is fully propagated" survives the abort — see
                // `Trail::requeue_last_propagated`.
                self.trail.requeue_last_propagated();
                return Some(conflict);
            }
        }

        None
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
            Some(c) if c.lits.len() >= 2 && c.lits.len() <= 4 => c.lits.clone(),
            _ => return,
        };

        // Check if we can derive a binary clause
        // Look for literals in the reason clause that are assigned at the current level
        let current_level = self.trail.decision_level();
        let mut current_level_lits = SmallVec::<[Lit; 4]>::new();
        let mut has_non_zero_level_other = false;

        for &reason_lit in &reason_clause {
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
                // binary implication graph — where it both propagates and serves
                // as a conflict reason — it yields a wrong top-level UNSAT on
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
                // learning step does — see `Solver::solve` in `solver/mod.rs`,
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
                //   *original* clauses — the whole reported symptom of task #28
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
                //   level-0 for the current assertion scope — `add_clause`
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
                if let Some(clause) = self.clauses.get_mut(clause_id) {
                    clause.lbd = lbd;
                }
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
}
