//! Clause learning, LBD computation, database reduction, inprocessing, and vivification

use super::*;
use smallvec::SmallVec;

impl Solver {
    /// Compute LBD (Literal Block Distance) of a clause
    /// LBD is the number of distinct decision levels in the clause
    pub(super) fn compute_lbd(&mut self, lits: &[Lit]) -> u32 {
        self.lbd_mark += 1;
        let mark = self.lbd_mark;

        let mut count = 0u32;
        for &lit in lits {
            let level = self.trail.level(lit.var()) as usize;
            if level < self.level_marks.len() && self.level_marks[level] != mark {
                self.level_marks[level] = mark;
                count += 1;
            }
        }

        count
    }

    /// Learn a clause and set up watches
    /// Includes on-the-fly subsumption check
    /// Tracks allocation via memory optimizer for size-class pool accounting
    pub(super) fn learn_clause(&mut self, learnt_clause: SmallVec<[Lit; 16]>) {
        // Track allocation in memory optimizer for pool accounting
        let _pool_buf = self.memory_optimizer.allocate(learnt_clause.len());

        // Record the learned clause in the DRAT proof (no-op unless enabled). It
        // is RUP-derivable from the current database by 1-UIP construction.
        self.drat_add(&learnt_clause);

        if learnt_clause.len() == 1 {
            // Store unit learned clause in database for persistence across backtracks
            let clause_id = self.clauses.add_learned(learnt_clause.iter().copied());
            self.stats.learned_clauses += 1;
            self.stats.unit_clauses += 1;
            self.learned_clause_ids.push(clause_id);

            self.trail.assign_decision(learnt_clause[0]);
        } else if learnt_clause.len() == 2 {
            // Binary learned clause - add to binary implication graph
            let lbd = self.compute_lbd(&learnt_clause);
            let clause_id = self.clauses.add_learned(learnt_clause.iter().copied());
            self.stats.learned_clauses += 1;
            self.stats.binary_clauses += 1;
            self.stats.total_lbd += lbd as u64;

            if let Some(clause) = self.clauses.get_mut(clause_id) {
                clause.lbd = lbd;
            }

            self.learned_clause_ids.push(clause_id);

            let lit0 = learnt_clause[0];
            let lit1 = learnt_clause[1];

            // Add to binary graph
            self.binary_graph.add(lit0.negate(), lit1, clause_id);
            self.binary_graph.add(lit1.negate(), lit0, clause_id);

            self.watches
                .add(lit0.negate(), Watcher::new(clause_id, lit1));
            self.watches
                .add(lit1.negate(), Watcher::new(clause_id, lit0));

            self.trail.assign_propagation(learnt_clause[0], clause_id);
        } else {
            let lbd = self.compute_lbd(&learnt_clause);
            self.stats.total_lbd += lbd as u64;
            let clause_id = self.clauses.add_learned(learnt_clause.iter().copied());
            self.stats.learned_clauses += 1;

            if let Some(clause) = self.clauses.get_mut(clause_id) {
                clause.lbd = lbd;
            }

            self.learned_clause_ids.push(clause_id);

            let lit0 = learnt_clause[0];
            let lit1 = learnt_clause[1];
            self.watches
                .add(lit0.negate(), Watcher::new(clause_id, lit1));
            self.watches
                .add(lit1.negate(), Watcher::new(clause_id, lit0));

            self.trail.assign_propagation(learnt_clause[0], clause_id);

            // On-the-fly subsumption: check if this new clause subsumes existing clauses
            if learnt_clause.len() <= 5 && lbd <= 3 {
                self.check_subsumption(clause_id);
            }
        }
    }

    /// Check if the given clause subsumes any existing clauses
    /// A clause C subsumes C' if all literals of C are in C'
    pub(super) fn check_subsumption(&mut self, new_clause_id: ClauseId) {
        let new_clause = match self.clauses.get(new_clause_id) {
            Some(c) => c.lits.clone(),
            None => return,
        };

        if new_clause.len() > 10 {
            return; // Don't check subsumption for large clauses (too expensive)
        }

        // Check against learned clauses only
        let mut to_remove = Vec::new();
        for &cid in &self.learned_clause_ids {
            if cid == new_clause_id {
                continue;
            }

            if let Some(clause) = self.clauses.get(cid) {
                if clause.deleted || clause.lits.len() < new_clause.len() {
                    continue;
                }

                // Check if new_clause subsumes clause
                if new_clause.iter().all(|&lit| clause.lits.contains(&lit)) {
                    to_remove.push(cid);
                }
            }
        }

        // Remove subsumed clauses
        for cid in to_remove {
            // Purge binary-graph edges and record the DRAT deletion before the
            // clause's literals become inaccessible.
            self.purge_binary_edges(cid);
            self.drat_delete(cid);
            self.clauses.remove(cid);
            self.stats.deleted_clauses += 1;
        }
    }

    /// Add a theory reason clause
    /// The clause is: reason_lits[0] OR reason_lits[1] OR ... OR propagated_lit
    pub(super) fn add_theory_reason_clause(
        &mut self,
        reason_lits: &[Lit],
        propagated_lit: Lit,
    ) -> ClauseId {
        let mut clause_lits: SmallVec<[Lit; 8]> = SmallVec::new();
        clause_lits.push(propagated_lit);
        for &lit in reason_lits {
            clause_lits.push(lit.negate());
        }

        let clause_id = self.clauses.add_learned(clause_lits.iter().copied());

        // Set up watches
        if clause_lits.len() >= 2 {
            let lit0 = clause_lits[0];
            let lit1 = clause_lits[1];
            self.watches
                .add(lit0.negate(), Watcher::new(clause_id, lit1));
            self.watches
                .add(lit1.negate(), Watcher::new(clause_id, lit0));
        }

        clause_id
    }

    /// Reduce the learned clause database using tier-based deletion strategy
    /// - Core tier (Tier 1): Rarely deleted, only if very inactive
    /// - Mid tier (Tier 2): Delete ~30% based on activity
    /// - Local tier (Tier 3): Delete ~75% based on activity
    pub(super) fn reduce_clause_database(&mut self) {
        use crate::clause::ClauseTier;

        let mut core_candidates: Vec<(ClauseId, f64)> = Vec::new();
        let mut mid_candidates: Vec<(ClauseId, f64)> = Vec::new();
        let mut local_candidates: Vec<(ClauseId, f64)> = Vec::new();

        for &cid in &self.learned_clause_ids {
            if let Some(clause) = self.clauses.get(cid) {
                if clause.deleted {
                    continue;
                }

                // Don't delete binary clauses (very useful)
                if clause.lits.len() <= 2 {
                    continue;
                }

                // Check if clause is currently a reason for any assignment
                // (We can't delete reason clauses)
                let is_reason = clause.lits.iter().any(|&lit| {
                    let var = lit.var();
                    if self.trail.is_assigned(var) {
                        matches!(self.trail.reason(var), Reason::Propagation(r) if r == cid)
                    } else {
                        false
                    }
                });

                if !is_reason {
                    match clause.tier {
                        ClauseTier::Core => core_candidates.push((cid, clause.activity)),
                        ClauseTier::Mid => mid_candidates.push((cid, clause.activity)),
                        ClauseTier::Local => local_candidates.push((cid, clause.activity)),
                    }
                }
            }
        }

        // Sort by activity (ascending) - delete low-activity clauses first
        core_candidates.sort_by(|a, b| a.1.partial_cmp(&b.1).unwrap_or(core::cmp::Ordering::Equal));
        mid_candidates.sort_by(|a, b| a.1.partial_cmp(&b.1).unwrap_or(core::cmp::Ordering::Equal));
        local_candidates
            .sort_by(|a, b| a.1.partial_cmp(&b.1).unwrap_or(core::cmp::Ordering::Equal));

        // Delete different percentages from each tier
        // Core: Delete bottom 10% (very conservative)
        let num_core_delete = core_candidates.len() / 10;
        // Mid: Delete bottom 30%
        let num_mid_delete = (mid_candidates.len() * 3) / 10;
        // Local: Delete bottom 75% (very aggressive)
        let num_local_delete = (local_candidates.len() * 3) / 4;

        for (cid, _) in core_candidates.iter().take(num_core_delete) {
            // Track clause size for memory pool accounting before removal
            if let Some(clause) = self.clauses.get(*cid) {
                let num_lits = clause.lits.len();
                let buf = self.memory_optimizer.allocate(num_lits);
                self.memory_optimizer.free(buf, num_lits);
            }
            self.drat_delete(*cid);
            self.clauses.remove(*cid);
            self.stats.deleted_clauses += 1;
        }

        for (cid, _) in mid_candidates.iter().take(num_mid_delete) {
            if let Some(clause) = self.clauses.get(*cid) {
                let num_lits = clause.lits.len();
                let buf = self.memory_optimizer.allocate(num_lits);
                self.memory_optimizer.free(buf, num_lits);
            }
            self.drat_delete(*cid);
            self.clauses.remove(*cid);
            self.stats.deleted_clauses += 1;
        }

        for (cid, _) in local_candidates.iter().take(num_local_delete) {
            if let Some(clause) = self.clauses.get(*cid) {
                let num_lits = clause.lits.len();
                let buf = self.memory_optimizer.allocate(num_lits);
                self.memory_optimizer.free(buf, num_lits);
            }
            self.drat_delete(*cid);
            self.clauses.remove(*cid);
            self.stats.deleted_clauses += 1;
        }

        // Clean up learned_clause_ids (remove deleted clauses)
        self.learned_clause_ids
            .retain(|&cid| self.clauses.get(cid).is_some_and(|c| !c.deleted));

        // Apply memory optimizer recommendations after deletion
        match self.memory_optimizer.recommend_action() {
            MemoryAction::Compact => {
                self.memory_optimizer.compact();
                self.clauses.compact();
            }
            MemoryAction::ReduceClauseDatabase => {
                // Already reduced; just compact the pool
                self.memory_optimizer.compact();
            }
            MemoryAction::ExpandPools | MemoryAction::None => {
                // No action needed
            }
        }
    }

    /// Handle clause deletion check and restart check
    pub(super) fn handle_clause_deletion_and_restart(&mut self) {
        self.conflicts_since_deletion += 1;

        if self.conflicts_since_deletion >= self.config.clause_deletion_threshold as u64 {
            self.reduce_clause_database();
            self.conflicts_since_deletion = 0;
        }

        if self.stats.conflicts >= self.restart_threshold {
            self.restart();
        }
    }

    /// Handle clause deletion and restart, but don't backtrack past assumptions
    pub(super) fn handle_clause_deletion_and_restart_limited(&mut self, min_level: u32) {
        self.conflicts_since_deletion += 1;

        if self.conflicts_since_deletion >= self.config.clause_deletion_threshold as u64 {
            self.reduce_clause_database();
            self.conflicts_since_deletion = 0;
        }

        if self.stats.conflicts >= self.restart_threshold {
            // Limited restart - don't backtrack past assumptions
            self.backtrack(min_level);
            self.stats.restarts += 1;
            self.luby_index += 1;
            self.restart_threshold =
                self.stats.conflicts + self.config.restart_interval * Self::luby(self.luby_index);
        }
    }

    /// Save the model
    pub(super) fn save_model(&mut self) {
        self.model.resize(self.num_vars, LBool::Undef);
        for i in 0..self.num_vars {
            self.model[i] = self.trail.value(Var::new(i as u32));
        }

        // Reconstruct pure literals eliminated during inprocessing. Their clauses
        // were deleted on the promise that the literal is fixed to its polarity;
        // the search may have assigned the variable the opposite phase, so force
        // it here. This can only satisfy additional clauses: no remaining clause
        // contains the opposite polarity (that is exactly what "pure" means).
        for &lit in &self.pure_literal_reconstruction {
            let idx = lit.var().index();
            if idx < self.model.len() {
                self.model[idx] = if lit.is_pos() {
                    LBool::True
                } else {
                    LBool::False
                };
            }
        }
    }

    /// Remove the literal at `idx` from a learned clause and rebuild its two
    /// watches so the two-watched-literal invariant is preserved.
    ///
    /// Vivification and inprocessing strengthening shrink a clause in place. If
    /// the removed literal sat at a watched position (index 0 or 1), the stale
    /// watcher would keep pointing at a literal no longer in the clause, breaking
    /// watch firing — a watched literal becoming false would no longer re-examine
    /// the clause, causing missed unit propagations and, if index 0 were removed
    /// repeatedly, a clause left effectively unwatched (a missed conflict). This
    /// detaches the old watches (always keyed on the pre-removal literals at
    /// positions 0 and 1), removes the literal, re-selects the two best watch
    /// literals (mirroring [`Solver::add_clause`]), and re-attaches them.
    pub(super) fn remove_literal_and_rewatch(&mut self, clause_id: ClauseId, idx: usize) {
        let mut lits: Vec<Lit> = match self.clauses.get(clause_id) {
            Some(c) if !c.deleted && c.lits.len() > 2 && idx < c.lits.len() => {
                c.lits.iter().copied().collect()
            }
            _ => return,
        };

        // Snapshot the pre-strengthening literals so the DRAT proof can retire the
        // original clause once the shorter (still F-entailed) form is recorded.
        let original_lits = lits.clone();

        // Detach the existing watches (keyed on the current positions 0 and 1).
        let old_w0 = lits[0];
        let old_w1 = lits[1];
        self.watches.remove_clause(old_w0.negate(), clause_id);
        self.watches.remove_clause(old_w1.negate(), clause_id);

        // Remove the redundant literal.
        lits.remove(idx);

        // Re-select the two best watch literals: prefer a satisfied literal, then
        // an unassigned one, and finally the latest-falsified. Mirrors
        // `Solver::add_clause` so a watched literal always fires when re-falsified.
        let n = lits.len();
        let mut best = 0;
        for i in 1..n {
            if self.watch_rank(lits[i]) > self.watch_rank(lits[best]) {
                best = i;
            }
        }
        lits.swap(0, best);
        let mut second = 1;
        for i in 2..n {
            if self.watch_rank(lits[i]) > self.watch_rank(lits[second]) {
                second = i;
            }
        }
        lits.swap(1, second);

        let w0 = lits[0];
        let w1 = lits[1];

        // Write the reordered literals back into the clause.
        if let Some(clause) = self.clauses.get_mut(clause_id) {
            clause.lits.clear();
            clause.lits.extend(lits.iter().copied());
        }

        // Re-attach watches on the new positions 0 and 1.
        self.watches.add(w0.negate(), Watcher::new(clause_id, w1));
        self.watches.add(w1.negate(), Watcher::new(clause_id, w0));

        // Record the in-place strengthening in the DRAT proof: add the shorter
        // clause (RUP-derivable — vivification proved it entailed) then delete the
        // original, keeping the proof's clause set consistent with the database.
        if self.drat.is_some() {
            let new_lits: SmallVec<[Lit; 8]> = lits.iter().copied().collect();
            self.drat_add(&new_lits);
            self.drat_delete_lits(&original_lits);
        }
    }

    /// Vivification: try to strengthen clauses by checking if some literals are redundant
    /// This is an inprocessing technique that should be called periodically
    pub(super) fn vivify_clauses(&mut self) {
        if self.trail.decision_level() != 0 {
            return; // Only vivify at decision level 0
        }

        let mut vivified_count = 0;
        let max_vivifications = 100; // Limit to avoid too much overhead

        // Try to vivify some learned clauses
        let clause_ids: Vec<ClauseId> = self
            .learned_clause_ids
            .iter()
            .copied()
            .take(max_vivifications)
            .collect();

        for clause_id in clause_ids {
            if vivified_count >= max_vivifications {
                break;
            }

            let clause_lits = match self.clauses.get(clause_id) {
                Some(c) if !c.deleted && c.lits.len() > 2 => c.lits.clone(),
                _ => continue,
            };

            // Try to find redundant literals in the clause
            // Assign all literals except one to false and see if we can derive the last one
            for skip_idx in 0..clause_lits.len() {
                // Save current state
                let saved_level = self.trail.decision_level();

                // Assign all literals except skip_idx to false
                self.trail.new_decision_level();
                let mut conflict = false;

                for (i, &lit) in clause_lits.iter().enumerate() {
                    if i == skip_idx {
                        continue;
                    }

                    let value = self.trail.lit_value(lit);
                    if value.is_true() {
                        // Clause is already satisfied
                        conflict = false;
                        break;
                    } else if value.is_false() {
                        // Already false
                        continue;
                    } else {
                        // Assign to false
                        self.trail.assign_decision(lit.negate());

                        // Propagate
                        if self.propagate().is_some() {
                            conflict = true;
                            break;
                        }
                    }
                }

                // Backtrack
                self.backtrack(saved_level);

                if conflict {
                    // The literal at skip_idx is implied by the rest, so it can
                    // be dropped (vivification succeeded). Remove it *and* rebuild
                    // the clause's watches so the two-watched invariant survives.
                    let removable = self
                        .clauses
                        .get(clause_id)
                        .is_some_and(|c| !c.deleted && c.lits.len() > 2 && skip_idx < c.lits.len());
                    if removable {
                        self.remove_literal_and_rewatch(clause_id, skip_idx);
                        vivified_count += 1;
                        break; // Done with this clause
                    }
                }
            }
        }
    }

    /// Perform inprocessing (apply preprocessing during search)
    pub(super) fn inprocess(&mut self) {
        use crate::Preprocessor;

        // Only inprocess at decision level 0
        if self.trail.decision_level() != 0 {
            return;
        }

        // Create preprocessor with current number of variables
        let mut preprocessor = Preprocessor::new(self.num_vars);

        // Snapshot every live clause's literals before the elimination passes
        // below run. `Preprocessor::pure_literal_elimination` and
        // `subsumption_elimination` retire clauses by setting `Clause::deleted`
        // directly on `self.clauses` (they don't go through
        // `ClauseDatabase::remove`) and report only a count, not which ids were
        // touched. `drat_delete(id)` can't be used afterwards either — by
        // design it refuses to read literals off a clause already marked
        // deleted, to avoid ever emitting a deletion line with garbage
        // literals. Without this snapshot the deletions below would never
        // reach the DRAT proof: the checker would still accept the proof (an
        // omitted deletion hint only makes it larger, never invalid), but the
        // proof would keep clauses the live database no longer has, which is
        // exactly the minimality gap this snapshot closes. Skipped entirely
        // when proof logging is off.
        let pre_lits: Vec<(ClauseId, SmallVec<[Lit; 8]>)> = if self.drat.is_some() {
            self.clauses
                .iter_ids()
                .filter_map(|id| {
                    self.clauses
                        .get(id)
                        .map(|c| (id, c.lits.iter().copied().collect()))
                })
                .collect()
        } else {
            Vec::new()
        };

        // Pure-literal elimination deletes original clauses; that is only
        // satisfiability-preserving if the pure literal is fixed to its polarity
        // in the reconstructed model. It is also unsound across incremental
        // scopes, where a later `add_clause` could reintroduce the opposite
        // polarity after the clauses were dropped, so it is only run at the base
        // assertion level (no active `push`).
        if self.assertion_levels.len() <= 1 {
            let _pure_elim = preprocessor.pure_literal_elimination(&mut self.clauses);
            // Record each eliminated pure literal so `save_model` can fix it to
            // `true`, keeping the deleted clauses satisfied even if the search
            // later assigns the variable the opposite phase. Keep at most one
            // polarity per variable (the first recorded).
            for &lit in preprocessor.eliminated_pure_literals() {
                let already = self
                    .pure_literal_reconstruction
                    .iter()
                    .any(|existing| existing.var() == lit.var());
                if !already {
                    self.pure_literal_reconstruction.push(lit);
                }
            }
        }

        let _subsumption = preprocessor.subsumption_elimination(&mut self.clauses);

        // Emit a DRAT deletion line for every clause the two passes above
        // retired, identified by diffing against the pre-pass snapshot (any
        // previously-live clause that is now deleted).
        for (id, lits) in &pre_lits {
            if self.clauses.get(*id).is_some_and(|c| c.deleted) {
                self.drat_delete_lits(lits);
            }
        }

        // On-the-fly clause strengthening
        self.strengthen_clauses_inprocessing();

        // Rebuild watch lists for any modified clauses
        // This is a simplified approach - in a full implementation,
        // we would track which clauses were removed and update watches incrementally
    }

    /// On-the-fly clause strengthening during inprocessing
    ///
    /// Try to remove literals from clauses by checking if they're redundant.
    /// A literal is redundant if the clause is satisfied when it's assigned to false.
    pub(super) fn strengthen_clauses_inprocessing(&mut self) {
        if self.trail.decision_level() != 0 {
            return;
        }

        let max_clauses_to_strengthen = 50; // Limit to avoid overhead
        let mut strengthened_count = 0;

        // Collect candidate clauses (learned clauses with LBD > 2)
        let mut candidates: Vec<(ClauseId, u32)> = Vec::new();

        for &clause_id in &self.learned_clause_ids {
            if let Some(clause) = self.clauses.get(clause_id)
                && !clause.deleted
                && clause.lits.len() > 3
                && clause.lbd > 2
            {
                candidates.push((clause_id, clause.lbd));
            }
        }

        // Sort by LBD (prioritize higher LBD clauses for strengthening)
        candidates.sort_by_key(|(_, lbd)| core::cmp::Reverse(*lbd));

        for (clause_id, _) in candidates.iter().take(max_clauses_to_strengthen) {
            if strengthened_count >= max_clauses_to_strengthen {
                break;
            }

            let clause_lits = match self.clauses.get(*clause_id) {
                Some(c) if !c.deleted && c.lits.len() > 3 => c.lits.clone(),
                _ => continue,
            };

            // Correct self-subsumption / vivification.
            //
            // A literal `l_k` of clause C is redundant iff the formula F already
            // entails C \ {l_k}. To prove that, assert the negation of every
            // *other* literal of C and propagate: a conflict means
            //   F ∧ ¬(C \ {l_k}) ⊨ ⊥   ⇔   F ⊨ (C \ {l_k}),
            // so `l_k` can be dropped while the clause stays F-entailed.
            //
            // The previous implementation asserted only ¬l_k and, on conflict,
            // concluded F ⊨ l_k (a backbone) — then removed l_k. That is the
            // wrong direction: F ⊨ l_k does NOT imply F ⊨ C \ {l_k}, so the
            // shrunken clause excluded legitimate models and could flip SAT to
            // UNSAT whenever inprocessing was enabled. This version negates the
            // *other* literals (matching `vivify_clauses`) and never assigns an
            // already-assigned variable.
            let mut removed_idx: Option<usize> = None;

            for skip_idx in 0..clause_lits.len() {
                let saved_level = self.trail.decision_level();
                self.trail.new_decision_level();

                let mut conflict = false;
                let mut already_sat = false;

                for (i, &lit) in clause_lits.iter().enumerate() {
                    if i == skip_idx {
                        continue;
                    }
                    let value = self.trail.lit_value(lit);
                    if value.is_true() {
                        // C \ {skip_idx} is already satisfied under F, so this
                        // probe cannot justify removing skip_idx.
                        already_sat = true;
                        break;
                    } else if value.is_false() {
                        continue;
                    } else {
                        self.trail.assign_decision(lit.negate());
                        if self.propagate().is_some() {
                            conflict = true;
                            break;
                        }
                    }
                }

                self.backtrack(saved_level);

                if conflict && !already_sat && clause_lits.len() > 2 {
                    removed_idx = Some(skip_idx);
                    break; // Only remove one literal at a time
                }
            }

            // Apply strengthening if we found a redundant literal.
            if let Some(idx) = removed_idx {
                // Remove the redundant literal and rebuild the clause's watches
                // (removing a watched literal in place would break the
                // two-watched invariant, causing missed propagations/conflicts).
                let removable = self
                    .clauses
                    .get(*clause_id)
                    .is_some_and(|c| !c.deleted && c.lits.len() > 2 && idx < c.lits.len());
                if removable {
                    self.remove_literal_and_rewatch(*clause_id, idx);
                }

                // Recompute LBD after the removal.
                if let Some(clause) = self.clauses.get(*clause_id) {
                    let lits_clone = clause.lits.clone();
                    let new_lbd = self.compute_lbd(&lits_clone);

                    if let Some(clause) = self.clauses.get_mut(*clause_id) {
                        clause.lbd = new_lbd;
                    }

                    strengthened_count += 1;
                }
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    /// Regression test for the `inprocess()` DRAT-deletion gap: pure-literal
    /// elimination and subsumption elimination retire original clauses
    /// directly on the clause database (setting `Clause::deleted` without
    /// going through `ClauseDatabase::remove`), and every clause they retire
    /// must show up as a `d`-line in the DRAT proof — not just the separate
    /// on-the-fly-strengthening path (`remove_literal_and_rewatch`), which
    /// already logged correctly before this fix.
    #[test]
    fn inprocess_drat_deletion_count_matches_removed_clauses() {
        let path = std::env::temp_dir().join("oxiz_sat_inprocess_drat_deletion_count.drat");

        let mut solver = Solver::new();
        let y = solver.new_var();
        let w1 = solver.new_var();
        let w2 = solver.new_var();
        let p = solver.new_var();
        let q = solver.new_var();
        let r = solver.new_var();

        // Pure-literal family: `y` occurs only positively, across two
        // clauses that must both be deleted by `pure_literal_elimination`.
        solver.add_clause([Lit::pos(y), Lit::pos(w1)]);
        solver.add_clause([Lit::pos(y), Lit::pos(w2)]);

        // Subsumption pair: (p ∨ q) subsumes (p ∨ q ∨ r), so the latter must
        // be deleted by `subsumption_elimination`.
        solver.add_clause([Lit::pos(p), Lit::pos(q)]);
        solver.add_clause([Lit::pos(p), Lit::pos(q), Lit::pos(r)]);

        // Decoy giving w1, w2, p, q, r an opposite-polarity occurrence each,
        // so none of them is independently pure (only `y` is) — this keeps
        // the (p ∨ q ∨ r) deletion attributable to subsumption alone rather
        // than being pre-empted by pure-literal elimination on `r`.
        solver.add_clause([
            Lit::neg(w1),
            Lit::neg(w2),
            Lit::neg(p),
            Lit::neg(q),
            Lit::neg(r),
        ]);

        solver
            .enable_drat_proof(&path)
            .expect("enable DRAT proof logging");

        // `inprocess` only acts at decision level 0, which a freshly built
        // solver already is.
        assert_eq!(solver.trail.decision_level(), 0);
        let live_before: Vec<ClauseId> = solver.clauses.iter_ids().collect();

        solver.inprocess();

        let removed: Vec<ClauseId> = live_before
            .into_iter()
            .filter(|&id| solver.clauses.get(id).is_some_and(|c| c.deleted))
            .collect();
        assert_eq!(
            removed.len(),
            3,
            "expected exactly 3 clauses removed (2 pure-literal + 1 subsumed)"
        );

        solver.disable_drat_proof();

        let contents = std::fs::read_to_string(&path).expect("read DRAT proof file");
        std::fs::remove_file(&path).ok();

        let deletion_lines = contents
            .lines()
            .filter(|line| line.trim_start().starts_with("d "))
            .count();

        assert_eq!(
            deletion_lines,
            removed.len(),
            "DRAT deletion-line count must match the number of clauses inprocess() removed"
        );
    }
}
