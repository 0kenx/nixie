//! Clause learning, LBD computation, database reduction, inprocessing, and vivification

use super::*;
use smallvec::SmallVec;
use std::time::Instant;

impl Solver {
    /// Install the consequence of a freshly learned clause on the trail.
    ///
    /// This is the single place where a learned clause's asserting literal gets
    /// assigned, and it is where chronological backtracking's central invariant
    /// lives: **a propagated literal's decision level is the maximum level over
    /// the other literals of its reason clause, not the level the search happens
    /// to sit at.**
    ///
    /// Without chronological backtracking those two coincide, because a backjump
    /// always lands exactly on the assertion level. With it the solver
    /// deliberately stops above the assertion level and keeps the intervening
    /// decisions, so recording the current level instead would claim the literal
    /// depends on decisions it does not depend on. That is not merely imprecise:
    /// a **unit** learned clause is a consequence of the formula alone and must
    /// be pinned at level 0, and recording it at the post-backtrack level both
    /// loses it on the next rollback and plants a second reason-less literal
    /// inside a decision level, which breaks the termination invariant of the
    /// 1-UIP walk in [`Solver::analyze`] and lets it emit clauses that are
    /// stronger than what resolution derives – a direct route to a false `unsat`.
    ///
    /// The clause is asserted only when it really is unit under the
    /// post-backtrack assignment. A degenerate analysis result (two literals at
    /// the top level, which the theory-propagation path can still produce) is
    /// therefore added to the database but not propagated, rather than
    /// overwriting a live trail entry.
    ///
    /// Reference: Z3's `sat_solver.cpp` (`assign_core` / `propagate_clause`
    /// compute the same `assign_level`).
    pub(super) fn assert_learned_clause(&mut self, lits: &[Lit], clause_id: ClauseId) {
        let Some(&asserting) = lits.first() else {
            return;
        };

        if self.trail.is_assigned(asserting.var()) {
            // Already satisfied is fine – nothing to install. Already *falsified*
            // is not: every caller backtracks to a level strictly below the
            // asserting literal's own before getting here (`analyze` and
            // `analyze_theory_conflict` both assert that invariant, and
            // `analyze_theory_asserting_lemma` picks an unassigned literal for
            // index 0), so the literal must be free. If it ever were false the
            // silent return would drop a refutation on the floor: a unit lemma is
            // stored without watches, and a longer clause gets both of its watches
            // pinned on literals that are already false, whose watch events have
            // been and gone. Either way nothing re-examines the clause and the
            // search can go on to report `Sat` over a trail that falsifies it.
            debug_assert!(
                !self.trail.lit_value(asserting).is_false(),
                "learned clause {lits:?} is already falsified at its asserting literal \
                 (level {}, search at level {}); returning silently would drop the refutation",
                self.trail.level(asserting.var()),
                self.trail.decision_level()
            );
            return;
        }

        if lits.len() == 1 {
            self.trail.assign_unit_fact(asserting);
            return;
        }

        let mut level = 0;
        for &lit in &lits[1..] {
            if !self.trail.lit_value(lit).is_false() {
                // Not actually unit – do not fabricate a propagation.
                return;
            }
            level = level.max(self.trail.level(lit.var()));
        }

        self.trail
            .assign_propagation_at(asserting, clause_id, level);
    }

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

        // Record the learned clause in the proof (no-op unless enabled). It is
        // RUP-derivable from the current database by 1-UIP construction; the
        // returned id is bound to the stored clause in each branch below.
        let proof_id = self.proof_learn_clause(&learnt_clause);

        if learnt_clause.len() == 1 {
            // Store unit learned clause in database for persistence across backtracks
            let clause_id = self.clauses.add_learned(learnt_clause.iter().copied());
            self.proof_set_clause_id(clause_id, proof_id);
            self.stats.learned_clauses += 1;
            self.stats.unit_clauses += 1;
            self.learned_clause_ids.push(clause_id);

            self.assert_learned_clause(&learnt_clause, clause_id);
        } else if learnt_clause.len() == 2 {
            // Binary learned clause - add to binary implication graph
            let lbd = self.compute_lbd(&learnt_clause);
            let clause_id = self.clauses.add_learned(learnt_clause.iter().copied());
            self.proof_set_clause_id(clause_id, proof_id);
            self.stats.learned_clauses += 1;
            self.stats.binary_clauses += 1;
            self.stats.total_lbd += lbd as u64;

            if let Some(clause) = self.clauses.get_mut(clause_id) {
                clause.lbd = lbd;
                clause.assign_tier_from_lbd();
            }
            self.debug_check_learned_clause_lbd(clause_id);

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

            self.assert_learned_clause(&learnt_clause, clause_id);
        } else {
            let lbd = self.compute_lbd(&learnt_clause);
            self.stats.total_lbd += lbd as u64;
            let clause_id = self.clauses.add_learned(learnt_clause.iter().copied());
            self.proof_set_clause_id(clause_id, proof_id);
            self.stats.learned_clauses += 1;

            if let Some(clause) = self.clauses.get_mut(clause_id) {
                clause.lbd = lbd;
                clause.assign_tier_from_lbd();
            }
            self.debug_check_learned_clause_lbd(clause_id);

            self.learned_clause_ids.push(clause_id);

            // Second watch: the literal that stays "watchable" longest, i.e. the
            // false one at the highest decision level (`watch_rank`), not blindly
            // `learnt_clause[1]`.
            //
            // Soundness, not tuning.  `learnt_clause[0]` is the asserting literal
            // and is fine as the first watch, but index 1 is only the correct
            // second watch when `analyze` happens to leave the highest-level
            // literal there.  `analyze_theory_conflict` builds its clause from a
            // theory explanation whose literals arrive in the theory's order, so
            // index 1 can be a literal that backtracking leaves false *below* the
            // level we return to.  Both watches then sit on literals that are
            // already false and never change again, the watch events never fire,
            // and the clause stops being enforced: `propagate` reports no conflict
            // while the clause is falsified.
            //
            // This restores for learned clauses the same invariant `add_clause`
            // already maintains for original ones (see `watch_rank`).  It is a
            // latent-hole fix found while chasing the QF_UF quasigroup wrong
            // answers, not the cause of those – they were traced to
            // `check_hyper_binary_resolution`.
            let lit0 = learnt_clause[0];
            let mut best = 1;
            for i in 2..learnt_clause.len() {
                if self.watch_rank(learnt_clause[i]) > self.watch_rank(learnt_clause[best]) {
                    best = i;
                }
            }
            let lit1 = learnt_clause[best];
            self.watches
                .add(lit0.negate(), Watcher::new(clause_id, lit1));
            self.watches
                .add(lit1.negate(), Watcher::new(clause_id, lit0));

            self.assert_learned_clause(&learnt_clause, clause_id);

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

    /// Add a *reasoned* theory explanation clause for a propagation.
    ///
    /// The clause is `(propagated_lit ∨ ¬r0 ∨ … ∨ ¬r_{n-1})`, sound because the
    /// theory guarantees every `r_i` is currently TRUE on the trail, so the
    /// clause is unit under the current assignment and propagates
    /// `propagated_lit`.  The clause is registered as a two-watched learned
    /// clause so that, after any later backtrack, BCP re-derives the
    /// propagation as soon as the reasons are re-established – the
    /// two-watched-literal invariant that keeps the clause enforced.
    ///
    /// `reason_lits` MUST be non-empty.  An empty reason denotes an
    /// *unconditional* theory fact – a level-0 unit, which cannot be
    /// two-watched and which would break 1-UIP conflict analysis if used as a
    /// mid-level propagation reason (the unit resolves to nothing, so the
    /// propagated literal becomes a spurious UIP and the learned clause can
    /// negate a genuinely-forced atom → false UNSAT).  The caller routes
    /// empty-reason propagations through [`Solver::force_theory_unit`].
    ///
    /// Watch literals are picked with [`Solver::watch_rank`] (prefer a
    /// satisfied literal, then an unassigned one, then the latest-falsified)
    /// and swapped into positions 0 and 1 of the stored clause, because the
    /// watcher / propagation loop assumes the watched literals live there.
    /// `propagated_lit` is currently unassigned (the caller only propagates
    /// unassigned variables) and so is the highest-ranked literal – it stays
    /// at index 0; the second watch is the latest-falsified reason, so a watch
    /// always fires on re-falsification.  The previous code watched indices 0
    /// and 1 blindly, which on a clause whose index-1 literal was false below
    /// the eventual backtrack level left both watches cold and the clause
    /// silently unenforced after backtracking.
    pub(super) fn add_theory_reason_clause(
        &mut self,
        reason_lits: &[Lit],
        propagated_lit: Lit,
    ) -> ClauseId {
        debug_assert!(
            !reason_lits.is_empty(),
            "add_theory_reason_clause requires non-empty reasons; empty-reason \
             theory facts must go through force_theory_unit"
        );

        // Build the explanation clause: (propagated_lit ∨ ¬r0 ∨ …).
        let mut clause_lits: SmallVec<[Lit; 8]> = SmallVec::new();
        clause_lits.push(propagated_lit);
        for &lit in reason_lits {
            let neg = lit.negate();
            // Dedup by variable (keep first occurrence so propagated_lit stays
            // at index 0) and skip a degenerate self-negation that would make
            // the clause a tautology (`propagated_lit ∨ ¬propagated_lit`).
            if neg.var() == propagated_lit.var() {
                continue;
            }
            if clause_lits.iter().any(|&l| l.var() == neg.var()) {
                continue;
            }
            clause_lits.push(neg);
        }

        // After dedup at least propagated_lit + one distinct reason remain.
        let n = clause_lits.len();
        debug_assert!(
            n >= 2,
            "theory reason clause collapsed to a unit; route through force_theory_unit"
        );

        // Select the two best watch literals and swap them into positions 0
        // and 1 (the watcher/propagation loop assumes watched literals live
        // there), mirroring `add_clause` / `learn_clause`.
        if n >= 2 {
            let mut best = 0;
            for i in 1..n {
                if self.watch_rank(clause_lits[i]) > self.watch_rank(clause_lits[best]) {
                    best = i;
                }
            }
            clause_lits.swap(0, best);
            let mut second = 1;
            for i in 2..n {
                if self.watch_rank(clause_lits[i]) > self.watch_rank(clause_lits[second]) {
                    second = i;
                }
            }
            clause_lits.swap(1, second);
        }

        let lbd = self.compute_lbd(&clause_lits);
        let clause_id = self.clauses.add_learned(clause_lits.iter().copied());

        // Track as a Core-tier learned clause so it is accounted for (clause-db
        // reduction, compaction, DRAT-minimality) and never aggressively
        // deleted: a theory lemma is entailed for as long as the formula stands.
        self.learned_clause_ids.push(clause_id);
        if let Some(clause) = self.clauses.get_mut(clause_id) {
            clause.lbd = lbd;
            clause.promote_to_core();
        }

        // Proof: the explanation clause is a valid theory lemma (recorded with an
        // empty RUP chain; bound to the stored clause below).
        let proof_id = self.proof_theory_clause(
            &clause_lits
                .iter()
                .map(|l| l.to_dimacs())
                .collect::<SmallVec<[i32; 8]>>(),
        );
        self.proof_set_clause_id(clause_id, proof_id);

        let lit0 = clause_lits[0];
        let lit1 = clause_lits[1];
        if n == 2 {
            // Binary clause: also register in the binary implication graph,
            // matching how `learn_clause` attaches binaries.
            self.binary_graph.add(lit0.negate(), lit1, clause_id);
            self.binary_graph.add(lit1.negate(), lit0, clause_id);
        }
        self.watches
            .add(lit0.negate(), Watcher::new(clause_id, lit1));
        self.watches
            .add(lit1.negate(), Watcher::new(clause_id, lit0));

        clause_id
    }

    /// Force an *unconditional* theory fact (a propagation the theory reported
    /// with an empty reason clause) as a permanent level-0 unit.
    ///
    /// Must be called at decision level 0 – the caller backtracks to the root
    /// first (see `install_theory_units`).  Stores the unit lemma `[lit]` as a
    /// Core-tier clause (so the DRAT proof records it and it survives clause-db
    /// reduction) and assigns `lit` as a level-0 decision so it persists across
    /// every later backtrack.
    ///
    /// A unit clause cannot be two-watched, and using one as the reason of a
    /// mid-level propagation breaks 1-UIP conflict analysis (the unit resolves
    /// to nothing, so the propagated literal becomes a spurious UIP and the
    /// learned clause can negate a genuinely-forced atom → false UNSAT).
    /// Installing the fact at level 0 keeps it out of 1-UIP resolution (the
    /// `level > 0` filter in `analyze`) while still constraining the search.
    pub(super) fn force_theory_unit(&mut self, lit: Lit) {
        debug_assert_eq!(
            self.trail.decision_level(),
            0,
            "force_theory_unit requires decision level 0 (caller backtracks first)"
        );
        // Store the unit lemma permanently (Core tier, tracked for reduction).
        let clause_id = self.clauses.add_learned(std::iter::once(lit));
        self.learned_clause_ids.push(clause_id);
        if let Some(clause) = self.clauses.get_mut(clause_id) {
            clause.lbd = 1;
            clause.promote_to_core();
        }
        // Proof: the unit lemma (recorded as a derived unit with empty chain;
        // bound to the stored clause and the unit-id table).
        let proof_id = self.proof_theory_unit(lit.to_dimacs());
        self.proof_set_clause_id(clause_id, proof_id);
        // Assign at level 0 as a decision (no propagation reason): this is the
        // only sound home for a unit, and it survives every backtrack.
        self.trail.assign_decision(lit);
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

                // A clause is a current propagation reason iff the variable of its
                // asserting literal (always `lits[0]`) records this clause as its
                // reason. While a clause is a reason its `lits[0]` is the literal
                // it propagated and is never swapped away (any watcher visit that
                // would touch it finds it true and bails), so checking `lits[0]`
                // alone is both necessary and sufficient – O(1) instead of the
                // previous O(clause-length) scan over every clause every
                // reduction.
                let is_reason = matches!(
                    self.trail.reason(clause.lits[0].var()),
                    Reason::Propagation(r) if r == cid
                );

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
            self.debug_check_invariants("after clause database reduction");
            self.conflicts_since_deletion = 0;
        }

        if self.stats.conflicts >= self.restart_threshold {
            self.restart();
            // `restart()` lands at decision level 0 only when reuse-trail is
            // off; with reuse-trail on (the default) it backtracks only as far
            // as `reuse_trail()`, so the level-0
            // `debug_check_restart_consistency` invariant does not apply (same
            // reasoning as the `_limited` variant below).
            if !self.config.reuse_trail {
                self.debug_check_restart_consistency();
            }
        }
    }

    /// Handle clause deletion and restart, but don't backtrack past assumptions
    pub(super) fn handle_clause_deletion_and_restart_limited(&mut self, min_level: u32) {
        self.conflicts_since_deletion += 1;

        if self.conflicts_since_deletion >= self.config.clause_deletion_threshold as u64 {
            self.reduce_clause_database();
            self.debug_check_invariants("after clause database reduction (assumptions)");
            self.conflicts_since_deletion = 0;
        }

        if self.stats.conflicts >= self.restart_threshold {
            // Limited restart - don't backtrack past assumptions, so unlike
            // `Solver::restart` this does NOT land at decision level 0;
            // `debug_check_restart_consistency` (which asserts exactly that)
            // does not apply here.
            self.backtrack(min_level);
            self.stats.restarts += 1;
            self.luby_index += 1;
            self.restart_threshold =
                self.stats.conflicts + self.config.restart_interval * Self::luby(self.luby_index);
            self.debug_check_invariants("after limited restart (assumptions)");
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

        // Reconstruct variables eliminated by equivalent-literal substitution
        // (equiv.rs / congruence.rs): give each the value of its representative
        // literal (flipped when polarities differ). Iterated to a fixpoint so a
        // representative that is itself eliminated (or whose value arrives via
        // BVE reconstruction below) is handled regardless of variable order.
        if !self.equiv_substitution.is_empty() {
            loop {
                let mut changed = false;
                for v in 0..self.num_vars {
                    if self.model[v] != LBool::Undef {
                        continue;
                    }
                    let Some(rep) = self.equiv_substitution.get(v).copied() else {
                        continue;
                    };
                    if rep.var().index() == v {
                        continue; // not eliminated
                    }
                    let Some(rep_val) = self.model.get(rep.var().index()).copied() else {
                        continue;
                    };
                    if rep_val == LBool::Undef {
                        continue; // rep not yet known; retry next iteration
                    }
                    self.model[v] = if rep.is_pos() {
                        rep_val
                    } else {
                        rep_val.negate()
                    };
                    changed = true;
                }
                if !changed {
                    break;
                }
            }
        }

        // Reconstruct variables eliminated by BVE in reverse elimination order.
        // For eliminated `v` with positive clauses `(v ∨ A_i)` (stripped of `v`):
        //   - if EVERY `A_i` already has a satisfied literal, set `v = false`
        //     (the `(v ∨ A_i)` are satisfied without it, and `¬v` satisfies the
        //     `(¬v ∨ B_j)`);
        //   - else SOME `A_k` is all-false, forcing `v = true` to satisfy
        //     `(v ∨ A_k)`. The resolvents `(A_k ∨ B_j)` then guarantee every
        //     `B_j` is true, so the `(¬v ∨ B_j)` are satisfied too.
        // (The earlier version used "any satisfied" → wrong when some but not
        //  all `A_i` are satisfied: it set v=false and violated the all-false
        //  clause.)
        if !self.bve_order.is_empty() {
            for &v in self.bve_order.iter().rev() {
                let clauses = match self.bve_def.get(v.index()) {
                    Some(c) if !c.is_empty() => c,
                    _ => continue,
                };
                let lit_true = |l: Lit| {
                    self.model
                        .get(l.var().index())
                        .copied()
                        .unwrap_or(LBool::Undef)
                        == if l.is_pos() {
                            LBool::True
                        } else {
                            LBool::False
                        }
                };
                let all_satisfied = clauses
                    .iter()
                    .all(|clause| clause.iter().any(|&l| lit_true(l)));
                self.model[v.index()] = if all_satisfied {
                    LBool::False
                } else {
                    LBool::True
                };
            }
        }
    }

    /// Safety net for the purely Boolean entry points: check that the model just
    /// saved actually satisfies the clause database.
    ///
    /// A false `Unsat` merely fails to solve; a false `Sat` hands every
    /// downstream consumer an assignment they will trust. Verifying the finished
    /// model is one linear pass, so in debug builds – which covers every test and
    /// CI run – this converts such corruption into a loud, precisely localised
    /// failure instead of a silently wrong answer. It compiles to nothing in
    /// release, so the shipped hot path is unaffected.
    ///
    /// Deliberately **not** called from `solve_with_theory`; that path has its own
    /// narrower guard, [`Solver::debug_verify_model_input`]. There the database
    /// also holds lemmas injected through `TheoryCallback` (see
    /// [`Solver::add_theory_reason_clause`]) whose validity and lifetime this
    /// crate does not control: the theory retracts its context through
    /// `on_backtrack` without the Boolean core retracting the corresponding
    /// lemma, so a final model may legitimately falsify one. Asserting on those
    /// would make `oxiz-sat` fail on behalf of a component it cannot police.
    pub(super) fn debug_verify_model(&self) {
        #[cfg(debug_assertions)]
        if let Some(id) = self.find_model_violation(true) {
            let lits = self.clauses.get(id).map(|c| c.lits.clone());
            panic!(
                "solve() reported Sat with a model that violates clause {id:?} ({lits:?}); \
                 the search accepted an assignment that does not satisfy the database"
            );
        }
    }

    /// Safety net for the CDCL(T) entry point [`Solver::solve_with_theory`].
    ///
    /// The full check above cannot be used there, but the reason it cannot –
    /// `TheoryCallback`-injected lemmas whose validity `oxiz-sat` does not own –
    /// applies only to *learned* clauses: theory reason clauses and theory lemmas
    /// all enter through `ClauseDb::add_learned`, as do the resolvents that 1-UIP
    /// analysis derives over them. **Original** clauses are a different matter
    /// entirely. They arrived through `add_clause` from the caller, they are the
    /// Boolean abstraction the caller asked to be satisfied, and nothing but
    /// `pop` retracts them. A `Sat` answer that falsifies one is a bug in this
    /// crate no matter what the theory did, so restricting the scan to them gives
    /// a guard that is both meaningful and impossible to trip on the theory's
    /// behalf.
    ///
    /// That is precisely the class the propagation-fixpoint bug produced: an
    /// original ternary clause with all three literals falsified by level-0 facts
    /// while `final_check` answered `Sat`.
    pub(super) fn debug_verify_model_input(&self) {
        #[cfg(debug_assertions)]
        if let Some(id) = self.find_model_violation(false) {
            let lits = self.clauses.get(id).map(|c| c.lits.clone());
            panic!(
                "solve_with_theory() reported Sat with a model that violates ORIGINAL clause \
                 {id:?} ({lits:?}); the CDCL(T) search accepted an assignment that does not \
                 satisfy the input formula's Boolean abstraction"
            );
        }
    }

    /// Find a live, *enforced* clause that the saved model does not satisfy.
    ///
    /// The scope is deliberately "everything the two-watched-literal scheme is
    /// responsible for": non-deleted clauses of at least two literals. A model
    /// falsifying one of those means propagation failed to fire on a watch, which
    /// is a soundness bug whether the clause is original or learned. Callers that
    /// cannot vouch for learned clauses pass `include_learned == false`.
    ///
    /// Unit clauses are excluded because the database is not what enforces them.
    /// `add_clause` never stores a unit at all – it assigns the literal at level
    /// 0 – and the copies that learned units leave behind carry no watches; their
    /// force comes solely from that level-0 trail assignment. An incremental
    /// caller that retracts the assignment (`pop`, `restore_to_trail_size`)
    /// without also dropping the record leaves a lemma the formula no longer
    /// entails, which a later model may legitimately falsify.
    ///
    /// Clauses retired by inprocessing are skipped for a similar reason: they are
    /// re-satisfied by model reconstruction rather than by the assignment, and
    /// their literals need not even be in the model's variable range.
    #[cfg(debug_assertions)]
    fn find_model_violation(&self, include_learned: bool) -> Option<ClauseId> {
        self.clauses.iter_ids().find(|&id| {
            self.clauses.get(id).is_some_and(|clause| {
                (include_learned || !clause.learned)
                    && clause.lits.len() >= 2
                    && !clause
                        .lits
                        .iter()
                        .any(|lit| match self.model.get(lit.var().index()) {
                            Some(LBool::True) => lit.is_pos(),
                            Some(LBool::False) => !lit.is_pos(),
                            _ => false,
                        })
            })
        })
    }

    /// Release build: compiles away entirely.
    #[cfg(not(debug_assertions))]
    #[inline]
    pub(super) fn debug_check_invariants(&self, _context: &str) {}

    /// Debug-only structural/soundness net over the whole CDCL data model:
    /// clause well-formedness, trail/assignment consistency, decision-level
    /// bookkeeping, static learned-clause LBD bounds, live reason clauses, and
    /// implication-graph acyclicity. See `crate::invariants` for exactly what
    /// each check covers and why the checks this sweep deliberately does
    /// *not* run are situational instead (only meaningful right after a
    /// specific event, such as a conflict or a restart). Compiles to nothing
    /// in release builds.
    #[cfg(debug_assertions)]
    pub(super) fn debug_check_invariants(&self, context: &str) {
        if let Err(msg) = crate::invariants::check_all_sat_invariants(self) {
            panic!("SAT solver invariant violated ({context}): {msg}");
        }
    }

    /// Release build: compiles away entirely.
    #[cfg(not(debug_assertions))]
    #[inline]
    pub(super) fn debug_check_fixpoint_invariants(&self, _context: &str) {}

    /// Debug-only net for the two invariants that only hold once
    /// `propagate()` has reached a fixpoint (returned `None`): no live clause
    /// has both watched literals false while unsatisfied
    /// (`crate::invariants::check_watched_literals`), and no live clause is a
    /// hanging unit (`crate::invariants::check_unit_propagation_complete`).
    /// Call this only at a fixpoint – mid-scan both are routinely and
    /// harmlessly violated. Compiles to nothing in release builds.
    #[cfg(debug_assertions)]
    pub(super) fn debug_check_fixpoint_invariants(&self, context: &str) {
        if let Err(msg) = crate::invariants::check_watched_literals(self) {
            panic!("SAT solver invariant violated at a propagation fixpoint ({context}): {msg}");
        }
        if let Err(msg) = crate::invariants::check_unit_propagation_complete(self) {
            panic!("SAT solver invariant violated at a propagation fixpoint ({context}): {msg}");
        }
    }

    /// Release build: compiles away entirely.
    #[cfg(not(debug_assertions))]
    #[inline]
    pub(super) fn debug_check_conflict_clause(&self, _conflict: ClauseId) {}

    /// Debug-only net: the clause `propagate()` just reported as a conflict
    /// is fully assigned and fully falsified. Call this right where
    /// `propagate()` returns `Some(conflict)`, before any backtrack changes
    /// the trail. Compiles to nothing in release builds.
    #[cfg(debug_assertions)]
    pub(super) fn debug_check_conflict_clause(&self, conflict: ClauseId) {
        if let Err(msg) = crate::invariants::check_conflict_clause(self, conflict) {
            panic!("SAT solver invariant violated at conflict detection: {msg}");
        }
    }

    /// Release build: compiles away entirely.
    #[cfg(not(debug_assertions))]
    #[inline]
    pub(super) fn debug_check_restart_consistency(&self) {}

    /// Debug-only net: right after a restart, the decision level is 0 and
    /// every trail entry is a level-0 fact. Compiles to nothing in release
    /// builds.
    #[cfg(debug_assertions)]
    pub(super) fn debug_check_restart_consistency(&self) {
        if let Err(msg) = crate::invariants::check_restart_consistency(self) {
            panic!("SAT solver invariant violated after restart: {msg}");
        }
    }

    /// Release build: compiles away entirely.
    #[cfg(not(debug_assertions))]
    #[inline]
    pub(super) fn debug_check_learned_clause_lbd(&self, _clause_id: ClauseId) {}

    /// Debug-only net: a freshly learned clause's stored LBD matches
    /// recomputing it right now. Only sound to call in the instant right
    /// after `clause_id` was learned and its `lbd` field set – see
    /// `crate::invariants::check_learned_clause_lbd`'s doc comment for why
    /// this cannot be a standing, whole-database invariant. Compiles to
    /// nothing in release builds.
    #[cfg(debug_assertions)]
    pub(super) fn debug_check_learned_clause_lbd(&self, clause_id: ClauseId) {
        if let Err(msg) = crate::invariants::check_learned_clause_lbd(self, clause_id) {
            panic!("SAT solver invariant violated for freshly learned clause: {msg}");
        }
    }

    /// Remove the literal at `idx` from a learned clause and rebuild its two
    /// watches so the two-watched-literal invariant is preserved.
    ///
    /// Vivification and inprocessing strengthening shrink a clause in place. If
    /// the removed literal sat at a watched position (index 0 or 1), the stale
    /// watcher would keep pointing at a literal no longer in the clause, breaking
    /// watch firing – a watched literal becoming false would no longer re-examine
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

        // Record the in-place strengthening in the proof: add the shorter
        // clause (RUP-derivable – vivification proved it entailed) then delete the
        // original, keeping the proof's clause set consistent with the database.
        if self.proof.is_some() {
            let new_lits: SmallVec<[Lit; 8]> = lits.iter().copied().collect();
            self.proof_strengthen_clause(clause_id, &new_lits);
        }
    }

    /// Vivification (asymmetric branching, cadical-style): shorten/strengthen
    /// clauses by assuming their literals false in order and propagating. If a
    /// prefix of literals falsified leads to a conflict, that prefix clause is
    /// implied by the formula, so the clause can be replaced by the (shorter)
    /// prefix. If a later literal of the clause is forced true during the
    /// prefix assignment, the clause (prefix ∨ that-literal) is implied.
    /// Soundness-preserving: the replacement clause is always a consequence of
    /// the formula. Bounded by a wall-clock budget and a clause count.
    pub(super) fn vivify_clauses(&mut self) {
        if self.trail.decision_level() != 0 {
            return;
        }
        const TIME_BUDGET_MS: u128 = 200;
        const MAX_CLAUSES: usize = 5_000;
        let t0 = Instant::now();
        let mut done = 0usize;

        // Snapshot candidate ids up front (vivify mutates the clause DB).
        let candidates: SmallVec<[ClauseId; 64]> = self
            .learned_clause_ids
            .iter()
            .copied()
            .take(MAX_CLAUSES)
            .collect();

        for cid in candidates {
            if done >= MAX_CLAUSES || t0.elapsed().as_millis() > TIME_BUDGET_MS {
                break;
            }
            // Need len > 2 (binary/unit clauses aren't worth vivifying).
            let lits: SmallVec<[Lit; 8]> = match self.clauses.get(cid) {
                Some(c) if !c.deleted && c.lits.len() > 2 => c.lits.iter().copied().collect(),
                _ => continue,
            };
            if self.vivify_clause(cid, &lits) {
                done += 1;
            }
        }
    }

    /// Try to vivify one clause. Returns true if the clause was shortened.
    fn vivify_clause(&mut self, cid: ClauseId, lits: &[Lit]) -> bool {
        let saved_level = self.trail.decision_level();
        let n = lits.len();
        let mut shorten_to: Option<SmallVec<[Lit; 8]>> = None;

        'outer: for j in 0..n {
            match self.trail.lit_value(lits[j]) {
                // Already true: clause is satisfied, nothing to vivify.
                crate::literal::LBool::True => break 'outer,
                // Already false: counts as assumed, no new decision needed.
                crate::literal::LBool::False => {}
                crate::literal::LBool::Undef => {
                    self.trail.new_decision_level();
                    self.trail.assign_decision(lits[j].negate());
                    if self.propagate().is_some() {
                        // Falsifying lits[0..=j] conflicts → prefix implied.
                        shorten_to = Some(lits[0..=j].iter().copied().collect());
                        break 'outer;
                    }
                }
            }
            // Did the propagation force a later clause literal true?
            // (lits[0..=j] ∨ lits[m]) is then implied.
            for m in (j + 1)..n {
                if self.trail.lit_value(lits[m]).is_true() {
                    let mut s: SmallVec<[Lit; 8]> = lits[0..=j].iter().copied().collect();
                    s.push(lits[m]);
                    shorten_to = Some(s);
                    break 'outer;
                }
            }
        }

        self.backtrack(saved_level);

        let Some(new_lits) = shorten_to else {
            return false;
        };
        // Only replace if we actually shrank (and kept ≥ 2 literals: a unit /
        // empty clause from vivification needs separate handling we skip here).
        if new_lits.len() >= lits.len() || new_lits.len() < 2 {
            return false;
        }
        self.replace_clause_lits(cid, &new_lits);
        true
    }

    /// Replace a clause's literals in place, re-attaching the two watched
    /// literals. (DRAT: the caller's context logs the strengthening; here we
    /// just keep the watched-literal invariant consistent.)
    fn replace_clause_lits(&mut self, cid: ClauseId, new_lits: &[Lit]) {
        // Detach old watches (on the current positions 0 and 1).
        let (old_w0, old_w1) = match self.clauses.get(cid) {
            Some(c) if !c.deleted && c.lits.len() >= 2 => (c.lits[0], c.lits[1]),
            _ => return,
        };
        self.watches.remove_clause(old_w0.negate(), cid);
        self.watches.remove_clause(old_w1.negate(), cid);

        // Pick the two best watch literals (prefer satisfied, then unassigned).
        let mut idxs: SmallVec<[usize; 8]> = (0..new_lits.len()).collect();
        idxs.sort_by(|&a, &b| {
            self.watch_rank(new_lits[b])
                .cmp(&self.watch_rank(new_lits[a]))
        });
        let (i0, i1) = (idxs[0], idxs[1]);

        if let Some(clause) = self.clauses.get_mut(cid) {
            // Move the chosen watches to positions 0 and 1.
            let mut lits: SmallVec<[Lit; 8]> = new_lits.iter().copied().collect();
            lits.swap(0, i0);
            // i1 may have shifted if i1 == 0; recompute against the swapped vec.
            let i1 = if i1 == 0 {
                i0
            } else if i1 == i0 {
                0
            } else {
                i1
            };
            lits.swap(1, i1);
            clause.lits.clear();
            clause.lits.extend(lits.iter().copied());
            let w0 = lits[0];
            let w1 = lits[1];
            self.watches.add(w0.negate(), Watcher::new(cid, w1));
            self.watches.add(w1.negate(), Watcher::new(cid, w0));
        }
    }

    /// Run propagation capped at `limit` steps. Returns `(conflict, aborted)`:
    /// `aborted=true` means the step budget was hit before propagation finished
    /// – treat as "bail this probe" (neither a real conflict nor a complete
    /// model). Used by preprocessing passes (probing/vivify) so a single
    /// doomed cascade can't run unbounded (a ~7s slowdown on Urquhart).
    pub(super) fn propagate_bounded(&mut self, limit: u64) -> (bool, bool) {
        self.propagate_step_limit = Some(limit);
        self.propagate_aborted = false;
        let conflict = self.propagate().is_some();
        let aborted = self.propagate_aborted;
        self.propagate_step_limit = None;
        self.propagate_aborted = false;
        (conflict, aborted)
    }

    /// Failed-literal probing with on-the-fly hyper-binary resolution
    /// (cadical-style, simplified – no dominator LCA).
    ///
    /// Probe each still-unassigned literal `r` at decision level 1 and run BCP.
    ///   * If the probe conflicts, `r` is a *failed literal*: force `¬r` as a
    ///     level-0 unit (every model must set `r` false).
    ///   * If it does not conflict, every literal `q` forced during the probe by
    ///     a *non-binary* clause satisfies `r → q` (the clause became unit solely
    ///     because `r` made its other literals false), so the binary clause
    ///     `(¬r ∨ q)` is implied – add it as a learned binary (a hyper-binary
    ///     resolvent) when not already present. This enriches the binary
    ///     implication graph, making later propagation/probing stronger.
    ///
    /// Soundness: forced units and derived binaries are all consequences of the
    /// formula (BCP is sound and learned clauses are implied). Bounded by a
    /// wall-clock budget and a per-probe cap so it never dominates.
    pub(super) fn probe_hyper_binary(&mut self) -> (usize, usize) {
        if self.trail.decision_level() != 0 {
            return (0, 0);
        }
        const TIME_BUDGET_MS: u128 = 200;
        const PER_PROBE_CAP: u32 = 20_000;
        let t0 = Instant::now();
        let mut failed = 0usize;
        let mut hyper = 0usize;

        let n = self.num_vars;
        for i in 0..n {
            if self.trivially_unsat {
                break;
            }
            if t0.elapsed().as_millis() > TIME_BUDGET_MS {
                break;
            }
            let v = Var::new(i as u32);
            if self.trail.is_assigned(v) {
                continue;
            }
            let r = Lit::pos(v);

            self.trail.new_decision_level();
            self.trail.assign_decision(r);
            let (conflict, aborted) = self.propagate_bounded(PER_PROBE_CAP.into());
            if conflict {
                self.backtrack(0);
                self.force_level0(r.negate());
                failed += 1;
            } else if aborted {
                // Cascade hit the step cap – densely constrained, skip.
                self.backtrack(0);
            } else {
                self.derive_hyper_binaries(r, &mut hyper);
                self.backtrack(0);
            }
        }
        (failed, hyper)
    }

    /// Add `(¬r ∨ q)` as a learned binary for every literal `q` forced during the
    /// probe of `r` whose reason is a non-binary clause (the hyper-binary case).
    fn derive_hyper_binaries(&mut self, r: Lit, hyper: &mut usize) {
        // Walk the literals assigned at the probe level (level >= 1) with a
        // propagation reason; the probe literal itself is a decision, skipped.
        let probe_lits: SmallVec<[Lit; 64]> = self.trail.level_assignments().to_vec().into();
        let mut added = 0u32;
        for q in probe_lits {
            if added >= 64 {
                break; // cap binaries derived per probe to limit clutter
            }
            let Reason::Propagation(cid) = self.trail.reason(q.var()) else {
                continue;
            };
            // Only derive from non-binary reasons (binary reasons are already edges).
            let is_long = self.clauses.get(cid).is_some_and(|c| c.lits.len() > 2);
            if !is_long {
                continue;
            }
            // r → q already? (binary (¬r ∨ q) present)
            if self.has_binary_implication(r, q) {
                continue;
            }
            let id = self.clauses.add_learned([r.negate(), q]);
            // Set the LBD this hyper-binary-resolution clause actually has.
            // Every other `add_learned` site computes and stores it (see the
            // sibling HBR path in `propagate.rs` and its design note: a stuck
            // LBD of 0 at `Clause::learned`'s default gave every HBR clause an
            // artificially easy path into permanent Core retention via
            // `record_usage`'s `lbd <= 2` promote, regardless of quality).
            // This site used to be the exception – the LBD-0 invariant
            // (debug) caught it on the pigeonhole case.
            let lbd = self.compute_lbd(&[r.negate(), q]);
            if let Some(clause) = self.clauses.get_mut(id) {
                clause.lbd = lbd;
            }
            self.debug_check_learned_clause_lbd(id);
            self.binary_graph.add(r, q, id);
            self.binary_graph.add(q.negate(), r.negate(), id);
            self.watches.add(r, Watcher::new(id, q));
            self.watches.add(q.negate(), Watcher::new(id, r.negate()));
            *hyper += 1;
            added += 1;
        }
    }

    /// Failed-literal probing (at decision level 0).
    ///
    /// For each unassigned variable, tentatively assign each polarity and run
    /// unit propagation. If a probe leads to a conflict, the opposite polarity
    /// is implied by the current level-0 facts, so we add it as a permanent
    /// level-0 unit and propagate. This deduces forced assignments that plain
    /// unit propagation cannot – it is the technique that lets cadical solve
    /// structured instances such as `simon` with zero search decisions. Bounded
    /// by a propagation budget so it never dominates on huge instances.
    ///
    /// Returns the number of units forced this round.
    pub(super) fn failed_literal_probing(&mut self) -> usize {
        if self.trail.decision_level() != 0 {
            return 0;
        }

        // Propagation budget for the whole pass. The old `num_vars*8` value
        // (~62K props on longmult15) allowed barely a single probe before
        // bailing, so probing was effectively a no-op even with `INPROCESS=1`.
        // A full failed-literal pass is ~2*num_vars probes; on the binary-heavy
        // structured instances it targets, BCP is cheap, so allow a generous
        // fraction of a full sweep.
        let budget = (self.num_vars.saturating_mul(512)).max(50_000) as u64;
        let start_props = self.stats.propagations;
        let mut forced = 0usize;

        // Snapshot the currently-unassigned variables (probing forces some).
        let vars: SmallVec<[Var; 64]> = (0..self.num_vars as u32).map(Var::new).collect();

        for &v in &vars {
            if self.trivially_unsat {
                break;
            }
            if self.stats.propagations.saturating_sub(start_props) > budget {
                break;
            }
            if self.trail.is_assigned(v) {
                continue;
            }

            // Probe positive polarity.
            if self.probe_conflicts(Lit::pos(v)) {
                self.force_level0(Lit::neg(v));
                forced += 1;
                continue;
            }
            // Probe negative polarity.
            if self.probe_conflicts(Lit::neg(v)) {
                self.force_level0(Lit::pos(v));
                forced += 1;
            }
        }
        forced
    }

    /// Probe a single literal: assign it at a fresh decision level, propagate,
    /// then undo. Returns true if the probe conflicted (the literal is false).
    fn probe_conflicts(&mut self, lit: Lit) -> bool {
        self.trail.new_decision_level();
        self.trail.assign_decision(lit);
        let (conflict, _aborted) = self.propagate_bounded(50_000);
        self.backtrack_with_phase_saving(0);
        conflict
    }

    /// Force a literal as a permanent level-0 fact and propagate. Assumes we
    /// are at decision level 0. Sets `trivially_unsat` if it conflicts.
    fn force_level0(&mut self, lit: Lit) {
        use crate::literal::LBool;
        match self.trail.lit_value(lit) {
            LBool::True => return,
            LBool::False => {
                self.trivially_unsat = true;
                return;
            }
            LBool::Undef => {}
        }
        self.trail.assign_decision(lit);
        if self.propagate().is_some() {
            self.trivially_unsat = true;
        }
    }

    /// Perform inprocessing (apply preprocessing during search)
    pub(super) fn inprocess(&mut self) {
        use crate::Preprocessor;

        // Only inprocess at decision level 0. LRAT tracing steps aside entirely:
        // `strengthen_clauses_inprocessing`'s redundant-literal check derives its
        // shorter clause via a hypothetical assign-and-propagate probe this
        // module does not thread a hint chain through (and the subsumption /
        // pure-literal-elimination passes rewrite the live clause set in ways the
        // tracer cannot back with sound addition/deletion lines), so rather than
        // emit proof steps this port cannot justify, the whole pass is skipped
        // while an LRAT tracer is attached. Faithful port of v0.3.2's
        // `|| self.lrat.is_some()` gate (main's `lrat` is a `bool`).
        if self.trail.decision_level() != 0 || self.lrat {
            return;
        }

        // Create preprocessor with current number of variables
        let mut preprocessor = Preprocessor::new(self.num_vars);

        // Snapshot every live clause's literals before the elimination passes
        // below run. `Preprocessor::pure_literal_elimination` and
        // `subsumption_elimination` retire clauses by setting `Clause::deleted`
        // directly on `self.clauses` (they don't go through
        // `ClauseDatabase::remove`) and report only a count, not which ids were
        // touched. `drat_delete(id)` can't be used afterwards either – by
        // design it refuses to read literals off a clause already marked
        // deleted, to avoid ever emitting a deletion line with garbage
        // literals. Without this snapshot the deletions below would never
        // reach the DRAT proof: the checker would still accept the proof (an
        // omitted deletion hint only makes it larger, never invalid), but the
        // proof would keep clauses the live database no longer has, which is
        // exactly the minimality gap this snapshot closes. Skipped entirely
        // when proof logging is off.
        let pre_lits: Vec<(ClauseId, SmallVec<[Lit; 8]>)> = if self.proof.is_some() {
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
            // Variables already fixed on the level-0 trail must be excluded
            // from pure-literal elimination (see
            // `Preprocessor::pure_literal_elimination`).
            let assigned: Vec<bool> = (0..self.num_vars)
                .map(|i| self.trail.is_assigned(Var::new(i as u32)))
                .collect();
            let _pure_elim = preprocessor.pure_literal_elimination(&mut self.clauses, &assigned);
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
            // concluded F ⊨ l_k (a backbone) – then removed l_k. That is the
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
    /// must show up as a `d`-line in the DRAT proof – not just the separate
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
        // so none of them is independently pure (only `y` is) – this keeps
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
