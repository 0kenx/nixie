//! Extended search entry points split out of `solver/mod.rs`.
//!
//! Currently hosts the CDCL(T) search loop [`Solver::solve_with_theory`]. It
//! lives in its own file so `solver/mod.rs` stays under the 2000-line limit
//! while keeping all `impl Solver` search variants close together.

use super::*;

impl Solver {
    /// Solve with theory integration via callbacks
    ///
    /// This implements the CDCL(T) loop:
    /// 1. BCP (Boolean Constraint Propagation)
    /// 2. Theory propagation (via callback)
    /// 3. On conflict: analyze and learn
    /// 4. Decision
    /// 5. Final theory check when all vars assigned
    ///
    /// # Propagation fixpoint invariant
    ///
    /// Every conflict handler here ends by rejoining the **outer** `'search`
    /// loop, whose first act is `propagate()`. That is what makes step 4/5 sound:
    /// a decision, and above all the `final_check`/`save_model` step that answers
    /// `Sat`, may only run once Boolean propagation has reached a fixpoint over
    /// the *whole* clause database.
    ///
    /// Handling a conflict inside the theory loop and rejoining that inner loop
    /// instead — which is what the theory-conflict branches used to do — skips
    /// BCP: the learned clause's asserting literal (for a unit lemma, a fresh
    /// level-0 fact) is appended to the trail but never propagated. If the theory
    /// conflict happens to resolve the *last* unassigned variable, `pick_branch_var`
    /// then reports "all assigned", `final_check` sees a theory-consistent atom
    /// assignment and answers `Sat` — over a trail on which an **original** clause
    /// is already falsified by level-0 facts alone. The instance is `Unsat` and
    /// the caller is handed a model that does not satisfy the formula.
    pub fn solve_with_theory<T: TheoryCallback>(&mut self, theory: &mut T) -> SolverResult {
        if self.trivially_unsat {
            return SolverResult::Unsat;
        }

        // Initial propagation
        if self.propagate().is_some() {
            return SolverResult::Unsat;
        }

        // Track how many assignments have been sent to the theory.
        // We only send NEW assignments (not previously processed ones) to avoid
        // duplicate theory constraints that would cause spurious UNSAT.
        let mut theory_processed: usize = 0;

        'search: loop {
            // Resource budget / interrupt check: honor a configured conflict
            // limit or an external interrupt by returning Unknown.
            if self.should_stop_search() {
                return SolverResult::Unknown;
            }

            // Boolean propagation
            if let Some(conflict) = self.propagate() {
                self.stats.conflicts += 1;

                if self.trail.decision_level() == 0 {
                    return SolverResult::Unsat;
                }

                let (backtrack_level, learnt_clause) = self.analyze(conflict);

                // Empty learned clause = genuine root-level (level-0) refutation:
                // the conflict clause is falsified under unconditional facts alone,
                // so the instance is UNSAT. `analyze` returns this even when the
                // trail sits above decision level 0 (an on-the-fly clause added
                // already-falsified at the root).
                if learnt_clause.is_empty() {
                    self.trivially_unsat = true;
                    return SolverResult::Unsat;
                }

                theory.on_backtrack(backtrack_level);
                // Clamp the theory cursor to the rollback boundary, not to the
                // trail length: chronological backtracking re-appends the
                // literals that survive the rollback above that boundary, and
                // the theory — which was just told to unwind to
                // `backtrack_level` — has to see them again.
                let boundary = self.backtrack_with_phase_saving(backtrack_level);
                theory_processed = theory_processed.min(boundary);
                self.learn_clause(learnt_clause);

                self.vsids.decay();
                self.decay_clause_activity();
                self.handle_deletion_restart_with_theory(theory, &mut theory_processed);
                continue;
            }

            // Theory propagation check after each assignment
            loop {
                // Get only NEW (unprocessed) assignments and notify theory
                let assignments = self.trail.assignments().to_vec();
                let mut theory_conflict = None;
                let mut theory_propagations = Vec::new();

                // Check only NEW assignments with theory (skip already-processed ones).
                // Guard against stale theory_processed after backtracks/restarts.
                let safe_start = theory_processed.min(assignments.len());
                for &lit in &assignments[safe_start..] {
                    match theory.on_assignment(lit) {
                        TheoryCheckResult::Sat => {}
                        TheoryCheckResult::Conflict(conflict_lits) => {
                            theory_conflict = Some(conflict_lits);
                            break;
                        }
                        TheoryCheckResult::Propagated(props) => {
                            theory_propagations.extend(props);
                        }
                    }
                }
                // Update processed count
                theory_processed = assignments.len();

                // Handle theory conflict
                if let Some(conflict_lits) = theory_conflict {
                    self.stats.conflicts += 1;

                    if self.trail.decision_level() == 0 {
                        return SolverResult::Unsat;
                    }

                    let (backtrack_level, learnt_clause) =
                        self.analyze_theory_conflict(&conflict_lits);

                    // Empty learned clause signals all-level-0 conflict = fundamental UNSAT
                    if learnt_clause.is_empty() {
                        self.trivially_unsat = true;
                        return SolverResult::Unsat;
                    }

                    theory.on_backtrack(backtrack_level);
                    let boundary = self.backtrack_with_phase_saving(backtrack_level);
                    theory_processed = theory_processed.min(boundary);
                    self.learn_clause(learnt_clause);

                    self.vsids.decay();
                    self.decay_clause_activity();
                    self.handle_deletion_restart_with_theory(theory, &mut theory_processed);
                    // Rejoin the outer loop, NOT this one: the clause just learned
                    // put its asserting literal on the trail unpropagated, and only
                    // `'search`'s leading `propagate()` closes that gap. See the
                    // propagation-fixpoint invariant on `solve_with_theory`.
                    continue 'search;
                }

                // Handle theory propagations
                let mut made_propagation = false;
                for (lit, reason_lits) in theory_propagations {
                    if !self.trail.is_assigned(lit.var()) {
                        // Add reason clause and propagate
                        let clause_id = self.add_theory_reason_clause(&reason_lits, lit);
                        self.trail.assign_propagation(lit, clause_id);
                        made_propagation = true;
                    }
                }

                if made_propagation {
                    // Re-run Boolean propagation
                    if let Some(conflict) = self.propagate() {
                        self.stats.conflicts += 1;

                        if self.trail.decision_level() == 0 {
                            return SolverResult::Unsat;
                        }

                        let (backtrack_level, learnt_clause) = self.analyze(conflict);

                        // Empty learned clause = genuine root-level (level-0)
                        // refutation → UNSAT (see the companion guard above).
                        if learnt_clause.is_empty() {
                            self.trivially_unsat = true;
                            return SolverResult::Unsat;
                        }

                        theory.on_backtrack(backtrack_level);
                        let boundary = self.backtrack_with_phase_saving(backtrack_level);
                        theory_processed = theory_processed.min(boundary);
                        self.learn_clause(learnt_clause);

                        self.vsids.decay();
                        self.decay_clause_activity();
                        self.handle_deletion_restart_with_theory(theory, &mut theory_processed);
                        // Same reason as the theory-conflict branch above: the
                        // learned clause left an unpropagated asserting literal.
                        continue 'search;
                    }
                    continue;
                }

                break;
            }

            // The theory loop is quiescent. Boolean propagation must be at a
            // fixpoint before a decision is taken and, critically, before
            // `final_check` is allowed to answer `Sat` over this trail. Every path
            // that assigns without propagating rejoins `'search` above, so this
            // guard is the belt to that braces — one comparison, and it makes the
            // invariant hold no matter how the branches above are later edited.
            if self.trail.has_pending_propagation() {
                continue 'search;
            }

            // Try to decide
            if let Some(var) = self.pick_branch_var() {
                self.stats.decisions += 1;
                self.trail.new_decision_level();
                let new_level = self.trail.decision_level();
                theory.on_new_level(new_level);

                let polarity = if self.rand_bool(self.config.random_polarity_prob) {
                    self.rand_bool(0.5)
                } else {
                    self.phase[var.index()]
                };
                let lit = if polarity {
                    Lit::pos(var)
                } else {
                    Lit::neg(var)
                };
                self.trail.assign_decision(lit);
            } else {
                // All variables assigned - do final theory check
                match theory.final_check() {
                    TheoryCheckResult::Sat => {
                        // Never hand back a "model" that violates a clause we
                        // ourselves asserted (see `trail_falsifies_live_clause`).
                        if self.trail_falsifies_live_clause() {
                            return SolverResult::Unknown;
                        }
                        self.save_model();
                        self.debug_verify_model_input();
                        return SolverResult::Sat;
                    }
                    TheoryCheckResult::Conflict(conflict_lits) => {
                        self.stats.conflicts += 1;

                        if self.trail.decision_level() == 0 {
                            return SolverResult::Unsat;
                        }

                        let (backtrack_level, learnt_clause) =
                            self.analyze_theory_conflict(&conflict_lits);

                        // If all conflict literals are at level 0, analyze_theory_conflict
                        // returns an empty learned clause as a signal of fundamental UNSAT.
                        if learnt_clause.is_empty() {
                            self.trivially_unsat = true;
                            return SolverResult::Unsat;
                        }

                        theory.on_backtrack(backtrack_level);
                        let boundary = self.backtrack_with_phase_saving(backtrack_level);
                        theory_processed = theory_processed.min(boundary);
                        self.learn_clause(learnt_clause);

                        self.vsids.decay();
                        self.decay_clause_activity();
                        self.handle_deletion_restart_with_theory(theory, &mut theory_processed);
                    }
                    TheoryCheckResult::Propagated(props) => {
                        // Handle late propagations
                        for (lit, reason_lits) in props {
                            if !self.trail.is_assigned(lit.var()) {
                                let clause_id = self.add_theory_reason_clause(&reason_lits, lit);
                                self.trail.assign_propagation(lit, clause_id);
                            }
                        }
                    }
                }
            }
        }
    }

    /// Run clause-database reduction and the restart check, keeping the theory's
    /// view of the trail in sync.
    ///
    /// A restart backtracks the trail (to level 0 for the global strategies, or a
    /// local level for `LocalLbd`) purely inside the Boolean core — `restart()`
    /// only holds `&mut self` and cannot reach the theory. Without notifying the
    /// theory, its per-atom polarity bookkeeping keeps the assignments the restart
    /// just discarded and, on the next check, reports a "conflict" whose clause
    /// still lists those now-unassigned literals. That stale clause is not a real
    /// conflict (its open literals are unassigned), and feeding it into
    /// conflict analysis corrupts the trail (see `analyze_theory_conflict`). By
    /// detecting the trail shrinking and forwarding the new level through
    /// `on_backtrack`, the theory unwinds exactly what the Boolean core did, so no
    /// stale literal survives into the next theory check. `theory_processed` is
    /// clamped to the shortened trail so the newly-restored prefix is re-sent to
    /// the theory on the following iteration.
    fn handle_deletion_restart_with_theory<T: TheoryCallback>(
        &mut self,
        theory: &mut T,
        theory_processed: &mut usize,
    ) {
        let level_before = self.trail.decision_level();
        self.handle_clause_deletion_and_restart();
        let level_after = self.trail.decision_level();
        if level_after < level_before {
            theory.on_backtrack(level_after);
            // The restart backtracked inside `handle_clause_deletion_and_restart`,
            // so the rollback boundary is not returned here. The propagation head
            // is rewound to that boundary by every rollback, so it is a safe (never
            // too large) stand-in — important under chronological backtracking,
            // where literals surviving the rollback are re-appended above the
            // boundary and must be re-sent to the theory.
            *theory_processed = (*theory_processed).min(self.trail.propagation_head());
        }
    }
}
