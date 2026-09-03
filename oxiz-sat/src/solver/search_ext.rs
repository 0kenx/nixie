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
    /// instead – which is what the theory-conflict branches used to do – skips
    /// BCP: the learned clause's asserting literal (for a unit lemma, a fresh
    /// level-0 fact) is appended to the trail but never propagated. If the theory
    /// conflict happens to resolve the *last* unassigned variable, `pick_branch_var`
    /// then reports "all assigned", `final_check` sees a theory-consistent atom
    /// assignment and answers `Sat` – over a trail on which an **original** clause
    /// is already falsified by level-0 facts alone. The instance is `Unsat` and
    /// the caller is handed a model that does not satisfy the formula.
    pub fn solve_with_theory<T: TheoryCallback>(&mut self, theory: &mut T) -> SolverResult {
        // LRAT: solve-entry deferred parse-unit flush (see `Solver::solve`).
        if !self.pending_parse_unit_flushes.is_empty() {
            let pending = core::mem::take(&mut self.pending_parse_unit_flushes);
            for (lit, cid) in pending {
                self.flush_level0_unit(lit, cid);
            }
        }
        // Mark the search as theory-carrying so `inprocess` can drop its
        // pure-literal pass (unsound when theory lemmas may later force the
        // opposite polarity of a Boolean-pure variable – see
        // `TheoryCallback::is_real_theory`).  Saved and restored so a nesting
        // `solve` (which calls this with a no-op theory) does not inherit the
        // flag.
        let saved_theory_attached = self.real_theory_attached;
        self.real_theory_attached = theory.is_real_theory();
        let result = self.solve_with_theory_inner(theory);
        self.real_theory_attached = saved_theory_attached;
        result
    }

    /// The body of [`Self::solve_with_theory`], split out so the
    /// `real_theory_attached` save/restore above cannot be bypassed by an
    /// early return.
    fn solve_with_theory_inner<T: TheoryCallback>(&mut self, theory: &mut T) -> SolverResult {
        if self.trivially_unsat {
            return SolverResult::Unsat;
        }

        // Initial propagation.  A conflict here completes an UNSAT proof, so
        // emit the empty clause into the proof stream (`solve`'s pre-search
        // passes do the same); a no-op unless proof logging is attached.
        if let Some(conflict) = self.propagate() {
            self.drat_emit_empty(Some(conflict));
            return SolverResult::Unsat;
        }

        // Track how many assignments have been sent to the theory.
        // We only send NEW assignments (not previously processed ones) to avoid
        // duplicate theory constraints that would cause spurious UNSAT.
        let mut theory_processed: usize = 0;

        // cadical `init_search_limits`: (re-)initialize the rephase limit and
        // reset the per-mode rephase round counters on every solve, so an
        // incremental second `check-sat` starts the phase schedule from fresh
        // while keeping the target/best arrays (they are only ever refined
        // and stay the best material a rephase can replay).
        self.init_rephase_limits();

        'search: loop {
            // Resource budget / interrupt check: honor a configured conflict
            // limit or an external interrupt by returning Unknown.
            if self.should_stop_search() {
                return SolverResult::Unknown;
            }

            // A mid-search inprocessing pass (elimination) can derive the
            // empty clause without leaving a falsified clause for
            // propagation to trip over, so poll the flag here.
            if self.trivially_unsat {
                if !self.lrat {
                    self.drat_emit_empty(None);
                }
                return SolverResult::Unsat;
            }

            // Boolean propagation
            if let Some(conflict) = self.propagate() {
                self.stats.conflicts += 1;

                if self.trail.decision_level() == 0 {
                    // Conflict under only level-0 facts: UNSAT, and the proof
                    // stream needs the empty clause (see `Solver::solve`).
                    self.drat_emit_empty(Some(conflict));
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
                    self.drat_emit_empty(Some(conflict));
                    return SolverResult::Unsat;
                }

                self.trace_conflict(
                    "bool",
                    self.trail.decision_level(),
                    learnt_clause.len(),
                    backtrack_level,
                );
                theory.on_backtrack(backtrack_level);
                // Clamp the theory cursor to the rollback boundary, not to the
                // trail length: chronological backtracking re-appends the
                // literals that survive the rollback above that boundary, and
                // the theory – which was just told to unwind to
                // `backtrack_level` – has to see them again.
                self.backtrack_with_phase_saving(backtrack_level);
                let boundary = self.trail.assignments().len();
                theory_processed = theory_processed.min(boundary);
                self.learn_clause(learnt_clause);

                self.decay_vsids();
                if self.config.use_chb_branching {
                    self.chb.decay();
                }
                if self.config.use_lrb_branching {
                    self.lrb.decay();
                    self.lrb.on_conflict();
                }
                self.decay_clause_activity();
                self.handle_deletion_restart_with_theory(theory, &mut theory_processed);
                continue;
            }

            // Theory propagation check after each assignment
            loop {
                let mut theory_conflict = None;
                let mut theory_propagations = Vec::new();

                // Process only NEW (unprocessed) trail assignments.  Iterate the
                // trail slice in place – the previous code cloned the *entire*
                // trail (`to_vec()`) on every iteration of this loop, which is
                // O(trail) allocation + copy per theory-check and dominated QF_UF
                // runtime (trails reach thousands of literals).  The trail is not
                // mutated inside this loop – only after, when propagations /
                // conflicts are applied – so holding an immutable borrow across
                // the `on_assignment` calls (which take `&mut theory`, a separate
                // parameter, not `&mut self`) is sound.
                let new_len = {
                    let trail = self.trail.assignments();
                    // Guard against stale theory_processed after backtracks/restarts.
                    let safe_start = theory_processed.min(trail.len());
                    for &lit in &trail[safe_start..] {
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
                    trail.len()
                };
                // Update processed count
                theory_processed = new_len;

                // Handle theory conflict
                if let Some(conflict_lits) = theory_conflict {
                    self.stats.conflicts += 1;
                    // Candidate theory lemma for downstream proof
                    // consumers (certified mode re-verifies before use).
                    theory.record_lemma(&conflict_lits);

                    if self.trail.decision_level() == 0 {
                        self.drat_emit_empty(None);
                        return SolverResult::Unsat;
                    }

                    let (backtrack_level, learnt_clause) =
                        self.analyze_theory_conflict(&conflict_lits);

                    // Empty learned clause signals all-level-0 conflict = fundamental UNSAT
                    if learnt_clause.is_empty() {
                        self.trivially_unsat = true;
                        self.drat_emit_empty(None);
                        return SolverResult::Unsat;
                    }

                    self.trace_conflict(
                        "theory-assign",
                        self.trail.decision_level(),
                        learnt_clause.len(),
                        backtrack_level,
                    );
                    theory.on_backtrack(backtrack_level);
                    self.backtrack_with_phase_saving(backtrack_level);
                    let boundary = self.trail.assignments().len();
                    theory_processed = theory_processed.min(boundary);
                    self.learn_clause(learnt_clause);

                    self.decay_vsids();
                    if self.config.use_chb_branching {
                        self.chb.decay();
                    }
                    if self.config.use_lrb_branching {
                        self.lrb.decay();
                        self.lrb.on_conflict();
                    }
                    self.decay_clause_activity();
                    self.handle_deletion_restart_with_theory(theory, &mut theory_processed);
                    // Rejoin the outer loop, NOT this one: the clause just learned
                    // put its asserting literal on the trail unpropagated, and only
                    // `'search`'s leading `propagate()` closes that gap. See the
                    // propagation-fixpoint invariant on `solve_with_theory`.
                    continue 'search;
                }

                // Handle theory propagations.
                //
                // Split empty-reason (unconditional) propagations from
                // reasoned ones. A non-empty reason yields a regular two-watched
                // explanation clause assigned at the current level. An empty
                // reason is a level-0 theory fact: a unit cannot be two-watched,
                // and using it as a mid-level propagation reason breaks 1-UIP
                // conflict analysis (it resolves to nothing, so the propagated
                // literal becomes a spurious UIP and the learned clause can
                // negate a genuinely-forced atom → false UNSAT). Such facts
                // must be installed at level 0 – handled first, which discards
                // the reasoned propagations in a mixed batch (they were derived
                // from the now-backtracked trail and will be re-derived).
                let has_units = theory_propagations.iter().any(|(_, r)| r.is_empty());
                if has_units {
                    let units: SmallVec<[Lit; 4]> = theory_propagations
                        .iter()
                        .filter(|(_, r)| r.is_empty())
                        .map(|(l, _)| *l)
                        .collect();
                    if self.install_theory_units(theory, &mut theory_processed, &units) {
                        return SolverResult::Unsat;
                    }
                    // Restart the theory loop so the newly forced level-0
                    // literals are re-sent to the theory via on_assignment.
                    continue;
                }

                let mut made_propagation = false;
                for (lit, reason_lits) in theory_propagations {
                    // The explanation clause `lit ∨ ¬r₁ ∨ … ∨ ¬rₖ` is a
                    // theory lemma whether or not it is materialized below
                    // (the lazy path keeps it immaterialized, but conflict
                    // analysis still resolves through it, so the final
                    // refutation depends on it either way).
                    if !reason_lits.is_empty() {
                        let mut lemma_clause: SmallVec<[Lit; 8]> =
                            SmallVec::with_capacity(reason_lits.len() + 1);
                        lemma_clause.push(lit);
                        for &r in &reason_lits {
                            lemma_clause.push(r.negate());
                        }
                        theory.record_lemma(&lemma_clause);
                    }
                    if !self.trail.is_assigned(lit.var()) {
                        if self.theory_lazy_reasons_enabled() && !reason_lits.is_empty() {
                            // Lazy explanation: no clause is materialized; the
                            // antecedents live in `theory_prop_reasons` and are
                            // resolved through only when conflict analysis
                            // actually reaches this literal. (With a proof
                            // connected, `add_theory_reason_clause` below keeps
                            // the reason in the database where the checker can
                            // see it.)
                            self.assign_theory_propagation(lit, reason_lits);
                        } else {
                            // Materialize the two-watched reason clause and
                            // propagate at the current level.  Each fire adds a
                            // fresh clause by design: they are Local-tier (75%
                            // deleted per reduction cycle), so the database
                            // self-limits, and the surviving duplicates act as
                            // deletion redundancy for hot lemmas – measured
                            // dedup-with-reuse against this showed a single
                            // reused clause gets deleted between fires and the
                            // search loses the lemma (+30% conflicts on
                            // propagation-storm inputs).
                            let clause_id = self.add_theory_reason_clause(&reason_lits, lit);
                            self.theory_reason_clauses += 1;
                            self.trail.assign_propagation(lit, clause_id);
                        }
                        made_propagation = true;
                    }
                }

                if made_propagation {
                    // Re-run Boolean propagation
                    if let Some(conflict) = self.propagate() {
                        self.stats.conflicts += 1;

                        if self.trail.decision_level() == 0 {
                            self.drat_emit_empty(Some(conflict));
                            return SolverResult::Unsat;
                        }

                        let (backtrack_level, learnt_clause) = self.analyze(conflict);

                        // Empty learned clause = genuine root-level (level-0)
                        // refutation → UNSAT (see the companion guard above).
                        if learnt_clause.is_empty() {
                            self.trivially_unsat = true;
                            self.drat_emit_empty(Some(conflict));
                            return SolverResult::Unsat;
                        }

                        self.trace_conflict(
                            "theory-prop",
                            self.trail.decision_level(),
                            learnt_clause.len(),
                            backtrack_level,
                        );
                        theory.on_backtrack(backtrack_level);
                        self.backtrack_with_phase_saving(backtrack_level);
                        let boundary = self.trail.assignments().len();
                        theory_processed = theory_processed.min(boundary);
                        self.learn_clause(learnt_clause);

                        self.decay_vsids();
                        if self.config.use_chb_branching {
                            self.chb.decay();
                        }
                        if self.config.use_lrb_branching {
                            self.lrb.decay();
                            self.lrb.on_conflict();
                        }
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
            // guard is the belt to that braces – one comparison, and it makes the
            // invariant hold no matter how the branches above are later edited.
            if self.trail.has_pending_propagation() {
                continue 'search;
            }

            // Try to decide
            // Propagation-fixpoint diagnostic (`OXIZ_CHECK_FIXPOINT`): a
            // debug-build-only sweep that catches a hanging unit at the
            // decision point (a clause with exactly one unassigned literal
            // that propagation should already have fired on).  Costs one
            // env check when unset; was the first tool reached for when
            // auditing the shallow-cascade anomaly (it came back clean).
            #[cfg(all(feature = "std", debug_assertions))]
            if std::env::var("OXIZ_CHECK_FIXPOINT").is_ok()
                && self.stats.decisions.is_multiple_of(100)
                && let Err(msg) = crate::invariants::check_unit_propagation_complete(self)
            {
                eprintln!(
                    "FIXPOINT-VIOLATION at decision {}: {msg}",
                    self.stats.decisions
                );
            }
            if let Some(var) = self.pick_branch_var() {
                self.stats.decisions += 1;
                self.trail.new_decision_level();
                let new_level = self.trail.decision_level();
                theory.on_new_level(new_level);

                let polarity = self.decision_polarity(var);
                let lit = if polarity {
                    Lit::pos(var)
                } else {
                    Lit::neg(var)
                };
                self.trail.assign_decision(lit);
                self.trace_decision(var, new_level, polarity);
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
                        // Candidate theory lemma for downstream proof
                        // consumers (certified mode re-verifies before use).
                        theory.record_lemma(&conflict_lits);

                        if self.trail.decision_level() == 0 {
                            self.drat_emit_empty(None);
                            return SolverResult::Unsat;
                        }

                        let (backtrack_level, learnt_clause) =
                            self.analyze_theory_conflict(&conflict_lits);

                        // If all conflict literals are at level 0, analyze_theory_conflict
                        // returns an empty learned clause as a signal of fundamental UNSAT.
                        if learnt_clause.is_empty() {
                            self.trivially_unsat = true;
                            self.drat_emit_empty(None);
                            return SolverResult::Unsat;
                        }

                        self.trace_conflict(
                            "final-check",
                            self.trail.decision_level(),
                            learnt_clause.len(),
                            backtrack_level,
                        );
                        theory.on_backtrack(backtrack_level);
                        self.backtrack_with_phase_saving(backtrack_level);
                        let boundary = self.trail.assignments().len();
                        theory_processed = theory_processed.min(boundary);
                        self.learn_clause(learnt_clause);

                        self.decay_vsids();
                        if self.config.use_chb_branching {
                            self.chb.decay();
                        }
                        if self.config.use_lrb_branching {
                            self.lrb.decay();
                            self.lrb.on_conflict();
                        }
                        self.decay_clause_activity();
                        self.handle_deletion_restart_with_theory(theory, &mut theory_processed);
                    }
                    TheoryCheckResult::Propagated(props) => {
                        // Handle late propagations with the same sound split as
                        // the mid-search path: unconditional facts become
                        // level-0 units, reasoned ones become two-watched
                        // explanation clauses.
                        let has_units = props.iter().any(|(_, r)| r.is_empty());
                        if has_units {
                            let units: SmallVec<[Lit; 4]> = props
                                .iter()
                                .filter(|(_, r)| r.is_empty())
                                .map(|(l, _)| *l)
                                .collect();
                            if self.install_theory_units(theory, &mut theory_processed, &units) {
                                return SolverResult::Unsat;
                            }
                            // Loop back: the outer loop re-decides from the new
                            // level-0 state (final_check fired at a full
                            // assignment, so the forced unit opens new search).
                        } else {
                            for (lit, reason_lits) in props {
                                if !self.trail.is_assigned(lit.var()) {
                                    if self.theory_lazy_reasons_enabled() && !reason_lits.is_empty()
                                    {
                                        self.assign_theory_propagation(lit, reason_lits);
                                    } else {
                                        let clause_id =
                                            self.add_theory_reason_clause(&reason_lits, lit);
                                        self.theory_reason_clauses += 1;
                                        self.trail.assign_propagation(lit, clause_id);
                                    }
                                }
                            }
                        }
                    }
                }
            }
        }
    }

    /// Install a batch of *unconditional* (empty-reason) theory facts as
    /// permanent level-0 units, backtracking to the root first and notifying
    /// the theory so its trail view stays in sync.
    ///
    /// An empty reason means the propagated literal is a consequence of nothing
    /// on the trail – a theory tautology. It must live at level 0: a unit
    /// clause cannot be two-watched, and using one as the reason of a mid-level
    /// propagation breaks 1-UIP conflict analysis. Each fact is stored as a
    /// Core-tier unit clause ([`Solver::force_theory_unit`]) and forced as a
    /// level-0 decision.
    ///
    /// `theory_processed` is clamped to the post-backtrack trail so the newly
    /// forced literals are re-sent to the theory on the next `on_assignment`
    /// sweep. Returns `true` if installing the units discovered a contradiction
    /// at level 0 (with `trivially_unsat` set); the caller then returns `Unsat`.
    fn install_theory_units<T: TheoryCallback>(
        &mut self,
        theory: &mut T,
        theory_processed: &mut usize,
        units: &[Lit],
    ) -> bool {
        // Backtrack to root so the units can be assigned at level 0.
        if self.trail.decision_level() > 0 {
            theory.on_backtrack(0);
            self.backtrack_with_phase_saving(0);
            *theory_processed = (*theory_processed).min(self.trail.assignments().len());
        }
        for &lit in units {
            // The theory's view was just rewound to level 0, so a unit may now
            // collide with a pre-existing level-0 fact.
            match self.trail.lit_value(lit) {
                LBool::True => {}
                LBool::False => {
                    self.trivially_unsat = true;
                    return true;
                }
                LBool::Undef => self.force_theory_unit(lit),
            }
        }
        if self.propagate().is_some() {
            self.trivially_unsat = true;
            return true;
        }
        false
    }

    /// Run clause-database reduction and the restart check, keeping the theory's
    /// view of the trail in sync.
    ///
    /// A restart backtracks the trail (to level 0 for the global strategies, or a
    /// local level for `LocalLbd`) purely inside the Boolean core – `restart()`
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
            // too large) stand-in – important under chronological backtracking,
            // where literals surviving the rollback are re-appended above the
            // boundary and must be re-sent to the theory.
            *theory_processed = (*theory_processed).min(self.trail.propagation_head());
        }
    }
}
