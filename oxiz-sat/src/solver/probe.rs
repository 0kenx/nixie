//! Failed-literal probing with on-the-fly hyper-binary resolution.
//!
//! Both passes tentatively assign a currently-unassigned literal at a fresh
//! decision level, run bounded propagation, and undo the assignment
//! afterward — the decision itself is never committed to the search. What
//! survives is only what BCP proves as a genuine consequence of the formula:
//!
//! * **Failed-literal probing**: if assigning `r` propagates to a conflict,
//!   the formula entails `¬r` unconditionally (every model must set `r`
//!   false), so `¬r` is forced as a permanent level-0 fact.
//! * **Hyper-binary resolution**: if assigning `r` does *not* conflict, every
//!   literal `q` it forced through a clause of length > 2 satisfies `r → q`
//!   purely because `r` falsified that clause's other literals — so the
//!   binary clause `(¬r ∨ q)` is implied by the formula and can be added
//!   outright, strengthening the binary implication graph for every
//!   propagation and probe that follows.
//!
//! Reference (technique, not implementation): Biere & Fröhlich's `kitten`/
//! CaDiCaL probing (failed-literal elimination + hyper-binary resolution),
//! itself tracing back to Freeman's failed-literal rule.
//!
//! Deliberately count-based rather than wall-clock-based: `oxiz-sat`'s
//! `solver` module has no `std` feature gate (it must build `no_std`), and a
//! step-count budget is reproducible across machines, which a millisecond
//! budget is not.

use super::*;

impl Solver {
    /// One round of failed-literal probing over every currently-unassigned
    /// variable, forcing a permanent unit for every literal whose assignment
    /// self-contradicts. Only runs at decision level 0 (probing is a
    /// pre-search / inprocessing pass, not something to interleave with a
    /// live search trail).
    ///
    /// Bounded by a propagation-count budget scaled to the instance size so
    /// a densely-connected formula cannot make a single call unboundedly
    /// expensive; once the budget is spent the remaining variables are left
    /// unprobed rather than skipped-and-forgotten (a later probing round can
    /// pick them back up).
    ///
    /// Returns the number of units forced.
    ///
    /// Skipped outright while any proof (DRAT or LRAT) is being traced: a
    /// forced unit here is always self-justifying for DRAT (it is exactly
    /// the failed-literal property — assuming its negation reaches a
    /// conflict via the current formula alone), but this pass does not (yet)
    /// build the hint chain LRAT needs, and — importantly — neither this nor
    /// [`Self::probe_hyper_binaries`] previously checked `self.drat` at all,
    /// so a DRAT proof recorded with probing enabled could silently omit a
    /// clause the rest of the derivation went on to depend on. Gating both
    /// off here closes that gap rather than half-fixing it for DRAT only.
    pub(super) fn failed_literal_probing(&mut self) -> usize {
        if self.trail.decision_level() != 0 || self.proof_tracing_active() {
            return 0;
        }

        // A budget of ~256 propagation steps per variable comfortably covers
        // a full two-polarity probe on all but pathologically dense
        // instances, while keeping the whole pass linear-ish in problem size
        // instead of unbounded.
        let mut budget_left = (self.num_vars as u64).saturating_mul(256).max(20_000);
        let mut forced = 0usize;

        for i in 0..self.num_vars {
            if self.trivially_unsat || budget_left == 0 {
                break;
            }
            let var = Var::new(i as u32);
            if self.trail.is_assigned(var) {
                continue;
            }

            let per_probe_cap = budget_left.min(50_000);
            if self.probe_literal_conflicts(Lit::pos(var), per_probe_cap) {
                self.force_permanent_unit(Lit::neg(var));
                forced += 1;
            } else if !self.trivially_unsat
                && self.probe_literal_conflicts(Lit::neg(var), per_probe_cap)
            {
                self.force_permanent_unit(Lit::pos(var));
                forced += 1;
            }
            budget_left = budget_left.saturating_sub(per_probe_cap);
        }
        forced
    }

    /// Tentatively assign `lit` at a fresh decision level, propagate under
    /// `step_cap`, then unwind unconditionally. Returns `true` only when the
    /// probe reached a genuine conflict — an aborted (budget-exhausted) probe
    /// is treated as "no information", matching [`Self::propagate_bounded`]'s
    /// contract that an aborted pass proves nothing either way.
    fn probe_literal_conflicts(&mut self, lit: Lit, step_cap: u64) -> bool {
        self.trail.new_decision_level();
        self.trail.assign_decision(lit);
        let (conflict, aborted) = self.propagate_bounded(step_cap);
        self.backtrack(0);
        conflict && !aborted
    }

    /// Force `lit` as a permanent (level-0) fact and propagate its
    /// consequences. Must only be called at decision level 0. Sets
    /// `trivially_unsat` instead of panicking if `lit` is already falsified —
    /// the caller (probing) derived `lit` from a sound proof, so a clash here
    /// means the *formula* is unsatisfiable, not that anything went wrong.
    fn force_permanent_unit(&mut self, lit: Lit) {
        match self.trail.lit_value(lit) {
            LBool::True => return,
            LBool::False => {
                self.trivially_unsat = true;
                return;
            }
            LBool::Undef => {}
        }
        self.trail.assign_unit_fact(lit);
        if self.propagate().is_some() {
            self.trivially_unsat = true;
        }
    }

    /// One round of hyper-binary-resolution probing: for every currently
    /// unassigned literal `r`, tentatively assign it and see what non-binary
    /// clauses it forces unit. Each such consequence `q` licenses the learned
    /// binary `(¬r ∨ q)` (see the module doc for why). Also forces a
    /// permanent unit for any `r` whose probe conflicts outright, exactly
    /// like [`Self::failed_literal_probing`] — the two passes are natural
    /// companions, so this one performs both jobs in a single sweep over the
    /// trail contents built by each probe.
    ///
    /// Returns `(failed_units, hyper_binaries_added)`.
    ///
    /// Skipped outright while any proof is being traced — see
    /// [`Self::failed_literal_probing`]'s doc comment; the same reasoning
    /// applies to the hyper-binary clauses this pass adds.
    pub(super) fn probe_hyper_binaries(&mut self) -> (usize, usize) {
        if self.trail.decision_level() != 0 || self.proof_tracing_active() {
            return (0, 0);
        }

        let mut budget_left = (self.num_vars as u64).saturating_mul(256).max(20_000);
        let mut failed = 0usize;
        let mut hyper = 0usize;

        for i in 0..self.num_vars {
            if self.trivially_unsat || budget_left == 0 {
                break;
            }
            let var = Var::new(i as u32);
            if self.trail.is_assigned(var) {
                continue;
            }
            let r = Lit::pos(var);
            let per_probe_cap = budget_left.min(20_000);
            budget_left = budget_left.saturating_sub(per_probe_cap);

            self.trail.new_decision_level();
            self.trail.assign_decision(r);
            let (conflict, aborted) = self.propagate_bounded(per_probe_cap);
            if conflict {
                self.backtrack(0);
                self.force_permanent_unit(r.negate());
                failed += 1;
            } else if aborted {
                // Densely connected from this literal — bail without drawing
                // any conclusion, exactly like a failed-probe timeout.
                self.backtrack(0);
            } else {
                self.learn_hyper_binaries_from_probe(r, &mut hyper);
                self.backtrack(0);
            }
        }
        (failed, hyper)
    }

    /// After a non-conflicting probe of `r`, add `(¬r ∨ q)` for every literal
    /// `q` the probe forced through a reason clause of length > 2 (a binary
    /// reason is already an edge in the implication graph, so only
    /// non-binary reasons contribute anything new).
    fn learn_hyper_binaries_from_probe(&mut self, r: Lit, hyper: &mut usize) {
        let forced: SmallVec<[Lit; 64]> = self.trail.level_assignments().to_vec().into();
        // Cap how many binaries a single probe may contribute so one
        // extremely well-connected literal cannot flood the binary graph.
        const MAX_PER_PROBE: usize = 64;
        let mut added = 0usize;
        for q in forced {
            if added >= MAX_PER_PROBE {
                break;
            }
            let Reason::Propagation(reason_id) = self.trail.reason(q.var()) else {
                continue;
            };
            let is_long_reason = self
                .clauses
                .get(reason_id)
                .is_some_and(|c| !c.deleted && c.lits.len() > 2);
            if !is_long_reason {
                continue;
            }
            if self.has_binary_implication(r, q) {
                continue;
            }
            let binary_lits = [r.negate(), q];
            // Every other path that learns a binary clause
            // (`Solver::learn_clause`'s two-literal branch,
            // `Solver::check_hyper_binary_resolution`) computes and stores an
            // LBD; leaving it at `Clause::learned`'s default of 0 would give
            // this clause `lbd <= 2`'s automatic promotion straight to the
            // rarely-deleted Core tier regardless of its actual quality — see
            // `check_hyper_binary_resolution`'s own note on exactly this
            // defect.
            let lbd = self.compute_lbd(&binary_lits);
            let clause_id = self.clauses.add_learned(binary_lits);
            if let Some(clause) = self.clauses.get_mut(clause_id) {
                clause.lbd = lbd;
                clause.assign_tier_from_lbd();
            }
            self.stats.learned_clauses += 1;
            self.stats.binary_clauses += 1;
            self.stats.total_lbd += u64::from(lbd);
            self.binary_graph.add(r, q, clause_id);
            self.binary_graph.add(q.negate(), r.negate(), clause_id);
            self.watches.add(r, Watcher::new(clause_id, q));
            self.watches
                .add(q.negate(), Watcher::new(clause_id, r.negate()));
            // Register on the same ledgers a main-loop learned binary uses
            // (`Solver::learn_clause`'s two-literal branch): both
            // `learned_clause_ids` (so it can be reduced/reported like any
            // other learned clause) and the base assertion level's own list
            // (so `pop()` can retract it, since it is only ever derived
            // while `assertion_levels.len() <= 1`).
            self.learned_clause_ids.push(clause_id);
            if let Some(ids) = self.assertion_clause_ids.last_mut() {
                ids.push(clause_id);
            }
            *hyper += 1;
            added += 1;
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_pr26_probe_forces_failed_literal() {
        // (a ∨ b) ∧ (¬a ∨ b) ∧ (¬a ∨ ¬b): assigning a=true forces b=true (from
        // clause 2) and then conflicts with clause 3 (¬a ∨ ¬b, both literals
        // false). So a is a failed literal — probing must force a=false.
        let mut solver = Solver::new();
        let a = solver.new_var();
        let b = solver.new_var();
        solver.add_clause([Lit::pos(a), Lit::pos(b)]);
        solver.add_clause([Lit::neg(a), Lit::pos(b)]);
        solver.add_clause([Lit::neg(a), Lit::neg(b)]);

        let forced = solver.failed_literal_probing();
        assert!(forced >= 1, "probing must force at least one unit");
        assert_eq!(solver.trail.lit_value(Lit::pos(a)), LBool::False);
    }

    #[test]
    fn test_pr26_probe_hyper_binary_adds_implied_binary() {
        // (¬a ∨ x ∨ y) ∧ (¬a ∨ ¬x) : probing a=true forces x=false (2nd
        // clause), which then forces y=true through the ternary clause
        // (since x is now false and it is the only remaining undetermined
        // literal besides ¬a). y's reason is the ternary clause (length 3),
        // so hyper-binary resolution should learn (¬a ∨ y).
        let mut solver = Solver::new();
        let a = solver.new_var();
        let x = solver.new_var();
        let y = solver.new_var();
        solver.add_clause([Lit::neg(a), Lit::pos(x), Lit::pos(y)]);
        solver.add_clause([Lit::neg(a), Lit::neg(x)]);

        let (_failed, hyper) = solver.probe_hyper_binaries();
        assert!(hyper >= 1, "expected at least one hyper-binary clause");
        assert!(
            solver.has_binary_implication(Lit::pos(a), Lit::pos(y)),
            "(¬a ∨ y) should have been learned as a binary"
        );
    }

    #[test]
    fn test_pr26_probe_noop_above_level_zero() {
        let mut solver = Solver::new();
        let a = solver.new_var();
        let b = solver.new_var();
        solver.add_clause([Lit::pos(a), Lit::pos(b)]);
        solver.trail.new_decision_level();
        solver.trail.assign_decision(Lit::pos(a));

        assert_eq!(solver.failed_literal_probing(), 0);
        assert_eq!(solver.probe_hyper_binaries(), (0, 0));
    }
}
