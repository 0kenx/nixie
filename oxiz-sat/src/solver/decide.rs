//! Decision heuristics, phase saving, backtracking, and restarts

use super::*;

impl Solver {
    /// Pick next variable to branch on
    pub(super) fn pick_branch_var(&mut self) -> Option<Var> {
        // Try external branching heuristic first.
        if let Some(ref ext) = self.config.external_branching {
            let candidates: Vec<Var> = (0..self.num_vars)
                .map(|i| Var::new(i as u32))
                .filter(|&v| !self.trail.is_assigned(v) && !self.var_eliminated(v))
                .collect();
            let scores: Vec<f64> = candidates.iter().map(|&v| self.vsids.activity(v)).collect();
            if let Ok(mut h) = ext.lock()
                && let Some(chosen) = h.select(&candidates, &scores)
            {
                return Some(chosen);
            }
        }

        if self.config.use_lrb_branching {
            // Use LRB branching
            while let Some(var) = self.lrb.select() {
                if !self.trail.is_assigned(var) && !self.var_eliminated(var) {
                    self.lrb.on_assign(var);
                    return Some(var);
                }
            }
        } else if self.config.use_chb_branching {
            // Use CHB branching
            // Rebuild heap periodically to reflect score changes
            if self.stats.decisions.is_multiple_of(100) {
                self.chb.rebuild_heap();
            }

            while let Some(var) = self.chb.pop_max() {
                if !self.trail.is_assigned(var) && !self.var_eliminated(var) {
                    return Some(var);
                }
            }
        } else {
            // Mode-dependent branching: focused mode favors VMTF (cheap,
            // recency-ordered decisions with no heap maintenance); stable
            // mode favors VSIDS (its activity ordering pays off over the
            // longer, quieter stable-mode runs). When the stable/focused
            // schedule itself is disabled, `use_vmtf` picks the heuristic
            // outright for the whole run.
            let vmtf_now = if self.config.enable_stabilize {
                !self.stable
            } else {
                self.config.use_vmtf
            };
            if vmtf_now {
                // `next_decision`'s closure borrows only `&self.trail` plus
                // (for the elimination check) the disjoint `equiv_*`/`bve_def`
                // fields, never `self` as a whole, so it can run alongside the
                // `&mut self.vmtf` receiver below.
                let trail = &self.trail;
                let equiv_substitution_sized = self.equiv_substitution_sized;
                let equiv_substitution = &self.equiv_substitution;
                let bve_def = &self.bve_def;
                let is_eliminated = |v: Var| {
                    let by_equiv = equiv_substitution_sized
                        && equiv_substitution
                            .get(Lit::pos(v).code() as usize)
                            .is_some_and(|&rep| rep.var() != v);
                    let by_bve = bve_def.get(v.index()).is_some_and(|def| !def.is_empty());
                    by_equiv || by_bve
                };
                if let Some(var) = self
                    .vmtf
                    .next_decision(|v| trail.is_assigned(v) || is_eliminated(v))
                {
                    return Some(var);
                }
                // VMTF found no unassigned, non-eliminated candidate (every
                // queued variable is either assigned or was removed from the
                // live formula); fall through to VSIDS below, which is always
                // kept in sync by `backtrack_with_phase_saving`/`backtrack`
                // and so remains a complete source of decisions regardless of
                // which heuristic is "active".
            }
            while let Some(var) = self.vsids.pop_max() {
                if !self.trail.is_assigned(var) && !self.var_eliminated(var) {
                    return Some(var);
                }
            }
        }

        // An exhausted heap is *not* proof that every variable is assigned.
        // All three heuristics consume their candidates destructively
        // (`pop_max` / `select`), so any variable unassigned by a rollback that
        // failed to re-insert it disappears from the search entirely.
        //
        // Both search loops read `None` as "all variables assigned - SAT" and
        // hand the trail straight to `save_model`, so a drained heap used to
        // surface as a `Sat` verdict over a *partial* assignment: the model kept
        // `Undef` entries for the lost variables and falsified clauses that
        // nothing had ever decided. Conceding only when the assignment really is
        // total makes `None` mean what its callers assume it means. With the
        // heaps kept in repair by `backtrack`, this scan is a fallback that
        // essentially never runs.
        //
        // A variable the inprocessing toolkit eliminated is deliberately
        // *excluded* here too, even though it is never actually assigned:
        // `None` from this whole function is what makes `save_model` run
        // (see `Solver::solve`), and its own reconstruction passes are what
        // give an eliminated variable its final value — branching on it
        // would try to search over clauses that no longer exist.
        (0..self.num_vars)
            .map(|i| Var::new(i as u32))
            .find(|&var| !self.trail.is_assigned(var) && !self.var_eliminated(var))
            .inspect(|&var| {
                if self.config.use_lrb_branching {
                    self.lrb.on_assign(var);
                }
            })
    }

    /// Backtrack with phase saving.
    ///
    /// Returns the trail index at which the rolled-back region started (see
    /// [`Trail::backtrack_to_with_callback`]). Callers holding a cursor into the
    /// trail must clamp it to this value, not to the trail length: under
    /// chronological backtracking, literals that survive the rollback are
    /// re-appended above this index and have to be reprocessed.
    pub(super) fn backtrack_with_phase_saving(&mut self, level: u32) -> usize {
        // Collect variables that will be unassigned
        let mut unassigned_vars = Vec::new();

        // Save phases before backtracking
        let phase = &mut self.phase;
        let lrb = &mut self.lrb;
        let boundary = self.trail.backtrack_to_with_callback(level, |lit| {
            let var = lit.var();
            if var.index() < phase.len() {
                phase[var.index()] = lit.is_pos();
            }
            // Re-insert variable into LRB heap
            lrb.unassign(var);
            unassigned_vars.push(var);
        });

        // Re-insert unassigned variables into VSIDS and CHB heaps, and let
        // VMTF's search cursor reconsider any of them that is a better
        // (more-recently-bumped) candidate than wherever it currently sits.
        for var in unassigned_vars {
            if !self.vsids.contains(var) {
                self.vsids.insert(var);
            }
            if !self.chb.contains(var) {
                self.chb.insert(var);
            }
            self.vmtf.on_unassign(var);
        }

        boundary
    }

    /// Backtrack to a given level without saving phases.
    ///
    /// Returns the rollback boundary, exactly like
    /// [`Self::backtrack_with_phase_saving`]; the only difference between the
    /// two is that this one does not record the discarded polarities.
    ///
    /// In particular it must still hand the freed variables back to the decision
    /// heaps. `pick_branch_var` pops candidates *destructively*, so a variable
    /// unassigned without being re-inserted is lost to the search for good.
    /// `solve_with_assumptions` ends every probe on this path, so each probe used
    /// to drain the heaps a little further; once they ran dry the next probe had
    /// nothing left to branch on and reported `Sat` over a partial assignment —
    /// a model with `Undef` entries that falsified clauses the search had never
    /// even looked at. The vivification and distillation probes in
    /// `learn.rs` unwind through here too, with the same consequence.
    pub(super) fn backtrack(&mut self, level: u32) -> usize {
        let mut unassigned_vars = Vec::new();

        let lrb = &mut self.lrb;
        let boundary = self.trail.backtrack_to_with_callback(level, |lit| {
            let var = lit.var();
            lrb.unassign(var);
            unassigned_vars.push(var);
        });

        for var in unassigned_vars {
            if !self.vsids.contains(var) {
                self.vsids.insert(var);
            }
            if !self.chb.contains(var) {
                self.chb.insert(var);
            }
            self.vmtf.on_unassign(var);
        }

        boundary
    }

    /// Compute the Luby sequence value for index i (1-indexed: luby(1)=1, luby(2)=1, ...)
    /// Sequence: 1, 1, 2, 1, 1, 2, 4, 1, 1, 2, 1, 1, 2, 4, 8, ...
    /// For 0-indexed input, we add 1 internally.
    pub(super) fn luby(i: u64) -> u64 {
        let i = i + 1; // Convert to 1-indexed

        // Find k such that 2^k - 1 >= i
        let mut k = 1u32;
        while (1u64 << k) - 1 < i {
            k += 1;
        }

        let seq_len = (1u64 << k) - 1;

        if i == seq_len {
            // i is exactly 2^k - 1, return 2^(k-1)
            1u64 << (k - 1)
        } else {
            // Recurse: luby(i) = luby(i - (2^(k-1) - 1))
            // The sequence up to 2^k - 1 is: luby(1..2^(k-1)-1), luby(1..2^(k-1)-1), 2^(k-1)
            let half_len = (1u64 << (k - 1)) - 1;
            if i <= half_len {
                Self::luby(i - 1) // Already 0-indexed internally
            } else if i <= 2 * half_len {
                Self::luby(i - half_len - 1)
            } else {
                1u64 << (k - 1)
            }
        }
    }

    /// Reuse-trail restart (Heule; also known as "partial restart").
    ///
    /// Rather than always discarding the whole decision trail, keep the
    /// longest prefix of decisions the search would make again anyway: a
    /// decision at level `l` is worth keeping if its variable's ranking
    /// under whichever heuristic [`Self::pick_branch_var`] is *currently*
    /// deciding from is at least as high as the ranking of the variable that
    /// heuristic would hand out *next* — meaning a fresh restart would just
    /// re-decide it (perhaps with a different polarity via phase saving, but
    /// the same variable). Levels are only ever kept as a *prefix*: the
    /// first level whose decision variable falls below the threshold, and
    /// everything after it, is discarded — a later, lower-ranked decision
    /// being kept while an earlier, higher-ranked one is dropped would leave
    /// the trail in an order the heuristic itself would never have produced.
    ///
    /// Comparing against VSIDS activity while VMTF is the one actually
    /// deciding (focused mode, per `pick_branch_var`'s own mode switch)
    /// compares two unrelated numbers: VSIDS's bump-decayed float says
    /// nothing about whether VMTF's recency queue would reconsider the same
    /// variable. Each branch below therefore uses its own heuristic's
    /// ranking for both the threshold and the walk, via the shared
    /// [`Self::reuse_prefix_len`] helper.
    ///
    /// Always returns a level strictly below the current one (or 0), so a
    /// restart is guaranteed to make backward progress — a heuristic that
    /// happens to rank every existing decision variable at or above the
    /// threshold does not turn a restart into a no-op.
    pub(super) fn reuse_trail(&self) -> u32 {
        // Neither heap-free heuristic exposes an activity ranking reuse_trail
        // can compare against.
        if self.config.use_chb_branching || self.config.use_lrb_branching {
            return 0;
        }
        if !self.config.reuse_trail {
            return 0;
        }
        let level = self.trail.decision_level();
        if level <= 1 {
            return 0;
        }

        let vmtf_now = if self.config.enable_stabilize {
            !self.stable
        } else {
            self.config.use_vmtf
        };

        if vmtf_now {
            // Mirrors `pick_branch_var`'s own VMTF eligibility check: a
            // variable that is assigned or was eliminated by the
            // inprocessing toolkit is not a candidate VMTF would ever
            // actually hand out.
            let trail = &self.trail;
            let equiv_substitution_sized = self.equiv_substitution_sized;
            let equiv_substitution = &self.equiv_substitution;
            let bve_def = &self.bve_def;
            let is_eliminated = |v: Var| {
                let by_equiv = equiv_substitution_sized
                    && equiv_substitution
                        .get(Lit::pos(v).code() as usize)
                        .is_some_and(|&rep| rep.var() != v);
                let by_bve = bve_def.get(v.index()).is_some_and(|def| !def.is_empty());
                by_equiv || by_bve
            };
            let Some(next_var) = self
                .vmtf
                .peek_next_decision(|v| trail.is_assigned(v) || is_eliminated(v))
            else {
                return 0;
            };
            let threshold = self.vmtf.activity(next_var);
            return self.reuse_prefix_len(level, threshold, |v| self.vmtf.activity(v));
        }

        let Some(next_var) = self.vsids.peek_max() else {
            return 0;
        };
        let threshold = self.vsids.activity(next_var);
        self.reuse_prefix_len(level, threshold, |v| self.vsids.activity(v))
    }

    /// Shared walk for [`Self::reuse_trail`]: the longest prefix of decision
    /// levels `1..level` whose decision variables all rank at or above
    /// `threshold` under `ranking`, kept as a *prefix* (stops at the first
    /// level that falls below it, exactly like the doc comment on the caller
    /// describes). Generic over the ranking's number type so the same walk
    /// serves VSIDS's `f64` activity and VMTF's `u64` bump timestamp.
    fn reuse_prefix_len<T: PartialOrd>(
        &self,
        level: u32,
        threshold: T,
        ranking: impl Fn(Var) -> T,
    ) -> u32 {
        let mut reuse = 0u32;
        for l in 1..level {
            let Some(dec_var) = self.trail.decision_var_at_level(l) else {
                break;
            };
            if ranking(dec_var) >= threshold {
                reuse = l;
            } else {
                break;
            }
        }
        reuse
    }

    /// Switch between *focused* and *stable* search modes once the active
    /// mode's tick budget is exhausted (cadical's `stabilizing()`).
    ///
    /// Focused mode runs frequent, cheap restarts driven by short-term glue
    /// degradation (the Glucose EMA condition) and favors VMTF decisions;
    /// stable mode runs long, quiet stretches with rare reluctant-doubling
    /// restarts, VSIDS decisions, and periodic rephasing. Alternating the two
    /// gets the exploration benefits of frequent restarts without paying
    /// their overhead for the *entire* search, and the benefits of a long
    /// stable stretch without risking getting stuck in one for the whole run.
    ///
    /// Each switch's tick budget grows quadratically in the number of
    /// switches so far, so later stretches (of both modes) run
    /// proportionally longer — mirroring how restart-avoidance strategies
    /// generally widen their commitment once early switches haven't found a
    /// decisive advantage either way.
    pub(super) fn check_stabilize(&mut self) {
        if !self.config.enable_stabilize {
            return;
        }
        let current_mode_ticks = if self.stable {
            self.ticks_stable
        } else {
            self.ticks_focused
        };
        // Ticks have barely accumulated for the very first switch, so gate it
        // on conflicts instead; every switch after that uses the tick budget.
        let ready = if self.stabphases == 0 {
            self.stats.conflicts >= self.config.stabilize_base
        } else {
            current_mode_ticks >= self.lim_stabilize
        };
        if !ready {
            return;
        }

        core::mem::swap(&mut self.glue_current, &mut self.glue_saved);
        self.stable = !self.stable;
        self.stabphases = self.stabphases.saturating_add(1);

        let phase_budget = self
            .config
            .stabilize_base
            .saturating_mul(self.stabphases)
            .saturating_mul(self.stabphases);
        let entering_mode_ticks = if self.stable {
            self.ticks_stable
        } else {
            self.ticks_focused
        };
        self.lim_stabilize = entering_mode_ticks.saturating_add(phase_budget);

        if self.stable {
            self.reluctant.arm(1024, 1 << 20);
        } else {
            self.reluctant.disarm();
        }
    }

    /// Restart
    pub(super) fn restart(&mut self) {
        self.stats.restarts += 1;

        // Best-phase tracking: remember the polarities of the longest trail
        // reached so far (before this restart discards it). A later rephase
        // round can restore this snapshot to refocus the search near the
        // best-known region instead of blindly inverting the saved phases.
        let trail_size = self.trail.size();
        if trail_size > self.best_trail_size {
            self.best_trail_size = trail_size;
            self.best_phase.resize(self.num_vars, false);
            for &lit in self.trail.assignments() {
                self.best_phase[lit.var().index()] = lit.is_pos();
            }
        }

        self.backtrack_with_phase_saving(self.reuse_trail());

        // Rephasing: periodically flip the saved-polarity baseline so the
        // next descent explores territory it would not otherwise reach by
        // phase-saving alone. Restricted to stable mode: stable mode's long,
        // quiet stretches give a phase change room to compound into a
        // meaningfully different search path, whereas under focused mode's
        // frequent restarts a rephase mostly just discards work the very
        // next restart would redo.
        if self.config.rephase_interval > 0
            && self.stable
            && self
                .stats
                .restarts
                .is_multiple_of(u64::from(self.config.rephase_interval))
        {
            self.rephase_count += 1;
            if self.rephase_count.is_multiple_of(2) || self.best_trail_size == 0 {
                // Even rounds (and the case where no snapshot exists yet):
                // invert the current baseline outright.
                self.phase_inverted = !self.phase_inverted;
            } else {
                // Odd rounds: restore the best-known partial assignment
                // instead of a blind inversion.
                let n = self.best_phase.len().min(self.phase.len());
                self.phase[..n].copy_from_slice(&self.best_phase[..n]);
                self.phase_inverted = false;
            }
        }

        // Calculate next restart threshold based on strategy
        match self.config.restart_strategy {
            RestartStrategy::Luby => {
                self.luby_index += 1;
                // Cap the raw Luby multiplier: its `2^k` growth otherwise
                // inflates the restart interval into a multi-thousand-conflict
                // grind on long runs. The cap is mode-dependent under the
                // stable/focused schedule (focused stays frequent via a small
                // cap; stable is left uncapped, matching how rare its own
                // reluctant-doubling restarts already are) and falls back to
                // the flat `luby_cap` when the schedule itself is disabled.
                let cap = if self.config.enable_stabilize {
                    if self.stable {
                        0
                    } else {
                        self.config.focused_luby_cap
                    }
                } else {
                    self.config.luby_cap
                };
                let raw = Self::luby(self.luby_index);
                let luby = if cap == 0 { raw } else { raw.min(cap) };
                self.restart_threshold = self.stats.conflicts + luby * self.config.restart_interval;
            }
            RestartStrategy::Geometric => {
                let current_interval = if self.restart_threshold > self.stats.conflicts {
                    self.restart_threshold - self.stats.conflicts
                } else {
                    self.config.restart_interval
                };
                let next_interval =
                    (current_interval as f64 * self.config.restart_multiplier) as u64;
                self.restart_threshold = self.stats.conflicts + next_interval;
            }
            RestartStrategy::Glucose => {
                // Glucose-style dynamic restarts based on LBD
                // Restart when recent average LBD is higher than global average
                // For now, use geometric with dynamic adjustment
                let current_interval = if self.restart_threshold > self.stats.conflicts {
                    self.restart_threshold - self.stats.conflicts
                } else {
                    self.config.restart_interval
                };

                // Adjust based on recent LBD trend
                let next_interval = if self.recent_lbd_count > 50 {
                    let recent_avg = self.recent_lbd_sum / self.recent_lbd_count.max(1);
                    // If recent LBD is low (good), increase interval; if high, decrease
                    if recent_avg < 5 {
                        // Good quality clauses - increase interval
                        ((current_interval as f64) * 1.1) as u64
                    } else {
                        // Poor quality clauses - decrease interval
                        ((current_interval as f64) * 0.9) as u64
                    }
                } else {
                    current_interval
                };

                self.restart_threshold = self.stats.conflicts + next_interval.max(100);
            }
            RestartStrategy::LocalLbd => {
                // Local restarts based on LBD
                // Check if we should do a local restart
                self.conflicts_since_local_restart += 1;

                if self.conflicts_since_local_restart >= 50 && self.should_local_restart() {
                    // Perform local restart - backtrack to a safe level, not to 0
                    let local_level = self.compute_local_restart_level();
                    self.backtrack_with_phase_saving(local_level);
                    self.conflicts_since_local_restart = 0;
                    // Reset recent LBD for next window
                    self.recent_lbd_sum = 0;
                    self.recent_lbd_count = 0;
                } else {
                    // Standard restart if too many conflicts
                    let current_interval = if self.restart_threshold > self.stats.conflicts {
                        self.restart_threshold - self.stats.conflicts
                    } else {
                        self.config.restart_interval
                    };
                    self.restart_threshold = self.stats.conflicts + current_interval;
                }
                return; // Don't do full backtrack to 0
            }
        }

        // Re-add all unassigned variables to VSIDS heap
        for i in 0..self.num_vars {
            let var = Var::new(i as u32);
            if !self.trail.is_assigned(var) && !self.vsids.contains(var) {
                self.vsids.insert(var);
            }
        }
    }

    /// Check if we should perform a local restart
    /// Returns true if recent average LBD is significantly higher than global average
    pub(super) fn should_local_restart(&self) -> bool {
        if self.recent_lbd_count < 50 || self.global_lbd_count < 100 {
            return false;
        }

        let recent_avg = self.recent_lbd_sum / self.recent_lbd_count.max(1);
        let global_avg = self.global_lbd_sum / self.global_lbd_count.max(1);

        // Local restart if recent average is 1.25x higher than global average
        recent_avg * 4 > global_avg * 5
    }

    /// Compute the level to backtrack to for local restart
    /// Use a level that preserves some of the search progress
    pub(super) fn compute_local_restart_level(&self) -> u32 {
        let current_level = self.trail.decision_level();

        // Backtrack to about 20% of current depth to preserve some work
        if current_level > 5 {
            current_level / 5
        } else {
            0
        }
    }

    /// Seed the internal xorshift64 PRNG from a user-supplied `:random-seed`.
    ///
    /// The raw seed is mixed through a splitmix64 step before it becomes the
    /// xorshift state, because xorshift64 has a fixed point at `0`: a raw seed of
    /// `0` (the single most common user choice) would otherwise disable phase
    /// randomization entirely.  The mixing also spreads nearby seeds (`1`, `2`,
    /// `3`, …) into well-separated states so consecutive seeds explore genuinely
    /// different search orders.  A seed of `0` maps to the historical default
    /// state, so `set_random_seed(0)` reproduces the out-of-the-box behaviour.
    pub fn set_random_seed(&mut self, seed: u64) {
        self.rng_state = Self::seed_to_rng_state(seed);
    }

    /// Derive a nonzero xorshift64 state from a user seed via one splitmix64
    /// round.  A seed of `0` (or any input that mixes to `0`) falls back to the
    /// solver's historical default state so default behaviour is preserved.
    #[must_use]
    pub(crate) fn seed_to_rng_state(seed: u64) -> u64 {
        const DEFAULT_STATE: u64 = 0x853c_49e6_748f_ea9b;
        if seed == 0 {
            return DEFAULT_STATE;
        }
        let mut z = seed.wrapping_add(0x9E37_79B9_7F4A_7C15);
        z = (z ^ (z >> 30)).wrapping_mul(0xBF58_476D_1CE4_E5B9);
        z = (z ^ (z >> 27)).wrapping_mul(0x94D0_49BB_1331_11EB);
        z ^= z >> 31;
        if z == 0 { DEFAULT_STATE } else { z }
    }

    /// Generate a random u64 using xorshift64
    pub(super) fn rand_u64(&mut self) -> u64 {
        let mut x = self.rng_state;
        x ^= x << 13;
        x ^= x >> 7;
        x ^= x << 17;
        self.rng_state = x;
        x
    }

    /// Generate a random f64 in [0, 1)
    pub(super) fn rand_f64(&mut self) -> f64 {
        const MAX: f64 = u64::MAX as f64;
        (self.rand_u64() as f64) / MAX
    }

    /// Generate a random boolean with given probability of being true
    pub(super) fn rand_bool(&mut self, probability: f64) -> bool {
        self.rand_f64() < probability
    }
}
