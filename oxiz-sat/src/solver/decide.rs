//! Decision heuristics, phase saving, backtracking, and restarts

use super::*;

/// Whether decision/conflict tracing is enabled (env var `OXIZ_TRACE_DECISIONS`).
///
/// Read once and cached in a `OnceLock` so the per-decision cost when *off*
/// is a single load. Truthy unless the value is empty, `"0"`, or `"false"`
/// (case-insensitive). Only meaningful under the `std` feature (env access +
/// stderr both need it); without `std` tracing is always disabled.
#[cfg(feature = "std")]
fn trace_decisions_enabled() -> bool {
    use std::sync::OnceLock;
    static FLAG: OnceLock<bool> = OnceLock::new();
    *FLAG.get_or_init(|| {
        std::env::var("OXIZ_TRACE_DECISIONS")
            .is_ok_and(|v| !v.is_empty() && v != "0" && !v.eq_ignore_ascii_case("false"))
    })
}

#[cfg(not(feature = "std"))]
fn trace_decisions_enabled() -> bool {
    false
}

/// Which snapshot array [`Solver::copy_phases`] writes (`phases.target` /
/// `phases.best` in cadical).
#[derive(Clone, Copy)]
pub(super) enum PhaseArray {
    /// `phases.target`.
    Target,
    /// `phases.best`.
    Best,
}

impl Solver {
    /// Pick next variable to branch on
    pub(super) fn pick_branch_var(&mut self) -> Option<Var> {
        // Finite-domain equalities first (O(|priority|), not O(num_vars)).
        if !self.domain_priority.is_empty() {
            for &v in &self.domain_priority {
                if !self.trail.is_assigned(v) && !self.var_eliminated(v) {
                    self.last_branch_source = BranchSource::Domain;
                    return Some(v);
                }
            }
        }

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
                self.last_branch_source = BranchSource::External;
                return Some(chosen);
            }
        }

        if self.config.use_lrb_branching {
            // Use LRB branching
            while let Some(var) = self.lrb.select() {
                if !self.trail.is_assigned(var) && !self.var_eliminated(var) {
                    self.lrb.on_assign(var);
                    self.last_branch_source = BranchSource::Lrb;
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
                    self.last_branch_source = BranchSource::Chb;
                    return Some(var);
                }
            }
        } else {
            // Mode-dependent branching (cadical use_scores = score && stable):
            // focused → VMTF, stable → VSIDS/EVSIDS.
            // cadical uses VMTF scores in focused mode and VSIDS in stable;
            // the CDCL(T) loop opts out via `focused_vmtf=false` to run VSIDS
            // in both modes, matching z3's smt_context (EVSIDS throughout) –
            // measured 91:45 vs VMTF-focused on a 150-file QF_UF sample, with
            // every family member improving (e.g. quasigroup icl785 1.49s →
            // 0.76s).
            let use_vmtf_now = if self.config.enable_stabilize {
                !self.stable && self.config.focused_vmtf
            } else {
                self.config.use_vmtf
            };
            if use_vmtf_now {
                // Borrow only `trail`, `equiv_substitution`, and `bve_def`
                // (disjoint from the `&mut self.vmtf` the call below needs) –
                // a full `&self` method like `var_eliminated` would conflict.
                let trail = &self.trail;
                let subst = &self.equiv_substitution;
                let bve = &self.bve_def;
                let eliminated = |v: Var| {
                    subst.get(v.index()).is_some_and(|&r| r.var() != v)
                        || bve.get(v.index()).is_some_and(|d| !d.is_empty())
                };
                if let Some(var) = self
                    .vmtf
                    .next_decision(|v| trail.is_assigned(v) || eliminated(v))
                {
                    self.last_branch_source = BranchSource::Vmtf;
                    return Some(var);
                }
            }
            while let Some(var) = self.vsids.pop_max() {
                if !self.trail.is_assigned(var) && !self.var_eliminated(var) {
                    self.last_branch_source = BranchSource::Vsids;
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
        // The fallback must respect elimination exactly like the primary
        // heuristics: an eliminated variable (ELS-substituted, BVE/eliminator
        // folded) is not a free decision. Deciding one force-assigns it a
        // phase-saved polarity that `save_model`'s reconstruction then cannot
        // overwrite (the trail copy is not `Undef`), handing back a model
        // that violates clauses over the eliminated variable – reproduced by
        // ELS-folding `b` in `a≡b`, then `add_clause(b∨c)`: the fallback
        // decided `¬b` after the heaps drained and the model falsified
        // `(b∨c)`.
        let fallback = (0..self.num_vars)
            .map(|i| Var::new(i as u32))
            .find(|&var| !self.trail.is_assigned(var) && !self.var_eliminated(var))
            .inspect(|&var| {
                if self.config.use_lrb_branching {
                    self.lrb.on_assign(var);
                }
            });
        if fallback.is_some() {
            self.last_branch_source = BranchSource::Fallback;
        }
        fallback
    }

    /// Emit one decision-trace line to stderr when the `OXIZ_TRACE_DECISIONS`
    /// environment variable is set.
    ///
    /// Tab-separated format, one line per decision:
    /// `oxiz-dec <decision#> <level> <var> <src> <pol>`
    /// where `<src>` is the [`BranchSource`] (`pick_branch_var` set
    /// `last_branch_source`) and `<pol>` is `1` for positive / `0` for
    /// negative. Correlate `<var>` with the `oxiz-varlegend` lines the SMT
    /// solver emits (see `oxiz-solver`) to classify each decision's atom.
    ///
    /// When the env var is unset this is a single cached-`bool` check and an
    /// early return – safe to call on every decision in a release build.
    #[cfg(feature = "std")]
    pub(super) fn trace_decision(&self, var: Var, level: u32, polarity: bool) {
        if !trace_decisions_enabled() {
            return;
        }
        eprintln!(
            "oxiz-dec\t{}\t{}\t{}\t{:?}\t{}",
            self.stats.decisions,
            level,
            var.index(),
            self.last_branch_source,
            u8::from(polarity),
        );
    }

    #[cfg(not(feature = "std"))]
    pub(super) fn trace_decision(&self, _var: Var, _level: u32, _polarity: bool) {}

    /// Emit one conflict-trace line when `OXIZ_TRACE_DECISIONS` is set.
    ///
    /// `path` identifies which of the CDCL(T) loop's conflict branches fired,
    /// i.e. *where* the conflict was detected – the key diagnostic for the
    /// qlock bound-propagation question:
    ///
    /// * `bool`          - pure boolean BCP conflict.
    /// * `theory-assign` - theory conflict from `on_assignment` (incremental /
    ///   "propagated"; surfaces at the level where the triggering literal was
    ///   assigned – shallow when the theory propagates eagerly).
    /// * `theory-prop`   - boolean conflict caused by a theory-derived
    ///   propagation (also shallow).
    /// * `final-check`   - theory conflict from `final_check` (the theory only
    ///   noticed the inconsistency once the full assignment was reached – deep).
    ///
    /// Tab-separated: `oxiz-conflict <path> <level> <learnt_len> <props>` where
    /// `level` is the decision level at the moment of conflict (before
    /// backtrack) and `<props>` is the running propagation count (so the BCP
    /// power metric `propagations/conflict` = last `<props>` / #conflicts).
    #[cfg(feature = "std")]
    pub(super) fn trace_conflict(&self, path: &str, level: u32, learnt_len: usize, backjump: u32) {
        if !trace_decisions_enabled() {
            return;
        }
        eprintln!(
            "oxiz-conflict\t{path}\t{level}\t{learnt_len}\t{}\t{backjump}\t{}",
            self.stats.propagations,
            self.trail.assignments().len()
        );
    }

    #[cfg(not(feature = "std"))]
    pub(super) fn trace_conflict(
        &self,
        _path: &str,
        _level: u32,
        _learnt_len: usize,
        _backjump: u32,
    ) {
    }

    /// Backtrack with phase saving
    ///
    /// Performs every per-variable side effect of unassignment (phase saving
    /// and branching-heap reinsertion) directly inside the trail's backtrack
    /// callback by borrowing the disjoint Solver fields, instead of first
    /// collecting the unassigned variables into a throwaway `Vec`. That
    /// allocation happened on every backtrack (one per conflict) and showed up
    /// as ~3% allocator time on BCP-heavy runs.
    ///
    /// This is cadical's `backtrack` (not `backtrack_without_updating_phases`):
    /// before rolling the trail back it runs [`Self::update_target_and_best`]
    /// over the largest conflict-free prefix, so every conflict backjump and
    /// every restart keeps the target/best phase arrays current – the two
    /// arrays the rephase strategies replay. Skipping this (e.g. updating
    /// best only inside `restart`, as this solver once did) leaves the best
    /// phase frozen at the longest *restarted* trail instead of the longest
    /// conflict-free one, and gives rephase_best stale material.
    pub(super) fn backtrack_with_phase_saving(&mut self, level: u32) {
        if level >= self.trail.decision_level() {
            return;
        }
        self.update_target_and_best();
        // Borrow disjoint Solver fields (everything except `trail`, which the
        // `backtrack_to_with_callback` call borrows mutably).
        let phase = &mut self.phase;
        let lrb = &mut self.lrb;
        let vsids = &mut self.vsids;
        let chb = &mut self.chb;
        let vmtf = &mut self.vmtf;
        let use_lrb = self.config.use_lrb_branching;
        let use_chb = self.config.use_chb_branching;
        let use_vmtf = self.config.use_vmtf;
        self.trail.backtrack_to_with_callback(level, move |lit| {
            let var = lit.var();
            let vi = var.index();
            if vi < phase.len() {
                phase[vi] = lit.is_pos();
            }
            // Re-insert variable into the LRB heap (only when LRB is active).
            if use_lrb {
                lrb.unassign(var);
            }
            // Re-insert into VSIDS/CHB heaps and update the VMTF search pointer
            // (cadical `unassign` → `update_queue_unassigned`): the pointer
            // moves to the most-recently-bumped unassigned variable, keeping
            // decisions O(1) amortized.
            if !vsids.contains(var) {
                vsids.insert(var);
            }
            if use_chb && !chb.contains(var) {
                chb.insert(var);
            }
            if use_vmtf {
                vmtf.notify_unassigned(var);
            }
        });
        // cadical `backtrack_without_updating_phases`: the conflict-free
        // prefix can never point past the surviving trail.
        let kept = self.trail.assignments().len();
        self.no_conflict_until = self.no_conflict_until.min(kept);
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
    /// nothing left to branch on and reported `Sat` over a partial assignment –
    /// a model with `Undef` entries that falsified clauses the search had never
    /// even looked at. The vivification and distillation probes in
    /// `learn.rs` unwind through here too, with the same consequence.
    pub(super) fn backtrack(&mut self, level: u32) -> usize {
        let mut unassigned_vars = Vec::new();

        let lrb = &mut self.lrb;
        self.trail.backtrack_to_with_callback(level, |lit| {
            let var = lit.var();
            lrb.unassign(var);
            unassigned_vars.push(var);
        });

        // cadical clamps the conflict-free prefix here too
        // (`backtrack_without_updating_phases`); target/best are *not* updated
        // from probe/assumption unwinds (cadical reserves that for `backtrack`).
        let kept = self.trail.assignments().len();
        self.no_conflict_until = self.no_conflict_until.min(kept);

        for var in unassigned_vars {
            if !self.vsids.contains(var) {
                self.vsids.insert(var);
            }
            if !self.chb.contains(var) {
                self.chb.insert(var);
            }
        }

        // `backtrack_to_with_callback` no longer returns the rollback boundary
        // (main's alloc-free variant); derive it from the post-backtrack trail.
        self.trail.assignments().len()
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

    /// Reuse-trail restart (Marijn Heule / cadical): instead of backtracking to
    /// the root on every restart, backtrack only as far as the highest level
    /// whose decision variable would be re-decided anyway (activity >= the
    /// next variable to decide). This preserves the optimal decision prefix so
    /// the restart does not throw away and re-derive the whole trail – the main
    /// reason frequent restarts were counterproductive here.
    pub(super) fn reuse_trail(&mut self) -> u32 {
        // Only meaningful under the branching orders that actually pick the
        // next decision (the default); under CHB/LRB neither heap reflects
        // the active branching order.
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
        // The reuse threshold must be read from the branching source that
        // will pick the next decision, mirroring `pick_branch_var`'s
        // mode-dependent choice. The default focused mode branches via VMTF,
        // but this function used to consult the *VSIDS* heap regardless: the
        // mismatched threshold almost never matched the VMTF order, so reuse
        // collapsed to ~0 and every restart re-descended from the root –
        // cadical keeps decision levels whose `bumped` timestamp is at least
        // the next decision's (`restart.cpp` `reuse_trail`, queue branch).
        // That mismatch measured as a 4.5x decisions-per-conflict gap
        // against cadical on dense instances (stable-300: 5.7 vs 1.27).
        let use_vmtf_now = if self.config.enable_stabilize {
            !self.stable && self.config.focused_vmtf
        } else {
            self.config.use_vmtf
        };
        if use_vmtf_now {
            // Focused VMTF: keep decision levels whose bump timestamp is at
            // least the next decision variable's (cadical `bumped`).
            let Some(next_var) = self.vmtf.next_decision(|v| self.trail.is_assigned(v)) else {
                return 0;
            };
            let limit = self.vmtf.activity(next_var);
            let mut reuse = 0u32;
            for l in 1..=level {
                let Some(dec_var) = self.trail.decision_var_at_level(l) else {
                    break;
                };
                if self.vmtf.activity(dec_var) >= limit {
                    reuse = l;
                } else {
                    break;
                }
            }
            reuse
        } else {
            // Stable VSIDS: next variable to decide = top of the VSIDS heap;
            // its activity is the reuse threshold (decisions with at least
            // that activity are kept).
            let Some(next_var) = self.vsids.peek_max() else {
                return 0;
            };
            let threshold = self.vsids.activity(next_var);
            let mut reuse = 0u32;
            for l in 1..=level {
                let Some(dec_var) = self.trail.decision_var_at_level(l) else {
                    break;
                };
                if self.vsids.activity(dec_var) >= threshold {
                    reuse = l;
                } else {
                    break;
                }
            }
            reuse
        }
    }

    /// cadical `stabilizing()`: switch focused/stable modes when the current
    /// mode's tick (propagation) count reaches `lim_stabilize`, swapping the
    /// per-mode glue averages and growing the interval quadratically
    /// (`stabilize_base × phase²`). On entering stable mode the reluctant
    /// (Luby) restart trigger is enabled; on entering focused it is disabled
    /// (focused mode uses the Glucose EMA condition instead).
    pub(super) fn check_stabilize(&mut self) {
        if !self.config.enable_stabilize {
            return;
        }
        let current_ticks = if self.stable {
            self.ticks_stable
        } else {
            self.ticks_focused
        };
        let faithful = crate::stab_faithful_enabled() || crate::stab_null_enabled();
        // First switch: the faithful port uses cadical `stabilizing ()`'s
        // conflict-based trigger (`stats.conflicts <= lim.stabilize` with
        // `stabilizeinit` = 1000); the historical schedule used a fixed tick
        // budget (`stabilize_base`).
        let ready = if self.stabphases == 0 {
            if faithful {
                self.stats.conflicts < 1000
            } else {
                self.ticks_focused < self.config.stabilize_base
            }
        } else {
            current_ticks < self.lim_stabilize
        };
        if ready {
            return;
        }
        // Swap per-mode averages and switch mode.
        core::mem::swap(&mut self.glue_current, &mut self.glue_saved);
        self.stable = !self.stable;
        self.stabphases = self.stabphases.saturating_add(1);

        if faithful {
            // cadical restart.cpp::stabilizing tail:
            //
            //   if (!inc.stabilize) inc.stabilize = delta_ticks (phase 1);
            //   next_delta_ticks = inc.stabilize * stabphases^2;
            //   lim.stabilize = ticks[next_mode] + next_delta_ticks;
            //   last.stabilize.ticks = ticks[next_mode];
            //
            // The increment is *measured* from phase 1's consumed ticks, not
            // a config constant; growth is quadratic in completed phases.
            let old_mode_ticks = if self.stable {
                self.ticks_focused
            } else {
                self.ticks_stable
            };
            let delta_ticks = old_mode_ticks.saturating_sub(self.stab_last_ticks);
            // Phase-1 delta defines the increment; later deltas are ignored
            // by cadical (`if (!inc.stabilize)`).
            if self.stab_inc == 0 {
                self.stab_inc = delta_ticks.max(1);
            }
            let stabphases = self.stabphases;
            let next_delta = if crate::stab_null_enabled() && stabphases > 1 {
                // NULL ARM: same multiset of quadratic lengths
                // {inc*k^2 : k <= stabphases}, drawn without replacement in a
                // pseudo-random order – growth semantics removed.
                if self.stab_null_pending.is_empty() {
                    self.stab_null_pending = (1..=stabphases)
                        .map(|k| self.stab_inc.saturating_mul(k).saturating_mul(k))
                        .collect();
                }
                let idx = (self.rand_u64() as usize) % self.stab_null_pending.len();
                self.stab_null_pending.swap_remove(idx)
            } else {
                self.stab_inc
                    .saturating_mul(stabphases)
                    .saturating_mul(stabphases)
            };
            let new_mode_ticks = if self.stable {
                self.ticks_stable
            } else {
                self.ticks_focused
            };
            self.lim_stabilize = new_mode_ticks.saturating_add(next_delta.max(1));
            self.stab_last_ticks = new_mode_ticks;
        } else {
            // Quadratic growth of the next phase length (cadical `next_delta =
            // inc × stabphases²`), measured in the new mode's ticks. The
            // historical schedule pins the increment to `stabilize_base`.
            let next_delta = self
                .config
                .stabilize_base
                .saturating_mul(self.stabphases)
                .saturating_mul(self.stabphases);
            let new_mode_ticks = if self.stable {
                self.ticks_stable
            } else {
                self.ticks_focused
            };
            self.lim_stabilize = new_mode_ticks.saturating_add(next_delta);
        }
        // Enable/disable the reluctant (Luby) restart trigger for stable mode.
        if self.stable {
            self.reluctant.enable(1024, 1 << 20);
        } else {
            self.reluctant.disable();
        }
    }

    /// Restart
    pub(super) fn restart(&mut self) {
        self.stats.restarts += 1;
        if self.stable {
            self.stats.restarts_stable += 1;
        }
        // Target/best phase bookkeeping no longer lives here: every
        // `backtrack_with_phase_saving` (this one included) routes through
        // `update_target_and_best`, keyed on the conflict-free prefix –
        // cadical's exact update point (backtrack.cpp).
        let reuse = self.reuse_trail();
        if reuse > 0 {
            self.stats.reused_trails += 1;
            self.stats.reused_levels += u64::from(reuse);
        }
        #[cfg(feature = "std")]
        if trace_decisions_enabled() {
            eprintln!(
                "oxiz-restart\t{}\t{}\t{}\t{}",
                self.stats.conflicts,
                self.trail.decision_level(),
                reuse,
                self.stats.propagations
            );
        }
        self.backtrack_with_phase_saving(reuse);

        // Calculate next restart threshold based on strategy
        match self.config.restart_strategy {
            RestartStrategy::Luby => {
                self.luby_index += 1;
                // Cap the Luby value: the sequence grows as 2^k, so on long runs
                // the restart interval explodes into multi-10k-conflict grinds
                // (a 3-30x slowdown vs cadical on r3sat n300/n350). Capping
                // keeps restarts regular without losing Luby's short-window
                // structure. Mode-dependent under the stable/focused schedule:
                // focused = frequent (focused_luby_cap), stable = rare (uncapped).
                let cap = if self.config.enable_stabilize {
                    if self.stable {
                        0
                    } else {
                        self.config.focused_luby_cap
                    }
                } else {
                    self.config.luby_cap
                };
                let luby = if cap == 0 {
                    Self::luby(self.luby_index)
                } else {
                    Self::luby(self.luby_index).min(cap)
                };
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
                // LBD-driven restart: the restart *decision* is made in the solve
                // loop (fire only when the fast LBD EMA exceeds the slow one).
                // Here we just enforce a minimum gap between restarts
                // (`restart_interval`) so the solver does not thrash, then wait
                // for the next degradation.
                self.restart_threshold = self.stats.conflicts + self.config.restart_interval;
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

    /*---------------------------------------------------------------------
     * Target/best phase maintenance – faithful port of cadical's
     * `update_target_and_best` (backtrack.cpp) and the rephase machinery
     * (rephase.cpp).
     *
     * `no_conflict_until` is maintained by `propagate`: the whole trail on a
     * clean fixpoint, the prefix before the current decision level on a
     * conflict.  Every phase-saving backtrack then records that prefix as the
     * *target* phase (used for stable-mode decisions) and, when it is the
     * longest conflict-free prefix ever seen, as the *best* phase (replayed by
     * the `best` rephase strategy).  After a rephase, `rephased` stays set
     * until the first conflict that follows it; that first post-rephase
     * backtrack resets `target_assigned` (and `best_assigned` for a `best`
     * rephase) so both arrays are re-established from the new phase instead of
     * inheriting pre-rephase material.
     *-------------------------------------------------------------------*/

    /// cadical `Internal::update_target_and_best`: record the current phases
    /// as target (and best) if the conflict-free trail prefix grew.
    pub(super) fn update_target_and_best(&mut self) {
        // cadical: `if (opts.rephase == 2 && !stable) return;` – under the
        // stable-only schedule the focused phase never consults target phases,
        // so do not spend the copies there.
        if self.config.rephase == 2 && !self.stable {
            return;
        }
        let reset = self.rephased.is_some() && self.stats.conflicts > self.last_rephase_conflicts;
        if reset {
            self.target_assigned = 0;
            // A `best` rephase just replayed the old best array; re-arm it so
            // the next conflict-free prefix can establish a fresh best.
            if self.rephased == Some(RephaseKind::Best) {
                self.best_assigned = 0;
            }
        }
        if self.no_conflict_until > self.target_assigned {
            self.copy_phases(PhaseArray::Target);
            self.target_assigned = self.no_conflict_until;
        }
        if self.no_conflict_until > self.best_assigned {
            self.copy_phases(PhaseArray::Best);
            self.best_assigned = self.no_conflict_until;
        }
        if reset {
            self.rephased = None;
        }
    }

    /// cadical `copy_phases (dst)`: snapshot the saved phases into `dst`.
    ///
    /// cadical's `phases.saved` is written at *assignment* time, so at the
    /// moment `update_target_and_best` runs it equals the current trail
    /// values.  OxiZ saves phases at *unassignment* time, so the array can be
    /// stale for variables currently on the trail; refresh those from the
    /// trail first (one pass, same complexity class as the copy itself) and
    /// the snapshot is bit-for-bit what cadical would have copied.
    ///
    /// cadical skips zero (never-assigned) entries in `dst`; a `false` bool is
    /// the zero-equivalent here because the arrays start all-`false` and the
    /// cadical initial phase is negative (`false`) too – writing `false` over
    /// an unset entry produces the same decision polarity.
    fn copy_phases(&mut self, dst: PhaseArray) {
        // Refresh the saved phases for every variable currently on the
        // trail first (see the doc comment on `PhaseArray`); then snapshot.
        for &lit in self.trail.assignments() {
            let vi = lit.var().index();
            if vi < self.phase.len() {
                self.phase[vi] = lit.is_pos();
            }
        }
        let dst = match dst {
            PhaseArray::Target => &mut self.target_phase,
            PhaseArray::Best => &mut self.best_phase,
        };
        dst.resize(self.num_vars, false);
        dst.copy_from_slice(&self.phase);
    }

    /// cadical `Internal::rephasing()`: whether the rephase limit was reached.
    pub(super) fn rephasing(&self) -> bool {
        if self.config.rephase == 0 || self.config.rephase_interval == 0 {
            return false;
        }
        if self.config.rephase == 2 {
            self.stable && self.stats.stable_conflicts > self.lim_rephase
        } else {
            self.stats.conflicts > self.lim_rephase
        }
    }

    /// cadical `init_search_limits` (rephase part): fresh limit and per-mode
    /// round counters on every solve. Called from both search drivers
    /// (`solve`'s inlined loop and `solve_with_theory`).
    pub(super) fn init_rephase_limits(&mut self) {
        if self.config.rephase > 0 && self.config.rephase_interval > 0 {
            self.lim_rephase = self
                .stats
                .conflicts
                .saturating_add(self.config.rephase_interval);
            self.rephase_rounds = [0, 0];
        }
        // cadical's initial probe limit (init_search_limits): conflicts +
        // `inprobeint × log10(irredundant + 10)²`, i.e. scaled by the size of
        // the original formula (≈ 900 conflicts at 1k clauses, ≈ 1 700 at
        // 13k, ≈ 2 300 at 60k) – and kept as-is on incremental solves once
        // initialized (cadical's `incremental` branch). Only the first solve
        // of a solver instance takes this branch (`lim_inprobe_inited`).
        if !self.lim_inprobe_inited {
            self.lim_inprobe_inited = true;
            let irredundant = self.clauses.num_original() as f64;
            let delta = (irredundant + 10.0).log10();
            let delta = (delta * delta) * super::probe::INPROBE_BASE_INTERVAL as f64;
            self.lim_inprobe = self.stats.conflicts.saturating_add(delta.max(1.0) as u64);
        }
    }

    /// cadical `Internal::rephase()`: backtrack to the root (routing through
    /// `update_target_and_best` one last time over the trail being discarded),
    /// then overwrite the saved phases according to the mode-dependent
    /// strategy schedule, and make the new phases the fresh target.
    pub(super) fn rephase(&mut self) {
        self.rephase_skipped = false;
        self.stats.rephased.total += 1;

        // cadical's leading `backtrack()`: full root backtrack, which updates
        // target/best from the outgoing trail before any strategy overwrites
        // the phase array.
        self.backtrack_with_phase_saving(0);

        let stable = self.stable;
        let count = self.rephase_rounds[usize::from(stable)];
        self.rephase_rounds[usize::from(stable)] += 1;

        // cadical `single = !opts.stabilize || opts.stabilizeonly`: with the
        // stable/focused schedule active (default), the strategy cycles are
        // per-mode; without it a single fixed cycle runs in both modes.
        let single = !self.config.enable_stabilize;
        let walk = self.config.walk;

        let kind = if single && !walk {
            // (inverted,best,flipping,best,random,best,original,best)^ω
            match count % 8 {
                0 => self.rephase_inverted(),
                1 => self.rephase_best(),
                2 => self.rephase_flipping(),
                3 => self.rephase_best(),
                4 => self.rephase_random(),
                5 => self.rephase_best(),
                6 => self.rephase_original(),
                _ => self.rephase_best(),
            }
        } else if single && walk {
            // (inverted,best,walk,flipping,best,walk,random,best,walk,
            //  original,best,walk)^ω
            match count % 12 {
                0 => self.rephase_inverted(),
                1 => self.rephase_best(),
                2 => self.rephase_walk(),
                3 => self.rephase_flipping(),
                4 => self.rephase_best(),
                5 => self.rephase_walk(),
                6 => self.rephase_random(),
                7 => self.rephase_best(),
                8 => self.rephase_walk(),
                9 => self.rephase_original(),
                10 => self.rephase_best(),
                _ => self.rephase_walk(),
            }
        } else if self.config.rephase == 2 && walk {
            // same 12-cycle as `single && walk` (cadical branches 3 and 2 are
            // literally identical)
            match count % 12 {
                0 => self.rephase_inverted(),
                1 => self.rephase_best(),
                2 => self.rephase_walk(),
                3 => self.rephase_flipping(),
                4 => self.rephase_best(),
                5 => self.rephase_walk(),
                6 => self.rephase_random(),
                7 => self.rephase_best(),
                8 => self.rephase_walk(),
                9 => self.rephase_original(),
                10 => self.rephase_best(),
                _ => self.rephase_walk(),
            }
        } else if stable && !walk {
            // original,inverted,(best,original,best,inverted)^ω
            match count {
                0 => self.rephase_original(),
                1 => self.rephase_inverted(),
                _ => match (count - 2) % 4 {
                    0 => self.rephase_best(),
                    1 => self.rephase_original(),
                    2 => self.rephase_best(),
                    _ => self.rephase_inverted(),
                },
            }
        } else if stable && walk {
            // original,inverted,(best,walk,original,best,walk,inverted)^ω
            match count {
                0 => self.rephase_original(),
                1 => self.rephase_inverted(),
                _ => match (count - 2) % 6 {
                    0 => self.rephase_best(),
                    1 => self.rephase_walk(),
                    2 => self.rephase_original(),
                    3 => self.rephase_best(),
                    4 => self.rephase_walk(),
                    _ => self.rephase_inverted(),
                },
            }
        } else if !walk || !self.config.walk_nonstable {
            // focused: flipping,(random,best,flipping,best)^ω
            match count {
                0 => self.rephase_flipping(),
                _ => match (count - 1) % 4 {
                    0 => self.rephase_random(),
                    1 => self.rephase_best(),
                    2 => self.rephase_flipping(),
                    _ => self.rephase_best(),
                },
            }
        } else {
            // focused with walks – cadical's code (its comment says
            // `flipping,…` but the code calls `rephase_original` first; code
            // is ground truth):
            // original,(random,best,walk,flipping,best,walk)^ω
            match count {
                0 => self.rephase_original(),
                _ => match (count - 1) % 6 {
                    0 => self.rephase_random(),
                    1 => self.rephase_best(),
                    2 => self.rephase_walk(),
                    3 => self.rephase_flipping(),
                    4 => self.rephase_best(),
                    _ => self.rephase_walk(),
                },
            }
        };

        // The new phases become the new target (cadical: `copy_phases
        // (phases.target); target_assigned = 0;` – the walk reads the saved
        // phases first, hence the ordering).
        self.target_phase.resize(self.num_vars, false);
        self.target_phase.copy_from_slice(&self.phase);
        self.target_assigned = 0;

        // Arithmetic growth of the next interval, in the schedule's own
        // conflict counter (stable-only schedule counts stable conflicts).
        let conflicts = if self.config.rephase == 2 {
            self.stats.stable_conflicts
        } else {
            self.stats.conflicts
        };
        let delta = self
            .config
            .rephase_interval
            .saturating_mul(self.stats.rephased.total + 1);
        self.lim_rephase = conflicts.saturating_add(delta);

        // Arms `update_target_and_best` to reset target (and best for a `best`
        // rephase) at the first backtrack after the next conflict.
        self.last_rephase_conflicts = self.stats.conflicts;
        self.rephased = Some(kind);
    }

    /// All phases to the initial phase (negative) – cadical `rephase_original`.
    fn rephase_original(&mut self) -> RephaseKind {
        self.stats.rephased.original += 1;
        self.phase.clear();
        self.phase.resize(self.num_vars, false);
        RephaseKind::Original
    }

    /// All phases to the inverted initial phase (positive) – cadical
    /// `rephase_inverted`.
    fn rephase_inverted(&mut self) -> RephaseKind {
        self.stats.rephased.inverted += 1;
        self.phase.clear();
        self.phase.resize(self.num_vars, true);
        RephaseKind::Inverted
    }

    /// Flip every phase in place – cadical `rephase_flipping` (`saved *= -1`).
    fn rephase_flipping(&mut self) -> RephaseKind {
        self.stats.rephased.flipped += 1;
        for p in &mut self.phase {
            *p = !*p;
        }
        self.phase.resize(self.num_vars, false);
        RephaseKind::Flipping
    }

    /// Randomize all phases – cadical `rephase_random`.
    fn rephase_random(&mut self) -> RephaseKind {
        self.stats.rephased.random += 1;
        self.phase.clear();
        self.phase.resize(self.num_vars, false);
        let mut rng_state = self.rng_state;
        for p in &mut self.phase {
            // Inline xorshift (the shared `rand_bool` needs `&mut self`).
            let mut x = rng_state;
            x ^= x << 13;
            x ^= x >> 7;
            x ^= x << 17;
            *p = (x & 1) == 1;
            rng_state = x;
        }
        self.rng_state = rng_state;
        RephaseKind::Random
    }

    /// Overwrite saved phases with the best-phase array – cadical
    /// `rephase_best`. Only ever replays material recorded by
    /// [`Self::update_target_and_best`].
    fn rephase_best(&mut self) -> RephaseKind {
        self.stats.rephased.best += 1;
        self.phase.resize(self.num_vars, false);
        self.best_phase.resize(self.num_vars, false);
        self.phase.copy_from_slice(&self.best_phase);
        RephaseKind::Best
    }

    /// Run the ProbSAT local search (`solver/walk.rs`) seeded from the saved
    /// phases – cadical `rephase_walk`. A zero-broken-clause walk still only
    /// writes the phases (cadical's `walk()` discards its result too); the
    /// subsequent descent reaches that model through ordinary search.
    fn rephase_walk(&mut self) -> RephaseKind {
        self.stats.rephased.walk += 1;
        self.walk();
        RephaseKind::Walk
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
        let state = Self::seed_to_rng_state(seed);
        // Record the configured state so `reset()` restores the same stream
        // instead of stomping back to the built-in constant (a user seed used
        // to survive only until the first reset, silently reverting every
        // randomized decision to the default trajectory mid-portfolio).
        self.rng_seed = state;
        self.rng_state = state;
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
