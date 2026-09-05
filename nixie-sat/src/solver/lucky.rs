//! "Lucky" pre-solving phases – faithful port of CaDiCaL's `lucky.cpp`.
//!
//! Before entering CDCL search, attempt to satisfy the formula without (much)
//! search by testing a small set of structured phase assignments. Each
//! strategy is *soundness-preserving*: a failed attempt is backtracked to the
//! root with no lasting effect on the search state (phases, VSIDS, watches),
//! because every strategy either
//!   * performs a pure `O(|literals|)` scan *before* any assignment – so a
//!     doomed guess never perturbs the watched-literal state (this is the key
//!     difference from the old opt-in guess, which fired one giant doomed
//!     propagation cascade on dense UNSAT); or
//!   * propagates only one literal at a time and bails immediately on the
//!     first conflict.
//!
//! Strategies (tried in CaDiCaL order, see `lucky_phases`):
//!   1. `lucky_trivially(false)` – every clause has a negative literal
//!   2. `lucky_trivially(true)`  – every clause has a positive literal
//!   3. `lucky_ordered(false, true)`  – assume vars false, ascending, w/ flip
//!   4. `lucky_ordered(true,  true)`  – assume vars true,  ascending, w/ flip
//!   5. `lucky_ordered(false, false)` – descending
//!   6. `lucky_ordered(true,  false)` – descending
//!   7. `lucky_horn(false)`     – first negative literal of each clause
//!   8. `lucky_horn(true)`      – first positive literal of each clause
//!
//! Flip / discrepancy (`lucky_discrepancy`, CaDiCaL
//! `lucky_propagate_discrepancy`): when assuming a literal `dec` conflicts we
//! flip to `¬dec`; if both polarities conflict the partial prefix is doomed and
//! the strategy aborts. Unlike CaDiCaL this does not analyze a root-level
//! conflict to learn a unit or prove UNSAT – that would mutate the clause
//! database / VSIDS and break the snapshot/restore that keeps lucky
//! transparent to the search (see `lucky_phases`).
//!
//! Runs automatically in `Solver::solve` whenever `enable_lucky` is on
//! (default, matching CaDiCaL's `opts.lucky = 1`). Skipped under
//! assumptions / external branching, where a CDCL loop is required.

use super::*;

/// Outcome of a single lucky strategy.
#[derive(Clone, Copy, PartialEq, Eq)]
enum LuckyOutcome {
    /// Strategy neither satisfied the formula nor proved it UNSAT – try the
    /// next one (trail already restored to the root).
    Fail,
    /// A full model is on the trail (caller saves it).
    Sat,
}

/// Outcome of a single discrepancy probe.
#[derive(Clone, Copy, PartialEq, Eq)]
enum Discrepancy {
    /// `dec` (or its flip) propagated without conflict – the variable is now
    /// assigned; the caller re-checks and advances.
    Ok,
    /// Both `dec` and `¬dec` conflicted – abandon the strategy (trail left at
    /// the conflicting level; caller backtracks to the root).
    BothConflict,
}

impl Solver {
    /// Cheap external-interrupt poll (CaDiCaL `terminated_asynchronously`).
    fn lucky_interrupted(&self) -> bool {
        self.interrupt
            .as_ref()
            .is_some_and(|f| f.load(Ordering::Relaxed))
    }

    /// Try all eight CaDiCaL "lucky" pre-solving strategies. Returns
    /// `Some(Sat)` if a model is on the trail, `Some(Unsat)` if the formula
    /// is refuted, or `None` if no strategy applied (fall back to search).
    ///
    /// On every non-`Sat`/`Unsat` return the trail is back at decision level 0
    /// and no phases / activities have been perturbed (barring the rare
    /// root-discrepancy path, which learns sound implied units).
    pub(super) fn lucky_phases(&mut self) -> Option<SolverResult> {
        if self.trail.decision_level() != 0 || self.trivially_unsat || self.num_vars == 0 {
            return None;
        }
        // External branching / assumptions need a real CDCL loop.
        if self.config.external_branching.is_some() {
            return None;
        }

        // Propagate root-level units first. A conflict here is a direct UNSAT
        // (mirrors the top of CaDiCaL's `lucky_phases`).
        if let Some(conflict) = self.propagate() {
            self.trivially_unsat = true;
            self.drat_emit_empty(Some(conflict));
            return Some(SolverResult::Unsat);
        }
        if self.lucky_interrupted() || self.trivially_unsat {
            return None;
        }

        self.stats.lucky_tried += 1;

        // Snapshot the search-relevant state that lucky's propagation mutates:
        //   * the two-watched-literal lists (propagation moves watches) and the
        //     clause literal order (`clause.swap` in propagate);
        //   * the per-mode tick counters, which drive the focused/stable
        //     stabilization schedule – lucky's propagation would otherwise
        //     shift the whole restart trajectory.
        // CaDiCaL avoids this by running lucky outside search accounting
        // (START/STOP); nixie's solver is sensitive to all three, so we restore
        // them on failure. On `Sat` we keep the trail (the model) and return.
        // Lucky never learns clauses or bumps VSIDS (see `lucky_discrepancy`),
        // so these three are the *complete* set of persistent mutations.
        //
        // Both bulk snapshots are PACKED (one buffer each) rather than deep
        // clones: the previous `Vec<(ClauseId, Vec<Lit>)>` + `watches.clone()`
        // paid one heap allocation and a 40-byte tuple per clause and doubled
        // the watch memory – on clause-dense instances (worker-class, 10M+
        // originals) a ~900 MB transient that dominated peak RSS. The packed
        // forms restore the identical state (same ids, same literal order,
        // same watcher contents per list) at a fraction of the footprint.
        // Only clauses with **>= 3 literals** can be permuted by lucky's
        // propagation: binaries are BIG-authoritative (no watch entries --
        // `attach_watchers`/`rebuild_watches_and_binary_graph` register them
        // in the binary graph only), and the BIG scan in `propagate` reads
        // edges without ever touching clause bytes; units/empties are never
        // watched. Rewriting a binary's literals with their own bytes (what
        // the restore below did for them historically) is a no-op, so
        // skipping them here is trajectory-identical and cuts the snapshot
        // to the small large-clause minority on binary-dense instances
        // (worker-class: 97% binaries -- the ~190 MB transient was almost
        // entirely no-op restore data).
        let snap_watches = self.watches.packed_snapshot();
        let mut snap_ids: Vec<ClauseId> = Vec::new();
        let mut snap_ends: Vec<u32> = Vec::new();
        let mut snap_buf: Vec<Lit> = Vec::new();
        for id in self.clauses.iter_ids() {
            if let Some(v) = self.clauses.get(id) {
                if v.lits.len() < 3 {
                    continue;
                }
                snap_ids.push(id);
                snap_buf.extend_from_slice(v.lits);
                snap_ends.push(snap_buf.len() as u32);
            }
        }
        let snap_ticks = (
            self.ticks_focused,
            self.ticks_stable,
            self.stats.propagations,
        );

        // Try each strategy in CaDiCaL order. Each leaves the trail at level 0
        // on `Fail`, so they compose cleanly.
        let mut res = self.lucky_trivially(false);
        if res == LuckyOutcome::Fail {
            res = self.lucky_trivially(true);
        }
        if res == LuckyOutcome::Fail {
            res = self.lucky_ordered(true, true);
        }
        if res == LuckyOutcome::Fail {
            res = self.lucky_ordered(false, true);
        }
        if res == LuckyOutcome::Fail {
            res = self.lucky_ordered(true, false);
        }
        if res == LuckyOutcome::Fail {
            res = self.lucky_ordered(false, false);
        }
        if res == LuckyOutcome::Fail {
            res = self.lucky_horn(false);
        }
        if res == LuckyOutcome::Fail {
            res = self.lucky_horn(true);
        }

        match res {
            LuckyOutcome::Sat => {
                self.stats.lucky_succeeded += 1;
                // Trail holds the full model (possibly spread over several
                // decision levels); the caller saves it via `save_model`.
                Some(SolverResult::Sat)
            }
            LuckyOutcome::Fail => {
                // Restore the pre-lucky search state so the probe is fully
                // transparent to the CDCL search.
                self.watches.restore(snap_watches);
                let mut start = 0u32;
                for (&id, &end) in snap_ids.iter().zip(snap_ends.iter()) {
                    // Watch-position swaps during the probe are undone by
                    // rewriting the same-length literal array in place
                    // (exactly the previous per-clause `shrink(id, &lits)`,
                    // now slicing one concatenated buffer).
                    self.clauses
                        .shrink(id, &snap_buf[start as usize..end as usize]);
                    start = end;
                }
                let (tf, ts, prop) = snap_ticks;
                self.ticks_focused = tf;
                self.ticks_stable = ts;
                self.stats.propagations = prop;
                debug_assert_eq!(
                    self.trail.decision_level(),
                    0,
                    "lucky left a non-root trail on failure"
                );
                None
            }
        }
    }

    /// `trivially_{false,true}_satisfiable` (CaDiCaL). If `want_positive`,
    /// succeed only when every live original clause contains an unassigned
    /// *positive* literal (then set everything true); otherwise require a
    /// *negative* literal (set everything false). A pure `O(|literals|)` scan
    /// first – zero propagation on a doomed guess.
    fn lucky_trivially(&mut self, want_positive: bool) -> LuckyOutcome {
        debug_assert_eq!(self.trail.decision_level(), 0);

        // Phase 1 – pure scan: bail before assigning anything if any clause
        // lacks an unassigned literal of the wanted polarity.
        let ids: Vec<ClauseId> = self.clauses.iter_ids().collect();
        for &id in &ids {
            if self.lucky_interrupted() {
                return LuckyOutcome::Fail;
            }
            let ok = self.clauses.get(id).is_some_and(|c| {
                if c.deleted || c.learned {
                    return true;
                }
                let mut satisfied = false;
                let mut found = false;
                for &lit in c.lits {
                    match self.trail.lit_value(lit) {
                        LBool::True => {
                            satisfied = true;
                            break;
                        }
                        LBool::False => continue,
                        LBool::Undef => {
                            if lit.is_pos() == want_positive {
                                found = true;
                                break;
                            }
                        }
                    }
                }
                satisfied || found
            });
            if !ok {
                return LuckyOutcome::Fail;
            }
        }

        // Phase 2 – scan passed: assign every free variable to the wanted
        // polarity and confirm with one propagation per variable.
        for i in 0..self.num_vars {
            if self.lucky_interrupted() {
                self.backtrack(0);
                return LuckyOutcome::Fail;
            }
            let v = Var::new(i as u32);
            if self.trail.is_assigned(v) {
                continue;
            }
            let lit = if want_positive {
                Lit::pos(v)
            } else {
                Lit::neg(v)
            };
            self.trail.new_decision_level();
            self.trail.assign_decision(lit);
            if self.propagate().is_some() {
                self.backtrack(0);
                return LuckyOutcome::Fail;
            }
        }
        LuckyOutcome::Sat
    }

    /// `{positive,negative}_horn_satisfiable` (CaDiCaL). If `want_positive`,
    /// assign each (non-satisfied) clause's first unassigned *positive* literal
    /// true, else its first *negative* literal; remaining free variables are
    /// set to the *opposite* polarity.
    fn lucky_horn(&mut self, want_positive: bool) -> LuckyOutcome {
        debug_assert_eq!(self.trail.decision_level(), 0);

        let ids: Vec<ClauseId> = self.clauses.iter_ids().collect();
        for &id in &ids {
            if self.lucky_interrupted() {
                self.backtrack(0);
                return LuckyOutcome::Fail;
            }
            // Re-read fresh: propagation may have added learned binaries.
            let chosen = self.clauses.get(id).and_then(|c| {
                if c.deleted || c.learned {
                    return None;
                }
                let mut satisfied = false;
                let mut pick: Option<Lit> = None;
                for &lit in c.lits {
                    match self.trail.lit_value(lit) {
                        LBool::True => {
                            satisfied = true;
                            break;
                        }
                        LBool::False => continue,
                        LBool::Undef => {
                            if lit.is_pos() == want_positive {
                                pick = Some(lit);
                                break;
                            }
                        }
                    }
                }
                if satisfied { None } else { Some(pick) }
            });
            match chosen {
                None => continue,
                Some(Some(lit)) => {
                    self.trail.new_decision_level();
                    self.trail.assign_decision(lit);
                    if self.propagate().is_some() {
                        self.backtrack(0);
                        return LuckyOutcome::Fail;
                    }
                }
                // Not satisfied and no unassigned literal of the wanted
                // polarity – this strategy cannot work.
                Some(None) => {
                    self.backtrack(0);
                    return LuckyOutcome::Fail;
                }
            }
        }

        // Any variable left free does not appear (with the wanted polarity) in
        // any still-unsatisfied clause: set it to the opposite polarity.
        for i in 0..self.num_vars {
            if self.lucky_interrupted() {
                self.backtrack(0);
                return LuckyOutcome::Fail;
            }
            let v = Var::new(i as u32);
            if self.trail.is_assigned(v) {
                continue;
            }
            let lit = if want_positive {
                Lit::neg(v)
            } else {
                Lit::pos(v)
            };
            self.trail.new_decision_level();
            self.trail.assign_decision(lit);
            if self.propagate().is_some() {
                self.backtrack(0);
                return LuckyOutcome::Fail;
            }
        }
        LuckyOutcome::Sat
    }

    /// `forward_{false,true}_satisfiable` / `backward_{false,true}_satisfiable`
    /// (CaDiCaL). Assume variables to polarity `want_positive` in index order
    /// (`forward`) or reverse (`backward`), flipping on conflict via
    /// [`lucky_discrepancy`]. Subsumes a plain uniform guess but tolerates
    /// per-variable flips, so it finds models a single all-false/all-true
    /// cascade cannot.
    fn lucky_ordered(&mut self, want_positive: bool, forward: bool) -> LuckyOutcome {
        debug_assert_eq!(self.trail.decision_level(), 0);
        let n = self.num_vars;
        if n == 0 {
            return LuckyOutcome::Sat;
        }
        let mut idx = if forward { 0 } else { n - 1 };
        loop {
            let v = Var::new(idx as u32);
            // `goto START`: re-check this variable until it is assigned or the
            // strategy fails. A successful discrepancy assigns `v` (either
            // polarity), so we re-check `is_assigned(v)` before advancing.
            loop {
                if self.lucky_interrupted() {
                    self.backtrack(0);
                    return LuckyOutcome::Fail;
                }
                if self.trail.is_assigned(v) {
                    break;
                }
                let dec = if want_positive {
                    Lit::pos(v)
                } else {
                    Lit::neg(v)
                };
                match self.lucky_discrepancy(dec) {
                    Discrepancy::Ok => {} // re-check `is_assigned(v)`
                    Discrepancy::BothConflict => {
                        self.backtrack(0);
                        return LuckyOutcome::Fail;
                    }
                }
            }
            // Advance to the next variable.
            if forward {
                idx += 1;
                if idx >= n {
                    break;
                }
            } else if idx == 0 {
                break;
            } else {
                idx -= 1;
            }
        }
        LuckyOutcome::Sat
    }

    /// `lucky_propagate_discrepancy` (CaDiCaL). Decide `dec`; on conflict flip
    /// to `¬dec`. If both polarities conflict the prefix is doomed and the
    /// strategy aborts. Unlike CaDiCaL this does *not* analyze a root-level
    /// (level-1) conflict to learn a unit / prove UNSAT: doing so would mutate
    /// the clause database and VSIDS, breaking the snapshot/restore that keeps
    /// lucky transparent to the search (see `lucky_phases`). The lost early
    /// UNSAT detection is rare and the search recovers it.
    fn lucky_discrepancy(&mut self, dec: Lit) -> Discrepancy {
        self.trail.new_decision_level();
        self.trail.assign_decision(dec);
        if self.propagate().is_none() {
            return Discrepancy::Ok;
        }
        // Conflict: undo just this decision and try the opposite polarity.
        let level = self.trail.decision_level();
        self.backtrack(level - 1);
        self.trail.new_decision_level();
        self.trail.assign_decision(dec.negate());
        if self.propagate().is_none() {
            Discrepancy::Ok
        } else {
            Discrepancy::BothConflict
        }
    }
}
