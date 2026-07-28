//! "Lucky" pre-solving phases — faithful port of CaDiCaL's `lucky.cpp`.
//!
//! Before entering CDCL search, attempt to satisfy the formula without (much)
//! search by testing a small set of structured phase assignments. Each
//! strategy is *soundness-preserving*: a failed attempt is backtracked to the
//! root with no lasting effect on the search state (phases, VSIDS, watches),
//! because every strategy either
//!   * performs a pure `O(|literals|)` scan *before* any assignment — so a
//!     doomed guess never perturbs the watched-literal state (this is the key
//!     difference from the old opt-in guess, which fired one giant doomed
//!     propagation cascade on dense UNSAT); or
//!   * propagates only one literal at a time and bails immediately on the
//!     first conflict.
//!
//! Strategies (tried in CaDiCaL order, see `lucky_phases`):
//!   1. `lucky_trivially(false)` — every clause has a negative literal
//!   2. `lucky_trivially(true)`  — every clause has a positive literal
//!   3. `lucky_ordered(false, true)`  — assume vars false, ascending, w/ flip
//!   4. `lucky_ordered(true,  true)`  — assume vars true,  ascending, w/ flip
//!   5. `lucky_ordered(false, false)` — descending
//!   6. `lucky_ordered(true,  false)` — descending
//!   7. `lucky_horn(false)`     — first negative literal of each clause
//!   8. `lucky_horn(true)`      — first positive literal of each clause
//!
//! Flip / discrepancy (`lucky_discrepancy`, CaDiCaL
//! `lucky_propagate_discrepancy`): when assuming a literal `dec` conflicts we
//! flip to `¬dec`; if *both* polarities conflict above the root the partial
//! prefix is doomed and the strategy aborts; if both conflict at the root
//! (level 1) the formula is UNSAT — analyzed and reported like any other
//! root-level refutation.
//!
//! Runs automatically in `Solver::solve` whenever `enable_lucky` is on
//! (default, matching CaDiCaL's `opts.lucky = 1`). Skipped under
//! assumptions / external branching, where a CDCL loop is required.

use super::*;

/// Outcome of a single lucky strategy.
#[derive(Clone, Copy, PartialEq, Eq)]
enum LuckyOutcome {
    /// Strategy neither satisfied the formula nor proved it UNSAT — try the
    /// next one (trail already restored to the root).
    Fail,
    /// A full model is on the trail (caller saves it).
    Sat,
    /// The formula was proven UNSAT (empty clause emitted, `trivially_unsat`
    /// set).
    Unsat,
}

/// Outcome of a single discrepancy probe.
#[derive(Clone, Copy, PartialEq, Eq)]
enum Discrepancy {
    /// `dec` (or its flip) propagated without conflict — the variable is now
    /// assigned; the caller re-checks and advances.
    Ok,
    /// Both `dec` and `¬dec` conflicted above the root — abandon the strategy
    /// (trail left at the conflicting level; caller backtracks to the root).
    BothConflict,
    /// A root-level (level-1) double conflict proved the formula UNSAT.
    Unsat,
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
        if self.propagate().is_some() {
            self.trivially_unsat = true;
            self.drat_emit_empty();
            return Some(SolverResult::Unsat);
        }
        if self.lucky_interrupted() || self.trivially_unsat {
            return None;
        }

        self.stats.lucky_tried += 1;

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
            LuckyOutcome::Unsat => Some(SolverResult::Unsat),
            LuckyOutcome::Fail => {
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
    /// first — zero propagation on a doomed guess.
    fn lucky_trivially(&mut self, want_positive: bool) -> LuckyOutcome {
        debug_assert_eq!(self.trail.decision_level(), 0);

        // Phase 1 — pure scan: bail before assigning anything if any clause
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
                for &lit in &c.lits {
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

        // Phase 2 — scan passed: assign every free variable to the wanted
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
            let lit = if want_positive { Lit::pos(v) } else { Lit::neg(v) };
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
                for &lit in &c.lits {
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
                if satisfied {
                    None
                } else {
                    Some(pick)
                }
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
                // polarity — this strategy cannot work.
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
            let lit = if want_positive { Lit::neg(v) } else { Lit::pos(v) };
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
            // strategy fails. A successful discrepancy either assigns `v`
            // directly (no-conflict path) or learns a root unit (level-1
            // analyze path) that may assign a *different* variable — so we
            // must re-check `is_assigned(v)` rather than blindly advancing.
            loop {
                if self.lucky_interrupted() {
                    self.backtrack(0);
                    return LuckyOutcome::Fail;
                }
                if self.trail.is_assigned(v) {
                    break;
                }
                let dec = if want_positive { Lit::pos(v) } else { Lit::neg(v) };
                match self.lucky_discrepancy(dec) {
                    Discrepancy::Ok => {} // re-check `is_assigned(v)`
                    Discrepancy::BothConflict => {
                        self.backtrack(0);
                        return LuckyOutcome::Fail;
                    }
                    Discrepancy::Unsat => return LuckyOutcome::Unsat,
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
    /// to `¬dec`. A root-level (level-1) conflict is analyzed and the implied
    /// unit learned (a follow-up root conflict proves UNSAT); a double conflict
    /// above the root just abandons the probe.
    fn lucky_discrepancy(&mut self, dec: Lit) -> Discrepancy {
        self.trail.new_decision_level();
        self.trail.assign_decision(dec);
        let conflict = match self.propagate() {
            None => return Discrepancy::Ok,
            Some(c) => c,
        };
        let level = self.trail.decision_level();
        if level > 1 {
            // Undo just this decision and try the opposite polarity.
            self.backtrack(level - 1);
            self.trail.new_decision_level();
            self.trail.assign_decision(dec.negate());
            if self.propagate().is_none() {
                Discrepancy::Ok
            } else {
                Discrepancy::BothConflict
            }
        } else {
            // Level 1: analyze the conflict, learn the implied root unit,
            // propagate. A second conflict completes a root-level refutation.
            let (bt, learnt) = self.analyze(conflict);
            if learnt.is_empty() {
                self.trivially_unsat = true;
                self.drat_emit_empty();
                self.backtrack(0);
                return Discrepancy::Unsat;
            }
            self.backtrack(bt);
            self.learn_clause(learnt);
            if self.propagate().is_some() {
                self.trivially_unsat = true;
                self.drat_emit_empty();
                self.backtrack(0);
                return Discrepancy::Unsat;
            }
            // The learnt root unit may have assigned `dec`'s variable (or
            // another); the caller re-checks before advancing.
            Discrepancy::Ok
        }
    }
}
