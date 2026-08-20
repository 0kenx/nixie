//! Chronological backtracking support
//!
//! Chronological backtracking (Nadel & Ryvchin, *Chronological Backtracking*,
//! SAT 2018; refined by Möhle & Biere, *Backing Backtracking*, SAT 2019) trades
//! the textbook backjump for a one-level rollback: instead of jumping all the
//! way down to the learned clause's assertion level `a`, the solver backtracks
//! only to `conflict_level - 1` and keeps every decision in between.  That saves
//! the work of re-deriving all the propagations those decisions imply, which is
//! exactly the win when the backjump would otherwise be very deep.
//!
//! Two invariants make this sound, and both live outside this module:
//!
//! * the asserting literal must be assigned at its **true** implication level
//!   (the maximum level over the learned clause's remaining literals), not at
//!   the level the search happens to sit at after the rollback – see
//!   [`crate::trail::Trail::assign_propagation_at`]; and
//! * the trail is consequently no longer sorted by decision level, so rollback
//!   filters by level instead of truncating – see
//!   [`crate::trail::Trail::backtrack_to_with_callback`] – and the solver's
//!   1-UIP conflict analysis skips trail literals that are not at the conflict
//!   level.
//!
//! A **unit** learned clause is never backtracked chronologically: it is a
//! consequence of the formula alone and belongs at level 0.

use crate::literal::Lit;
#[allow(unused_imports)]
use crate::prelude::*;
use crate::trail::Trail;

/// Chronological backtracking helper
#[derive(Debug)]
pub struct ChronoBacktrack {
    /// Enable chronological backtracking
    enabled: bool,
    /// Force chronological on every conflict (cadical `chronoalways`).
    always: bool,
    /// Minimum backjump distance (`conflict_level - assertion_level`) that makes
    /// chronological backtracking worthwhile.  Jumps of at most this many levels
    /// use ordinary backjumping; anything deeper is backtracked chronologically.
    /// `0` forces chronological backtracking on every non-unit conflict.
    threshold: u32,
}

impl ChronoBacktrack {
    /// Create a new chronological backtracking helper
    #[must_use]
    pub fn new(enabled: bool, threshold: u32) -> Self {
        Self {
            enabled,
            always: false,
            threshold,
        }
    }

    /// Set the always-chronological flag (cadical `chronoalways`).
    #[allow(dead_code)]
    pub fn set_always(&mut self, always: bool) {
        self.always = always;
    }

    /// Determine the backtrack level for a learned clause.
    ///
    /// Returns a level in `[assertion_level, conflict_level - 1]`: the assertion
    /// level for an ordinary backjump, or `conflict_level - 1` for a
    /// chronological backtrack.  The upper bound is not negotiable – the
    /// asserting literal sits at `conflict_level`, so the rollback must go at
    /// least one level below it or the literal would still be assigned when the
    /// learned clause tries to imply it, duplicating it on the trail.
    ///
    /// # Arguments
    ///
    /// * `trail` - The assignment trail (used only for debug invariant checks)
    /// * `learnt` - The learned clause, `learnt[0]` being the asserting literal
    /// * `conflict_level` - The level of the asserting literal `learnt[0]`
    /// * `assertion_level` - The second highest level in the clause, i.e. the
    ///   level at which the clause becomes unit (0 for a unit clause)
    ///
    /// # Returns
    ///
    /// The level to backtrack to.
    #[must_use]
    pub fn compute_backtrack_level(
        &self,
        trail: &Trail,
        learnt: &[Lit],
        conflict_level: u32,
        assertion_level: u32,
    ) -> u32 {
        // A unit (or empty) learned clause is implied by the formula alone, so
        // it must be installed at the root level where nothing can retract it.
        // Backtracking chronologically here would pin a global fact inside some
        // decision level, losing it on the next rollback – and, because the
        // asserting literal of a unit clause has no reason clause to resolve
        // against, planting a second reason-less literal in the middle of a
        // level, which breaks 1-UIP termination and yields over-strong (unsound)
        // learned clauses.
        if learnt.len() <= 1 {
            return 0;
        }

        if !self.enabled || conflict_level == 0 || assertion_level >= conflict_level {
            return assertion_level;
        }
        if self.always {
            return conflict_level.saturating_sub(1);
        }

        // Ordinary backjumping for short hops: chronological backtracking pays
        // off precisely when the backjump would throw away many levels of
        // propagation work, and costs (a deeper trail, more re-propagation)
        // when it would not.  Mirrors Z3's `use_backjumping` /
        // `m_backtrack_scopes` and CaDiCaL's `chronolevelim`.
        if conflict_level - assertion_level <= self.threshold {
            return assertion_level;
        }

        let chrono_level = conflict_level - 1;
        debug_assert!(
            self.is_clause_asserting_at_level(trail, learnt, chrono_level),
            "the learned clause must be unit at the chronological backtrack level"
        );
        chrono_level
    }

    /// Check if the clause is asserting at the given level
    ///
    /// A clause is asserting at level L if, restricted to the assignment as
    /// it stood upon *reaching* level L, exactly one literal is unassigned
    /// and all others are false.
    ///
    /// "Unassigned as of level L" covers two distinct cases that must both
    /// be counted, and must NOT be confused with each other:
    /// - The variable is genuinely unassigned in the (current, full) trail.
    /// - The variable *is* assigned, but only at some level strictly above
    ///   `level` – i.e. it hadn't been decided yet by the time the search
    ///   was at level L.
    ///
    /// Crucially, level 0 is a real decision level (unit facts derived by
    /// root-level propagation), not a sentinel for "unassigned" – treating
    /// `trail.level(var) == 0` as "unassigned" would misclassify every
    /// level-0 literal in the clause, and variables actually assigned above
    /// `level` must still be tallied as unassigned rather than silently
    /// dropped from both counts.
    fn is_clause_asserting_at_level(&self, trail: &Trail, clause: &[Lit], level: u32) -> bool {
        let mut unassigned_count = 0;
        let mut false_count = 0;

        for &lit in clause {
            let var = lit.var();

            if !trail.is_assigned(var) {
                // Genuinely unassigned (never decided/propagated at all).
                unassigned_count += 1;
                continue;
            }

            let var_level = trail.level(var);
            if var_level > level {
                // Assigned, but only after the point we're testing: as of
                // reaching `level`, this literal hadn't been decided yet.
                unassigned_count += 1;
            } else {
                // Assigned at or before `level` (including level 0 facts).
                let value = trail.lit_value(lit);
                if value.is_false() {
                    false_count += 1;
                }
            }
        }

        // Clause is asserting if exactly one literal is unassigned and rest are false
        unassigned_count == 1 && false_count == clause.len() - 1
    }

    /// Enable or disable chronological backtracking
    #[allow(dead_code)]
    pub fn set_enabled(&mut self, enabled: bool) {
        self.enabled = enabled;
    }

    /// Set the threshold for chronological backtracking
    #[allow(dead_code)]
    pub fn set_threshold(&mut self, threshold: u32) {
        self.threshold = threshold;
    }

    /// Check if chronological backtracking is enabled
    #[must_use]
    #[allow(dead_code)]
    pub const fn is_enabled(&self) -> bool {
        self.enabled
    }

    /// Get the threshold
    #[must_use]
    #[allow(dead_code)]
    pub const fn threshold(&self) -> u32 {
        self.threshold
    }
}

impl Default for ChronoBacktrack {
    fn default() -> Self {
        // Default: enabled with threshold of 100 levels
        Self::new(true, 100)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::literal::Var;
    use crate::trail::Trail;

    /// Build a trail with `x9` as a level-0 fact and `x1..=x5` decided at
    /// levels 1..=5, matching the shape used by the backtrack-level tests.
    fn chain_trail() -> Trail {
        let mut trail = Trail::new(10);
        trail.assign_decision(Lit::pos(Var::new(9)));
        for v in 1..=5u32 {
            trail.new_decision_level();
            trail.assign_decision(Lit::pos(Var::new(v)));
        }
        trail
    }

    #[test]
    fn test_chrono_disabled() {
        let chrono = ChronoBacktrack::new(false, 100);
        let trail = chain_trail();
        let learnt = vec![Lit::neg(Var::new(5)), Lit::neg(Var::new(1))];

        let level = chrono.compute_backtrack_level(&trail, &learnt, 5, 1);
        assert_eq!(level, 1); // Should use assertion level when disabled
    }

    // The threshold selects between backjumping and chronological backtracking
    // the way Z3's `use_backjumping` does: short hops are backjumped, long ones
    // are backtracked chronologically.  A previous revision had this inverted
    // (chronological only for *short* hops), which made chronological
    // backtracking fire on essentially every conflict – the opposite of the
    // heuristic's intent, and the amplifier that turned the level bugs it was
    // paired with into false `unsat` answers.
    #[test]
    fn test_chrono_threshold_selects_backjump_for_short_hops() {
        let trail = chain_trail();
        let learnt = vec![Lit::neg(Var::new(5)), Lit::neg(Var::new(1))];

        // Jump distance is 5 - 1 = 4.
        let short = ChronoBacktrack::new(true, 10);
        assert_eq!(
            short.compute_backtrack_level(&trail, &learnt, 5, 1),
            1,
            "a 4-level hop is below the threshold and must be backjumped"
        );

        let long = ChronoBacktrack::new(true, 2);
        assert_eq!(
            long.compute_backtrack_level(&trail, &learnt, 5, 1),
            4,
            "a 4-level hop exceeds the threshold and must backtrack chronologically"
        );
    }

    // A unit learned clause is a consequence of the formula alone: it belongs at
    // level 0 regardless of how deep the search was when it was derived, and no
    // threshold setting may override that.
    #[test]
    fn test_chrono_never_lifts_a_unit_clause_off_the_root_level() {
        let trail = chain_trail();
        let learnt = vec![Lit::neg(Var::new(5))];

        for threshold in [0, 1, 100] {
            let chrono = ChronoBacktrack::new(true, threshold);
            assert_eq!(
                chrono.compute_backtrack_level(&trail, &learnt, 5, 0),
                0,
                "unit learned clauses must always be installed at the root level"
            );
        }
    }

    // The asserting literal lives at `conflict_level`, so the rollback must go
    // strictly below it – otherwise the literal is still assigned when the
    // learned clause implies it and it ends up duplicated on the trail.
    #[test]
    fn test_chrono_level_stays_below_the_asserting_literal() {
        let trail = chain_trail();
        let learnt = vec![Lit::neg(Var::new(5)), Lit::neg(Var::new(1))];

        for threshold in [0, 1, 2, 3, 100] {
            let chrono = ChronoBacktrack::new(true, threshold);
            let level = chrono.compute_backtrack_level(&trail, &learnt, 5, 1);
            assert!(
                (1..5).contains(&level),
                "backtrack level {level} must lie in [assertion_level, conflict_level)"
            );
        }
    }

    #[test]
    fn test_chrono_enabled() {
        let chrono = ChronoBacktrack::new(true, 100);
        assert!(chrono.is_enabled());
        assert_eq!(chrono.threshold(), 100);
    }

    #[test]
    fn test_chrono_default() {
        let chrono = ChronoBacktrack::default();
        assert!(chrono.is_enabled());
        assert_eq!(chrono.threshold(), 100);
    }

    // Chronological backtracking keeps the decisions between the assertion
    // level and the conflict level instead of throwing them away: with x9 a
    // level-0 fact, x1..x4 decided at levels 1..4 and x5 (the UIP) at level 5,
    // the clause `¬x5 ∨ ¬x9 ∨ ¬x1` is asserting from level 1 upwards, and a
    // chronological rollback stops at level 4 – retaining the levels 2..4 that a
    // plain backjump to the assertion level 1 would have discarded.
    #[test]
    fn test_chrono_backtrack_keeps_intervening_decisions() {
        let chrono = ChronoBacktrack::new(true, 0);
        let trail = chain_trail();

        let learnt = vec![
            Lit::neg(Var::new(5)),
            Lit::neg(Var::new(9)),
            Lit::neg(Var::new(1)),
        ];

        let level = chrono.compute_backtrack_level(&trail, &learnt, 5, 1);

        assert_eq!(
            level, 4,
            "chronological backtracking should stop one level below the conflict \
             level instead of jumping down to the assertion level"
        );
    }

    // Companion test isolating just the level-0-vs-unassigned confusion:
    // a clause containing only a level-0 literal (always false) and the
    // current-level UIP literal must be recognized as asserting even at
    // level 0 itself.
    #[test]
    fn test_asserting_check_treats_level_zero_as_assigned_not_unassigned() {
        let chrono = ChronoBacktrack::new(true, 100);
        let mut trail = Trail::new(10);

        // Level 0 fact: x0 = true, so ¬x0 is false.
        trail.assign_decision(Lit::pos(Var::new(0)));

        trail.new_decision_level();
        trail.assign_decision(Lit::pos(Var::new(1)));

        let learnt = vec![Lit::neg(Var::new(1)), Lit::neg(Var::new(0))];

        assert!(
            chrono.is_clause_asserting_at_level(&trail, &learnt, 0),
            "with x0 correctly read as false (not unassigned) at level 0, \
             ¬x1 is the sole unassigned literal, so the clause is asserting"
        );
    }
}
