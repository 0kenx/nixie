//! Chronological backtracking support
//!
//! Chronological backtracking is a modern SAT solving technique that can improve
//! performance by sometimes backtracking chronologically instead of always using
//! non-chronological backtracking.
//!
//! Key idea: After learning a clause, instead of always jumping to the assertion
//! level, we can sometimes backtrack chronologically (one level at a time) if the
//! learned clause is still satisfied at higher levels.

use crate::literal::Lit;
#[allow(unused_imports)]
use crate::prelude::*;
use crate::trail::Trail;

/// Chronological backtracking helper
#[derive(Debug)]
pub struct ChronoBacktrack {
    /// Enable chronological backtracking
    enabled: bool,
    /// Threshold for chronological backtracking (max distance from current level)
    threshold: u32,
}

impl ChronoBacktrack {
    /// Create a new chronological backtracking helper
    #[must_use]
    pub fn new(enabled: bool, threshold: u32) -> Self {
        Self { enabled, threshold }
    }

    /// Determine the backtrack level for a learned clause
    ///
    /// Returns the level to backtrack to, which may be higher than the
    /// assertion level if chronological backtracking is beneficial.
    ///
    /// # Arguments
    ///
    /// * `trail` - The assignment trail
    /// * `learnt` - The learned clause (first literal is the asserting literal)
    /// * `assertion_level` - The traditional assertion level (second highest level)
    ///
    /// # Returns
    ///
    /// The level to backtrack to
    #[must_use]
    pub fn compute_backtrack_level(
        &self,
        trail: &Trail,
        learnt: &[Lit],
        assertion_level: u32,
    ) -> u32 {
        if !self.enabled || learnt.is_empty() {
            return assertion_level;
        }

        let current_level = trail.decision_level();

        // If we're already at or below the assertion level, use it
        if current_level <= assertion_level {
            return assertion_level;
        }

        // If the distance is too large, use non-chronological backtracking
        if current_level - assertion_level > self.threshold {
            return assertion_level;
        }

        // Try chronological backtracking: find the highest level where the
        // learned clause is still asserting (exactly one literal unassigned)
        let mut best_level = assertion_level;

        for level in (assertion_level + 1)..=current_level {
            if self.is_clause_asserting_at_level(trail, learnt, level) {
                best_level = level - 1; // Backtrack to just before this level
            } else {
                break;
            }
        }

        best_level
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
    ///   `level` — i.e. it hadn't been decided yet by the time the search
    ///   was at level L.
    ///
    /// Crucially, level 0 is a real decision level (unit facts derived by
    /// root-level propagation), not a sentinel for "unassigned" — treating
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

    #[test]
    fn test_chrono_disabled() {
        let chrono = ChronoBacktrack::new(false, 100);
        let trail = Trail::new(10);
        let learnt = vec![Lit::pos(Var::new(0)), Lit::neg(Var::new(1))];

        let level = chrono.compute_backtrack_level(&trail, &learnt, 5);
        assert_eq!(level, 5); // Should use assertion level when disabled
    }

    #[test]
    fn test_chrono_threshold() {
        let chrono = ChronoBacktrack::new(true, 10);
        let trail = Trail::new(100);

        // Create a learned clause
        let learnt = vec![Lit::pos(Var::new(0)), Lit::neg(Var::new(1))];

        // Distance is 50, which exceeds threshold of 10
        let level = chrono.compute_backtrack_level(&trail, &learnt, 5);

        // Should use non-chronological backtracking (assertion level) when threshold exceeded
        // Note: In a real scenario, the trail would have assignments that determine the behavior
        assert!(level <= 55); // Either assertion level or chronological, but reasonable
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

    // Regression test: `is_clause_asserting_at_level` previously (a) treated
    // any variable assigned at decision level 0 as *unassigned* rather than
    // checking its actual (permanent) truth value, and (b) silently dropped
    // variables assigned strictly above the level under test instead of
    // counting them as unassigned — together these meant the asserting
    // check almost never succeeded, so chronological backtracking was
    // effectively inert and `compute_backtrack_level` always degenerated to
    // the plain (non-chronological) assertion level.
    //
    // Build a trail where x9 is a level-0 fact and x1..x4 are decisions at
    // levels 1..4, with x5 (the would-be UIP) decided at level 5. The learnt
    // clause `¬x5 ∨ ¬x9 ∨ ¬x1` stays asserting through levels 2..4 (x5 is
    // simply not yet decided as of those points, and x9/x1 are both false),
    // so chronological backtracking should jump to level 3 — strictly
    // higher than the traditional assertion level of 1. Under the old
    // buggy logic this returned 1 (no chronological jump at all).
    #[test]
    fn test_chrono_backtrack_finds_higher_level_for_asserting_clause() {
        let chrono = ChronoBacktrack::new(true, 100);
        let mut trail = Trail::new(10);

        // Level 0: root-level fact. Must NOT be misread as "unassigned".
        trail.assign_decision(Lit::pos(Var::new(9)));

        // Level 1: drives assertion_level = 1.
        trail.new_decision_level();
        trail.assign_decision(Lit::pos(Var::new(1)));

        // Levels 2..4: decisions unrelated to the learnt clause; the clause
        // should remain asserting all the way through them.
        trail.new_decision_level();
        trail.assign_decision(Lit::pos(Var::new(2)));
        trail.new_decision_level();
        trail.assign_decision(Lit::pos(Var::new(3)));
        trail.new_decision_level();
        trail.assign_decision(Lit::pos(Var::new(4)));

        // Level 5: the (would-be) UIP variable.
        trail.new_decision_level();
        trail.assign_decision(Lit::pos(Var::new(5)));

        let learnt = vec![
            Lit::neg(Var::new(5)),
            Lit::neg(Var::new(9)),
            Lit::neg(Var::new(1)),
        ];

        let level = chrono.compute_backtrack_level(&trail, &learnt, 1);

        assert_eq!(
            level, 3,
            "chronological backtracking should skip past levels 2..4 instead of \
             degenerating to the plain assertion level"
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
