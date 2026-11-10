//! Query budgets are armed once, outside all theory and arithmetic repair rounds.

use super::Solver;

impl Solver {
    pub(super) fn begin_check_budget(&mut self) {
        self.check_deadline = (self.config.timeout_ms > 0)
            .then(|| {
                nixie_time::Instant::now()
                    .checked_add(core::time::Duration::from_millis(self.config.timeout_ms))
            })
            .flatten();
        let conflicts = (self.config.max_conflicts > 0).then_some(self.config.max_conflicts);
        let decisions = (self.config.max_decisions > 0).then_some(self.config.max_decisions);
        let conflict_ceiling = conflicts.map(|n| self.sat.stats().conflicts.saturating_add(n));
        let decision_ceiling = decisions.map(|n| self.sat.stats().decisions.saturating_add(n));
        self.sat.set_max_conflicts(conflict_ceiling);
        self.sat.set_max_decisions(decision_ceiling);
        self.sat.set_deadline(self.check_deadline);
        self.bv.set_budget(conflicts, self.check_deadline);
        self.statistics.bv_embedded_checks = 0;
        self.statistics.array_refinement_rounds = 0;
        self.statistics.array_lemma_instances = 0;
        self.check_theory_conflict_ceiling = conflicts
            .map(|n| self.statistics.conflicts.saturating_add(n))
            .unwrap_or(0);
    }

    /// Conflicts spent by embedded bit-vector searches in the most recent query.
    #[must_use]
    pub fn bv_conflicts_spent(&self) -> u64 {
        self.bv.conflicts_spent()
    }
}
