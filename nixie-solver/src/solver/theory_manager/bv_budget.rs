//! Deterministic bound on embedded checks, including checks that need no conflicts.

use super::TheoryManager;

// Upstream 0.3.4's calibrated cap. Explicit options can only lower it.
const BV_EMBEDDED_CHECK_CEILING: u64 = 250_000;

pub(super) fn effective_bv_embedded_check_ceiling(user: u64) -> u64 {
    if user == 0 {
        BV_EMBEDDED_CHECK_CEILING
    } else {
        user.min(BV_EMBEDDED_CHECK_CEILING)
    }
}

impl TheoryManager<'_> {
    pub(super) fn charge_bv_embedded_check(&mut self) -> bool {
        self.statistics.bv_embedded_checks = self.statistics.bv_embedded_checks.saturating_add(1);
        self.bv_embedded_budget_spent()
    }

    pub(super) fn bv_embedded_budget_spent(&self) -> bool {
        self.statistics.bv_embedded_checks > self.bv_embedded_check_ceiling
    }
}

#[cfg(test)]
mod tests {
    use super::effective_bv_embedded_check_ceiling;

    #[test]
    fn upstream_cap_can_only_be_lowered() {
        assert_eq!(effective_bv_embedded_check_ceiling(0), 250_000);
        assert_eq!(effective_bv_embedded_check_ceiling(20_000), 20_000);
        assert_eq!(effective_bv_embedded_check_ceiling(u64::MAX), 250_000);
    }
}
