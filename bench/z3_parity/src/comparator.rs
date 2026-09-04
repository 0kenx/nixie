use crate::SolverResult;
use serde::{Deserialize, Serialize};

#[derive(Debug, Clone, Serialize, Deserialize, PartialEq, Eq)]
pub enum MatchStatus {
    Correct,      // Both solvers agree on a decisive (Sat/Unsat) answer
    Wrong,        // Different decisive results (SAT vs UNSAT) - a real soundness problem
    Inconclusive, // Either or both solvers answered UNKNOWN - no parity claim can be made
    Timeout,      // One or both timed out
    Error,        // Parse/execution error in one or both
}

impl MatchStatus {
    /// True for statuses that represent a decisive (Sat/Unsat) comparison,
    /// i.e. statuses that should count towards the parity percentage.
    pub fn is_decisive(&self) -> bool {
        matches!(self, MatchStatus::Correct | MatchStatus::Wrong)
    }
}

pub fn compare_results(nixie: &SolverResult, z3: &SolverResult) -> MatchStatus {
    match (nixie, z3) {
        // Both agree on SAT
        (SolverResult::Sat, SolverResult::Sat) => MatchStatus::Correct,

        // Both agree on UNSAT
        (SolverResult::Unsat, SolverResult::Unsat) => MatchStatus::Correct,

        // Both agree on UNKNOWN - neither solver decided anything, so this
        // is NOT a "Correct" parity result: it carries zero evidence that
        // the two solvers agree on the actual answer. Report separately.
        (SolverResult::Unknown, SolverResult::Unknown) => MatchStatus::Inconclusive,

        // One returned UNKNOWN, the other a definite answer. This is not a
        // disagreement (Unknown is a valid, honest response), but it is
        // also not a confirmed parity match - the definite answer was
        // never cross-checked. Count it as inconclusive, not Correct, so a
        // solver cannot buy 100% "parity" by always answering Unknown.
        (SolverResult::Unknown, _) | (_, SolverResult::Unknown) => MatchStatus::Inconclusive,

        // Timeout cases
        (SolverResult::Timeout, _) | (_, SolverResult::Timeout) => MatchStatus::Timeout,

        // Error cases
        (SolverResult::Error(_), _) | (_, SolverResult::Error(_)) => MatchStatus::Error,

        // Disagreement on SAT/UNSAT - this is a real problem!
        (SolverResult::Sat, SolverResult::Unsat) | (SolverResult::Unsat, SolverResult::Sat) => {
            MatchStatus::Wrong
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_both_sat() {
        let status = compare_results(&SolverResult::Sat, &SolverResult::Sat);
        assert_eq!(status, MatchStatus::Correct);
    }

    #[test]
    fn test_both_unsat() {
        let status = compare_results(&SolverResult::Unsat, &SolverResult::Unsat);
        assert_eq!(status, MatchStatus::Correct);
    }

    #[test]
    fn test_both_unknown() {
        // Both solvers giving up carries no evidence of agreement - it must
        // NOT count as "Correct", or a solver could claim 100% parity by
        // always answering unknown.
        let status = compare_results(&SolverResult::Unknown, &SolverResult::Unknown);
        assert_eq!(status, MatchStatus::Inconclusive);
        assert!(!status.is_decisive());
    }

    #[test]
    fn test_disagreement() {
        let status = compare_results(&SolverResult::Sat, &SolverResult::Unsat);
        assert_eq!(status, MatchStatus::Wrong);
        assert!(status.is_decisive());
    }

    #[test]
    fn test_unknown_vs_sat() {
        // Unknown vs a definite answer is not a confirmed match: the
        // definite answer was never cross-checked by the other solver.
        let status = compare_results(&SolverResult::Unknown, &SolverResult::Sat);
        assert_eq!(status, MatchStatus::Inconclusive);
        assert!(!status.is_decisive());
    }

    #[test]
    fn test_sat_vs_unknown_symmetric() {
        let status = compare_results(&SolverResult::Sat, &SolverResult::Unknown);
        assert_eq!(status, MatchStatus::Inconclusive);
    }

    #[test]
    fn test_unknown_never_counts_as_correct() {
        // Regression guard for the "always answer unknown = 100% parity"
        // defect: no combination involving Unknown may ever produce
        // MatchStatus::Correct.
        let unknown_pairs = [
            (SolverResult::Unknown, SolverResult::Unknown),
            (SolverResult::Unknown, SolverResult::Sat),
            (SolverResult::Sat, SolverResult::Unknown),
            (SolverResult::Unknown, SolverResult::Unsat),
            (SolverResult::Unsat, SolverResult::Unknown),
        ];
        for (nixie, z3) in unknown_pairs {
            let status = compare_results(&nixie, &z3);
            assert_ne!(status, MatchStatus::Correct);
            assert!(!status.is_decisive());
        }
    }

    #[test]
    fn test_timeout() {
        let status = compare_results(&SolverResult::Timeout, &SolverResult::Sat);
        assert_eq!(status, MatchStatus::Timeout);
    }

    #[test]
    fn test_error() {
        let status = compare_results(&SolverResult::Error("test".to_string()), &SolverResult::Sat);
        assert_eq!(status, MatchStatus::Error);
    }
}
