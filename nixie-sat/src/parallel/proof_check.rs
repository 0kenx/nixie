//! Parallel Proof Checking (EXPERIMENTAL / structural only).
#![allow(missing_docs, dead_code)] // Under development
//!
//! Validates SAT proofs in parallel for faster verification.
//!
//! # Current status
//!
//! This checker performs only *structural* validation of the toy [`ProofStep`]
//! representation used here (every premise must reference an earlier step id).
//! It does **not** yet perform RUP / resolution semantic checking, because
//! [`ProofStep`] carries no clause literals to check against. Consequently a
//! well-formed but semantically unverified proof reports
//! [`ProofCheckResult::Incomplete`], never [`ProofCheckResult::Valid`]: this API
//! must never certify an unchecked proof as valid (that would be false
//! assurance about an UNSAT result). Use the DRAT/LRAT writers plus an external
//! checker for real certificate verification.

#[allow(unused_imports)]
use crate::prelude::*;
use rayon::iter::{IndexedParallelIterator, IntoParallelRefIterator, ParallelIterator};

/// Configuration for parallel proof checking.
#[derive(Debug, Clone)]
pub struct ProofCheckConfig {
    /// Number of parallel workers
    pub num_workers: usize,
    /// Chunk size for parallel processing
    pub chunk_size: usize,
    /// Enable detailed error reporting
    pub detailed_errors: bool,
}

impl Default for ProofCheckConfig {
    fn default() -> Self {
        Self {
            num_workers: std::thread::available_parallelism()
                .map(|n| n.get())
                .unwrap_or(4),
            chunk_size: 100,
            detailed_errors: true,
        }
    }
}

/// Result of proof checking.
#[derive(Debug, Clone)]
pub enum ProofCheckResult {
    /// Proof is valid
    Valid,
    /// Proof is invalid with error details
    Invalid { step_id: usize, reason: String },
    /// Checking incomplete (timeout or resource limit)
    Incomplete,
}

/// Parallel proof checker.
pub struct ParallelProofChecker {
    config: ProofCheckConfig,
}

impl ParallelProofChecker {
    /// Create a new parallel proof checker.
    pub fn new(config: ProofCheckConfig) -> Self {
        Self { config }
    }

    /// Create with default configuration.
    pub fn default_config() -> Self {
        Self::new(ProofCheckConfig::default())
    }

    /// Check a proof.
    ///
    /// Runs structural validation over the steps in parallel chunks. Returns:
    /// - [`ProofCheckResult::Valid`] only for the empty proof (nothing to reject);
    /// - [`ProofCheckResult::Invalid`] if any step is malformed (a premise that
    ///   does not reference a strictly-earlier step id);
    /// - [`ProofCheckResult::Incomplete`] for a structurally well-formed but
    ///   semantically unverified proof – the honest verdict, since RUP/resolution
    ///   checking is not implemented for this representation.
    pub fn check_proof(&self, proof_steps: &[ProofStep]) -> ProofCheckResult {
        if proof_steps.is_empty() {
            return ProofCheckResult::Valid;
        }

        // Divide proof into chunks and validate structure in parallel. Each
        // check is chunk-local (a premise must reference a smaller id), so no
        // shared context is needed.
        let chunks: Vec<_> = proof_steps.chunks(self.config.chunk_size).collect();

        let results: Vec<_> = chunks
            .par_iter()
            .enumerate()
            .map(|(chunk_idx, chunk)| self.check_chunk(chunk, chunk_idx * self.config.chunk_size))
            .collect();

        // Any structural error is decisive.
        for result in results {
            if let ProofCheckResult::Invalid { .. } = result {
                return result;
            }
        }

        // Structurally well-formed, but not semantically verified: report
        // Incomplete rather than fabricating a Valid certificate.
        ProofCheckResult::Incomplete
    }

    /// Structurally validate a chunk of proof steps.
    ///
    /// Returns [`ProofCheckResult::Invalid`] on the first malformed step, else
    /// [`ProofCheckResult::Incomplete`] (structure is fine; semantics unchecked).
    fn check_chunk(&self, steps: &[ProofStep], _base_idx: usize) -> ProofCheckResult {
        for step in steps {
            if !self.verify_step(step) {
                return ProofCheckResult::Invalid {
                    step_id: step.id,
                    reason: "malformed step: a premise does not reference an earlier step id"
                        .to_string(),
                };
            }
        }
        ProofCheckResult::Incomplete
    }

    /// Structural well-formedness of a single proof step.
    ///
    /// A necessary (but not sufficient) condition for a valid derivation: every
    /// premise of a derived step must reference a strictly-earlier step id, and a
    /// resolution step must have at least one premise. Input steps have no
    /// premises. This does not establish semantic (RUP) validity.
    fn verify_step(&self, step: &ProofStep) -> bool {
        match step.rule {
            ProofRule::Input => step.premises.is_empty(),
            ProofRule::Resolution => {
                !step.premises.is_empty() && step.premises.iter().all(|&p| p < step.id)
            }
            ProofRule::Deletion => step.premises.iter().all(|&p| p < step.id),
        }
    }
}

/// A proof step (simplified).
#[derive(Debug, Clone)]
pub struct ProofStep {
    pub id: usize,
    pub rule: ProofRule,
    pub premises: Vec<usize>,
}

/// Proof rules (simplified).
#[derive(Debug, Clone, Copy)]
pub enum ProofRule {
    Input,
    Resolution,
    Deletion,
}

/// Proof checking context.
#[derive(Debug, Clone)]
struct ProofContext {
    derived_clauses: FxHashMap<usize, Vec<i32>>,
}

impl ProofContext {
    fn new() -> Self {
        Self {
            derived_clauses: FxHashMap::default(),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_proof_checker_creation() {
        let checker = ParallelProofChecker::default_config();
        assert_eq!(checker.config.chunk_size, 100);
    }

    #[test]
    fn test_empty_proof() {
        let checker = ParallelProofChecker::default_config();
        let result = checker.check_proof(&[]);
        assert!(matches!(result, ProofCheckResult::Valid));
    }

    #[test]
    fn test_proof_check_result() {
        let valid = ProofCheckResult::Valid;
        assert!(matches!(valid, ProofCheckResult::Valid));

        let invalid = ProofCheckResult::Invalid {
            step_id: 42,
            reason: "test".to_string(),
        };
        assert!(matches!(invalid, ProofCheckResult::Invalid { .. }));
    }

    // Finding 4: a well-formed but semantically unverified proof must report
    // Incomplete, never a fabricated Valid.
    #[test]
    fn test_wellformed_proof_is_incomplete_not_valid() {
        let checker = ParallelProofChecker::default_config();
        let steps = vec![
            ProofStep {
                id: 1,
                rule: ProofRule::Input,
                premises: vec![],
            },
            ProofStep {
                id: 2,
                rule: ProofRule::Input,
                premises: vec![],
            },
            ProofStep {
                id: 3,
                rule: ProofRule::Resolution,
                premises: vec![1, 2],
            },
        ];
        let result = checker.check_proof(&steps);
        assert!(
            matches!(result, ProofCheckResult::Incomplete),
            "unverified proof must be Incomplete, got {result:?}"
        );
    }

    // A malformed step (premise referencing a later/self id, or a resolution
    // with no premises) must be rejected as Invalid.
    #[test]
    fn test_malformed_proof_is_invalid() {
        let checker = ParallelProofChecker::default_config();
        let steps = vec![
            ProofStep {
                id: 1,
                rule: ProofRule::Input,
                premises: vec![],
            },
            // Resolution referencing a not-yet-defined id 5.
            ProofStep {
                id: 2,
                rule: ProofRule::Resolution,
                premises: vec![5],
            },
        ];
        let result = checker.check_proof(&steps);
        assert!(
            matches!(result, ProofCheckResult::Invalid { step_id: 2, .. }),
            "forward premise reference must be Invalid, got {result:?}"
        );
    }

    #[test]
    fn test_resolution_without_premises_is_invalid() {
        let checker = ParallelProofChecker::default_config();
        let steps = vec![ProofStep {
            id: 1,
            rule: ProofRule::Resolution,
            premises: vec![],
        }];
        let result = checker.check_proof(&steps);
        assert!(matches!(result, ProofCheckResult::Invalid { .. }));
    }
}
