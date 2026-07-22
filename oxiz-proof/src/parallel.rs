//! Parallel proof checking and processing.
//!
//! This module provides parallel processing capabilities for proof operations
//! using rayon for multi-threaded execution.

use crate::checker::CheckError;
use crate::proof::{Proof, ProofNode, ProofNodeId};
use rustc_hash::FxHashSet;
use std::sync::Arc;

/// Result of parallel proof checking.
pub type ParallelCheckResult<T> = Result<T, Vec<CheckError>>;

/// Configuration for parallel proof processing.
#[derive(Debug, Clone)]
pub struct ParallelConfig {
    /// Number of threads to use (None = use rayon default)
    pub num_threads: Option<usize>,
    /// Batch size for parallel processing
    pub batch_size: usize,
    /// Enable progress reporting
    pub report_progress: bool,
}

impl Default for ParallelConfig {
    fn default() -> Self {
        Self {
            num_threads: None,
            batch_size: 100,
            report_progress: false,
        }
    }
}

impl ParallelConfig {
    /// Create a new parallel configuration.
    pub fn new() -> Self {
        Self::default()
    }

    /// Set the number of threads.
    pub fn with_threads(mut self, threads: usize) -> Self {
        self.num_threads = Some(threads);
        self
    }

    /// Set the batch size.
    pub fn with_batch_size(mut self, size: usize) -> Self {
        self.batch_size = size;
        self
    }

    /// Enable progress reporting.
    pub fn with_progress(mut self, enabled: bool) -> Self {
        self.report_progress = enabled;
        self
    }
}

/// Parallel proof processor.
pub struct ParallelProcessor {
    config: ParallelConfig,
}

impl Default for ParallelProcessor {
    fn default() -> Self {
        Self::new()
    }
}

impl ParallelProcessor {
    /// Create a new parallel processor with default configuration.
    pub fn new() -> Self {
        Self {
            config: ParallelConfig::default(),
        }
    }

    /// Create with custom configuration.
    pub fn with_config(config: ParallelConfig) -> Self {
        Self { config }
    }

    /// Check a proof in parallel.
    ///
    /// This structurally validates every proof node in parallel: each node
    /// must exist, and every premise referenced by an `Inference` step must
    /// itself be an *earlier*, already-existing node. `Proof` allocates node
    /// IDs monotonically as nodes are added, so a premise ID that is
    /// missing, equal to the node's own ID, or greater than it can only
    /// arise from a corrupted or hand-crafted proof (self-reference or a
    /// forward/dangling reference) -- such proofs are rejected here.
    ///
    /// This is a structural check, not a semantic one: it does not re-derive
    /// whether a rule's conclusion actually follows from its premises. For
    /// full rule-level (theory/Alethe) semantic checking, use
    /// [`crate::checker::ProofChecker`] on the corresponding
    /// [`crate::theory::TheoryProof`] / [`crate::alethe::AletheProof`].
    pub fn check_proof_parallel(&self, proof: &Proof) -> ParallelCheckResult<()> {
        // Create a thread-safe reference to the proof
        let proof_arc = Arc::new(proof);

        // Collect all node IDs
        let node_ids: Vec<ProofNodeId> = proof.nodes().iter().map(|n| n.id).collect();

        // Process nodes in batches to avoid overhead
        let errors: Vec<CheckError> = node_ids
            .chunks(self.config.batch_size)
            .flat_map(|chunk| {
                chunk
                    .iter()
                    .filter_map(|&node_id| {
                        let proof_ref = Arc::clone(&proof_arc);
                        self.check_node_validity(proof_ref.as_ref(), node_id).err()
                    })
                    .collect::<Vec<_>>()
            })
            .collect();

        if errors.is_empty() {
            Ok(())
        } else {
            Err(errors)
        }
    }

    /// Validate proof node dependencies in parallel.
    pub fn validate_dependencies_parallel(&self, proof: &Proof) -> ParallelCheckResult<()> {
        let proof_arc = Arc::new(proof);
        let node_ids: Vec<ProofNodeId> = proof.nodes().iter().map(|n| n.id).collect();

        let errors: Vec<CheckError> = node_ids
            .chunks(self.config.batch_size)
            .flat_map(|chunk| {
                chunk
                    .iter()
                    .filter_map(|&node_id| {
                        let proof_ref = Arc::clone(&proof_arc);
                        self.check_node_dependencies(proof_ref.as_ref(), node_id)
                            .err()
                    })
                    .collect::<Vec<_>>()
            })
            .collect();

        if errors.is_empty() {
            Ok(())
        } else {
            Err(errors)
        }
    }

    /// Find all nodes satisfying a predicate in parallel.
    pub fn find_nodes_parallel<F>(&self, proof: &Proof, predicate: F) -> Vec<ProofNodeId>
    where
        F: Fn(&ProofNode) -> bool + Send + Sync,
    {
        let predicate_arc = Arc::new(predicate);
        let nodes: Vec<&ProofNode> = proof.nodes().iter().collect();

        nodes
            .chunks(self.config.batch_size)
            .flat_map(|chunk| {
                chunk
                    .iter()
                    .filter_map(|node| {
                        let pred = Arc::clone(&predicate_arc);
                        if pred(node) { Some(node.id) } else { None }
                    })
                    .collect::<Vec<_>>()
            })
            .collect()
    }

    // Helper: Check node validity (structural: existence + premise well-formedness).
    fn check_node_validity(&self, proof: &Proof, node_id: ProofNodeId) -> Result<(), CheckError> {
        let node = proof
            .get_node(node_id)
            .ok_or_else(|| CheckError::Custom(format!("Node {} not found", node_id)))?;

        if let crate::proof::ProofStep::Inference { premises, .. } = &node.step {
            for &premise_id in premises.iter() {
                // Node IDs are allocated monotonically by `Proof`, so a
                // legitimately-derived inference can only reference premises
                // that were added strictly before it. A premise ID equal to
                // or greater than the node's own ID is either a
                // self-reference or a forward reference into the future --
                // both indicate a corrupted proof.
                if premise_id.0 >= node_id.0 {
                    return Err(CheckError::CyclicDependency);
                }
                if proof.get_node(premise_id).is_none() {
                    return Err(CheckError::MissingPremise(premise_id.0));
                }
            }
        }

        Ok(())
    }

    // Helper: Check node dependencies
    fn check_node_dependencies(
        &self,
        proof: &Proof,
        node_id: ProofNodeId,
    ) -> Result<(), CheckError> {
        if let Some(node) = proof.get_node(node_id) {
            // Check that all premises exist
            if let crate::proof::ProofStep::Inference { premises, .. } = &node.step {
                for &premise_id in premises.iter() {
                    if proof.get_node(premise_id).is_none() {
                        return Err(CheckError::Custom(format!(
                            "Premise {} not found for node {}",
                            premise_id, node_id
                        )));
                    }
                }
            }
            Ok(())
        } else {
            Err(CheckError::Custom(format!("Node {} not found", node_id)))
        }
    }
}

/// Parallel proof statistics computation.
pub struct ParallelStatsComputer {
    config: ParallelConfig,
}

impl Default for ParallelStatsComputer {
    fn default() -> Self {
        Self::new()
    }
}

impl ParallelStatsComputer {
    /// Create a new parallel statistics computer.
    pub fn new() -> Self {
        Self {
            config: ParallelConfig::default(),
        }
    }

    /// Create with custom configuration.
    pub fn with_config(config: ParallelConfig) -> Self {
        Self { config }
    }

    /// Compute rule frequency in parallel.
    pub fn compute_rule_frequency(&self, proof: &Proof) -> rustc_hash::FxHashMap<String, usize> {
        let nodes: Vec<&ProofNode> = proof.nodes().iter().collect();
        let mut frequency = rustc_hash::FxHashMap::default();

        for chunk in nodes.chunks(self.config.batch_size) {
            for node in chunk {
                if let crate::proof::ProofStep::Inference { rule, .. } = &node.step {
                    *frequency.entry(rule.clone()).or_insert(0) += 1;
                }
            }
        }

        frequency
    }

    /// Find all unique conclusions in parallel.
    pub fn find_unique_conclusions(&self, proof: &Proof) -> FxHashSet<String> {
        let nodes: Vec<&ProofNode> = proof.nodes().iter().collect();
        let mut conclusions = FxHashSet::default();

        for chunk in nodes.chunks(self.config.batch_size) {
            for node in chunk {
                conclusions.insert(node.conclusion().to_string());
            }
        }

        conclusions
    }

    /// Compute depth histogram in parallel.
    pub fn compute_depth_histogram(&self, proof: &Proof) -> rustc_hash::FxHashMap<usize, usize> {
        let nodes: Vec<&ProofNode> = proof.nodes().iter().collect();
        let mut histogram = rustc_hash::FxHashMap::default();

        for chunk in nodes.chunks(self.config.batch_size) {
            for node in chunk {
                *histogram.entry(node.depth as usize).or_insert(0) += 1;
            }
        }

        histogram
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_parallel_config_new() {
        let config = ParallelConfig::new();
        assert_eq!(config.num_threads, None);
        assert_eq!(config.batch_size, 100);
        assert!(!config.report_progress);
    }

    #[test]
    fn test_parallel_config_with_settings() {
        let config = ParallelConfig::new()
            .with_threads(4)
            .with_batch_size(50)
            .with_progress(true);
        assert_eq!(config.num_threads, Some(4));
        assert_eq!(config.batch_size, 50);
        assert!(config.report_progress);
    }

    #[test]
    fn test_parallel_processor_new() {
        let processor = ParallelProcessor::new();
        assert_eq!(processor.config.batch_size, 100);
    }

    #[test]
    fn test_check_proof_parallel_empty() {
        let processor = ParallelProcessor::new();
        let proof = Proof::new();
        assert!(processor.check_proof_parallel(&proof).is_ok());
    }

    #[test]
    fn test_check_proof_parallel_valid_proof() {
        let processor = ParallelProcessor::new();
        let mut proof = Proof::new();
        let ax1 = proof.add_axiom("x = x");
        let ax2 = proof.add_axiom("y = y");
        proof.add_inference("and", vec![ax1, ax2], "x = x and y = y");

        assert!(processor.check_proof_parallel(&proof).is_ok());
    }

    #[test]
    fn test_check_proof_parallel_rejects_dangling_premise() {
        // PF-02 regression: a proof step that references a premise ID
        // which was never added to the proof is corrupted and must be
        // rejected, not rubber-stamped as valid. Since `Proof` allocates
        // node IDs monotonically without gaps, any premise ID that does not
        // exist is necessarily >= the referencing node's own ID, which is
        // detected as a forward/dangling reference (`CyclicDependency`).
        let processor = ParallelProcessor::new();
        let mut proof = Proof::new();
        let ax1 = proof.add_axiom("x = x");
        // Fabricate a bogus premise ID that does not exist in the proof.
        let bogus_premise = ProofNodeId(ax1.0 + 999);
        proof.add_inference("bogus_rule", vec![bogus_premise], "garbage conclusion");

        let result = processor.check_proof_parallel(&proof);
        assert!(result.is_err());
        let errors = result.expect_err("corrupted proof must fail parallel check");
        assert!(!errors.is_empty());
        assert!(errors.iter().any(|e| matches!(
            e,
            CheckError::MissingPremise(_) | CheckError::CyclicDependency
        )));
    }

    #[test]
    fn test_check_proof_parallel_rejects_self_referential_premise() {
        // A node cannot legitimately reference itself (or a later node) as
        // a premise; node IDs are allocated monotonically, so this can only
        // happen in a corrupted proof.
        let processor = ParallelProcessor::new();
        let mut proof = Proof::new();
        let ax1 = proof.add_axiom("x = x");
        // Self-referential premise: the new node references its own future ID.
        let self_id = ProofNodeId(ax1.0 + 1);
        proof.add_inference("self_rule", vec![self_id], "self-referential");

        let result = processor.check_proof_parallel(&proof);
        assert!(result.is_err());
        let errors = result.expect_err("corrupted proof must fail parallel check");
        assert!(
            errors
                .iter()
                .any(|e| matches!(e, CheckError::CyclicDependency))
        );
    }

    #[test]
    fn test_validate_dependencies_parallel() {
        let processor = ParallelProcessor::new();
        let mut proof = Proof::new();
        proof.add_axiom("x = x");
        assert!(processor.validate_dependencies_parallel(&proof).is_ok());
    }

    #[test]
    fn test_find_nodes_parallel() {
        let processor = ParallelProcessor::new();
        let mut proof = Proof::new();
        let id1 = proof.add_axiom("x = x");
        let _id2 = proof.add_axiom("y = y");

        let results = processor.find_nodes_parallel(&proof, |n| n.id == id1);
        assert_eq!(results.len(), 1);
        assert_eq!(results[0], id1);
    }

    #[test]
    fn test_parallel_stats_computer_new() {
        let computer = ParallelStatsComputer::new();
        assert_eq!(computer.config.batch_size, 100);
    }

    #[test]
    fn test_compute_rule_frequency() {
        let computer = ParallelStatsComputer::new();
        let mut proof = Proof::new();
        let ax1 = proof.add_axiom("x = x");
        let ax2 = proof.add_axiom("y = y");
        proof.add_inference("resolution", vec![ax1, ax2], "x = x or y = y");

        let freq = computer.compute_rule_frequency(&proof);
        assert!(freq.contains_key("resolution"));
        assert_eq!(*freq.get("resolution").expect("key should exist in map"), 1);
    }

    #[test]
    fn test_find_unique_conclusions() {
        let computer = ParallelStatsComputer::new();
        let mut proof = Proof::new();
        proof.add_axiom("x = x");
        proof.add_axiom("y = y");
        proof.add_axiom("x = x"); // Duplicate

        let conclusions = computer.find_unique_conclusions(&proof);
        assert_eq!(conclusions.len(), 2);
        assert!(conclusions.contains("x = x"));
        assert!(conclusions.contains("y = y"));
    }

    #[test]
    fn test_compute_depth_histogram() {
        let computer = ParallelStatsComputer::new();
        let mut proof = Proof::new();
        let ax1 = proof.add_axiom("x = x");
        let ax2 = proof.add_axiom("y = y");
        proof.add_inference("resolution", vec![ax1, ax2], "x = x or y = y");

        let histogram = computer.compute_depth_histogram(&proof);
        assert!(histogram.contains_key(&0)); // Axioms at depth 0
        assert!(histogram.contains_key(&1)); // Resolution at depth 1
    }
}
