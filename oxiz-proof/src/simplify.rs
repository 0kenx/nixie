//! Proof simplification through logical rewriting.
//!
//! This module provides simplification of proof steps by applying logical
//! rewrite rules, combining redundant inferences, and normalizing conclusions.
//! Unlike compression (which removes unreachable nodes), simplification
//! transforms proof steps to equivalent but simpler forms.

use crate::metadata::Strategy;
use crate::proof::{Proof, ProofNodeId, ProofStep};
use rustc_hash::FxHashMap;

/// Configuration for proof simplification.
#[derive(Debug, Clone)]
pub struct SimplificationConfig {
    /// Apply De Morgan's laws to normalize negations
    pub apply_demorgan: bool,
    /// Simplify double negations (¬¬p → p)
    pub simplify_double_negation: bool,
    /// Remove identity operations (p ∧ true → p)
    pub remove_identities: bool,
    /// Combine consecutive inferences when possible
    pub combine_inferences: bool,
    /// Simplify tautologies (p ∨ ¬p → true)
    pub simplify_tautologies: bool,
    /// Maximum number of simplification passes
    pub max_passes: usize,
}

impl Default for SimplificationConfig {
    fn default() -> Self {
        Self {
            apply_demorgan: true,
            simplify_double_negation: true,
            remove_identities: true,
            combine_inferences: true,
            simplify_tautologies: true,
            max_passes: 5,
        }
    }
}

impl SimplificationConfig {
    /// Create a new configuration with all simplifications enabled.
    pub fn new() -> Self {
        Self::default()
    }

    /// Disable De Morgan's law simplification.
    pub fn without_demorgan(mut self) -> Self {
        self.apply_demorgan = false;
        self
    }

    /// Set maximum number of passes.
    pub fn with_max_passes(mut self, passes: usize) -> Self {
        self.max_passes = passes;
        self
    }
}

/// Statistics about simplification operations.
#[derive(Debug, Clone, Default)]
pub struct SimplificationStats {
    /// Number of simplification passes performed
    pub passes: usize,
    /// Number of double negations simplified
    pub double_negations: usize,
    /// Number of De Morgan transformations applied
    pub demorgan_applications: usize,
    /// Number of identity operations removed
    pub identities_removed: usize,
    /// Number of inferences combined
    pub inferences_combined: usize,
    /// Number of tautologies simplified
    pub tautologies_simplified: usize,
    /// Total nodes before simplification
    pub nodes_before: usize,
    /// Total nodes after simplification
    pub nodes_after: usize,
}

impl SimplificationStats {
    /// Calculate total simplifications applied.
    pub fn total_simplifications(&self) -> usize {
        self.double_negations
            + self.demorgan_applications
            + self.identities_removed
            + self.inferences_combined
            + self.tautologies_simplified
    }

    /// Calculate reduction ratio (0.0 = no reduction, 1.0 = complete reduction).
    pub fn reduction_ratio(&self) -> f64 {
        if self.nodes_before == 0 {
            0.0
        } else {
            1.0 - (self.nodes_after as f64 / self.nodes_before as f64)
        }
    }
}

/// Proof simplifier that applies logical rewrite rules.
pub struct ProofSimplifier {
    config: SimplificationConfig,
}

impl ProofSimplifier {
    /// Create a new simplifier with default configuration.
    pub fn new() -> Self {
        Self {
            config: SimplificationConfig::default(),
        }
    }

    /// Create a simplifier with custom configuration.
    pub fn with_config(config: SimplificationConfig) -> Self {
        Self { config }
    }

    /// Simplify a proof in-place, returning statistics.
    pub fn simplify(&self, proof: &mut Proof) -> SimplificationStats {
        let mut stats = SimplificationStats {
            nodes_before: proof.node_count(),
            ..Default::default()
        };

        for pass in 0..self.config.max_passes {
            let mut changed = false;

            if self.config.simplify_double_negation {
                let count = self.simplify_double_negations(proof);
                stats.double_negations += count;
                changed |= count > 0;
            }

            if self.config.apply_demorgan {
                let count = self.apply_demorgan_laws(proof);
                stats.demorgan_applications += count;
                changed |= count > 0;
            }

            if self.config.remove_identities {
                let count = self.remove_identity_operations(proof);
                stats.identities_removed += count;
                changed |= count > 0;
            }

            if self.config.simplify_tautologies {
                let count = self.simplify_tautology_steps(proof);
                stats.tautologies_simplified += count;
                changed |= count > 0;
            }

            if self.config.combine_inferences {
                let count = self.combine_inference_chains(proof);
                stats.inferences_combined += count;
                changed |= count > 0;
            }

            stats.passes = pass + 1;

            if !changed {
                break;
            }
        }

        stats.nodes_after = proof.node_count();
        stats
    }

    /// Record that `id`'s conclusion has just been rewritten by
    /// simplification, from `original_conclusion` to whatever it now reads.
    ///
    /// [`Proof`] intentionally exposes no way to also update an
    /// `Inference` node's `rule`/`premises` when its conclusion changes --
    /// only [`Proof::update_conclusion`] is public. Rewriting *only* the
    /// conclusion text leaves the node's stored `rule`/`premises` fields
    /// describing a derivation of the *original* conclusion, not the
    /// rewritten one: a strict proof checker that tried to literally
    /// replay `rule` against `premises` and expect the *current*
    /// conclusion would (correctly) reject the step as unsound, since
    /// that's not actually what the rule derives any more.
    ///
    /// Rather than leave that mismatch silently undiscoverable, every
    /// rewrite is tagged with [`Strategy::Simplify`] and the *first*
    /// (pre-simplification) conclusion this node ever had is preserved as
    /// a metadata attribute. Any consumer -- a proof checker, a human
    /// auditor, or a future `Proof` API enhancement that can rewire
    /// premises properly -- can then tell that `rule`/`premises` on this
    /// node certify the recorded original conclusion, not its current
    /// text, and treat it as "simplified, not directly re-checkable"
    /// rather than silently trusting a stale derivation record.
    fn record_simplification(&self, proof: &mut Proof, id: ProofNodeId, original_conclusion: &str) {
        let metadata = proof.get_or_create_metadata(id);
        metadata.add_strategy(Strategy::Simplify);
        if metadata.get_attribute("pre_simplify_conclusion").is_none() {
            metadata.set_attribute("pre_simplify_conclusion", original_conclusion);
        }
    }

    /// Simplify double negations (¬¬p → p).
    fn simplify_double_negations(&self, proof: &mut Proof) -> usize {
        let mut count = 0;
        let node_ids: Vec<_> = proof.nodes().iter().map(|node| node.id).collect();

        for id in node_ids {
            if let Some(node) = proof.get_node(id) {
                let conclusion = node.conclusion().to_string();
                if let Some(simplified) = self.simplify_conclusion_double_neg(&conclusion)
                    && simplified != conclusion
                    && proof.update_conclusion(id, simplified)
                {
                    self.record_simplification(proof, id, &conclusion);
                    count += 1;
                }
            }
        }

        count
    }

    /// Apply De Morgan's laws (¬(p ∧ q) → ¬p ∨ ¬q).
    fn apply_demorgan_laws(&self, proof: &mut Proof) -> usize {
        let mut count = 0;
        let node_ids: Vec<_> = proof.nodes().iter().map(|node| node.id).collect();

        for id in node_ids {
            if let Some(node) = proof.get_node(id) {
                let conclusion = node.conclusion().to_string();
                if let Some(simplified) = self.apply_demorgan_to_conclusion(&conclusion)
                    && simplified != conclusion
                    && proof.update_conclusion(id, simplified)
                {
                    self.record_simplification(proof, id, &conclusion);
                    count += 1;
                }
            }
        }

        count
    }

    /// Remove identity operations (p ∧ true → p, p ∨ false → p).
    fn remove_identity_operations(&self, proof: &mut Proof) -> usize {
        let mut count = 0;
        let node_ids: Vec<_> = proof.nodes().iter().map(|node| node.id).collect();

        for id in node_ids {
            if let Some(node) = proof.get_node(id) {
                let conclusion = node.conclusion().to_string();
                if let Some(simplified) = self.remove_identities_from_conclusion(&conclusion)
                    && simplified != conclusion
                    && proof.update_conclusion(id, simplified)
                {
                    self.record_simplification(proof, id, &conclusion);
                    count += 1;
                }
            }
        }

        count
    }

    /// Simplify tautological steps (p ∨ ¬p → true).
    fn simplify_tautology_steps(&self, proof: &mut Proof) -> usize {
        let mut count = 0;
        let node_ids: Vec<_> = proof.nodes().iter().map(|node| node.id).collect();

        for id in node_ids {
            if let Some(node) = proof.get_node(id) {
                let conclusion = node.conclusion().to_string();
                if self.is_tautology(&conclusion) && proof.update_conclusion(id, "true") {
                    self.record_simplification(proof, id, &conclusion);
                    count += 1;
                }
            }
        }

        count
    }

    /// Combine consecutive inference chains when possible.
    ///
    /// Folds a linear two-step derivation `A -> B` into a single synthetic
    /// node whenever it is safe to do so: `B` is an `Inference` step whose
    /// *only* premise is `A`, `A` is itself an `Inference` step (not an
    /// axiom, which is a foundational fact and never folded away), and `A`
    /// has exactly one dependent in the whole proof (`B` itself, so no
    /// other node relies on `A`'s conclusion existing as its own step).
    ///
    /// The combined node goes directly from `A`'s original premises to
    /// `B`'s (unchanged) conclusion. No provenance is discarded: the new
    /// node's rule is named `combine(A_rule;B_rule)`, its args are `A`'s
    /// args followed by `B`'s args, and `A`'s own (intermediate)
    /// conclusion plus original rule name are preserved as metadata
    /// attributes (`combined_intermediate_conclusion`,
    /// `combined_intermediate_rule`) so a checker or auditor can still
    /// replay the two original steps.
    ///
    /// Because folding removes a node, [`Proof`] must renumber every
    /// node's [`ProofNodeId`] to keep IDs contiguous with node storage --
    /// the same tradeoff [`crate::compress::ProofCompressor`] already
    /// makes elsewhere in this crate. Any `ProofNodeId` a caller captured
    /// before calling [`Self::simplify`] must be treated as invalidated
    /// once this pass reports `inferences_combined > 0`.
    fn combine_inference_chains(&self, proof: &mut Proof) -> usize {
        // How many other nodes reference each node as a premise.
        let mut dependent_count: FxHashMap<ProofNodeId, usize> = FxHashMap::default();
        for node in proof.nodes() {
            if let ProofStep::Inference { premises, .. } = &node.step {
                for &premise_id in premises.iter() {
                    *dependent_count.entry(premise_id).or_insert(0) += 1;
                }
            }
        }

        // Map each foldable premise `a_id` to the sole consumer `b_id`
        // that will absorb it.
        let mut raw_fold: FxHashMap<ProofNodeId, ProofNodeId> = FxHashMap::default();
        for node in proof.nodes() {
            let ProofStep::Inference { premises, .. } = &node.step else {
                continue;
            };
            let [a_id] = premises.as_slice() else {
                continue;
            };
            let a_is_foldable = proof
                .get_node(*a_id)
                .map(|a_node| matches!(a_node.step, ProofStep::Inference { .. }))
                .unwrap_or(false)
                && dependent_count.get(a_id).copied().unwrap_or(0) == 1;
            if a_is_foldable {
                raw_fold.insert(*a_id, node.id);
            }
        }

        // A chain of three or more nodes (X -> A -> B) can produce two
        // candidate pairs in the same pass: (X, A) and (A, B). Combining
        // both in one rebuild would drop X entirely -- A would be skipped
        // as "folded into B" before X ever gets spliced into it, orphaning
        // X's premise link. Instead, only ever fold a node whose target is
        // *not itself* about to be folded away this pass; the remaining
        // hop (A, B) is then a fresh single-hop candidate on the next call
        // to `simplify`'s pass loop, once A has already absorbed X.
        let folded_away_targets: std::collections::HashSet<ProofNodeId> =
            raw_fold.values().copied().collect();
        let fold_target: FxHashMap<ProofNodeId, ProofNodeId> = raw_fold
            .into_iter()
            .filter(|(a_id, _b_id)| !folded_away_targets.contains(a_id))
            .collect();

        if fold_target.is_empty() {
            return 0;
        }

        // Rebuild the proof, splicing out folded nodes and rewiring
        // premises, mirroring the ID-remap pattern used by
        // `crate::compress::ProofCompressor::inline_trivial_steps`.
        let mut new_proof = Proof::new();
        let mut id_map: FxHashMap<ProofNodeId, ProofNodeId> = FxHashMap::default();
        let mut combined_targets: Vec<(ProofNodeId, String, String)> = Vec::new();

        for node in proof.nodes() {
            if fold_target.contains_key(&node.id) {
                // Folded away: its content is absorbed into its sole
                // consumer below instead of being emitted on its own.
                continue;
            }

            let folded_premise = match &node.step {
                ProofStep::Inference { premises, .. } => match premises.as_slice() {
                    [a_id] if fold_target.get(a_id) == Some(&node.id) => Some(*a_id),
                    _ => None,
                },
                ProofStep::Axiom { .. } => None,
            };

            let (new_id, combined_from) = match folded_premise {
                Some(a_id) => {
                    match Self::emit_combined_node(proof, &node.step, a_id, &id_map, &mut new_proof)
                    {
                        Some(id) => (id, Some(a_id)),
                        None => (
                            Self::emit_plain_node(&node.step, &id_map, &mut new_proof),
                            None,
                        ),
                    }
                }
                None => (
                    Self::emit_plain_node(&node.step, &id_map, &mut new_proof),
                    None,
                ),
            };

            id_map.insert(node.id, new_id);

            if let Some(a_id) = combined_from
                && let Some(a_node) = proof.get_node(a_id)
                && let ProofStep::Inference { rule: a_rule, .. } = &a_node.step
            {
                combined_targets.push((new_id, a_node.conclusion().to_string(), a_rule.clone()));
            }

            if let Some(metadata) = proof.get_metadata(node.id) {
                new_proof.set_metadata(new_id, metadata.clone());
            }
        }

        let combined_count = combined_targets.len();
        for (new_id, intermediate_conclusion, intermediate_rule) in combined_targets {
            let metadata = new_proof.get_or_create_metadata(new_id);
            metadata.add_strategy(Strategy::Simplify);
            metadata.set_attribute("combined_intermediate_conclusion", intermediate_conclusion);
            metadata.set_attribute("combined_intermediate_rule", intermediate_rule);
        }

        *proof = new_proof;
        combined_count
    }

    /// Emit a node that absorbs a folded-away single premise `a_id` into
    /// `node_step` (which must be an `ProofStep::Inference` whose sole
    /// premise is `a_id`). Returns `None` (leaving `new_proof` untouched)
    /// if `a_id` does not resolve to an `Inference` node in `proof`, in
    /// which case the caller falls back to a plain (non-combined) copy.
    fn emit_combined_node(
        proof: &Proof,
        node_step: &ProofStep,
        a_id: ProofNodeId,
        id_map: &FxHashMap<ProofNodeId, ProofNodeId>,
        new_proof: &mut Proof,
    ) -> Option<ProofNodeId> {
        let ProofStep::Inference {
            rule: b_rule,
            conclusion: b_conclusion,
            args: b_args,
            ..
        } = node_step
        else {
            return None;
        };

        let a_node = proof.get_node(a_id)?;
        let ProofStep::Inference {
            rule: a_rule,
            premises: a_premises,
            args: a_args,
            ..
        } = &a_node.step
        else {
            return None;
        };

        let new_premises: Vec<ProofNodeId> = a_premises
            .iter()
            .filter_map(|p| id_map.get(p).copied())
            .collect();
        let combined_rule = format!("combine({};{})", a_rule, b_rule);
        let mut combined_args: Vec<String> = a_args.to_vec();
        combined_args.extend(b_args.iter().cloned());

        Some(new_proof.add_inference_with_args(
            combined_rule,
            new_premises,
            combined_args,
            b_conclusion.clone(),
        ))
    }

    /// Copy a node verbatim into `new_proof`, remapping its premises
    /// through `id_map`.
    fn emit_plain_node(
        node_step: &ProofStep,
        id_map: &FxHashMap<ProofNodeId, ProofNodeId>,
        new_proof: &mut Proof,
    ) -> ProofNodeId {
        match node_step {
            ProofStep::Axiom { conclusion } => new_proof.add_axiom(conclusion.clone()),
            ProofStep::Inference {
                rule,
                premises,
                conclusion,
                args,
            } => {
                let new_premises: Vec<ProofNodeId> = premises
                    .iter()
                    .filter_map(|p| id_map.get(p).copied())
                    .collect();
                new_proof.add_inference_with_args(
                    rule.clone(),
                    new_premises,
                    args.to_vec(),
                    conclusion.clone(),
                )
            }
        }
    }

    // Helper methods for conclusion simplification

    fn simplify_conclusion_double_neg(&self, conclusion: &str) -> Option<String> {
        let s = conclusion.trim();

        // Match patterns like: (not (not p))
        if s.starts_with("(not (not ") && s.ends_with("))") {
            let inner = &s[10..s.len() - 2];
            return Some(inner.trim().to_string());
        }

        // Match patterns like: ¬¬p (UTF-8 safe)
        if s.starts_with("¬") {
            let chars: Vec<char> = s.chars().collect();
            if chars.len() >= 3 && chars[0] == '¬' && chars[1] == '¬' {
                let result: String = chars[2..].iter().collect();
                return Some(result.trim().to_string());
            }
        }

        None
    }

    fn apply_demorgan_to_conclusion(&self, conclusion: &str) -> Option<String> {
        let s = conclusion.trim();

        // Match: (not (and p q)) → (or (not p) (not q))
        if s.starts_with("(not (and ") && s.ends_with("))") {
            let inner_content = &s[10..s.len() - 2];
            if let Some(inner) = self.extract_binary_args(&format!("{})", inner_content)) {
                return Some(format!("(or (not {}) (not {}))", inner.0, inner.1));
            }
        }

        // Match: (not (or p q)) → (and (not p) (not q))
        if s.starts_with("(not (or ") && s.ends_with("))") {
            let inner_content = &s[9..s.len() - 2];
            if let Some(inner) = self.extract_binary_args(&format!("{})", inner_content)) {
                return Some(format!("(and (not {}) (not {}))", inner.0, inner.1));
            }
        }

        None
    }

    fn remove_identities_from_conclusion(&self, conclusion: &str) -> Option<String> {
        let s = conclusion.trim();

        // Match: (and p true) → p
        if (s.contains(" true)") || s.contains(" true ))"))
            && s.starts_with("(and ")
            && let Some((left, right)) = self.extract_binary_args(&s[5..])
        {
            if right.trim() == "true" {
                return Some(left.to_string());
            }
            if left.trim() == "true" {
                return Some(right.to_string());
            }
        }

        // Match: (or p false) → p
        if (s.contains(" false)") || s.contains(" false ))"))
            && s.starts_with("(or ")
            && let Some((left, right)) = self.extract_binary_args(&s[4..])
        {
            if right.trim() == "false" {
                return Some(left.to_string());
            }
            if left.trim() == "false" {
                return Some(right.to_string());
            }
        }

        None
    }

    fn is_tautology(&self, conclusion: &str) -> bool {
        let s = conclusion.trim();

        // Check for patterns like: (or p (not p))
        if let Some(stripped) = s.strip_prefix("(or ")
            && let Some((left, right)) = self.extract_binary_args(stripped)
        {
            // Check if right is (not left) or left is (not right)
            if right.trim() == format!("(not {})", left.trim()) {
                return true;
            }
            if left.trim() == format!("(not {})", right.trim()) {
                return true;
            }
        }

        false
    }

    fn extract_binary_args(&self, s: &str) -> Option<(String, String)> {
        // Simple parser for binary operations
        // This is a basic implementation; a full s-expression parser would be better
        let trimmed = s.trim();
        if !trimmed.ends_with(')') {
            return None;
        }

        let content = &trimmed[..trimmed.len() - 1];
        let mut depth = 0;
        let mut split_pos = None;

        for (i, ch) in content.chars().enumerate() {
            match ch {
                '(' => depth += 1,
                ')' => depth -= 1,
                ' ' if depth == 0 => {
                    split_pos = Some(i);
                    break;
                }
                _ => {}
            }
        }

        if let Some(pos) = split_pos {
            let left = content[..pos].trim().to_string();
            let right = content[pos + 1..].trim().to_string();
            Some((left, right))
        } else {
            None
        }
    }
}

impl Default for ProofSimplifier {
    fn default() -> Self {
        Self::new()
    }
}

/// Simplify a proof using default configuration.
pub fn simplify_proof(proof: &mut Proof) -> SimplificationStats {
    ProofSimplifier::new().simplify(proof)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::proof::ProofNodeId;

    #[test]
    fn test_simplification_config_default() {
        let config = SimplificationConfig::default();
        assert!(config.apply_demorgan);
        assert!(config.simplify_double_negation);
        assert_eq!(config.max_passes, 5);
    }

    #[test]
    fn test_simplification_config_builder() {
        let config = SimplificationConfig::new()
            .without_demorgan()
            .with_max_passes(3);
        assert!(!config.apply_demorgan);
        assert_eq!(config.max_passes, 3);
    }

    #[test]
    fn test_simplification_stats_total() {
        let stats = SimplificationStats {
            double_negations: 2,
            demorgan_applications: 3,
            identities_removed: 1,
            ..Default::default()
        };
        assert_eq!(stats.total_simplifications(), 6);
    }

    #[test]
    fn test_simplification_stats_reduction_ratio() {
        let stats = SimplificationStats {
            nodes_before: 100,
            nodes_after: 80,
            ..Default::default()
        };
        assert!((stats.reduction_ratio() - 0.2).abs() < 1e-6);
    }

    #[test]
    fn test_simplify_double_negation_sexp() {
        let simplifier = ProofSimplifier::new();
        let conclusion = "(not (not p))";
        let result = simplifier.simplify_conclusion_double_neg(conclusion);
        assert_eq!(result, Some("p".to_string()));
    }

    #[test]
    fn test_simplify_double_negation_unicode() {
        let simplifier = ProofSimplifier::new();
        let conclusion = "¬¬p";
        let result = simplifier.simplify_conclusion_double_neg(conclusion);
        assert_eq!(result, Some("p".to_string()));
    }

    #[test]
    fn test_apply_demorgan_not_and() {
        let simplifier = ProofSimplifier::new();
        let conclusion = "(not (and p q))";
        let result = simplifier.apply_demorgan_to_conclusion(conclusion);
        assert_eq!(result, Some("(or (not p) (not q))".to_string()));
    }

    #[test]
    fn test_apply_demorgan_not_or() {
        let simplifier = ProofSimplifier::new();
        let conclusion = "(not (or p q))";
        let result = simplifier.apply_demorgan_to_conclusion(conclusion);
        assert_eq!(result, Some("(and (not p) (not q))".to_string()));
    }

    #[test]
    fn test_remove_identity_and_true() {
        let simplifier = ProofSimplifier::new();
        let conclusion = "(and p true)";
        let result = simplifier.remove_identities_from_conclusion(conclusion);
        assert_eq!(result, Some("p".to_string()));
    }

    #[test]
    fn test_remove_identity_or_false() {
        let simplifier = ProofSimplifier::new();
        let conclusion = "(or p false)";
        let result = simplifier.remove_identities_from_conclusion(conclusion);
        assert_eq!(result, Some("p".to_string()));
    }

    #[test]
    fn test_is_tautology_or_not() {
        let simplifier = ProofSimplifier::new();
        assert!(simplifier.is_tautology("(or p (not p))"));
        assert!(simplifier.is_tautology("(or (not p) p)"));
        assert!(!simplifier.is_tautology("(or p q)"));
    }

    #[test]
    fn test_extract_binary_args_simple() {
        let simplifier = ProofSimplifier::new();
        let result = simplifier.extract_binary_args("p q)");
        assert_eq!(result, Some(("p".to_string(), "q".to_string())));
    }

    #[test]
    fn test_extract_binary_args_nested() {
        let simplifier = ProofSimplifier::new();
        let result = simplifier.extract_binary_args("(and a b) q)");
        assert_eq!(result, Some(("(and a b)".to_string(), "q".to_string())));
    }

    #[test]
    fn test_simplify_proof_empty() {
        let mut proof = Proof::new();
        let stats = simplify_proof(&mut proof);
        assert_eq!(stats.total_simplifications(), 0);
        assert_eq!(stats.nodes_before, 0);
        assert_eq!(stats.nodes_after, 0);
    }

    #[test]
    fn test_simplify_proof_double_negation() {
        let mut proof = Proof::new();
        proof.add_axiom("(not (not p))".to_string());

        let stats = simplify_proof(&mut proof);
        assert!(stats.double_negations > 0);

        // Check that conclusion was simplified
        let node = proof
            .get_node(ProofNodeId(0))
            .expect("test operation should succeed");
        assert_eq!(node.conclusion(), "p");
    }

    #[test]
    fn test_simplify_proof_identity() {
        let mut proof = Proof::new();
        proof.add_axiom("(and p true)".to_string());

        let stats = simplify_proof(&mut proof);
        assert!(stats.identities_removed > 0);

        let node = proof
            .get_node(ProofNodeId(0))
            .expect("test operation should succeed");
        assert_eq!(node.conclusion(), "p");
    }

    #[test]
    fn test_simplify_proof_tautology() {
        let mut proof = Proof::new();
        proof.add_axiom("(or p (not p))".to_string());

        let stats = simplify_proof(&mut proof);
        assert!(stats.tautologies_simplified > 0);

        let node = proof
            .get_node(ProofNodeId(0))
            .expect("test operation should succeed");
        assert_eq!(node.conclusion(), "true");
    }

    #[test]
    fn test_simplify_proof_multiple_passes() {
        let mut proof = Proof::new();
        // Double negation of identity: (not (not (and p true)))
        // Should simplify in multiple passes: → (and p true) → p
        proof.add_axiom("(not (not (and p true)))".to_string());

        let config = SimplificationConfig::new().with_max_passes(3);
        let simplifier = ProofSimplifier::with_config(config);
        let stats = simplifier.simplify(&mut proof);

        assert!(stats.passes >= 2);
        // Note: Current implementation may not fully simplify this in all cases
        // This test validates that multiple passes occur
    }

    #[test]
    fn test_simplifier_with_custom_config() {
        let config = SimplificationConfig::new().without_demorgan();
        let simplifier = ProofSimplifier::with_config(config);

        let mut proof = Proof::new();
        proof.add_axiom("(not (and p q))".to_string());

        let stats = simplifier.simplify(&mut proof);
        // De Morgan should not be applied
        assert_eq!(stats.demorgan_applications, 0);
    }

    // ======== todo-1147: combine_inference_chains regression tests ========

    #[test]
    fn test_combine_inference_chains_basic() {
        let simplifier = ProofSimplifier::new();
        let mut proof = Proof::new();
        let ax = proof.add_axiom("p");
        let a = proof.add_inference("rule_a", vec![ax], "q");
        proof.add_inference("rule_b", vec![a], "r");

        assert_eq!(proof.node_count(), 3);

        let combined = simplifier.combine_inference_chains(&mut proof);
        assert_eq!(combined, 1);
        assert_eq!(proof.node_count(), 2);

        let combined_node = proof
            .nodes()
            .iter()
            .find(|n| n.conclusion() == "r")
            .expect("combined node with conclusion r should exist");

        match &combined_node.step {
            ProofStep::Inference {
                rule,
                premises,
                conclusion,
                ..
            } => {
                assert_eq!(rule, "combine(rule_a;rule_b)");
                assert_eq!(conclusion, "r");
                assert_eq!(premises.len(), 1);
                let premise_node = proof
                    .get_node(premises[0])
                    .expect("premise node should exist");
                assert_eq!(premise_node.conclusion(), "p");
            }
            ProofStep::Axiom { .. } => panic!("expected combined node to be an Inference"),
        }

        // Provenance of the folded intermediate step must be preserved.
        let metadata = proof
            .get_metadata(combined_node.id)
            .expect("combined node should carry metadata");
        assert_eq!(
            metadata.get_attribute("combined_intermediate_conclusion"),
            Some("q")
        );
        assert_eq!(
            metadata.get_attribute("combined_intermediate_rule"),
            Some("rule_a")
        );
    }

    #[test]
    fn test_combine_inference_chains_skips_shared_premise() {
        // A node used by two different consumers must never be folded
        // away: doing so would silently discard whichever consumer isn't
        // chosen, or duplicate the derivation.
        let simplifier = ProofSimplifier::new();
        let mut proof = Proof::new();
        let ax = proof.add_axiom("p");
        let a = proof.add_inference("rule_a", vec![ax], "q");
        proof.add_inference("rule_b1", vec![a], "r1");
        proof.add_inference("rule_b2", vec![a], "r2");

        let before = proof.node_count();
        let combined = simplifier.combine_inference_chains(&mut proof);
        assert_eq!(combined, 0);
        assert_eq!(proof.node_count(), before);
    }

    #[test]
    fn test_combine_inference_chains_no_candidates() {
        let simplifier = ProofSimplifier::new();
        let mut proof = Proof::new();
        let ax1 = proof.add_axiom("p");
        let ax2 = proof.add_axiom("q");
        // Two premises: never eligible to absorb a folded predecessor.
        proof.add_inference("and_intro", vec![ax1, ax2], "p and q");

        let before = proof.node_count();
        let combined = simplifier.combine_inference_chains(&mut proof);
        assert_eq!(combined, 0);
        assert_eq!(proof.node_count(), before);
    }

    #[test]
    fn test_combine_inference_chains_multi_hop_needs_multiple_passes() {
        // PF-related soundness check: a three-hop chain must never lose
        // its root premise across the rebuild, even though only one
        // adjacent pair can safely combine per pass.
        let simplifier = ProofSimplifier::new();
        let mut proof = Proof::new();
        let ax = proof.add_axiom("p0");
        let n1 = proof.add_inference("r1", vec![ax], "p1");
        let n2 = proof.add_inference("r2", vec![n1], "p2");
        proof.add_inference("r3", vec![n2], "p3");

        assert_eq!(proof.node_count(), 4);

        let first = simplifier.combine_inference_chains(&mut proof);
        assert_eq!(first, 1);
        assert_eq!(proof.node_count(), 3);

        let second = simplifier.combine_inference_chains(&mut proof);
        assert_eq!(second, 1);
        assert_eq!(proof.node_count(), 2);

        let final_node = proof
            .nodes()
            .iter()
            .find(|n| n.conclusion() == "p3")
            .expect("final combined node should exist");
        if let ProofStep::Inference { premises, .. } = &final_node.step {
            assert_eq!(premises.len(), 1);
            let root_premise = proof
                .get_node(premises[0])
                .expect("root premise should still exist");
            assert_eq!(root_premise.conclusion(), "p0");
        } else {
            panic!("expected the final surviving node to be an Inference");
        }
    }

    #[test]
    fn test_simplify_proof_combines_inference_chain() {
        // End-to-end: `combine_inferences` (on by default) must no longer
        // be an inert no-op when driven through the public `simplify_proof`.
        let mut proof = Proof::new();
        let ax = proof.add_axiom("base");
        let mid = proof.add_inference("step1", vec![ax], "mid");
        proof.add_inference("step2", vec![mid], "final");

        let stats = simplify_proof(&mut proof);
        assert!(stats.inferences_combined > 0);
        assert_eq!(proof.node_count(), 2);

        let final_node = proof
            .nodes()
            .iter()
            .find(|n| n.conclusion() == "final")
            .expect("final combined node should exist");
        assert!(
            matches!(&final_node.step, ProofStep::Inference { rule, .. } if rule.starts_with("combine("))
        );
    }
}
