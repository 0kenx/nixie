//! Proof builder for ergonomic proof construction.
//!
//! This module provides a fluent API for building proofs step by step:
//! [`ProofBuilder`] for the crate's generic, string-conclusion [`Proof`]
//! type, and [`TheoryProofBuilder`] for the more structured
//! [`crate::theory::TheoryProof`] used by theory solvers ([`crate::theory`]
//! has the full set of theory-specific step constructors this delegates to
//! -- `refl`/`trans` are only the two most common ones exposed directly
//! here; use [`TheoryProofBuilder::step`] for any other [`TheoryRule`]).
//!
//! # What building does *not* guarantee
//!
//! Neither builder validates the proof steps it records: `ProofBuilder`'s
//! `Proof` has no semantic checker in this crate at all (only structural
//! queries -- premises exist, `is_ancestor`, and so on), and
//! `TheoryProofBuilder` delegates straight to `TheoryProof`'s own
//! constructors, which likewise perform no validation (see
//! `TheoryProof::trans`'s doc comment). A built `TheoryProof` should be
//! passed to [`crate::checker::ProofChecker::check_theory_proof`] --
//! typically with [`crate::checker::CheckerConfig::verify_conclusions`] set,
//! to actually verify the rules it knows how to check -- before being
//! trusted. See the `# Examples` below for exactly that round trip,
//! including the negative case (a checker that accepts every proof would
//! also pass the positive case alone).
//!
//! Reusing a name already passed to a previous `axiom`/`inference`/`step`/
//! etc. call silently rebinds it (the earlier node is still in the proof,
//! just no longer reachable via [`ProofBuilder::get_named`] /
//! [`TheoryProofBuilder::get_named`]) -- this is a plain last-write-wins
//! name registry, not a validated one.
//!
//! # Examples
//!
//! ```
//! use nixie_proof::{CheckResult, CheckerConfig, ProofChecker, TheoryProofBuilder, TheoryRule};
//!
//! // Build (x = y), (y = z) |- (x = z) via transitivity.
//! let mut builder = TheoryProofBuilder::new();
//! let xy = builder.axiom(TheoryRule::Custom("assert".into()), "(= x y)", None);
//! let yz = builder.axiom(TheoryRule::Custom("assert".into()), "(= y z)", None);
//! builder.trans(xy, yz, "x", "z", None);
//! let proof = builder.build();
//!
//! // Building it is not evidence it is correct -- checking it is.
//! let mut checker = ProofChecker::with_config(CheckerConfig {
//!     verify_conclusions: true,
//!     ..Default::default()
//! });
//! assert!(matches!(checker.check_theory_proof(&proof), CheckResult::Valid));
//! ```

use crate::proof::{Proof, ProofNodeId};
use crate::theory::{ProofTerm, TheoryProof, TheoryRule, TheoryStepId};
use std::collections::HashMap;

/// Builder for constructing proofs with a fluent API.
#[derive(Debug)]
pub struct ProofBuilder {
    /// The proof being constructed.
    proof: Proof,
    /// Named nodes for easier reference.
    named_nodes: HashMap<String, ProofNodeId>,
}

impl ProofBuilder {
    /// Create a new proof builder starting with an axiom.
    #[must_use]
    pub fn new(conclusion: impl Into<String>) -> Self {
        let mut proof = Proof::new();
        let root = proof.add_axiom(conclusion);
        let mut named_nodes = HashMap::new();
        named_nodes.insert("root".to_string(), root);
        Self { proof, named_nodes }
    }

    /// Create a new proof builder starting with an inference.
    #[must_use]
    pub fn new_inference(
        rule: impl Into<String>,
        premises: Vec<ProofNodeId>,
        conclusion: impl Into<String>,
    ) -> Self {
        let mut proof = Proof::new();
        let root = proof.add_inference(rule, premises, conclusion);
        let mut named_nodes = HashMap::new();
        named_nodes.insert("root".to_string(), root);
        Self { proof, named_nodes }
    }

    /// Add an axiom node and optionally name it.
    pub fn axiom(&mut self, conclusion: impl Into<String>, name: Option<String>) -> ProofNodeId {
        let id = self.proof.add_axiom(conclusion);
        if let Some(n) = name {
            self.named_nodes.insert(n, id);
        }
        id
    }

    /// Add an inference node and optionally name it.
    pub fn inference(
        &mut self,
        rule: impl Into<String>,
        premises: Vec<ProofNodeId>,
        conclusion: impl Into<String>,
        name: Option<String>,
    ) -> ProofNodeId {
        let id = self.proof.add_inference(rule, premises, conclusion);
        if let Some(n) = name {
            self.named_nodes.insert(n, id);
        }
        id
    }

    /// Get a named node.
    #[must_use]
    pub fn get_named(&self, name: &str) -> Option<ProofNodeId> {
        self.named_nodes.get(name).copied()
    }

    /// Set the root of the proof.
    pub fn set_root(&mut self, root: ProofNodeId) {
        self.named_nodes.insert("root".to_string(), root);
    }

    /// Build the final proof.
    #[must_use]
    pub fn build(self) -> Proof {
        self.proof
    }

    /// Get a reference to the proof being built.
    #[must_use]
    pub fn proof(&self) -> &Proof {
        &self.proof
    }

    /// Get a mutable reference to the proof being built.
    pub fn proof_mut(&mut self) -> &mut Proof {
        &mut self.proof
    }
}

/// Builder for constructing theory proofs with a fluent API.
#[derive(Debug)]
pub struct TheoryProofBuilder {
    /// The theory proof being constructed.
    proof: TheoryProof,
    /// Named steps for easier reference.
    named_steps: HashMap<String, TheoryStepId>,
}

impl TheoryProofBuilder {
    /// Create a new theory proof builder.
    #[must_use]
    pub fn new() -> Self {
        Self {
            proof: TheoryProof::new(),
            named_steps: HashMap::new(),
        }
    }

    /// Add an axiom and optionally name it.
    pub fn axiom(
        &mut self,
        rule: TheoryRule,
        conclusion: impl Into<ProofTerm>,
        name: Option<String>,
    ) -> TheoryStepId {
        let id = self.proof.add_axiom(rule, conclusion);
        if let Some(n) = name {
            self.named_steps.insert(n, id);
        }
        id
    }

    /// Add a step and optionally name it.
    pub fn step(
        &mut self,
        rule: TheoryRule,
        premises: Vec<TheoryStepId>,
        conclusion: impl Into<ProofTerm>,
        name: Option<String>,
    ) -> TheoryStepId {
        let id = self.proof.add_step(rule, premises, conclusion);
        if let Some(n) = name {
            self.named_steps.insert(n, id);
        }
        id
    }

    /// Add a reflexivity step.
    pub fn refl(&mut self, term: impl Into<ProofTerm>, name: Option<String>) -> TheoryStepId {
        let id = self.proof.refl(term);
        if let Some(n) = name {
            self.named_steps.insert(n, id);
        }
        id
    }

    /// Add a transitivity step.
    pub fn trans(
        &mut self,
        p1: TheoryStepId,
        p2: TheoryStepId,
        t1: impl Into<ProofTerm>,
        t3: impl Into<ProofTerm>,
        name: Option<String>,
    ) -> TheoryStepId {
        let id = self.proof.trans(p1, p2, t1, t3);
        if let Some(n) = name {
            self.named_steps.insert(n, id);
        }
        id
    }

    /// Get a named step.
    #[must_use]
    pub fn get_named(&self, name: &str) -> Option<TheoryStepId> {
        self.named_steps.get(name).copied()
    }

    /// Build the final theory proof.
    #[must_use]
    pub fn build(self) -> TheoryProof {
        self.proof
    }

    /// Get a reference to the proof being built.
    #[must_use]
    pub fn proof(&self) -> &TheoryProof {
        &self.proof
    }

    /// Get a mutable reference to the proof being built.
    pub fn proof_mut(&mut self) -> &mut TheoryProof {
        &mut self.proof
    }
}

impl Default for TheoryProofBuilder {
    fn default() -> Self {
        Self::new()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_proof_builder_basic() {
        let mut builder = ProofBuilder::new("p");
        let root = builder
            .get_named("root")
            .expect("test operation should succeed");
        let p2 = builder.axiom("q", Some("q_axiom".to_string()));
        let p3 = builder.inference("and", vec![root, p2], "(and p q)", None);

        builder.set_root(p3);

        let proof = builder.build();
        assert_eq!(proof.len(), 3);
    }

    #[test]
    fn test_proof_builder_named() {
        let mut builder = ProofBuilder::new("p");
        builder.axiom("q", Some("q".to_string()));
        builder.axiom("r", Some("r".to_string()));

        let q_id = builder
            .get_named("q")
            .expect("test operation should succeed");
        let r_id = builder
            .get_named("r")
            .expect("test operation should succeed");

        assert!(builder.proof.get_node(q_id).is_some());
        assert!(builder.proof.get_node(r_id).is_some());
    }

    #[test]
    fn test_theory_proof_builder() {
        let mut builder = TheoryProofBuilder::new();

        let s1 = builder.axiom(
            TheoryRule::Custom("assert".into()),
            "(= x y)",
            Some("xy_eq".to_string()),
        );
        let s2 = builder.axiom(
            TheoryRule::Custom("assert".into()),
            "(= y z)",
            Some("yz_eq".to_string()),
        );

        builder.trans(s1, s2, "x", "z", Some("xz_eq".to_string()));

        let proof = builder.build();
        assert_eq!(proof.len(), 3);
    }

    #[test]
    fn test_theory_proof_builder_refl() {
        let mut builder = TheoryProofBuilder::new();
        builder.refl("x", Some("x_refl".to_string()));

        assert!(builder.get_named("x_refl").is_some());

        let proof = builder.build();
        assert_eq!(proof.len(), 1);
    }

    /// A proof object that is *built* is only evidence of anything once it
    /// is *checked*: this round-trips a well-formed transitivity chain built
    /// via [`TheoryProofBuilder`] through [`crate::checker::ProofChecker`]
    /// with semantic verification enabled, and confirms the checker actually
    /// accepts it.
    #[test]
    fn test_theory_proof_builder_output_passes_checker_with_valid_chain() {
        let mut builder = TheoryProofBuilder::new();
        let s1 = builder.axiom(TheoryRule::Custom("assert".into()), "(= x y)", None);
        let s2 = builder.axiom(TheoryRule::Custom("assert".into()), "(= y z)", None);
        builder.trans(s1, s2, "x", "z", None);

        let proof = builder.build();

        let mut checker =
            crate::checker::ProofChecker::with_config(crate::checker::CheckerConfig {
                verify_conclusions: true,
                ..Default::default()
            });
        let result = checker.check_theory_proof(&proof);
        assert!(
            matches!(result, crate::checker::CheckResult::Valid),
            "a genuine (x=y),(y=z) |- (x=z) chain must pass semantic verification: {result:?}"
        );
    }

    /// Companion: a *malformed* transitivity chain -- concluding `(= x w)`
    /// from premises that only chain `x` through `z`, never mentioning `w`
    /// at all -- must be *rejected* by the checker. `TheoryProofBuilder`
    /// itself performs no semantic validation (that is deliberately the
    /// checker's job, not the builder's -- see `Solver::Trans`'s doc comment
    /// in `theory.rs`), so this is the test that actually proves the checker
    /// does its job: a checker that accepts everything would also pass the
    /// test above.
    #[test]
    fn test_theory_proof_builder_output_is_rejected_by_checker_with_invalid_chain() {
        let mut builder = TheoryProofBuilder::new();
        let s1 = builder.axiom(TheoryRule::Custom("assert".into()), "(= x y)", None);
        let s2 = builder.axiom(TheoryRule::Custom("assert".into()), "(= y z)", None);
        // Wrong on purpose: the premises chain x -> y -> z, but this claims
        // x = w, a term that appears nowhere above.
        builder.trans(s1, s2, "x", "w", None);

        let proof = builder.build();

        let mut checker =
            crate::checker::ProofChecker::with_config(crate::checker::CheckerConfig {
                verify_conclusions: true,
                ..Default::default()
            });
        let result = checker.check_theory_proof(&proof);
        assert!(
            matches!(result, crate::checker::CheckResult::Invalid { .. }),
            "a transitivity step concluding something the premises do not \
             actually chain to must be rejected: {result:?}"
        );
    }
}
