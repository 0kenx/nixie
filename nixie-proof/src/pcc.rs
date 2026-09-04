//! Proof-Carrying Code (PCC) generation
//!
//! This module provides utilities for generating proof-carrying code,
//! which is code accompanied by a formal proof that it satisfies certain
//! safety or correctness properties.
//!
//! ## Overview
//!
//! Proof-carrying code allows producers of code to provide a proof
//! that the code satisfies specified security or safety properties.
//! Consumers can verify this proof without trusting the producer.
//!
//! ## References
//!
//! - Necula, G.C. (1997). "Proof-Carrying Code"
//! - Appel, A.W. (2001). "Foundational Proof-Carrying Code"

use crate::proof::{Proof, ProofNodeId, ProofStep};
use std::collections::{HashMap, HashSet, VecDeque};
use std::fmt;

/// A safety property that code must satisfy
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum SafetyProperty {
    /// Memory safety (no buffer overflows, use-after-free, etc.)
    MemorySafety,
    /// Type safety (well-typed operations)
    TypeSafety,
    /// Control flow integrity
    ControlFlowIntegrity,
    /// Resource bounds (e.g., bounded memory/time usage)
    ResourceBounds {
        memory: Option<usize>,
        time: Option<usize>,
    },
    /// Custom property with a name and description
    Custom { name: String, description: String },
}

impl fmt::Display for SafetyProperty {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::MemorySafety => write!(f, "MemorySafety"),
            Self::TypeSafety => write!(f, "TypeSafety"),
            Self::ControlFlowIntegrity => write!(f, "ControlFlowIntegrity"),
            Self::ResourceBounds { memory, time } => {
                write!(f, "ResourceBounds(memory=")?;
                if let Some(m) = memory {
                    write!(f, "{}", m)?;
                } else {
                    write!(f, "∞")?;
                }
                write!(f, ", time=")?;
                if let Some(t) = time {
                    write!(f, "{}", t)?;
                } else {
                    write!(f, "∞")?;
                }
                write!(f, ")")
            }
            Self::Custom { name, .. } => write!(f, "Custom({})", name),
        }
    }
}

/// A verification condition (VC) that must be proven
#[derive(Debug, Clone)]
pub struct VerificationCondition {
    /// Unique identifier for this VC
    pub id: String,
    /// The property being verified
    pub property: SafetyProperty,
    /// The condition that must be proven (as a formula)
    pub condition: String,
    /// Program point where this VC applies
    pub location: CodeLocation,
}

/// Location in the code where a verification condition applies
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct CodeLocation {
    /// Function or procedure name
    pub function: String,
    /// Basic block or statement label
    pub label: Option<String>,
    /// Line number (if available)
    pub line: Option<usize>,
}

impl fmt::Display for CodeLocation {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.function)?;
        if let Some(label) = &self.label {
            write!(f, "::{}", label)?;
        }
        if let Some(line) = self.line {
            write!(f, " (line {})", line)?;
        }
        Ok(())
    }
}

/// Verification status of a verification condition's attached proof.
///
/// A proof node being *attached* to a VC (via [`ProofCarryingCode::attach_proof`])
/// is not the same as that proof being *checked*: `Verified` is only ever
/// returned once the attached proof node has actually been walked and its
/// conclusion confirmed to match the VC's condition (see PF-04).
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum VcStatus {
    /// No proof has been attached to this VC.
    NotAttached,
    /// A proof node was attached, but it references a VC id that is not
    /// (yet) registered via [`ProofCarryingCode::add_vc`], so there is no
    /// condition to check it against. This is distinct from `Verified`:
    /// the proof has not been checked at all.
    Attached,
    /// The attached proof was checked: every node it transitively depends
    /// on exists and resolves premises to earlier, already-established
    /// nodes (no dangling/forward references), and its conclusion matches
    /// the VC's condition exactly.
    Verified,
    /// The attached proof was checked and rejected, with the reason.
    Invalid(String),
}

impl fmt::Display for VcStatus {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::NotAttached => write!(f, "UNVERIFIED (no proof attached)"),
            Self::Attached => write!(
                f,
                "UNVERIFIED (attached proof not checked: VC not registered)"
            ),
            Self::Verified => write!(f, "VERIFIED \u{2713}"),
            Self::Invalid(reason) => write!(f, "INVALID \u{2717} ({})", reason),
        }
    }
}

/// Proof-carrying code certificate
///
/// This combines code with proofs of its safety properties.
#[derive(Debug)]
pub struct ProofCarryingCode {
    /// The code (or reference to it)
    code: String,
    /// Safety properties that are certified
    properties: Vec<SafetyProperty>,
    /// Verification conditions
    vcs: Vec<VerificationCondition>,
    /// Proofs for each verification condition
    vc_proofs: HashMap<String, ProofNodeId>,
    /// The underlying proof structure
    proof: Proof,
}

impl ProofCarryingCode {
    /// Create a new proof-carrying code certificate
    #[must_use]
    pub fn new(code: impl Into<String>) -> Self {
        Self {
            code: code.into(),
            properties: Vec::new(),
            vcs: Vec::new(),
            vc_proofs: HashMap::new(),
            proof: Proof::new(),
        }
    }

    /// Add a safety property to be verified
    pub fn add_property(&mut self, property: SafetyProperty) {
        self.properties.push(property);
    }

    /// Add a verification condition
    pub fn add_vc(&mut self, vc: VerificationCondition) {
        self.vcs.push(vc);
    }

    /// Attach a proof for a verification condition.
    ///
    /// This only records *which* proof node claims to establish `vc_id`; it
    /// does not by itself mark the VC verified. Use [`Self::vc_status`],
    /// [`Self::is_complete`], [`Self::verified_count`], or
    /// [`Self::to_certificate`] to see whether the attached proof actually
    /// checks out (see [`VcStatus`]).
    pub fn attach_proof(&mut self, vc_id: &str, proof_node: ProofNodeId) {
        self.vc_proofs.insert(vc_id.to_string(), proof_node);
    }

    /// Compute the current verification status of `vc_id`'s attached proof.
    ///
    /// This is never cached: it re-walks the attached node against the
    /// current state of the underlying proof (and the current VC set) on
    /// every call, so the answer can never go stale after `proof_mut()` or
    /// `add_vc` mutate this certificate.
    #[must_use]
    pub fn vc_status(&self, vc_id: &str) -> VcStatus {
        let Some(&node_id) = self.vc_proofs.get(vc_id) else {
            return VcStatus::NotAttached;
        };
        let Some(vc) = self.vcs.iter().find(|vc| vc.id == vc_id) else {
            return VcStatus::Attached;
        };
        match self.check_vc_proof(vc, node_id) {
            Ok(()) => VcStatus::Verified,
            Err(reason) => VcStatus::Invalid(reason),
        }
    }

    /// Check that `node_id` actually proves `vc`.
    ///
    /// Two things are verified:
    /// 1. Structural soundness: `node_id`, and every node it transitively
    ///    depends on, exists, and every premise reference resolves to an
    ///    already-established (strictly earlier) node -- mirroring the
    ///    corruption checks in
    ///    [`crate::parallel::ParallelProcessor::check_proof_parallel`].
    /// 2. Relevance: the node's conclusion matches `vc.condition` exactly,
    ///    so an unrelated (but otherwise valid) proof cannot be attached to
    ///    a VC and reported as verifying it.
    fn check_vc_proof(
        &self,
        vc: &VerificationCondition,
        node_id: ProofNodeId,
    ) -> Result<(), String> {
        self.check_structural_soundness(node_id)?;

        let node = self
            .proof
            .get_node(node_id)
            .ok_or_else(|| format!("proof node {} does not exist", node_id))?;

        if node.conclusion() != vc.condition {
            return Err(format!(
                "attached proof concludes '{}', but VC '{}' requires '{}'",
                node.conclusion(),
                vc.id,
                vc.condition
            ));
        }

        Ok(())
    }

    /// Walk `node_id` and every node it transitively depends on, confirming
    /// each one exists and that every premise reference resolves to an
    /// already-established (strictly earlier) node. `Proof` allocates node
    /// IDs monotonically, so a premise ID that is missing, equal to, or
    /// greater than the referencing node's own ID can only arise from a
    /// corrupted or hand-crafted proof.
    fn check_structural_soundness(&self, node_id: ProofNodeId) -> Result<(), String> {
        let mut visited = HashSet::new();
        let mut queue = VecDeque::new();
        queue.push_back(node_id);

        while let Some(current) = queue.pop_front() {
            if !visited.insert(current) {
                continue;
            }

            let node = self
                .proof
                .get_node(current)
                .ok_or_else(|| format!("proof node {} does not exist", current))?;

            if let ProofStep::Inference { premises, .. } = &node.step {
                for &premise_id in premises.iter() {
                    if premise_id.0 >= current.0 {
                        return Err(format!(
                            "node {} has a forward/self-referential premise {}",
                            current, premise_id
                        ));
                    }
                    queue.push_back(premise_id);
                }
            }
        }

        Ok(())
    }

    /// Get the underlying proof structure
    #[must_use]
    pub fn proof(&self) -> &Proof {
        &self.proof
    }

    /// Get a mutable reference to the proof
    pub fn proof_mut(&mut self) -> &mut Proof {
        &mut self.proof
    }

    /// Get the code
    #[must_use]
    pub fn code(&self) -> &str {
        &self.code
    }

    /// Get the certified properties
    #[must_use]
    pub fn properties(&self) -> &[SafetyProperty] {
        &self.properties
    }

    /// Get the verification conditions
    #[must_use]
    pub fn verification_conditions(&self) -> &[VerificationCondition] {
        &self.vcs
    }

    /// Check if all VCs are verified (not merely attached; see [`VcStatus`]).
    #[must_use]
    pub fn is_complete(&self) -> bool {
        self.vcs
            .iter()
            .all(|vc| self.vc_status(&vc.id) == VcStatus::Verified)
    }

    /// Get the number of verified VCs (not merely attached; see [`VcStatus`]).
    #[must_use]
    pub fn verified_count(&self) -> usize {
        self.vcs
            .iter()
            .filter(|vc| self.vc_status(&vc.id) == VcStatus::Verified)
            .count()
    }

    /// Get the total number of VCs
    #[must_use]
    pub fn total_vc_count(&self) -> usize {
        self.vcs.len()
    }

    /// Generate a human-readable certificate
    #[must_use]
    pub fn to_certificate(&self) -> String {
        let mut cert = String::new();
        cert.push_str("=== Proof-Carrying Code Certificate ===\n\n");

        cert.push_str("Properties:\n");
        for prop in &self.properties {
            cert.push_str(&format!("  - {}\n", prop));
        }
        cert.push('\n');

        cert.push_str(&format!(
            "Verification Status: {}/{} VCs verified\n\n",
            self.verified_count(),
            self.total_vc_count()
        ));

        cert.push_str("Verification Conditions:\n");
        for vc in &self.vcs {
            cert.push_str(&format!(
                "  [{}] {} at {}\n",
                vc.id, vc.property, vc.location
            ));
            cert.push_str(&format!("    Status: {}\n", self.vc_status(&vc.id)));
        }

        cert.push_str("\n=== End Certificate ===\n");
        cert
    }
}

/// Builder for creating proof-carrying code certificates
pub struct PccBuilder {
    pcc: ProofCarryingCode,
}

impl PccBuilder {
    /// Create a new PCC builder
    #[must_use]
    pub fn new(code: impl Into<String>) -> Self {
        Self {
            pcc: ProofCarryingCode::new(code),
        }
    }

    /// Add a safety property
    pub fn with_property(mut self, property: SafetyProperty) -> Self {
        self.pcc.add_property(property);
        self
    }

    /// Add a verification condition
    pub fn with_vc(mut self, vc: VerificationCondition) -> Self {
        self.pcc.add_vc(vc);
        self
    }

    /// Build the PCC certificate
    #[must_use]
    pub fn build(self) -> ProofCarryingCode {
        self.pcc
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_pcc_creation() {
        let pcc = ProofCarryingCode::new("fn safe_add(a: i32, b: i32) -> i32 { a + b }");
        assert_eq!(pcc.total_vc_count(), 0);
        assert_eq!(pcc.verified_count(), 0);
        assert!(pcc.is_complete());
    }

    #[test]
    fn test_add_property() {
        let mut pcc = ProofCarryingCode::new("code");
        pcc.add_property(SafetyProperty::MemorySafety);
        assert_eq!(pcc.properties().len(), 1);
    }

    #[test]
    fn test_add_vc() {
        let mut pcc = ProofCarryingCode::new("code");
        let vc = VerificationCondition {
            id: "vc1".to_string(),
            property: SafetyProperty::TypeSafety,
            condition: "typeof(x) = int".to_string(),
            location: CodeLocation {
                function: "main".to_string(),
                label: Some("entry".to_string()),
                line: Some(10),
            },
        };
        pcc.add_vc(vc);
        assert_eq!(pcc.total_vc_count(), 1);
        assert!(!pcc.is_complete());
    }

    #[test]
    fn test_attach_proof() {
        let mut pcc = ProofCarryingCode::new("code");
        let vc = VerificationCondition {
            id: "vc1".to_string(),
            property: SafetyProperty::TypeSafety,
            condition: "typeof(x) = int".to_string(),
            location: CodeLocation {
                function: "main".to_string(),
                label: None,
                line: Some(5),
            },
        };
        pcc.add_vc(vc);

        let proof_node = pcc.proof_mut().add_axiom("typeof(x) = int");
        pcc.attach_proof("vc1", proof_node);

        assert!(pcc.is_complete());
        assert_eq!(pcc.verified_count(), 1);
        assert_eq!(pcc.vc_status("vc1"), VcStatus::Verified);
        assert!(pcc.to_certificate().contains("VERIFIED"));
    }

    #[test]
    fn test_attach_proof_unrelated_conclusion_is_not_verified() {
        // PF-04 regression: attaching a proof whose conclusion does not
        // match the VC's condition must not be reported as VERIFIED.
        let mut pcc = ProofCarryingCode::new("code");
        let vc = VerificationCondition {
            id: "vc1".to_string(),
            property: SafetyProperty::TypeSafety,
            condition: "typeof(x) = int".to_string(),
            location: CodeLocation {
                function: "main".to_string(),
                label: None,
                line: Some(5),
            },
        };
        pcc.add_vc(vc);

        // Attach a proof of a completely unrelated fact.
        let proof_node = pcc.proof_mut().add_axiom("1 + 1 = 2");
        pcc.attach_proof("vc1", proof_node);

        assert!(!pcc.is_complete());
        assert_eq!(pcc.verified_count(), 0);
        assert!(matches!(pcc.vc_status("vc1"), VcStatus::Invalid(_)));
        let cert = pcc.to_certificate();
        assert!(!cert.contains("VERIFIED \u{2713}"));
    }

    #[test]
    fn test_attach_proof_dangling_node_is_not_verified() {
        // PF-04 regression: attaching a `ProofNodeId` that does not exist
        // in the underlying proof at all must not be reported as VERIFIED.
        let mut pcc = ProofCarryingCode::new("code");
        let vc = VerificationCondition {
            id: "vc1".to_string(),
            property: SafetyProperty::TypeSafety,
            condition: "typeof(x) = int".to_string(),
            location: CodeLocation {
                function: "main".to_string(),
                label: None,
                line: Some(5),
            },
        };
        pcc.add_vc(vc);

        // No node with this ID was ever added to pcc's proof.
        pcc.attach_proof("vc1", ProofNodeId(42));

        assert!(!pcc.is_complete());
        assert_eq!(pcc.verified_count(), 0);
        assert!(matches!(pcc.vc_status("vc1"), VcStatus::Invalid(_)));
        assert!(!pcc.to_certificate().contains("VERIFIED \u{2713}"));
    }

    #[test]
    fn test_attach_proof_structurally_corrupted_is_not_verified() {
        // PF-04 regression: an attached proof whose premises are corrupted
        // (dangling/forward reference) must not be reported as VERIFIED,
        // even if its top-level conclusion string happens to match the VC.
        let mut pcc = ProofCarryingCode::new("code");
        let vc = VerificationCondition {
            id: "vc1".to_string(),
            property: SafetyProperty::TypeSafety,
            condition: "derived".to_string(),
            location: CodeLocation {
                function: "main".to_string(),
                label: None,
                line: Some(5),
            },
        };
        pcc.add_vc(vc);

        let proof = pcc.proof_mut();
        let ax1 = proof.add_axiom("premise1");
        // Fabricate a bogus premise ID that was never added to the proof.
        let bogus_premise = ProofNodeId(ax1.0 + 999);
        let derived = proof.add_inference("rule", vec![bogus_premise], "derived");

        pcc.attach_proof("vc1", derived);

        assert!(!pcc.is_complete());
        assert_eq!(pcc.verified_count(), 0);
        assert!(matches!(pcc.vc_status("vc1"), VcStatus::Invalid(_)));
        assert!(!pcc.to_certificate().contains("VERIFIED \u{2713}"));
    }

    #[test]
    fn test_pcc_builder() {
        let pcc = PccBuilder::new("safe code")
            .with_property(SafetyProperty::MemorySafety)
            .with_property(SafetyProperty::TypeSafety)
            .with_vc(VerificationCondition {
                id: "vc1".to_string(),
                property: SafetyProperty::MemorySafety,
                condition: "bounds_check(array, index)".to_string(),
                location: CodeLocation {
                    function: "access".to_string(),
                    label: None,
                    line: Some(15),
                },
            })
            .build();

        assert_eq!(pcc.properties().len(), 2);
        assert_eq!(pcc.total_vc_count(), 1);
    }

    #[test]
    fn test_certificate_generation() {
        let mut pcc = ProofCarryingCode::new("test code");
        pcc.add_property(SafetyProperty::MemorySafety);

        let cert = pcc.to_certificate();
        assert!(cert.contains("Proof-Carrying Code Certificate"));
        assert!(cert.contains("MemorySafety"));
    }

    #[test]
    fn test_resource_bounds_display() {
        let prop = SafetyProperty::ResourceBounds {
            memory: Some(1024),
            time: Some(100),
        };
        let s = format!("{}", prop);
        assert!(s.contains("1024"));
        assert!(s.contains("100"));
    }

    #[test]
    fn test_code_location_display() {
        let loc = CodeLocation {
            function: "process".to_string(),
            label: Some("loop_head".to_string()),
            line: Some(42),
        };
        let s = format!("{}", loc);
        assert!(s.contains("process"));
        assert!(s.contains("loop_head"));
        assert!(s.contains("42"));
    }
}
