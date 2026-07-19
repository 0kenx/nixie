//! Errors produced during interpolation.

use crate::proof::ProofNodeId;
use std::fmt;

/// Errors during interpolation
#[derive(Debug, Clone)]
pub enum InterpolationError {
    /// Proof has no root
    NoRoot,
    /// Node not found in proof
    NodeNotFound(ProofNodeId),
    /// Node has no computed color
    NoColor(ProofNodeId),
    /// Too few formulas for sequence interpolation
    TooFewFormulas,
    /// Interpolant validation failed
    ValidationFailed(String),
    /// Theory interpolation not supported
    TheoryNotSupported(String),
    /// An axiom's vocabulary spans both the A and B partitions (e.g. a
    /// theory lemma whose symbols touch both sides) and this clause-
    /// projection interpolation system cannot soundly assign it a base-case
    /// interpolant without knowing which part of its internal derivation
    /// belongs to each side.
    MixedAxiom(ProofNodeId),
}

impl fmt::Display for InterpolationError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::NoRoot => write!(f, "Proof has no root"),
            Self::NodeNotFound(id) => write!(f, "Node {} not found", id),
            Self::NoColor(id) => write!(f, "Node {} has no computed color", id),
            Self::TooFewFormulas => write!(f, "Need at least 2 formulas for interpolation"),
            Self::ValidationFailed(msg) => write!(f, "Validation failed: {}", msg),
            Self::TheoryNotSupported(theory) => {
                write!(f, "Theory {} not supported for interpolation", theory)
            }
            Self::MixedAxiom(id) => write!(
                f,
                "Axiom {} spans both partitions and cannot be soundly interpolated as a leaf",
                id
            ),
        }
    }
}

impl std::error::Error for InterpolationError {}
