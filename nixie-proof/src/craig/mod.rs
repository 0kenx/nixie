//! Craig Interpolation for SMT solving
//!
//! Provides complete Craig interpolation infrastructure:
//! - McMillan's algorithm (left-biased/weaker interpolants)
//! - Pudlák's algorithm (symmetric interpolation)
//! - Theory-specific interpolants (LIA, Arrays, EUF)
//! - Sequence interpolation for tree/DAG proofs
//!
//! Given an UNSAT formula A ∧ B, compute an interpolant I such that:
//! - A ⟹ I
//! - I ∧ B is UNSAT
//! - I only contains symbols common to A and B
//!
//! # Coloring and vocabulary
//!
//! Axiom (leaf) nodes are colored from the caller's explicit A/B premise
//! partition: each axiom's conclusion text is looked up in the
//! [`PremiseTracker`](crate::premise::PremiseTracker) to find its
//! [`PremiseId`](crate::premise::PremiseId), which is then checked
//! against the [`InterpolantPartition`]. Axioms that are *not* found this way
//! (typically theory lemmas synthesized during solving rather than original
//! user assertions) fall back to a McMillan-style heuristic: they are colored
//! by which side's *vocabulary* (as observed on the directly-colored axioms)
//! their symbols touch.
//!
//! The shared/global vocabulary -- the only symbols a sound interpolant may
//! mention -- is derived as the intersection of the vocabulary observed on
//! directly-colored A axioms and B axioms, unioned with any symbols the
//! caller explicitly declares shared via [`InterpolantPartition::set_shared_symbols`].
//!
//! # References
//!
//! - McMillan, K.L. "Interpolation and SAT-Based Model Checking" (CAV 2003)
//! - Pudlák, P. "Lower bounds for resolution and cutting plane proofs" (1997)
//! - Yorsh, G. & Musuvathi, M. "A Combination Method for Generating Interpolants" (CADE 2005)

mod config;
mod error;
mod interpolator;
mod parsing;
mod partition;
mod sequence;
mod term;
mod theory;
mod tree;

#[cfg(test)]
mod tests;

pub use config::{InterpolationAlgorithm, InterpolationConfig};
pub use error::InterpolationError;
pub use interpolator::{CraigInterpolator, InterpolationStats};
pub use partition::{InterpolantColor, InterpolantPartition, Symbol};
pub use sequence::SequenceInterpolator;
pub use term::InterpolantTerm;
pub use theory::{ArrayInterpolator, EufInterpolator, LiaInterpolator, TheoryInterpolator};
pub use tree::{TreeInterpolator, TreeNode};
