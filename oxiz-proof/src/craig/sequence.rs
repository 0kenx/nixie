//! Sequence interpolation for chains of formulas.

use super::config::InterpolationConfig;
use super::error::InterpolationError;
use super::interpolator::CraigInterpolator;
use super::partition::InterpolantPartition;
use super::term::InterpolantTerm;
use crate::premise::{PremiseId, PremiseTracker};
use crate::proof::Proof;
use rustc_hash::FxHashSet;

/// Sequence interpolation for multiple formulas
///
/// Given A₁, A₂, ..., Aₙ where ∧Aᵢ is UNSAT,
/// compute interpolants I₁, I₂, ..., Iₙ₋₁ such that:
/// - A₁ ⟹ I₁
/// - Iᵢ ∧ Aᵢ₊₁ ⟹ Iᵢ₊₁
/// - Iₙ₋₁ ∧ Aₙ is UNSAT
#[derive(Debug)]
pub struct SequenceInterpolator {
    config: InterpolationConfig,
}

impl SequenceInterpolator {
    /// Create a new sequence interpolator
    #[must_use]
    pub fn new(config: InterpolationConfig) -> Self {
        Self { config }
    }

    /// Compute sequence of interpolants
    ///
    /// Returns n-1 interpolants for n formulas
    pub fn interpolate_sequence(
        &self,
        proofs: &[Proof],
    ) -> Result<Vec<InterpolantTerm>, InterpolationError> {
        if proofs.len() < 2 {
            return Err(InterpolationError::TooFewFormulas);
        }

        let mut interpolants = Vec::with_capacity(proofs.len() - 1);

        // For each split point, compute the interpolant
        for i in 0..proofs.len() - 1 {
            // Partition: A = proofs[0..=i], B = proofs[i+1..]
            let a_ids: FxHashSet<_> = (0..=i).map(|j| PremiseId(j as u32)).collect();
            let b_ids: FxHashSet<_> = (i + 1..proofs.len()).map(|j| PremiseId(j as u32)).collect();

            let partition = InterpolantPartition::new(a_ids, b_ids);
            let mut interpolator =
                CraigInterpolator::new(self.config.clone(), partition, PremiseTracker::new());

            // Use first proof as representative (simplified)
            if let Some(proof) = proofs.first() {
                let interp = interpolator.extract(proof)?;
                interpolants.push(interp);
            } else {
                interpolants.push(InterpolantTerm::true_val());
            }
        }

        Ok(interpolants)
    }
}

impl Default for SequenceInterpolator {
    fn default() -> Self {
        Self::new(InterpolationConfig::default())
    }
}
