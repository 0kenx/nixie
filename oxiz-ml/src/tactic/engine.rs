//! High-level ML tactic-selection engine.
//!
//! This is the clean, stateful entry point external crates (e.g. `oxiz-cli`)
//! use to get ML-guided tactic recommendations without touching the solver's
//! internals: extract features from a formula, get a [`TacticRecommendation`],
//! run the solve, then feed the outcome back so the model learns. The model
//! can be persisted and reloaded so learning accumulates across process runs.

use crate::models::ModelError;
use crate::tactic::formula_features::FeatureExtractor;
use crate::tactic::selector::{TacticConfig, TacticId, TacticSelector};
use crate::tactic::{FormulaFeatures, TacticFeedback};

/// Number of distinct tactics the default engine chooses between.
pub const NUM_DEFAULT_TACTICS: usize = 5;

/// Map a tactic id to a stable, human-readable name.
///
/// The names describe the search posture the CLI applies for each id (see the
/// CLI's tactic->option mapping); ids outside the known range fall back to a
/// generic label rather than panicking.
pub fn tactic_name(tactic_id: TacticId) -> &'static str {
    match tactic_id {
        0 => "simplify-preprocess",
        1 => "cdcl-core",
        2 => "eager-theory",
        3 => "lazy-theory",
        4 => "portfolio",
        _ => "default",
    }
}

/// A tactic recommendation for a formula.
#[derive(Debug, Clone, Copy, PartialEq)]
pub struct TacticRecommendation {
    /// The recommended tactic id.
    pub tactic_id: TacticId,
    /// Stable, human-readable name for the tactic (see [`tactic_name`]).
    pub tactic_name: &'static str,
    /// Model confidence in the recommendation (0.0-1.0).
    pub confidence: f64,
    /// Estimated solve time in seconds, from historical feedback.
    pub estimated_time: f64,
}

/// Stateful ML tactic-selection engine: feature extraction + selection +
/// feedback-driven learning + persistence, bundled behind one façade.
pub struct MlTacticEngine {
    extractor: FeatureExtractor,
    selector: TacticSelector,
    last_features: Option<FormulaFeatures>,
    last_tactic: Option<TacticId>,
}

impl MlTacticEngine {
    /// Create an engine with the default configuration.
    pub fn new() -> Self {
        let config = TacticConfig {
            num_tactics: NUM_DEFAULT_TACTICS,
            ..TacticConfig::default()
        };
        Self {
            extractor: FeatureExtractor::new(),
            selector: TacticSelector::new(config),
            last_features: None,
            last_tactic: None,
        }
    }

    /// Recommend a tactic for the given SMT-LIB2 formula/script.
    ///
    /// The extracted feature vector and chosen tactic are remembered so a
    /// following [`MlTacticEngine::record_outcome`] can attribute the result
    /// to exactly this decision.
    pub fn recommend(&mut self, formula: &str) -> TacticRecommendation {
        let features = self.extractor.extract_from_formula(formula);
        let selection = self.selector.select_tactic(&features);
        self.last_features = Some(features);
        self.last_tactic = Some(selection.tactic_id);

        TacticRecommendation {
            tactic_id: selection.tactic_id,
            tactic_name: tactic_name(selection.tactic_id),
            confidence: selection.confidence,
            estimated_time: selection.estimated_time,
        }
    }

    /// Feed the outcome of the most recently recommended solve back into the
    /// model so it learns which tactics work for which formulas.
    ///
    /// No-op if no recommendation has been made yet.
    pub fn record_outcome(&mut self, was_successful: bool, actual_time: f64, conflicts: usize) {
        if let (Some(features), Some(tactic_id)) = (self.last_features.as_ref(), self.last_tactic) {
            let feedback = TacticFeedback {
                was_successful,
                actual_time,
                conflicts,
            };
            self.selector
                .learn_from_feedback(features, tactic_id, feedback);
        }
    }

    /// Number of supervised samples the underlying selector has learned from.
    pub fn training_samples(&self) -> usize {
        self.selector.training_samples()
    }

    /// Force an immediate retrain from accumulated feedback.
    pub fn retrain_now(&mut self) {
        self.selector.retrain_now();
    }

    /// Serialize the learned model for persistence.
    pub fn save_model(&self) -> Result<Vec<u8>, ModelError> {
        self.selector.save_model()
    }

    /// Load a previously-serialized model.
    pub fn load_model(&mut self, data: &[u8]) -> Result<(), ModelError> {
        self.selector.load_model(data)
    }
}

impl Default for MlTacticEngine {
    fn default() -> Self {
        Self::new()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_engine_recommends_for_real_formula() {
        let mut engine = MlTacticEngine::new();
        let rec = engine.recommend("(declare-const x Int)\n(assert (> x 0))\n(check-sat)\n");
        assert!(rec.tactic_id < NUM_DEFAULT_TACTICS);
        assert!(!rec.tactic_name.is_empty());
        assert!(rec.confidence >= 0.0 && rec.confidence <= 1.0);
    }

    #[test]
    fn test_engine_records_outcome_and_learns() {
        let mut engine = MlTacticEngine::new();
        let formula = "(declare-const x Int)\n(assert (> x 0))\n(check-sat)\n";
        for _ in 0..8 {
            let _ = engine.recommend(formula);
            engine.record_outcome(true, 0.5, 3);
        }
        engine.retrain_now();
        assert!(
            engine.training_samples() >= 8,
            "engine should have accumulated feedback samples"
        );
    }

    #[test]
    fn test_engine_record_without_recommend_is_noop() {
        let mut engine = MlTacticEngine::new();
        // No recommend() called yet: recording must not panic or learn.
        engine.record_outcome(true, 1.0, 0);
        assert_eq!(engine.training_samples(), 0);
    }

    #[test]
    fn test_tactic_name_stable() {
        assert_eq!(tactic_name(0), "simplify-preprocess");
        assert_eq!(tactic_name(4), "portfolio");
        assert_eq!(tactic_name(99), "default");
    }
}
