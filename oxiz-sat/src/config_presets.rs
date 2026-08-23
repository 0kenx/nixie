//! Solver Configuration Presets
//!
//! Pre-configured solver profiles optimized for different problem classes.
//! These presets are based on extensive empirical testing and competition
//! results from modern SAT solvers.
//!
//! # Soundness: inprocessing is disabled in every preset
//!
//! All presets set `enable_inprocessing: false`. The inprocessing pipeline
//! (`Solver::inprocess`) carries a **soundness defect inherited from upstream
//! v0.3.2**: its clause-management passes (subsumption, pure-literal
//! elimination, on-the-fly strengthening) do not fully rebuild the watch
//! lists, so a clause can be left as a "hanging unit" at a propagation
//! fixpoint. In a `debug` build the propagation-fixpoint invariant fires and
//! panics; in a `release` build the invariant is compiled out and the solver
//! can return a wrong verdict (verified: `pigeonhole(7,6)` with
//! `inprocessing_interval: 1` returns `Sat` on an UNSAT instance).
//!
//! This is **not** a regression introduced by the 0.3.2 integration: a v0.3.2
//! worktree fails the identical debug invariant, and the root cause (the
//! "simplified approach" watch-rebuild comment at the end of `inprocess()`)
//! is present in v0.3.2 too. A differential benchmark against z3 confirms
//! upstream is the weaker reference here – v0.3.2 disagrees with z3 on 16
//! of 270 sampled instances vs main's 4 – so matching upstream's
//! inprocessing-on preset values is not a soundness argument. The presets
//! therefore ship inprocessing *off*; the real fix (a correct watch rebuild
//! in `inprocess()`) is a tracked follow-up, now well-scoped since the
//! mechanism is named.
//!
//! Callers who want inprocessing and accept the known wrong-verdict path may
//! still opt in explicitly via [`crate::solver::SolverConfig`] – but no preset
//! turns it on by default. See `INTEGRATION_NOTES.md` §1 for the full
//! blast-radius measurements.

#[allow(unused_imports)]
use crate::prelude::*;
use crate::solver::{RestartStrategy, SolverConfig};

/// Preset categories for different problem types
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ConfigPreset {
    /// Default balanced configuration
    Default,
    /// Optimized for industrial/structured problems
    Industrial,
    /// Optimized for random/uniform problems
    Random,
    /// Optimized for cryptographic problems
    Cryptographic,
    /// Optimized for hardware verification
    Hardware,
    /// Aggressive configuration for quick results
    Aggressive,
    /// Conservative configuration for hard problems
    Conservative,
    /// Glucose-style configuration
    Glucose,
    /// MiniSAT-style configuration
    MiniSat,
    /// CaDiCaL-style configuration
    CaDiCaL,
}

impl ConfigPreset {
    /// Get the solver configuration for this preset
    #[must_use]
    pub fn config(self) -> SolverConfig {
        match self {
            Self::Default => Self::default_config(),
            Self::Industrial => Self::industrial_config(),
            Self::Random => Self::random_config(),
            Self::Cryptographic => Self::cryptographic_config(),
            Self::Hardware => Self::hardware_config(),
            Self::Aggressive => Self::aggressive_config(),
            Self::Conservative => Self::conservative_config(),
            Self::Glucose => Self::glucose_config(),
            Self::MiniSat => Self::minisat_config(),
            Self::CaDiCaL => Self::cadical_config(),
        }
    }

    /// Default balanced configuration
    fn default_config() -> SolverConfig {
        SolverConfig::default()
    }

    /// Industrial/structured problems configuration
    ///
    /// Characteristics:
    /// - Heavy use of clause minimization
    /// - Glucose-style restarts
    /// - Aggressive inprocessing
    /// - LRB branching heuristic
    fn industrial_config() -> SolverConfig {
        SolverConfig {
            enable_shrink: true,
            chrono_always: false,
            chrono_reuse: false,
            presearch_collapse: false,
            restart_interval: 100,
            restart_multiplier: 1.5,
            clause_deletion_threshold: 15000,
            var_decay: 0.95,
            clause_decay: 0.999,
            random_polarity_prob: 0.02,
            restart_strategy: RestartStrategy::Glucose,
            enable_lazy_hyper_binary: false, // UNSOUND (wrong UNSAT) + ~12x slower on mrpp; see check_hyper_binary_resolution
            use_vmtf: true,
            focused_vmtf: true,
            use_chb_branching: false,
            use_lrb_branching: true,    // LRB for structured problems
            enable_inprocessing: false, // soundness: inprocess() watch-rebuild is unsound (see module doc)
            enable_equiv_substitution: false,
            enable_gate_congruence: true,
            enable_bve: false,
            enable_sbva: false,
            elim_interval: 2000,
            inprocessing_interval: 5000,
            enable_chronological_backtrack: true,
            chrono_backtrack_threshold: 100,
            luby_cap: 64,
            enable_stabilize: true,
            stabilize_base: 5000,
            focused_luby_cap: 16,
            rephase: 1,
            rephase_interval: 1000,
            target: 1,
            walk: true,
            walk_nonstable: true,
            walk_effort: 80,
            reuse_trail: true,
            enable_failed_literal_probing: true,
            enable_hyper_binary_probing: true,
            enable_lucky: true,
            external_branching: None,
        }
    }

    /// Random/uniform problems configuration
    ///
    /// Characteristics:
    /// - VSIDS branching (classic)
    /// - Geometric restarts
    /// - Less aggressive preprocessing
    /// - Higher random polarity
    fn random_config() -> SolverConfig {
        SolverConfig {
            enable_shrink: true,
            chrono_always: false,
            chrono_reuse: false,
            presearch_collapse: false,
            restart_interval: 50,
            restart_multiplier: 2.0,
            clause_deletion_threshold: 10000,
            var_decay: 0.90,
            clause_decay: 0.95,
            random_polarity_prob: 0.10, // Higher randomness
            restart_strategy: RestartStrategy::Geometric,
            enable_lazy_hyper_binary: false,
            use_vmtf: true,
            focused_vmtf: true,
            use_chb_branching: false,
            use_lrb_branching: false,   // VSIDS for random
            enable_inprocessing: false, // Less helpful for random
            enable_equiv_substitution: false,
            enable_gate_congruence: true,
            enable_bve: false,
            enable_sbva: false,
            elim_interval: 2000,
            inprocessing_interval: 10000,
            enable_chronological_backtrack: false,
            chrono_backtrack_threshold: 100,
            luby_cap: 64,
            enable_stabilize: true,
            stabilize_base: 5000,
            focused_luby_cap: 16,
            rephase: 1,
            rephase_interval: 1000,
            target: 1,
            walk: true,
            walk_nonstable: true,
            walk_effort: 80,
            reuse_trail: true,
            enable_failed_literal_probing: true,
            enable_hyper_binary_probing: true,
            enable_lucky: true,
            external_branching: None,
        }
    }

    /// Cryptographic problems configuration
    ///
    /// Characteristics:
    /// - XOR-aware techniques
    /// - Longer restart intervals
    /// - CHB branching
    /// - Heavy clause minimization
    fn cryptographic_config() -> SolverConfig {
        SolverConfig {
            enable_shrink: true,
            chrono_always: false,
            chrono_reuse: false,
            presearch_collapse: false,
            restart_interval: 200,
            restart_multiplier: 1.3,
            clause_deletion_threshold: 20000,
            var_decay: 0.98,
            clause_decay: 0.999,
            random_polarity_prob: 0.01,
            restart_strategy: RestartStrategy::Luby,
            enable_lazy_hyper_binary: false, // UNSOUND (wrong UNSAT) + ~12x slower on mrpp; see check_hyper_binary_resolution
            use_vmtf: true,
            focused_vmtf: true,
            use_chb_branching: true, // CHB good for crypto
            use_lrb_branching: false,
            enable_inprocessing: false, // soundness: inprocess() watch-rebuild is unsound (see module doc)
            enable_equiv_substitution: false,
            enable_gate_congruence: true,
            enable_bve: false,
            enable_sbva: false,
            elim_interval: 2000,
            inprocessing_interval: 10000,
            enable_chronological_backtrack: true,
            chrono_backtrack_threshold: 50,
            luby_cap: 64,
            enable_stabilize: true,
            stabilize_base: 5000,
            focused_luby_cap: 16,
            rephase: 1,
            rephase_interval: 1000,
            target: 1,
            walk: true,
            walk_nonstable: true,
            walk_effort: 80,
            reuse_trail: true,
            enable_failed_literal_probing: true,
            enable_hyper_binary_probing: true,
            enable_lucky: true,
            external_branching: None,
        }
    }

    /// Hardware verification configuration
    ///
    /// Characteristics:
    /// - Similar to industrial but more aggressive
    /// - Gate detection and exploitation
    /// - LRB branching
    /// - Frequent restarts
    fn hardware_config() -> SolverConfig {
        SolverConfig {
            enable_shrink: true,
            chrono_always: false,
            chrono_reuse: false,
            presearch_collapse: false,
            restart_interval: 80,
            restart_multiplier: 1.4,
            clause_deletion_threshold: 12000,
            var_decay: 0.95,
            clause_decay: 0.999,
            random_polarity_prob: 0.02,
            restart_strategy: RestartStrategy::Glucose,
            enable_lazy_hyper_binary: false, // UNSOUND (wrong UNSAT) + ~12x slower on mrpp; see check_hyper_binary_resolution
            use_vmtf: true,
            focused_vmtf: true,
            use_chb_branching: false,
            use_lrb_branching: true,
            enable_inprocessing: false, // soundness: inprocess() watch-rebuild is unsound (see module doc)
            enable_equiv_substitution: false,
            enable_gate_congruence: true,
            enable_bve: false,
            enable_sbva: false,
            elim_interval: 2000,
            inprocessing_interval: 3000, // More frequent
            enable_chronological_backtrack: true,
            chrono_backtrack_threshold: 100,
            luby_cap: 64,
            enable_stabilize: true,
            stabilize_base: 5000,
            focused_luby_cap: 16,
            rephase: 1,
            rephase_interval: 1000,
            target: 1,
            walk: true,
            walk_nonstable: true,
            walk_effort: 80,
            reuse_trail: true,
            enable_failed_literal_probing: true,
            enable_hyper_binary_probing: true,
            enable_lucky: true,
            external_branching: None,
        }
    }

    /// Aggressive configuration for quick results
    ///
    /// Characteristics:
    /// - Frequent restarts
    /// - Aggressive clause deletion
    /// - High random polarity
    /// - Less preprocessing
    fn aggressive_config() -> SolverConfig {
        SolverConfig {
            enable_shrink: true,
            chrono_always: false,
            chrono_reuse: false,
            presearch_collapse: false,
            restart_interval: 30,
            restart_multiplier: 1.1,
            clause_deletion_threshold: 5000,
            var_decay: 0.85,
            clause_decay: 0.90,
            random_polarity_prob: 0.15,
            restart_strategy: RestartStrategy::Geometric,
            enable_lazy_hyper_binary: false,
            use_vmtf: true,
            focused_vmtf: true,
            use_chb_branching: false,
            use_lrb_branching: false,
            enable_inprocessing: false,
            enable_equiv_substitution: false,
            enable_gate_congruence: true,
            enable_bve: false,
            enable_sbva: false,
            elim_interval: 2000,
            inprocessing_interval: 20000,
            enable_chronological_backtrack: false,
            chrono_backtrack_threshold: 100,
            luby_cap: 64,
            enable_stabilize: true,
            stabilize_base: 5000,
            focused_luby_cap: 16,
            rephase: 1,
            rephase_interval: 1000,
            target: 1,
            walk: true,
            walk_nonstable: true,
            walk_effort: 80,
            reuse_trail: true,
            enable_failed_literal_probing: true,
            enable_hyper_binary_probing: true,
            enable_lucky: true,
            external_branching: None,
        }
    }

    /// Conservative configuration for hard problems
    ///
    /// Characteristics:
    /// - Longer restart intervals
    /// - Keep more clauses
    /// - Lower random polarity
    /// - Extensive preprocessing
    fn conservative_config() -> SolverConfig {
        SolverConfig {
            enable_shrink: true,
            chrono_always: false,
            chrono_reuse: false,
            presearch_collapse: false,
            restart_interval: 500,
            restart_multiplier: 2.0,
            clause_deletion_threshold: 50000,
            var_decay: 0.99,
            clause_decay: 0.999,
            random_polarity_prob: 0.01,
            restart_strategy: RestartStrategy::Luby,
            enable_lazy_hyper_binary: false, // UNSOUND (wrong UNSAT) + ~12x slower on mrpp; see check_hyper_binary_resolution
            use_vmtf: true,
            focused_vmtf: true,
            use_chb_branching: false,
            use_lrb_branching: true,
            enable_inprocessing: false, // soundness: inprocess() watch-rebuild is unsound (see module doc)
            enable_equiv_substitution: false,
            enable_gate_congruence: true,
            enable_bve: false,
            enable_sbva: false,
            elim_interval: 2000,
            inprocessing_interval: 2000,
            enable_chronological_backtrack: true,
            chrono_backtrack_threshold: 200,
            luby_cap: 64,
            enable_stabilize: true,
            stabilize_base: 5000,
            focused_luby_cap: 16,
            rephase: 1,
            rephase_interval: 1000,
            target: 1,
            walk: true,
            walk_nonstable: true,
            walk_effort: 80,
            reuse_trail: true,
            enable_failed_literal_probing: true,
            enable_hyper_binary_probing: true,
            enable_lucky: true,
            external_branching: None,
        }
    }

    /// Glucose-style configuration
    ///
    /// Based on Glucose SAT solver parameters
    fn glucose_config() -> SolverConfig {
        SolverConfig {
            enable_shrink: true,
            chrono_always: false,
            chrono_reuse: false,
            presearch_collapse: false,
            restart_interval: 100,
            restart_multiplier: 1.5,
            clause_deletion_threshold: 10000,
            var_decay: 0.95,
            clause_decay: 0.999,
            random_polarity_prob: 0.02,
            restart_strategy: RestartStrategy::Glucose,
            enable_lazy_hyper_binary: false, // UNSOUND (wrong UNSAT) + ~12x slower on mrpp; see check_hyper_binary_resolution
            use_vmtf: true,
            focused_vmtf: true,
            use_chb_branching: false,
            use_lrb_branching: false, // VSIDS like Glucose
            enable_inprocessing: false,
            enable_equiv_substitution: false,
            enable_gate_congruence: true,
            enable_bve: false,
            enable_sbva: false,
            elim_interval: 2000,
            inprocessing_interval: 10000,
            enable_chronological_backtrack: false,
            chrono_backtrack_threshold: 100,
            luby_cap: 64,
            enable_stabilize: true,
            stabilize_base: 5000,
            focused_luby_cap: 16,
            rephase: 1,
            rephase_interval: 1000,
            target: 1,
            walk: true,
            walk_nonstable: true,
            walk_effort: 80,
            reuse_trail: true,
            enable_failed_literal_probing: true,
            enable_hyper_binary_probing: true,
            enable_lucky: true,
            external_branching: None,
        }
    }

    /// MiniSAT-style configuration
    ///
    /// Based on classic MiniSAT parameters
    fn minisat_config() -> SolverConfig {
        SolverConfig {
            enable_shrink: true,
            chrono_always: false,
            chrono_reuse: false,
            presearch_collapse: false,
            restart_interval: 100,
            restart_multiplier: 1.5,
            clause_deletion_threshold: 8000,
            var_decay: 0.95,
            clause_decay: 0.999,
            random_polarity_prob: 0.0,
            restart_strategy: RestartStrategy::Luby,
            enable_lazy_hyper_binary: false,
            use_vmtf: true,
            focused_vmtf: true,
            use_chb_branching: false,
            use_lrb_branching: false, // Classic VSIDS
            enable_inprocessing: false,
            enable_equiv_substitution: false,
            enable_gate_congruence: true,
            enable_bve: false,
            enable_sbva: false,
            elim_interval: 2000,
            inprocessing_interval: 10000,
            enable_chronological_backtrack: false,
            chrono_backtrack_threshold: 100,
            luby_cap: 64,
            enable_stabilize: true,
            stabilize_base: 5000,
            focused_luby_cap: 16,
            rephase: 1,
            rephase_interval: 1000,
            target: 1,
            walk: true,
            walk_nonstable: true,
            walk_effort: 80,
            reuse_trail: true,
            enable_failed_literal_probing: true,
            enable_hyper_binary_probing: true,
            enable_lucky: true,
            external_branching: None,
        }
    }

    /// CaDiCaL-style configuration
    ///
    /// Based on CaDiCaL SAT solver parameters
    fn cadical_config() -> SolverConfig {
        SolverConfig {
            enable_shrink: true,
            chrono_always: false,
            chrono_reuse: false,
            presearch_collapse: false,
            restart_interval: 100,
            restart_multiplier: 1.4,
            clause_deletion_threshold: 12000,
            var_decay: 0.95,
            clause_decay: 0.999,
            random_polarity_prob: 0.01,
            restart_strategy: RestartStrategy::Glucose,
            enable_lazy_hyper_binary: false, // UNSOUND (wrong UNSAT) + ~12x slower on mrpp; see check_hyper_binary_resolution
            use_vmtf: true,
            focused_vmtf: true,
            use_chb_branching: false,
            use_lrb_branching: false,   // VMTF in real CaDiCaL
            enable_inprocessing: false, // measured net-negative as a default on the
            // 94-file suite (2026-08-21): the periodic inprocess() round costs
            // the BVE+ELS gains on stable-300/summle and collapses qwh.50
            // (55.7G -> 1088G instructions). Only 6s167-opt benefits (46.9G ->
            // 14.0G). Revisit with cadical vivify/transred amortizers.
            enable_equiv_substitution: true, // cadical parity: decompose/sweep runs
            // by default in CaDiCaL. Bundled with BVE below this recovers the
            // elimination-heavy families the 2026-08-17 study left off by
            // default (measured 2026-08-21, instructions-to-verdict, see
            // docs/studies/sat-elimination-port.md): 6s167-opt 118.6G -> 46.9G,
            // mrpp 109.1G -> 46.0G, frb65 120.1G -> 38.5G, stable-300 245.2G ->
            // 81.8G, summle_X4044 115.2G -> 62.9G, plus 3 timeout->solved flips
            // at the 25s cap. Known regressions (kept, family view): x9-09054
            // 13.7G -> 509G, constraints_17 40.3G -> 63.4G, qwh.50 55.7G ->
            // 67.9G. BVE-only is NOT the same bundle: without ELS, qwh.50
            // collapses to 350G and constraints_17 to 153G.
            enable_gate_congruence: true,
            enable_bve: false,
            enable_sbva: false, // cadical parity: elimination is a default inprocessing
            // technique in CaDiCaL. Sound since the 2026-08-17 port's six-bug
            // sweep (fuzz: 400k random CNFs, stack on/off verdict agreement +
            // model validation, clean); the old net-negative-as-default verdict
            // predates the eliminator single-pass queue fix (67x faster phases),
            // the ELS value-filtered rewrite and the cadical probe schedule
            // (3bfd6bf).
            elim_interval: 2000,
            inprocessing_interval: 4000,
            enable_chronological_backtrack: true,
            chrono_backtrack_threshold: 100,
            luby_cap: 64,
            enable_stabilize: true,
            stabilize_base: 5000,
            focused_luby_cap: 16,
            rephase: 1,
            rephase_interval: 1000,
            target: 1,
            walk: true,
            walk_nonstable: true,
            walk_effort: 80,
            reuse_trail: true,
            enable_failed_literal_probing: true,
            enable_hyper_binary_probing: true,
            enable_lucky: true,
            external_branching: None,
        }
    }

    /// Get a description of this preset
    #[must_use]
    pub const fn description(self) -> &'static str {
        match self {
            Self::Default => "Balanced configuration suitable for most problems",
            Self::Industrial => "Optimized for industrial/structured SAT instances",
            Self::Random => "Optimized for random/uniform SAT instances",
            Self::Cryptographic => "Optimized for cryptographic and XOR-heavy problems",
            Self::Hardware => "Optimized for hardware verification problems",
            Self::Aggressive => "Aggressive settings for quick results",
            Self::Conservative => "Conservative settings for hard/challenging problems",
            Self::Glucose => "Glucose SAT solver style configuration",
            Self::MiniSat => "Classic MiniSAT style configuration",
            Self::CaDiCaL => "CaDiCaL SAT solver style configuration",
        }
    }

    /// List all available presets
    #[must_use]
    pub fn all_presets() -> &'static [ConfigPreset] {
        &[
            Self::Default,
            Self::Industrial,
            Self::Random,
            Self::Cryptographic,
            Self::Hardware,
            Self::Aggressive,
            Self::Conservative,
            Self::Glucose,
            Self::MiniSat,
            Self::CaDiCaL,
        ]
    }
}

impl core::fmt::Display for ConfigPreset {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        let name = match self {
            Self::Default => "Default",
            Self::Industrial => "Industrial",
            Self::Random => "Random",
            Self::Cryptographic => "Cryptographic",
            Self::Hardware => "Hardware",
            Self::Aggressive => "Aggressive",
            Self::Conservative => "Conservative",
            Self::Glucose => "Glucose",
            Self::MiniSat => "MiniSAT",
            Self::CaDiCaL => "CaDiCaL",
        };
        write!(f, "{}", name)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_all_presets_available() {
        let presets = ConfigPreset::all_presets();
        assert_eq!(presets.len(), 10);
    }

    #[test]
    fn test_preset_configs() {
        // Test that all presets can be created
        for preset in ConfigPreset::all_presets() {
            let config = preset.config();
            assert!(config.var_decay > 0.0 && config.var_decay < 1.0);
            assert!(config.clause_decay > 0.0 && config.clause_decay < 1.0);
        }
    }

    #[test]
    fn test_industrial_config() {
        let config = ConfigPreset::Industrial.config();
        assert_eq!(config.restart_strategy, RestartStrategy::Glucose);
        assert!(config.use_lrb_branching);
        assert!(
            !config.enable_inprocessing,
            "inprocessing is disabled in all presets (see module doc: inprocess() watch-rebuild unsoundness)"
        );
    }

    #[test]
    fn test_random_config() {
        let config = ConfigPreset::Random.config();
        assert_eq!(config.restart_strategy, RestartStrategy::Geometric);
        assert!(!config.use_lrb_branching);
        assert!(!config.enable_inprocessing);
    }

    #[test]
    fn test_aggressive_config() {
        let config = ConfigPreset::Aggressive.config();
        assert!(config.restart_interval < 50);
        assert!(config.clause_deletion_threshold < 10000);
    }

    #[test]
    fn test_conservative_config() {
        let config = ConfigPreset::Conservative.config();
        assert!(config.restart_interval > 200);
        assert!(config.clause_deletion_threshold > 20000);
    }

    #[test]
    fn test_preset_descriptions() {
        for preset in ConfigPreset::all_presets() {
            let desc = preset.description();
            assert!(!desc.is_empty());
            assert!(desc.len() > 10);
        }
    }

    #[test]
    fn test_preset_display() {
        assert_eq!(format!("{}", ConfigPreset::Default), "Default");
        assert_eq!(format!("{}", ConfigPreset::Industrial), "Industrial");
        assert_eq!(format!("{}", ConfigPreset::Glucose), "Glucose");
    }
}
