//! Quantifier tactics for Nixie
//!
//! This module provides tactics for handling quantified formulas including:
//! - Ground term collection for instantiation candidates
//! - Pattern matching (E-matching) for trigger-based instantiation
//! - Quantifier instantiation tactics
//! - Skolemization tactics
//!
//! # Module organization
//!
//! Previously a single `tactic/quantifier.rs`, this was split into a module
//! directory purely to keep every file well under the workspace's 2000-line
//! ceiling (the single file had reached 1967 lines). The split is pure code
//! motion -- no item's behaviour, visibility or public path changed, and
//! every type/function is still reachable as
//! `crate::tactic::quantifier::*` through the re-exports below.
//!
//! The submodules themselves are private (they were never a public path);
//! only the items below are re-exported.
//!
//! * `ground_terms` -- [`GroundTermCollector`].
//! * `matching` -- [`Pattern`], [`Binding`], [`PatternMatcher`]
//!   (E-matching).
//! * `instantiation` -- [`QuantifierInstantiationTactic`].
//! * `skolemization` -- [`SkolemizationTactic`].
//! * `universal_elim` -- [`UniversalEliminationTactic`].
//! * `predicates` -- the [`contains_quantifier`] /
//!   [`goal_has_quantifiers`] queries.
//! * `der` -- Destructive Equality Resolution ([`DerConfig`],
//!   [`DerTactic`], [`StatelessDerTactic`]).
//! * `subst` -- `substitute_single_var`, the capture-avoiding
//!   single-variable substitution shared by `der` and `skolemization`.

mod der;
mod ground_terms;
mod instantiation;
mod matching;
mod predicates;
mod skolemization;
mod subst;
pub use subst::substitute_single_var;
mod universal_elim;

#[cfg(test)]
mod tests;

pub use der::{DerConfig, DerTactic, StatelessDerTactic};
pub use ground_terms::GroundTermCollector;
pub use instantiation::QuantifierInstantiationTactic;
pub use matching::{Binding, Pattern, PatternMatcher};
pub use predicates::{contains_quantifier, goal_has_quantifiers};
pub use skolemization::SkolemizationTactic;
pub use universal_elim::UniversalEliminationTactic;
