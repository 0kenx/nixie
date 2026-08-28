//! The nonlinear dispatch result types, kept OUT of the `nlsat` feature gate.
//!
//! The four ground-search drivers (`nl_model_search`, `ania_ground`,
//! `nia_cdcl`, `nl_dpll`) and the CDCL(T) fallback paths all speak this
//! vocabulary, and they stay compiled in the no-`nlsat` build — only the
//! cell-decomposition core (`nlsat`, and the `oxiz-nlsat` crate behind it) is
//! feature-gated. Splitting the vocabulary out is what lets the OFF build keep
//! answering QF_NIA nonlinear goals the searches can decide, exactly as
//! upstream v0.3.3's feature split does.

use num_rational::BigRational;
use oxiz_core::ast::TermId;
use std::collections::HashMap;

/// Concrete arithmetic assignment produced by a nonlinear decision procedure.
///
/// Keys are free arithmetic terms (`Var`, purified `select` constants, …);
/// values are the rational witnesses found by NIA/NRA/ANIA ground search.
#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub struct NlSatModel {
    /// TermId → rational value for every free arithmetic variable assigned.
    pub assignments: HashMap<TermId, BigRational>,
}

/// The definitive result from a nonlinear dispatch call.
///
/// `Unknown` is not included: `dispatch_*` functions return `None` to signal
/// "fall through to CDCL(T)" instead of wrapping Unknown.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum NlDispatchResult {
    /// The constraint set is satisfiable, with a concrete model witness.
    Sat(NlSatModel),
    /// The constraint set is unsatisfiable.
    Unsat,
}

impl NlDispatchResult {
    /// Satisfiable with an empty assignment map (defaults fill gaps).
    #[must_use]
    pub fn sat_empty() -> Self {
        Self::Sat(NlSatModel::default())
    }

    /// Satisfiable with the given term→value map.
    #[must_use]
    pub fn sat_with(assignments: HashMap<TermId, BigRational>) -> Self {
        Self::Sat(NlSatModel { assignments })
    }
}
