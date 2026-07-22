//! Core tactic types and traits.

use crate::ast::{TermId, TermManager};
use crate::error::Result;
#[allow(unused_imports)]
use crate::prelude::*;

/// A goal represents a formula to be solved
#[derive(Debug, Clone)]
pub struct Goal {
    /// The assertions in this goal
    pub assertions: Vec<TermId>,
    /// Model precision (for optimization)
    pub precision: Precision,
}

/// Precision level for model generation
#[derive(Debug, Clone, Copy, PartialEq, Eq, Default)]
pub enum Precision {
    /// Under approximation - may miss solutions
    Under,
    /// Exact solution required
    #[default]
    Precise,
    /// Over approximation - may include spurious solutions
    Over,
}

impl Goal {
    /// Create a new goal with the given assertions
    #[must_use]
    pub fn new(assertions: Vec<TermId>) -> Self {
        Self {
            assertions,
            precision: Precision::Precise,
        }
    }

    /// Create an empty goal (trivially satisfiable)
    #[must_use]
    pub fn empty() -> Self {
        Self {
            assertions: Vec::new(),
            precision: Precision::Precise,
        }
    }

    /// Add an assertion to the goal
    pub fn add(&mut self, term: TermId) {
        self.assertions.push(term);
    }

    /// Check if the goal is empty
    #[must_use]
    pub fn is_empty(&self) -> bool {
        self.assertions.is_empty()
    }

    /// Get the number of assertions
    #[must_use]
    pub fn len(&self) -> usize {
        self.assertions.len()
    }
}

/// Result of applying a tactic
#[derive(Debug)]
pub enum TacticResult {
    /// The goal was solved (sat/unsat)
    Solved(SolveResult),
    /// The goal was transformed into sub-goals
    SubGoals(Vec<Goal>),
    /// The tactic does not apply to this goal
    NotApplicable,
    /// The tactic failed with an error
    Failed(String),
}

/// Solve result
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum SolveResult {
    /// Satisfiable
    Sat,
    /// Unsatisfiable
    Unsat,
    /// Unknown
    Unknown,
}

/// A partial assignment mapping variable terms to their value terms.
///
/// This is the model representation threaded through the [`ModelConverter`]
/// mechanism. Keys are the `TermId` of a `Var` (or any term treated as an
/// unknown), values are the `TermId` of the assigned value (usually a
/// numeric/boolean constant). It intentionally mirrors the shape accepted by
/// [`TermManager::substitute`], so a converter can substitute a model into an
/// eliminated variable's defining expression and simplify it to a value.
#[derive(Debug, Clone, Default)]
pub struct TacticModel {
    /// Variable `TermId` -> value `TermId`.
    pub values: FxHashMap<TermId, TermId>,
}

impl TacticModel {
    /// Create an empty model.
    #[must_use]
    pub fn new() -> Self {
        Self::default()
    }

    /// Look up the value assigned to `var`, if any.
    #[must_use]
    pub fn get(&self, var: TermId) -> Option<TermId> {
        self.values.get(&var).copied()
    }

    /// Assign `value` to `var`.
    pub fn set(&mut self, var: TermId, value: TermId) {
        self.values.insert(var, value);
    }

    /// Number of assigned variables.
    #[must_use]
    pub fn len(&self) -> usize {
        self.values.len()
    }

    /// Whether the model assigns nothing.
    #[must_use]
    pub fn is_empty(&self) -> bool {
        self.values.is_empty()
    }
}

/// Reconstructs a model of the *original* goal from a model of the goal a
/// variable-eliminating (or variable-renaming) tactic produced.
///
/// When a tactic such as `solve-eqs`, `ackermannize`, or Fourier-Motzkin
/// eliminates a variable, a model found for the resulting sub-goal is missing
/// that variable's value (or, for Ackermannization, carries fresh auxiliary
/// variables that are not part of the original signature). A `ModelConverter`
/// lifts such a sub-goal model back to a model over the original goal's
/// variables.
///
/// Converters compose via [`ChainConverter`]: if tactic *A* transforms a goal
/// and then tactic *B* transforms *A*'s output, the model found for *B*'s
/// output is converted first by *B*'s converter and then by *A*'s.
///
/// Because [`TacticResult`] is a shared type matched exhaustively by several
/// downstream crates, the converter is *not* stored inside the
/// [`TacticResult::SubGoals`] variant (which would be a breaking change to
/// those crates). Instead, variable-eliminating tactics expose a companion
/// entry point (e.g. `SolveEqsTactic::apply_mut_with_converter`) that returns
/// the converter alongside the `TacticResult`.
pub trait ModelConverter: Send + Sync {
    /// Given `model` over the transformed goal's variables, return a model
    /// over the original goal's variables.
    fn convert(&self, model: &TacticModel, manager: &mut TermManager) -> TacticModel;
}

/// Identity converter for tactics that eliminate nothing.
#[derive(Debug, Default, Clone, Copy)]
pub struct IdentityConverter;

impl ModelConverter for IdentityConverter {
    fn convert(&self, model: &TacticModel, _manager: &mut TermManager) -> TacticModel {
        model.clone()
    }
}

/// Composition of two converters: `inner` (the later tactic in a pipeline) is
/// applied first, then `outer` (the earlier tactic).
pub struct ChainConverter {
    /// Converter of the tactic that ran *later* in the pipeline.
    pub inner: Box<dyn ModelConverter>,
    /// Converter of the tactic that ran *earlier* in the pipeline.
    pub outer: Box<dyn ModelConverter>,
}

impl ModelConverter for ChainConverter {
    fn convert(&self, model: &TacticModel, manager: &mut TermManager) -> TacticModel {
        let intermediate = self.inner.convert(model, manager);
        self.outer.convert(&intermediate, manager)
    }
}

/// A tactic transforms goals into sub-goals
pub trait Tactic: Send + Sync {
    /// Get the name of this tactic
    fn name(&self) -> &str;

    /// Apply the tactic to a goal
    fn apply(&self, goal: &Goal) -> Result<TacticResult>;

    /// Get a description of the tactic
    fn description(&self) -> &str {
        ""
    }
}

// Core tactics
//
// Note: `tactic::core::ctx_solver_simplify` (a dead placeholder module
// with its own disconnected `type TermId = usize` and always-false
// oracles — see P4-1112) and `tactic::core::goal_refinement` (an orphaned,
// never-compiled module written against a `TermKind::Forall`/`Exists`
// tuple shape that does not match the real struct-variant `TermKind` —
// see P4-1110) were deleted rather than wired in: both were unreachable
// dead code whose logic didn't compile against, or duplicated, the real
// implementations (`tactic::ctx_simplify::StatelessCtxSolverSimplifyTactic`
// is the live "ctx-solver-simplify" tactic).
pub mod ctx_simplify;
pub mod elim_unconstrained;
pub mod split_clause;
