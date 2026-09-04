//! Debugging Support for Nixie Solver.
//!
//! This module provides comprehensive debugging tools for SMT solving:
//!
//! - **Visualization**: Solver state snapshots and DOT graph generation
//! - **Tracing**: Event recording and trace generation
//! - **Conflict Explanation**: Human-readable UNSAT and conflict explanations
//! - **Model Minimization**: Finding minimal satisfying models
//!
//! Everything here is inert data plumbing: nothing in this module is invoked
//! by the solving path, so it costs nothing unless an embedder (or a
//! `#[cfg(debug_assertions)]` hook such as
//! [`crate::Solver::debug_check_invariants`]) reaches for it.

#[allow(unused_imports)]
use crate::prelude::*;

pub mod explain;
pub mod model_min;
pub mod trace;
pub mod visualize;

pub use explain::{
    ConflictExplainer, ConflictExplanation, PropagationStep, TheoryConflictInfo, UnsatExplanation,
};
pub use model_min::{
    MinStats, ModelAssignment, ModelMinResult, ModelMinimizer as DebugModelMinimizer,
    SatisfactionChecker,
};
pub use trace::{SolverTracer, TraceConfig, TraceEvent, TraceFilter};
pub use visualize::{
    ActiveConflict, ImplicationGraphDot, SolverStateSnapshot, StatsSnapshot, TheorySolverState,
    TrailDecision, VarAssignment,
};
