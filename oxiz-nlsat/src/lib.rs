//! # oxiz-nlsat
//!
//! Non-linear arithmetic solver for OxiZ using Cylindrical Algebraic Decomposition (CAD).
//!
//! This crate implements the NLSAT algorithm for solving non-linear real arithmetic
//! (QF_NRA) and non-linear integer arithmetic (QF_NIA) problems.
//!
//! ## Reference
//!
//! Z3's `nlsat/` directory (~180k lines), particularly `nlsat_solver.cpp`.
//!
//! ## Key Components
//!
//! - **Polynomial Constraints**: Representation of non-linear constraints
//! - **Variable Ordering**: Strategies for CAD variable ordering
//! - **Interval Sets**: Representation of solution intervals
//! - **Explanation**: Conflict explanation for CDCL integration
//!
//! ## Public API surface
//!
//! Only modules that are actually wired into the solving pipeline, are
//! standalone user-facing solvers/tactics, or are tested public utilities are
//! part of the public API: [`solver`], [`nia`], [`maxsat`], [`simplify`],
//! [`cad`], [`types`], [`clause`], [`assignment`], [`interval_set`],
//! [`restart`], [`var_order`], [`portfolio`], and the tested utility modules
//! [`evaluator`] and [`monotonicity`].
//!
//! A large family of correct-but-currently-unwired helper modules (SAT-style
//! preprocessing/inprocessing, structural analysis, alternative CAD/evaluator
//! implementations, proof logging, ...) were found by the architecture audit
//! to be exported but never called by the solver. They have been demoted to
//! `pub(crate)` (removed from the public API) rather than advertised as
//! working features; each retains a header note explaining the triage. They
//! remain compiled and tested so they can be wired in later without rework.

// Native builds must never silently end up on oxiz-time's frozen stub clock
// (the `std` feature forward in this crate's manifest is what selects the real
// one; see oxiz-time/src/lib.rs).
const _: () = assert!(!oxiz_time::IS_FROZEN);

pub mod assignment;
pub(crate) mod assumptions;
pub(crate) mod asymmetric_literal_addition;
pub(crate) mod bce;
pub(crate) mod bound_propagation;
pub(crate) mod bve;
pub mod cad;
pub(crate) mod cad_algebraic;
pub(crate) mod cad_optimization;
pub(crate) mod chrono_bt;
pub mod clause;
pub(crate) mod clause_tiers;
pub(crate) mod discriminant;
pub(crate) mod eval_cache;
pub mod evaluator;
pub(crate) mod explain;
pub(crate) mod grobner_preprocess;
pub(crate) mod incremental_cad;
pub(crate) mod inprocessing;
pub mod interval_set;
pub(crate) mod lemma;
pub(crate) mod lookahead;
pub mod maxsat;
pub mod monotonicity;
pub mod nia;
pub mod portfolio;
pub(crate) mod proof;
pub mod restart;
pub(crate) mod root_hints;
pub mod simplify;
pub mod solver;
pub(crate) mod structure_analyzer;
pub(crate) mod subsumption;
pub(crate) mod symmetry;
pub(crate) mod theory_conflict;
pub mod types;
pub mod var_order;
pub(crate) mod vivification;

// Re-exports (public API). Only modules that are wired into the solver or are
// standalone user-facing entry points are re-exported here; see the module
// list above for why the rest are `pub(crate)`.
pub use cad::{
    CadCell, CadConfig, CadDecomposer, CadError, CadLifter, CadPoint, CadProjection, ProjectionSet,
    SampleStrategy, SturmSequence,
};
pub use maxsat::{MaxSatConfig, MaxSatResult, MaxSatSolver, MaxSatStats, SoftConstraint};
pub use nia::{BranchingStrategy, NiaConfig, NiaSolver, NiaStats, VarType};
// `cutting_planes` types are re-exported because they are part of the public
// `nia` configuration/statistics surface (see `nia::NiaConfig`).
pub use oxiz_math::lp::cutting_planes::{
    CutType, CuttingPlane, CuttingPlaneConfig, CuttingPlaneGenerator, CuttingPlaneStats,
};
pub use portfolio::{PortfolioConfig, PortfolioResult, PortfolioSolver, PortfolioStats};
pub use restart::{RestartManager, RestartStrategy};
pub use solver::NlsatSolver;
pub use var_order::{OrderingAnalyzer, OrderingStats, OrderingStrategy, VariableOrdering};
