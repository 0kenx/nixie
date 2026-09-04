//! Difference Logic Theory Solver
//!
//! Implements efficient reasoning about difference constraints of the form:
//! - x - y ≤ c (non-strict)
//! - x - y < c (strict, converted to x - y ≤ c - 1 over the integers)
//!
//! # Algorithm
//!
//! Two engines (see `solver.rs` for the routing):
//!
//! * **Dense integer core** (`dense_core.rs`, Z3 `theory_dense_diff_logic`):
//!   incremental all-pairs shortest-path closure with occurrence-list theory
//!   propagation — the engine Z3 installs for dense difference logic
//!   (`setup_QF_IDL` with `st.is_dense()`).
//! * **Sparse graph** (`graph.rs` + `bellman_ford.rs`, Z3
//!   `theory_diff_logic`): constraint graph with seeded incremental SPFA
//!   over exact `Rational64` weights — used for QF_RDL and as the integer
//!   fallback outside the dense core's exactness envelope.
//!
//! Constraint graph semantics: variables are nodes; constraint `x - y ≤ c`
//! is the edge `(y → x)` with weight `c`. UNSAT iff a negative cycle exists;
//! a model is given by the shortest-path potentials.
//!
//! # Logics Supported
//!
//! - QF_IDL: Quantifier-Free Integer Difference Logic
//! - QF_RDL: Quantifier-Free Real Difference Logic
//!
//! # References
//!
//! - Cotton, S. & Maler, O. (2006). Fast and Flexible Difference Constraint
//!   Propagation
//! - Nieuwenhuis, R. & Oliveras, A. (2005). DPLL(T) with Exhaustive Theory
//!   Propagation
//! - de Moura, L. (2008). Dense difference logic (Z3 `theory_dense_diff_logic`)

#[allow(unused_imports)]
use crate::prelude::*;

mod bellman_ford;
mod dense_core;
mod graph;
mod solver;

pub use bellman_ford::{BellmanFord, BellmanFordResult, NegativeCycle, Spfa};
pub use dense_core::{DenseDlCore, DlAssert, DlPropagation};
pub use graph::{ConstraintGraph, DiffConstraint, DiffEdge, DiffVar};
pub use solver::{DiffLogicConfig, DiffLogicResult, DiffLogicSolver, DiffLogicStats};
