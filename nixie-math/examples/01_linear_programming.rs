//! # Linear Programming Example
//!
//! This example demonstrates linear programming algorithms.
//! It covers:
//! - Simplex method (primal and dual)
//! - Feasibility checking
//! - Optimization (min/max)
//! - Sensitivity analysis
//! - Integer linear programming basics
//!
//! ## Linear Programming
//! Optimize a linear objective subject to linear constraints.
//! Forms the basis for LRA and LIA theory solving in SMT.
//!
//! ## Complexity
//! - Simplex: O(2^n) worst case, polynomial average
//! - Interior point: O(n^3.5) polynomial
//! - Branch-and-bound (ILP): Exponential
//!
//! ## See Also
//! - [`LPSolver`](nixie_math::lp_core::LPSolver)
//! - [`DualSimplexSolver`](nixie_math::lp::DualSimplexSolver)
//!
//! Note: This example is a placeholder. The full LP API is available in
//! nixie_math::lp and nixie_math::lp_core modules.

fn main() {
    println!("=== Nixie Math: Linear Programming ===\n");
    println!("Linear programming modules available:");
    println!("  - nixie_math::lp_core::LPSolver - Full LP solver");
    println!("  - nixie_math::lp::DualSimplexSolver - Dual simplex method");
    println!("  - nixie_math::lp::BranchCutSolver - Branch and cut (MIP)");
    println!("  - nixie_math::lp::CuttingPlaneGenerator - Cutting plane methods");
    println!("  - nixie_math::lp::FarkasGenerator - Infeasibility certificates");
    println!("\nSee the module documentation for detailed usage.");
}
