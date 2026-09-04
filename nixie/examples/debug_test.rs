//! Regression example: verifies that a trivially unsatisfiable arithmetic
//! conjunction (`age >= 65 AND age < 18`) is correctly reported as `Unsat`.
//!
//! This was previously an orphaned file at the repository root
//! (`examples/debug_test.rs`) that was never compiled: the workspace root
//! is a virtual manifest with no `[package]`, so Cargo silently ignored it.
//! It now lives under the `nixie` crate's `examples/` directory where
//! `cargo run --example debug_test -p nixie` actually builds and runs it.

use nixie_core::TermManager;
use nixie_solver::{Solver, SolverResult};
use num_bigint::BigInt;

fn main() {
    let mut solver = Solver::new();
    solver.set_logic("QF_LIA");
    let mut tm = TermManager::new();

    // Create age variable
    let age = tm.mk_var("age", tm.sorts.int_sort);

    // age >= 65
    let val_65 = tm.mk_int(BigInt::from(65));
    let ge_65 = tm.mk_ge(age, val_65);

    // age < 18
    let val_18 = tm.mk_int(BigInt::from(18));
    let lt_18 = tm.mk_lt(age, val_18);

    // age >= 65 AND age < 18
    let conj = tm.mk_and([ge_65, lt_18]);

    solver.assert(conj, &mut tm);

    let result = solver.check(&mut tm);
    println!("Result: {:?}", result);
    println!("Expected: Unsat (contradiction)");

    match result {
        SolverResult::Sat => {
            eprintln!("PROBLEM: Solver returned SAT for age >= 65 AND age < 18");
            std::process::exit(1);
        }
        SolverResult::Unsat => println!("OK: Solver correctly returned UNSAT"),
        SolverResult::Unknown => {
            eprintln!("PROBLEM: Solver returned Unknown for a decidable QF_LIA instance");
            std::process::exit(1);
        }
    }
}
