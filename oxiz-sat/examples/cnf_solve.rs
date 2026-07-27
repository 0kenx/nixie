//! Minimal DIMACS CNF solver entry point.
//!
//! Parses a `.cnf` file with [`DimacsParser`], solves it, and prints the
//! standard `s SATISFIABLE` / `s UNSATISFIABLE` line (matching the output
//! convention used by CaDiCaL/MiniSAT, so results can be diffed directly).
//!
//! ```text
//! cargo run --release --example cnf_solve -- path/to/file.cnf
//! ```

use oxiz_sat::{DimacsParser, Solver, SolverResult};

fn main() {
    let path = std::env::args().nth(1).unwrap_or_else(|| {
        eprintln!("usage: cnf_solve <file.cnf>");
        std::process::exit(2);
    });

    let mut parser = DimacsParser::new();
    let mut solver = Solver::new();
    if let Err(e) = parser.parse_file(&path, &mut solver) {
        eprintln!("parse error: {e}");
        std::process::exit(2);
    }

    match solver.solve() {
        SolverResult::Sat => println!("s SATISFIABLE"),
        SolverResult::Unsat => println!("s UNSATISFIABLE"),
        SolverResult::Unknown => println!("s UNKNOWN"),
    }
}
