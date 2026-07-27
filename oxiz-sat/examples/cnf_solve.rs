//! Minimal DIMACS CNF solver entry point.
//!
//! Parses a `.cnf` file with [`DimacsParser`], solves it, and prints the
//! standard `s SATISFIABLE` / `s UNSATISFIABLE` line (matching the output
//! convention used by CaDiCaL/MiniSAT, so results can be diffed directly).
//!
//! Optional env overrides for A/B testing single files:
//!   RESTART=luby|glucose|geometric|locallbd  INTERVAL=N  REUSE=0|1
//!   REPHASE=N  MAXC=N (conflict limit → returns UNKNOWN if exceeded)
//!
//! ```text
//! cargo run --release --example cnf_solve -- path/to/file.cnf
//! ```

use oxiz_sat::{DimacsParser, RestartStrategy, Solver, SolverConfig, SolverResult};

fn main() {
    let path = std::env::args().nth(1).unwrap_or_else(|| {
        eprintln!("usage: cnf_solve <file.cnf>");
        std::process::exit(2);
    });

    let mut config = match std::env::var("RESTART").ok().as_deref() {
        Some("glucose") => SolverConfig {
            restart_strategy: RestartStrategy::Glucose,
            ..SolverConfig::default()
        },
        Some("geometric") => SolverConfig {
            restart_strategy: RestartStrategy::Geometric,
            ..SolverConfig::default()
        },
        Some("locallbd") => SolverConfig {
            restart_strategy: RestartStrategy::LocalLbd,
            ..SolverConfig::default()
        },
        _ => SolverConfig::default(),
    };
    if let Some(v) = std::env::var("INTERVAL").ok().filter(|s| !s.is_empty()) {
        if let Ok(n) = v.parse::<u64>() {
            config.restart_interval = n;
        }
    }
    if let Some(v) = std::env::var("REUSE")
        .ok()
        .filter(|s| !s.is_empty())
        .as_deref()
    {
        config.reuse_trail = v != "0";
    }
    if let Some(v) = std::env::var("INPROCESS")
        .ok()
        .filter(|s| !s.is_empty())
        .as_deref()
    {
        config.enable_inprocessing = v != "0";
    }
    if let Some(v) = std::env::var("LUCKY")
        .ok()
        .filter(|s| !s.is_empty())
        .as_deref()
    {
        config.enable_lucky = v != "0";
    }
    if let Some(v) = std::env::var("REPHASE").ok().filter(|s| !s.is_empty()) {
        if let Ok(n) = v.parse::<u32>() {
            config.rephase_interval = n;
        }
    }

    let mut parser = DimacsParser::new();
    let mut solver = Solver::with_config(config);
    if let Some(v) = std::env::var("MAXC").ok().filter(|s| !s.is_empty()) {
        if let Ok(n) = v.parse::<u64>() {
            solver.set_max_conflicts(Some(n));
        }
    }
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
