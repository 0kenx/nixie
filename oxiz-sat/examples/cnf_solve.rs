//! Minimal DIMACS CNF solver entry point.
//!
//! Parses a `.cnf` file with [`DimacsParser`], solves it, and prints the
//! standard `s SATISFIABLE` / `s UNSATISFIABLE` line (matching the output
//! convention used by CaDiCaL/MiniSAT, so results can be diffed directly).
//!
//! Defaults to the CaDiCaL preset (the strongest sound configuration:
//! Glucose-style stabilize restarts, inprocessing, rephase, probing). Pass
//! `PRESET=default` to recover the bare `SolverConfig::default()` baseline.
//!
//! Optional env overrides for A/B testing single files:
//!   PRESET=<name>   (cadical|default|industrial|glucose|...; wins over below)
//!   RESTART=luby|glucose|geometric|locallbd  INTERVAL=N  REUSE=0|1
//!   INPROCESS=0|1  BVE=0|1  EQUIV=0|1  STABLE=0|1  REPHASE=N  MAXC=N
//!
//! ```text
//! cargo run --release --example cnf_solve -- path/to/file.cnf
//! ```

use oxiz_sat::{ConfigPreset, DimacsParser, RestartStrategy, Solver, SolverConfig, SolverResult};

fn main() {
    let path = std::env::args().nth(1).unwrap_or_else(|| {
        eprintln!("usage: cnf_solve <file.cnf>");
        std::process::exit(2);
    });

    // Optional full-preset override (e.g. PRESET=cadical) takes precedence over
    // the individual RESTART/INPROCESS/... knobs below. Accepts lowercase names
    // matching the `ConfigPreset` variants.
    let preset_config = std::env::var("PRESET").ok().and_then(|s| {
        let s = s.trim().to_ascii_lowercase();
        let p = match s.as_str() {
            "default" => Some(ConfigPreset::Default),
            "industrial" => Some(ConfigPreset::Industrial),
            "random" => Some(ConfigPreset::Random),
            "cryptographic" => Some(ConfigPreset::Cryptographic),
            "hardware" => Some(ConfigPreset::Hardware),
            "aggressive" => Some(ConfigPreset::Aggressive),
            "conservative" => Some(ConfigPreset::Conservative),
            "glucose" => Some(ConfigPreset::Glucose),
            "minisat" => Some(ConfigPreset::MiniSat),
            "cadical" => Some(ConfigPreset::CaDiCaL),
            _ => None,
        };
        p.map(|preset| preset.config())
    });

    let mut config = if let Some(c) = preset_config {
        c
    } else {
        match std::env::var("RESTART").ok().as_deref() {
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
            _ => ConfigPreset::CaDiCaL.config(),
        }
    };
    if let Some(v) = std::env::var("INTERVAL").ok().filter(|s| !s.is_empty())
        && let Ok(n) = v.parse::<u64>()
    {
        config.restart_interval = n;
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
    if let Ok(v) = std::env::var("EQUIV") {
        config.enable_equiv_substitution = v != "0";
    }
    if let Ok(v) = std::env::var("BVE") {
        config.enable_bve = v != "0";
    }
    if let Ok(v) = std::env::var("STABLE") {
        config.enable_stabilize = v != "0";
    }
    if let Ok(v) = std::env::var("LUBYCAP")
        && let Ok(n) = v.parse::<u64>()
    {
        config.luby_cap = n;
    }
    if let Some(v) = std::env::var("LUCKY")
        .ok()
        .filter(|s| !s.is_empty())
        .as_deref()
    {
        // Lucky phases default to on (matching CaDiCaL); set LUCKY=0 to disable.
        config.enable_lucky = v != "0";
    }
    if let Some(v) = std::env::var("REPHASE").ok().filter(|s| !s.is_empty())
        && let Ok(n) = v.parse::<u64>()
    {
        config.rephase_interval = n;
    }

    let mut parser = DimacsParser::new();
    let mut solver = Solver::with_config(config);
    if let Some(v) = std::env::var("MAXC").ok().filter(|s| !s.is_empty())
        && let Ok(n) = v.parse::<u64>()
    {
        solver.set_max_conflicts(Some(n));
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
