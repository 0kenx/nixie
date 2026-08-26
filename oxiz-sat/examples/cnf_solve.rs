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
    // Chronological backtracking A/B knob (cadical defaults it on; our
    // measurements elsewhere were neutral-to-slightly-negative — the
    // satcomp standing-gap study names it the cheap first trial for the
    // dense-3-CNF model-finding deficit, where cadical runs 26 %
    // chronological).
    if let Ok(v) = std::env::var("CHRONO") {
        config.enable_chronological_backtrack = v != "0";
    }
    // Branching arm for the decision-quality study: VSIDS=1 switches the
    // preset's VMTF to VSIDS in BOTH stable and focused modes (the
    // standing-gap study's dec/conf deficit: 5.1 vs cadical's 3.1 with
    // schedule-level behaviour otherwise matched).
    if let Ok(v) = std::env::var("VSIDS") {
        config.use_vmtf = v == "0";
        if v != "0" {
            config.focused_vmtf = false;
            config.use_lrb_branching = false;
            config.use_chb_branching = false;
        }
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

    // Seed-portfolio mode (kissat-style seeded restarts): `SEEDS` gives a
    // comma-separated arm list (`default` keeps the built-in seed), and
    // `ARM_CONFLICTS` an optional per-arm conflict budget.  Each arm is a
    // FULL solve restart (fresh solver, same clauses, own seed): CDCL cost
    // is strongly seed-dependent (measured spread on the satcomp2024
    // timeout residue: same file 64G vs 524G vs TO>1.7T instructions
    // across seeds), so exhausting one trajectory's budget and rolling a
    // fresh one converts hard timeouts into solves.  Deterministic: the
    // arm list and budgets are counters, never wall-clock.
    // `Unsat`/`Sat` from any arm is a real verdict (SAT verdicts are
    // seed-independent facts) and returns immediately; only budget
    // exhaustion advances to the next arm.
    let seeds: Vec<Option<u64>> = match std::env::var("SEEDS") {
        Ok(v) if !v.trim().is_empty() => v
            .split(',')
            .map(|t| match t.trim() {
                "" | "default" => None,
                other => other.parse::<u64>().ok(),
            })
            .collect(),
        _ => vec![None],
    };
    let arm_conflicts: Option<u64> = std::env::var("ARM_CONFLICTS")
        .ok()
        .and_then(|v| v.parse().ok());

    for (arm, seed) in seeds.iter().enumerate() {
        let mut solver = Solver::with_config(config.clone());
        if let Some(v) = std::env::var("MAXC").ok().filter(|s| !s.is_empty())
            && let Ok(n) = v.parse::<u64>()
        {
            solver.set_max_conflicts(Some(n));
        }
        // Per-arm budget: the tighter of the global MAXC (if any) and
        // ARM_CONFLICTS.
        if let Some(arm_cap) = arm_conflicts {
            let cap = solver
                .max_conflicts()
                .map_or(arm_cap, |global| global.min(arm_cap));
            solver.set_max_conflicts(Some(cap));
        }
        if let Some(sd) = seed {
            solver.set_random_seed(*sd);
        }
        let mut parser = DimacsParser::new();
        if let Err(e) = parser.parse_file(&path, &mut solver) {
            eprintln!("parse error: {e}");
            std::process::exit(2);
        }
        let result = solver.solve();
        if seeds.len() > 1 {
            eprintln!(
                "c arm {arm} seed {} -> {result:?} (conflicts {})",
                seed.map_or_else(|| "default".to_string(), |s| s.to_string()),
                solver.stats().conflicts,
            );
        }
        match result {
            SolverResult::Sat => {
                println!("s SATISFIABLE");
                return;
            }
            SolverResult::Unsat => {
                println!("s UNSATISFIABLE");
                return;
            }
            SolverResult::Unknown => continue,
        }
    }
    println!("s UNKNOWN");
}
