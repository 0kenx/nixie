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

use nixie_sat::{ConfigPreset, DimacsParser, RestartStrategy, Solver, SolverConfig, SolverResult};

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

    if std::env::var("WALK").as_deref() == Ok("0") {
        config.walk = false;
    }
    if let Ok(v) = std::env::var("RANDPOL")
        && let Ok(p) = v.parse::<f64>()
    {
        config.random_polarity_prob = p;
    }
    if let Ok(v) = std::env::var("RANDPOL_STABLE")
        && let Ok(p) = v.parse::<f64>()
    {
        config.random_polarity_prob_stable = Some(p);
    }
    if std::env::var("REPHASE").as_deref() == Ok("0") {
        config.rephase_interval = 0;
    }
    // Portfolio mode (kissat-style seeded restarts + heterogeneous config
    // arms): `SEEDS` gives a comma-separated arm list, `ARM_CONFLICTS` a
    // per-arm conflict budget (single number = all arms, or a comma list
    // matching the arm count).  Arm tokens:
    //   `default`  default config, built-in seed
    //   `<n>`      default config, seed `n`
    //   `chrono`   default config + `chrono_reuse` (ungated) — the
    //              endurance-instance variant measured to solve 8 of the
    //              25 cadical-only standing losses while being
    //              corpus-negative as a *default* (standing-gap study):
    //              as a later portfolio arm it converts those wins at
    //              zero risk to files the default arm already solves.
    //              Optional seed suffix: `chrono:<n>`.
    // Each arm is a FULL solve restart (fresh solver, same clauses): CDCL
    // cost is strongly seed- and config-dependent (measured spread on the
    // satcomp2024 timeout residue: same file 64G vs 524G vs TO>1.7T
    // instructions across seeds), so exhausting one trajectory's budget
    // and rolling a fresh one converts hard timeouts into solves.
    // Deterministic: the arm list and budgets are counters, never
    // wall-clock.  `Unsat`/`Sat` from any arm is a real verdict (verdicts
    // are arm-independent facts) and returns immediately; only budget
    // exhaustion advances to the next arm.
    let parse_arm = |t: &str| -> (Option<u64>, bool) {
        let t = t.trim();
        if t.is_empty() || t == "default" {
            return (None, false);
        }
        if let Some(rest) = t.strip_prefix("chrono") {
            let seed = rest
                .strip_prefix(':')
                .and_then(|s| s.trim().parse::<u64>().ok());
            return (seed, true);
        }
        (t.parse::<u64>().ok(), false)
    };
    let arms: Vec<(Option<u64>, bool)> = match std::env::var("SEEDS") {
        Ok(v) if !v.trim().is_empty() => v.split(',').map(&parse_arm).collect(),
        _ => vec![(None, false)],
    };
    let arm_budgets: Vec<Option<u64>> = match std::env::var("ARM_CONFLICTS") {
        Ok(v) if v.contains(',') => v.split(',').map(|t| t.trim().parse().ok()).collect(),
        Ok(v) => {
            let n = v.parse().ok();
            arms.iter().map(|_| n).collect()
        }
        Err(_) => arms.iter().map(|_| None).collect(),
    };

    for (arm, (seed, chrono)) in arms.iter().enumerate() {
        let mut arm_config = config.clone();
        if *chrono {
            arm_config.chrono_reuse = true;
            arm_config.chrono_reuse_after = 0;
        }
        let mut solver = Solver::with_config(arm_config);
        if let Some(v) = std::env::var("MAXC").ok().filter(|s| !s.is_empty())
            && let Ok(n) = v.parse::<u64>()
        {
            solver.set_max_conflicts(Some(n));
        }
        // Per-arm budget: the tighter of the global MAXC (if any) and this
        // arm's ARM_CONFLICTS entry.
        if let Some(Some(arm_cap)) = arm_budgets.get(arm).copied() {
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
        if arms.len() > 1 {
            eprintln!(
                "c arm {arm} seed {} chrono={} -> {result:?} (conflicts {})",
                seed.map_or_else(|| "default".to_string(), |s| s.to_string()),
                chrono,
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
