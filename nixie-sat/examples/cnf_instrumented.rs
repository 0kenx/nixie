//! Instrumented DIMACS solver: solves a CNF and prints solver stats.
//!
//! Supports `PRESET=name` plus the same env overrides as `cnf_solve`, and prints
//! decisions / propagations / conflicts / restarts / learnt-clause counts, used
//! to separate *search quality* (conflicts needed) from *raw speed*
//! (propagations/sec).
use nixie_sat::{ConfigPreset, DimacsParser, RestartStrategy, Solver, SolverConfig, SolverResult};
use std::time::Instant;

fn env_bool(k: &str) -> Option<bool> {
    std::env::var(k).ok().map(|v| v != "0")
}
fn env_u64(k: &str) -> Option<u64> {
    std::env::var(k).ok().and_then(|v| v.parse().ok())
}
fn env_f64(k: &str) -> Option<f64> {
    std::env::var(k).ok().and_then(|v| v.parse().ok())
}
fn env_usize(k: &str) -> Option<usize> {
    std::env::var(k).ok().and_then(|v| v.parse().ok())
}

fn main() {
    let path = std::env::args().nth(1).unwrap_or_else(|| {
        eprintln!("usage: cnf_instrumented <file.cnf>");
        std::process::exit(2);
    });

    let mut config = if let Some(p) = std::env::var("PRESET").ok().as_deref() {
        match p {
            "industrial" => ConfigPreset::Industrial.config(),
            "random" => ConfigPreset::Random.config(),
            "crypto" => ConfigPreset::Cryptographic.config(),
            "hardware" => ConfigPreset::Hardware.config(),
            "aggressive" => ConfigPreset::Aggressive.config(),
            "conservative" => ConfigPreset::Conservative.config(),
            "glucose" => ConfigPreset::Glucose.config(),
            "minisat" => ConfigPreset::MiniSat.config(),
            "cadical" => ConfigPreset::CaDiCaL.config(),
            _ => SolverConfig::default(),
        }
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
            _ => SolverConfig::default(),
        }
    };
    if let Some(v) = env_u64("INTERVAL") {
        config.restart_interval = v;
    }
    if let Some(v) = env_bool("REUSE") {
        config.reuse_trail = v;
    }
    if let Some(v) = env_bool("INPROCESS") {
        config.enable_inprocessing = v;
    }
    if let Some(v) = env_bool("EQUIV") {
        config.enable_equiv_substitution = v;
    }
    if let Some(v) = env_bool("BVE") {
        config.enable_bve = v;
    }
    if let Some(v) = env_bool("STABLE") {
        config.enable_stabilize = v;
    }
    if let Some(v) = env_u64("LUBYCAP") {
        config.luby_cap = v;
    }
    if let Some(v) = env_bool("LUCKY") {
        config.enable_lucky = v;
    }
    if let Some(v) = env_u64("REPHASE") {
        config.rephase_interval = v;
    }
    if let Some(v) = env_bool("VMTF") {
        config.use_vmtf = v;
    }
    if let Some(v) = env_bool("CHB") {
        config.use_chb_branching = v;
    }
    if let Some(v) = env_bool("LRB") {
        config.use_lrb_branching = v;
    }
    if let Some(v) = env_bool("CHRONO") {
        config.enable_chronological_backtrack = v;
    }
    if let Some(v) = env_bool("PROBE") {
        config.enable_failed_literal_probing = v;
    }
    if let Some(v) = env_bool("HYPER") {
        config.enable_hyper_binary_probing = v;
    }
    if let Some(v) = env_usize("DELTHRESH") {
        config.clause_deletion_threshold = v;
    }
    if let Some(v) = env_f64("VARDECAY") {
        config.var_decay = v;
    }
    if let Some(v) = env_f64("RANDOMPOL") {
        config.random_polarity_prob = v;
    }

    let mut parser = DimacsParser::new();
    let mut solver = Solver::with_config(config);
    if let Some(n) = env_u64("MAXC") {
        solver.set_max_conflicts(Some(n));
    }
    if let Err(e) = parser.parse_file(&path, &mut solver) {
        eprintln!("parse error: {e}");
        std::process::exit(2);
    }

    let t0 = Instant::now();
    let res = solver.solve();
    let dt = t0.elapsed().as_secs_f64();
    let s = solver.stats();
    eprintln!(
        "stats decisions={dec} propagations={prop} conflicts={conf} restarts={rst} \
         learnt={lc} lits_removed={lr} chrono={ch} nonchrono={nch} avg_lbd={lbd:.2}",
        dec = s.decisions,
        prop = s.propagations,
        conf = s.conflicts,
        rst = s.restarts,
        lc = s.learned_clauses,
        lr = s.literals_removed,
        ch = s.chrono_backtracks,
        nch = s.non_chrono_backtracks,
        lbd = if s.conflicts > 0 {
            s.total_lbd as f64 / s.conflicts as f64
        } else {
            0.0
        },
    );
    eprintln!(
        "rate props/s={ps:.0} conf/s={cs:.0} dec/s={ds:.0} mpps={mpp:.2}M dt={dt:.3}s",
        ps = s.propagations as f64 / dt.max(1e-9),
        cs = s.conflicts as f64 / dt.max(1e-9),
        ds = s.decisions as f64 / dt.max(1e-9),
        mpp = s.propagations as f64 / dt.max(1e-9) / 1e6,
        dt = dt,
    );
    match res {
        SolverResult::Sat => println!("s SATISFIABLE"),
        SolverResult::Unsat => println!("s UNSATISFIABLE"),
        SolverResult::Unknown => println!("s UNKNOWN"),
    }
}
