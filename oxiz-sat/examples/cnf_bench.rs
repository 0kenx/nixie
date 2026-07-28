//! In-process CNF benchmark: solve every `.cnf` under a directory (recursively)
//! and report total/mean SOLVE time (parsing timed separately), so per-process
//! startup does not pollute the measurement. Also reports aggregate conflicts.
//!
//! ```text
//! cargo run --release --example cnf_bench -- /path/to/cnf/dir
//! ```

use oxiz_sat::{DimacsParser, RestartStrategy, Solver, SolverConfig, SolverResult};
use std::env;
use std::path::{Path, PathBuf};
use std::time::Instant;

fn walk(dir: &Path, out: &mut Vec<PathBuf>) {
    if let Ok(rd) = std::fs::read_dir(dir) {
        for e in rd.flatten() {
            let p = e.path();
            if p.is_dir() {
                walk(&p, out);
            } else if p.extension().and_then(|s| s.to_str()) == Some("cnf") {
                out.push(p);
            }
        }
    }
}

fn main() {
    let root = env::args().nth(1).unwrap_or_else(|| {
        eprintln!("usage: cnf_bench <dir>");
        std::process::exit(2);
    });

    let mut files = Vec::new();
    walk(Path::new(&root), &mut files);
    files.sort();

    // Optional restart-strategy override (RESTART=luby|glucose|geometric|locallbd)
    // and rephase-interval override (REPHASE=N, 0 disables) for A/B comparisons.
    let mut base_config = match std::env::var("RESTART").ok().as_deref() {
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
    if let Ok(v) = std::env::var("REPHASE") {
        if let Ok(n) = v.parse::<u32>() {
            base_config.rephase_interval = n;
        }
    }
    if let Ok(v) = std::env::var("REUSE") {
        base_config.reuse_trail = v != "0";
    }
    if let Ok(v) = std::env::var("INPROCESS") {
        base_config.enable_inprocessing = v != "0";
    }
    if let Ok(v) = std::env::var("EQUIV") { base_config.enable_equiv_substitution = v != "0"; }
    if let Ok(v) = std::env::var("BVE") { base_config.enable_bve = v != "0"; }
    if let Ok(v) = std::env::var("CHRONO") {
        base_config.enable_chronological_backtrack = v != "0";
    }
    if let Ok(v) = std::env::var("STABLE") {
        base_config.enable_stabilize = v != "0";
    }
    if let Ok(v) = std::env::var("LUBYCAP") {
        if let Ok(n) = v.parse::<u64>() {
            base_config.luby_cap = n;
        }
    }
    if let Ok(v) = std::env::var("INTERVAL") {
        if let Ok(n) = v.parse::<u64>() {
            base_config.restart_interval = n;
        }
    }
    eprintln!(
        "restart={:?} rephase_interval={}",
        base_config.restart_strategy, base_config.rephase_interval
    );

    let mut total_solve_ns: u128 = 0;
    let mut total_parse_ns: u128 = 0;
    let mut conflicts: u64 = 0;
    let mut decisions: u64 = 0;
    let mut propagations: u64 = 0;
    let mut restarts: u64 = 0;
    let mut minimizations: u64 = 0;
    let mut literals_removed: u64 = 0;
    let mut learned_clauses: u64 = 0;
    let mut deleted_clauses: u64 = 0;
    let mut total_lbd: u64 = 0;
    let mut n = 0usize;
    let mut sat = 0usize;
    let mut unsat = 0usize;

    for f in &files {
        let mut parser = DimacsParser::new();
        let mut solver = Solver::with_config(base_config.clone());

        let t0 = Instant::now();
        if let Err(e) = parser.parse_file(f, &mut solver) {
            eprintln!("skip {}: {e}", f.display());
            continue;
        }
        total_parse_ns += t0.elapsed().as_nanos();

        let t1 = Instant::now();
        let r = solver.solve();
        total_solve_ns += t1.elapsed().as_nanos();

        let s = solver.stats();
        conflicts += s.conflicts;
        decisions += s.decisions;
        propagations += s.propagations;
        restarts += s.restarts;
        minimizations += s.minimizations;
        literals_removed += s.literals_removed;
        learned_clauses += s.learned_clauses;
        deleted_clauses += s.deleted_clauses;
        total_lbd += s.total_lbd;

        match r {
            SolverResult::Sat => sat += 1,
            SolverResult::Unsat => unsat += 1,
            SolverResult::Unknown => {}
        }
        n += 1;
    }

    let solve_ms = total_solve_ns as f64 / 1e6;
    let parse_ms = total_parse_ns as f64 / 1e6;
    eprintln!(
        "files={n} sat={sat} unsat={unsat} | parse={parse_ms:.1}ms solve={solve_ms:.1}ms \
         (mean {:.3}ms/file) | conflicts={conflicts} decisions={decisions} propagations={propagations} \
         ({:.2}M props/s) | restarts={restarts} learned={learned_clauses} \
         minizm={minimizations} lits_removed={literals_removed} avg_lbd={:.2} alive_learned={}",
        solve_ms / n.max(1) as f64,
        propagations as f64 / (solve_ms / 1000.0).max(1e-9) / 1e6,
        total_lbd as f64 / learned_clauses.max(1) as f64,
        learned_clauses.saturating_sub(deleted_clauses)
    );
}
