//! Search-shape diagnostics harness: parse + solve a DIMACS file with the
//! CaDiCaL preset and print the counters the studies in
//! `docs/studies/` compare (conflicts, decisions, propagations, restarts,
//! LBD average, per-mode ticks, stabilization switches, reason origins).
//!
//! Environment knobs (all optional):
//!   SEED=N              seed the solver PRNG (`Solver::set_random_seed`)
//!   OXIZ_REASON_STATS=1 count BCP reasons by clause origin (learned/original)
//!   NO_REDUCE=1         disable scheduled clause-database reduction
//!   NO_STAB=1           disable stable/focused alternation
//!   STAB_BASE=N         override `stabilize_base`
//! Study arms (`OXIZ_CADICAL_REDUCE`, `OXIZ_STAB_FAITHFUL`, ...) are read
//! directly by the solver; see their docs in `lib.rs`.
//!
//! ```text
//! cargo run --release --example stats_solve -- path/to/file.cnf
//! ```

use oxiz_sat::{ConfigPreset, DimacsParser, Solver};
fn main() {
    let path = std::env::args().nth(1).expect("path");
    let mut parser = DimacsParser::new();
    let mut cfg = ConfigPreset::CaDiCaL.config();
    if std::env::var("NO_REDUCE").is_ok() {
        cfg.clause_deletion_threshold = usize::MAX;
    }
    if std::env::var("NO_STAB").is_ok() {
        cfg.enable_stabilize = false;
    }
    if std::env::var("REPHASE").as_deref() == Ok("0") {
        cfg.rephase_interval = 0;
    }
    if let Ok(v) = std::env::var("RANDPOL")
        && let Ok(p) = v.parse::<f64>()
    {
        cfg.random_polarity_prob = p;
    }
    if let Ok(v) = std::env::var("RANDPOL_STABLE")
        && let Ok(p) = v.parse::<f64>()
    {
        cfg.random_polarity_prob_stable = Some(p);
    }
    if let Ok(v) = std::env::var("STAB_BASE")
        && let Ok(n) = v.parse::<u64>()
    {
        cfg.stabilize_base = n;
    }
    let mut solver = Solver::with_config(cfg);
    if let Ok(v) = std::env::var("MAXC")
        && let Ok(n) = v.parse::<u64>()
    {
        solver.set_max_conflicts(Some(n));
    }
    if let Ok(sd) = std::env::var("SEED") {
        solver.set_random_seed(sd.parse::<u64>().unwrap_or(0));
    }
    parser.parse_file(&path, &mut solver).expect("parse ok");
    if let Ok(path) = std::env::var("PHASE_HINT") {
        // cadical model file: `v 1 -2 3 ...` lines.  Index 0 unused.
        if let Ok(txt) = std::fs::read_to_string(&path) {
            let nv = solver.num_vars();
            let mut hint = vec![false; nv + 1];
            for tok in txt.split_whitespace() {
                if let Ok(lit) = tok.parse::<i64>() {
                    // DIMACS literals are 1-based; the phase arrays are
                    // indexed by 0-based `Var::index()`.
                    let v = lit.unsigned_abs() as usize;
                    if v >= 1 && v - 1 < hint.len() {
                        hint[v - 1] = lit > 0;
                    }
                }
            }
            solver.set_phase_hint(&hint);
        }
    }
    let r = solver.solve();
    let s = solver.stats();
    println!("result={r:?}");
    if std::env::var("OXIZ_REASON_STATS").is_ok() {
        let l = oxiz_sat::DIAG_REASON_LEARNED.load(std::sync::atomic::Ordering::Relaxed);
        let o = oxiz_sat::DIAG_REASON_ORIGINAL.load(std::sync::atomic::Ordering::Relaxed);
        let tot = l + o;
        if tot > 0 {
            println!(
                "reason_origins: learned={} original={} learned_share={:.1}%",
                l,
                o,
                100.0 * l as f64 / tot as f64
            );
        }
    }
    println!(
        "conflicts={} decisions={} propagations={} restarts={} (stable {})",
        s.conflicts, s.decisions, s.propagations, s.restarts, s.restarts_stable
    );
    println!(
        "learned={} deleted={} net_db={}",
        s.learned_clauses,
        s.deleted_clauses,
        s.learned_clauses.saturating_sub(s.deleted_clauses)
    );
    let avg_lbd = if s.learned_clauses > 0 {
        s.total_lbd as f64 / s.learned_clauses as f64
    } else {
        0.0
    };
    println!(
        "avg_lbd={:.2} chrono_bt={} non_chrono_bt={}",
        avg_lbd, s.chrono_backtracks, s.non_chrono_backtracks
    );
    let (tf, ts) = solver.search_ticks();
    println!(
        "ticks: focused={} stable={} total={} per_conflict={:.0}",
        tf,
        ts,
        tf + ts,
        (tf + ts) as f64 / s.conflicts.max(1) as f64
    );
    println!(
        "stable_conflicts={} reused_trails={} stabphases={}",
        s.stable_conflicts,
        s.reused_trails,
        solver.stabilization_phases()
    );
    let scan = oxiz_sat::DIAG_VMTF_SCAN.load(std::sync::atomic::Ordering::Relaxed);
    if scan > 0 {
        println!(
            "vmtf_scan_total={} per_decision={:.2}",
            scan,
            scan as f64 / s.decisions.max(1) as f64
        );
    }
    println!(
        "subsumed_removed={} self_subsumed={} shrunken={}",
        s.subsumed_removed, s.self_subsumed, s.shrunken
    );
    println!(
        "bve_eliminated={} substitutions={} units={}",
        s.bve_eliminated, s.substitutions, s.unit_clauses
    );
}
