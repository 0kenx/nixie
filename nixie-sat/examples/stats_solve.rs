//! Search-shape diagnostics harness: parse + solve a DIMACS file with the
//! CaDiCaL preset and print the counters the studies in
//! `docs/studies/` compare (conflicts, decisions, propagations, restarts,
//! LBD average, per-mode ticks, stabilization switches, reason origins).
//!
//! Environment knobs (all optional):
//!   SEED=N              seed the solver PRNG (`Solver::set_random_seed`)
//!   INPROCESS=0|1       flip `enable_inprocessing` (A/B arm for the
//!                       2026-09-04 standing-corpus inprocessing study)
//!   INPROC_INTERVAL=N   override `inprocessing_interval` (0 = u64::MAX,
//!                       i.e. mid-search rounds off; decomposition arm)
//!   ELS=0|1             flip `enable_equiv_substitution` (2026-09-05
//!                       study: the scheduled one-shot, measured 0.349x on
//!                       6s167-opt but -9 files at cap)
//!   ELS_PRE=0|1         pre-search ELS at full fixpoint effort (implies
//!                       ELS=1; consumes the mid-search one-shot)
//!   FACTOR=0|1          binary-chain factoring (kissat factor.c first
//!                       slice; the worker_550 lever)
//!   NIXIE_REASON_STATS=1 count BCP reasons by clause origin (learned/original)
//!   NO_REDUCE=1         disable scheduled clause-database reduction
//!   NO_STAB=1           disable stable/focused alternation
//!   STAB_BASE=N         override `stabilize_base`
//! Study arms (`NIXIE_CADICAL_REDUCE`, `NIXIE_STAB_FAITHFUL`, ...) are read
//! directly by the solver; see their docs in `lib.rs`.
//!
//! ```text
//! cargo run --release --example stats_solve -- path/to/file.cnf
//! ```

use nixie_sat::{ConfigPreset, DimacsParser, Solver};
fn main() {
    let path = std::env::args().nth(1).expect("path");
    let mut parser = DimacsParser::new();
    let mut cfg = ConfigPreset::CaDiCaL.config();
    if let Ok(v) = std::env::var("INPROCESS") {
        cfg.enable_inprocessing = v != "0";
    }
    if let Ok(v) = std::env::var("INPROC_INTERVAL")
        && let Ok(n) = v.parse::<u64>()
    {
        cfg.inprocessing_interval = if n == 0 { u64::MAX } else { n };
    }
    if let Ok(v) = std::env::var("ELS") {
        // ELS arm knobs for the 2026-09-05 study follow-up: ELS=1 enables
        // the pass (preset keeps it off); ELS_PRE=1 additionally moves the
        // extraction pre-search at full fixpoint effort (consumes the
        // mid-search one-shot).
        cfg.enable_equiv_substitution = v != "0";
    }
    if let Ok(v) = std::env::var("FACTOR") {
        // Binary-chain factoring arm (2026-09-05 factor port A/B).
        cfg.enable_factoring = v != "0";
    }
    if let Ok(v) = std::env::var("ELS_PRE") {
        cfg.enable_equiv_substitution = v != "0";
        cfg.els_presearch = v != "0";
    }
    if std::env::var("NO_REDUCE").is_ok() {
        cfg.clause_deletion_threshold = usize::MAX;
    }
    if std::env::var("NO_PROBE").is_ok() {
        cfg.enable_failed_literal_probing = false;
        cfg.enable_hyper_binary_probing = false;
    }
    if std::env::var("NO_BVE").is_ok() {
        cfg.enable_bve = false;
        cfg.enable_equiv_substitution = false;
    }
    if std::env::var("NO_ELIM").is_ok() {
        // Diagnostic arm: keep the pre-search elimination fixpoint, disable
        // the *scheduled* mid-search rounds (memory-composition studies).
        cfg.elim_interval = u64::MAX;
    }
    if std::env::var("NO_STAB").is_ok() {
        cfg.enable_stabilize = false;
    }
    if std::env::var("REPHASE").as_deref() == Ok("0") {
        cfg.rephase_interval = 0;
    }
    if std::env::var("WALK").as_deref() == Ok("0") {
        cfg.walk = false;
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
    if std::env::var("GATE_COUNT").is_ok() {
        // Structural telemetry (2026-09-05 gate-gating study): gates found in
        // the parsed formula, before any preprocessing.  Print and exit —
        // the metric is available before any search.
        println!("gates={}", solver.detected_gate_count());
        return;
    }
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
    if r == nixie_sat::SolverResult::Sat && std::env::var("PRINT_MODEL").is_ok() {
        // `v <lit> ...` lines (DIMACS order), for external model
        // validation in the A/B harnesses.
        let m = solver.model();
        let lits: Vec<String> = (1..m.len() + 1)
            .filter_map(|i| {
                let vi = i - 1;
                m.get(vi).map(|v| match v {
                    nixie_sat::LBool::True => format!("{i}"),
                    nixie_sat::LBool::False => format!("-{i}"),
                    _ => String::new(),
                })
            })
            .filter(|s| !s.is_empty())
            .collect();
        println!("v {}", lits.join(" "));
    }
    let s = solver.stats();
    {
        let w = solver.walk_counters();
        println!(
            "walk: count={} flips={} minimum={} broken={} ticks={}",
            w.count, w.flips, w.minimum, w.broken, w.ticks
        );
    }
    println!("result={r:?}");
    if std::env::var("NIXIE_MEM_STATS").is_ok() {
        let mc = solver.memory_composition();
        println!(
            "memstat arena={}/{}B waste={}B refs={}B watch={}/{}B big={}/{}B compactions={}",
            mc.arena_used_bytes,
            mc.arena_capacity_bytes,
            mc.arena_wasted_bytes,
            mc.refs_bytes,
            mc.watch_bytes,
            mc.watch_capacity_bytes,
            mc.big_edge_bytes,
            mc.big_capacity_bytes,
            mc.arena_compactions
        );
    }

    if std::env::var("NIXIE_REASON_STATS").is_ok() {
        let l = nixie_sat::DIAG_REASON_LEARNED.load(std::sync::atomic::Ordering::Relaxed);
        let o = nixie_sat::DIAG_REASON_ORIGINAL.load(std::sync::atomic::Ordering::Relaxed);
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
    let scan = nixie_sat::DIAG_VMTF_SCAN.load(std::sync::atomic::Ordering::Relaxed);
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
