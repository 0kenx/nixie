//! DIMACS CNF solver entry point — the single merged harness.
//!
//! Parses a `.cnf` file with [`DimacsParser`], solves it, and prints the
//! standard `s SATISFIABLE` / `s UNSATISFIABLE` line (matching the output
//! convention used by CaDiCaL/MiniSAT, so results can be diffed directly).
//!
//! This example subsumes the three former entry points; their extra output
//! is opt-in behind env flags (debug/instrumentation is never on by
//! default — the plain run prints only the verdict line):
//!
//!   STATS=1   solver counters and rates on stderr after the solve
//!             (decisions/propagations/conflicts/restarts/learned clauses,
//!             props/s, sweep counters) — formerly `cnf_instrumented`.
//!   DIAG=1    full search-shape diagnostics on stdout — formerly
//!             `stats_solve`: `walk:` / `result=` / `conflicts=` lines,
//!             learned/net-db counts, avg LBD, per-mode ticks,
//!             stabilization phases, VMTF scan, subsumption/BVE counters.
//!             The `s <VERDICT>` line is suppressed in this mode so stdout
//!             stays byte-compatible with the former `stats_solve` harness
//!             (registered bench suites diff observed stdout against
//!             pinned control stdout; `result=` carries the verdict).
//!
//! Independent opt-in diagnostics (work with or without STATS/DIAG):
//!   PRINT_MODEL=1     print the model as `v <lit> ...` (DIMACS order)
//!   NIXIE_MEM_STATS=1 memory composition line (arena/watches/BIG)
//!   NIXIE_REASON_STATS=1  BCP reason-origin census (learned vs original)
//!   GATE_COUNT=1      print parse-time congruence-gate count and exit
//!   SCC_MASS=1        print binary-implication-graph SCC mass and exit
//!   PHASE_HINT=path   seed phases from a cadical `v ...` model file
//!   NIXIE_RELATION_FACTOR=0|1  apply the checked exact relation transform
//!                     in memory and validate SAT on the original CNF
//!   ELS_GATE_SRC=gates|hash + ELS_GATE_K=N   per-instance ELS gate
//!                     (the decision needs the parsed formula; requires
//!                     ELS=1 to arm the pass)
//!   NIXIE_CLAUSE_TRAFFIC=N  clause-ID cost census (needs
//!                     `--features clause-traffic`); JSON report on stderr
//!   NIXIE_WATCH_GROUPS=N    sampled watch-list probe (needs
//!                     `--features bcp-groups`); JSON report on stderr
//!   NIXIE_REGION_STATS=N    sampled region traffic (needs
//!                     `--features bcp-regions`); JSON report on stderr
//!   `--features bcp-work`  per-solver BCP work ledger (no runtime flag)
//!   `--features bcp-stats` + NIXIE_BCP_STATS=1  BCP anatomy counters
//!
//! Configuration knobs (all optional). Defaults to the CaDiCaL preset (the
//! strongest sound configuration: Glucose-style stabilize restarts,
//! inprocessing, rephase, probing). `PRESET=default` recovers the bare
//! `SolverConfig::default()` baseline the former `cnf_instrumented` used:
//!   PRESET=<name>  default|industrial|random|cryptographic|crypto|hardware|
//!                  aggressive|conservative|glucose|minisat|cadical
//!                  (unknown tokens are a hard error)
//!   RESTART=luby|glucose|geometric|locallbd
//!                  strategy override applied on top of the chosen base;
//!                  the interval-scheduled strategies disable the
//!                  stabilize schedule (the stable/focused restart path
//!                  implements Glucose+reluctant and never consults
//!                  `restart_strategy`, so luby/geometric/locallbd would
//!                  otherwise be silently inert). Unknown tokens are a
//!                  hard error. INTERVAL drives the interval strategies'
//!                  schedule.
//!   INTERVAL=N  REUSE=0|1  INPROCESS=0|1  EQUIV=0|1  BVE=0|1
//!   PROBING=0|1 (both probes)  PROBE=0|1 (failed-literal only)
//!   HYPER=0|1 (hyper-binary only)  CHRONO=0|1
//!   VSIDS=0|1 (switches the preset's VMTF to VSIDS in both modes)
//!   VMTF=0|1  CHB=0|1  LRB=0|1  (VSIDS wins if both are given)
//!   STABLE=0|1  NO_STAB=1  STAB_BASE=N  LUBYCAP=N  LUCKY=0|1
//!   REPHASE=N (0 disables)  WALK=0|1
//!   RANDPOL=P  RANDOMPOL=P (alias; wins over RANDPOL)  RANDPOL_STABLE=P
//!   SAT_CACHING=0|1|2 (Z3 two-phase SAT-caching; 2 = matched null)
//!   DELTHRESH=N  VARDECAY=P
//! Study arms (formerly `stats_solve`; solver-side knobs like
//! NIXIE_FACTOR_SCHED are read directly by the solver):
//!   INPROC_INTERVAL=N (0 = u64::MAX, mid-search rounds off)
//!   ELS=0|1  ELS_PRE=0|1 (pre-search ELS at full fixpoint effort)
//!   FACTOR=0|1 (quotient-chain factoring, the full kissat factor.c port)
//!   NIXIE_BVA_MID=0|1  NIXIE_BVA_MID_NULL=1 (matched null)
//!   NIXIE_ANDGATE=0|1  NIXIE_ANDGATE_NULL=1 (matched null)
//!   NO_REDUCE=1 (no scheduled reduction)  NO_PROBE=1 (both probes off)
//!   NO_BVE=1 (BVE and ELS off)  NO_ELIM=1 (mid-search elimination off)
//! Portfolio mode (kissat-style seeded restarts + heterogeneous config
//! arms): `SEEDS` gives a comma-separated arm list, `ARM_CONFLICTS` a
//! per-arm conflict budget (single number = all arms, or a comma list
//! matching the arm count).  Arm tokens:
//!   `default`  default config, built-in seed
//!   `<n>`      default config, seed `n`
//!   `chrono`   default config + `chrono_reuse` (ungated) — the
//!              endurance-instance variant measured to solve 8 of the
//!              25 cadical-only standing losses while being
//!              corpus-negative as a *default* (standing-gap study):
//!              as a later portfolio arm it converts those wins at
//!              zero risk to files the default arm already solves.
//!              Optional seed suffix: `chrono:<n>`.
//!   `els`      default config + the scheduled equivalence-literal-
//!              substitution one-shot (`ELS=1` semantics) — the arm
//!              measured 0.349x conflicts on 6s167-opt whose static gates
//!              are falsified four ways. Optional seed suffix `els:<n>`.
//! Each arm is a FULL solve restart (fresh solver, same clauses): CDCL
//! cost is strongly seed- and config-dependent (measured spread on the
//! satcomp2024 timeout residue: same file 64G vs 524G vs TO>1.7T
//! instructions across seeds), so exhausting one trajectory's budget and
//! rolling a fresh one converts hard timeouts into solves.
//! Deterministic: the arm list and budgets are counters, never
//! wall-clock.  `Unsat`/`Sat` from any arm is a real verdict (verdicts
//! are arm-independent facts) and returns immediately; only budget
//! exhaustion advances to the next arm.  STATS/DIAG output prints per
//! arm in portfolio mode.
//!   MAXC=N  global conflict budget (per-arm budgets take the tighter of
//!           MAXC and their ARM_CONFLICTS entry); SEED=N per-invocation
//!           PRNG seed (an arm token's explicit seed wins). Both are hard
//!           errors when set to a non-number — a silently-ignored seed
//!           or budget makes "seeded" screens replicas (2026-09-07
//!           portfolio campaign lesson).
//!
//! ```text
//! cargo run --release --example cnf_solve -- path/to/file.cnf
//! ```

use nixie_sat::{ConfigPreset, DimacsParser, RestartStrategy, Solver, SolverResult};
use std::time::Instant;

#[path = "support/relation_input.rs"]
mod relation_input;
#[path = "support/relation_solve.rs"]
mod relation_solve;

fn env_bool(key: &str) -> Option<bool> {
    std::env::var(key).ok().map(|v| v != "0")
}

fn env_u64(key: &str) -> Option<u64> {
    std::env::var(key).ok().and_then(|v| v.trim().parse().ok())
}

fn env_usize(key: &str) -> Option<usize> {
    std::env::var(key).ok().and_then(|v| v.trim().parse().ok())
}

fn env_f64(key: &str) -> Option<f64> {
    std::env::var(key).ok().and_then(|v| v.trim().parse().ok())
}

/// Like [`env_u64`] but a *hard error* when set to a non-number: budgets
/// and seeds silently falling back to their default is exactly how the
/// replica-seed screen bug happened (a typo'd SEED replayed one arm).
fn env_u64_strict(key: &str) -> Option<u64> {
    match std::env::var(key) {
        Ok(v) if v.trim().is_empty() => None,
        Ok(v) => match v.trim().parse::<u64>() {
            Ok(n) => Some(n),
            Err(_) => {
                eprintln!("invalid {key}: expected u64, got {v:?}");
                std::process::exit(2);
            }
        },
        Err(_) => None,
    }
}

/// Base config plus every env knob shared by the three former entry
/// points. Knob order is fixed: base preset, restart strategy, shared
/// search-shape knobs, then the stats_solve study arms (the `NO_*` arms
/// come last so they can switch a knob back off).
fn config_from_env() -> nixie_sat::SolverConfig {
    // Base: explicit preset, else the CaDiCaL preset (the strongest sound
    // configuration). `PRESET=default` recovers the bare
    // `SolverConfig::default()` baseline. An unknown token is a hard
    // error, not a silent preset fallback.
    let preset_name = std::env::var("PRESET")
        .ok()
        .map(|s| s.trim().to_ascii_lowercase());
    let mut config = match preset_name.as_deref() {
        Some("default") => ConfigPreset::Default.config(),
        Some("industrial") => ConfigPreset::Industrial.config(),
        Some("random") => ConfigPreset::Random.config(),
        // `crypto` was the former `cnf_instrumented` spelling.
        Some("cryptographic") | Some("crypto") => ConfigPreset::Cryptographic.config(),
        Some("hardware") => ConfigPreset::Hardware.config(),
        Some("aggressive") => ConfigPreset::Aggressive.config(),
        Some("conservative") => ConfigPreset::Conservative.config(),
        Some("glucose") => ConfigPreset::Glucose.config(),
        Some("minisat") => ConfigPreset::MiniSat.config(),
        Some("cadical") => ConfigPreset::CaDiCaL.config(),
        Some(other) => {
            eprintln!(
                "unknown PRESET {other:?} (expected default|industrial|random|cryptographic|crypto|hardware|aggressive|conservative|glucose|minisat|cadical)"
            );
            std::process::exit(2);
        }
        None => ConfigPreset::CaDiCaL.config(),
    };

    // Restart strategy override on top of the chosen base. The interval-
    // scheduled strategies disable the stabilize schedule — the
    // stable/focused restart path implements Glucose+reluctant and never
    // consults `restart_strategy`, so `RESTART=luby/geometric/locallbd`
    // was silently inert on the preset (geo22 == geo200, 2026-09-07
    // campaign harness notes). An unknown token is a hard error, not a
    // silent preset fallback.
    match std::env::var("RESTART").ok().as_deref() {
        Some("luby") => {
            config.restart_strategy = RestartStrategy::Luby;
            config.enable_stabilize = false;
        }
        Some("geometric") => {
            config.restart_strategy = RestartStrategy::Geometric;
            config.enable_stabilize = false;
        }
        Some("locallbd") => {
            config.restart_strategy = RestartStrategy::LocalLbd;
            config.enable_stabilize = false;
        }
        Some("glucose") => {
            config.restart_strategy = RestartStrategy::Glucose;
        }
        Some(other) => {
            eprintln!(
                "unknown RESTART strategy {other:?} (expected luby|glucose|geometric|locallbd)"
            );
            std::process::exit(2);
        }
        None => {}
    }

    // Base restart interval. Only the interval-scheduled strategies read
    // it as their schedule (luby/geometric — which disable stabilize, see
    // RESTART above); for glucose it is the minimum restart gap of the
    // non-stabilize path.
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
    // Pre-search probing bundle (failed-literal + hyper-binary): the
    // CaDiCaL preset enables both, bare Default neither — the 2026-09-07
    // preset-ablation arm isolates which carries the tail-class swings.
    // PROBING toggles both; PROBE/HYPER (the former cnf_instrumented
    // spellings) toggle one each and apply after the bundle.
    if let Some(v) = env_bool("PROBING") {
        config.enable_failed_literal_probing = v;
        config.enable_hyper_binary_probing = v;
    }
    if let Some(v) = env_bool("PROBE") {
        config.enable_failed_literal_probing = v;
    }
    if let Some(v) = env_bool("HYPER") {
        config.enable_hyper_binary_probing = v;
    }
    // Chronological backtracking A/B knob (cadical defaults it on; our
    // measurements elsewhere were neutral-to-slightly-negative — the
    // satcomp standing-gap study names it the cheap first trial for the
    // dense-3-CNF model-finding deficit, where cadical runs 26 %
    // chronological).
    if let Some(v) = env_bool("CHRONO") {
        config.enable_chronological_backtrack = v;
    }
    // Fine-grained branching toggles first, then the VSIDS bundle arm for
    // the decision-quality study (VSIDS=1 switches the preset's VMTF to
    // VSIDS in BOTH stable and focused modes — the standing-gap study's
    // dec/conf deficit: 5.1 vs cadical's 3.1 with schedule-level
    // behaviour otherwise matched), so an explicit VSIDS wins.
    if let Some(v) = env_bool("VMTF") {
        config.use_vmtf = v;
    }
    if let Some(v) = env_bool("CHB") {
        config.use_chb_branching = v;
    }
    if let Some(v) = env_bool("LRB") {
        config.use_lrb_branching = v;
    }
    if let Ok(v) = std::env::var("VSIDS") {
        config.use_vmtf = v == "0";
        if v != "0" {
            config.focused_vmtf = false;
            config.use_lrb_branching = false;
            config.use_chb_branching = false;
        }
    }
    if let Some(v) = env_bool("STABLE") {
        config.enable_stabilize = v;
    }
    if let Some(v) = env_u64("LUBYCAP") {
        config.luby_cap = v;
    }
    // Lucky phases default to on (matching CaDiCaL); set LUCKY=0 to disable.
    if let Some(v) = env_bool("LUCKY") {
        config.enable_lucky = v;
    }
    if let Some(v) = env_u64("REPHASE") {
        // REPHASE=0 disables (interval 0).
        config.rephase_interval = v;
    }
    if let Some(v) = env_bool("WALK") {
        config.walk = v;
    }
    // RANDOMPOL is the former cnf_instrumented spelling of RANDPOL; it
    // wins when both are set.
    if let Some(p) = env_f64("RANDPOL") {
        config.random_polarity_prob = p;
    }
    if let Some(p) = env_f64("RANDOMPOL") {
        config.random_polarity_prob = p;
    }
    if let Some(p) = env_f64("RANDPOL_STABLE") {
        config.random_polarity_prob_stable = Some(p);
    }
    if let Some(v) = std::env::var("SAT_CACHING")
        .ok()
        .and_then(|s| s.trim().parse::<u8>().ok())
    {
        config.sat_caching = v;
    }
    if let Some(v) = env_usize("DELTHRESH") {
        config.clause_deletion_threshold = v;
    }
    if let Some(v) = env_f64("VARDECAY") {
        config.var_decay = v;
    }
    if let Some(v) = env_u64("STAB_BASE") {
        config.stabilize_base = v;
    }

    // --- study arms (formerly stats_solve) ---
    // Mid-search BVA study knobs (2026-09-07 follow-up #0): ride the
    // inprocessing rounds; NIXIE_BVA_MID_NULL implies the treatment flag
    // (matched null — same generation/budgets/apply, scrambled rank).
    if let Some(v) = env_bool("NIXIE_BVA_MID") {
        config.enable_mid_bva = v;
    }
    if std::env::var("NIXIE_BVA_MID_NULL").is_ok() {
        config.enable_mid_bva = true;
        config.mid_bva_null = true;
    }
    // AND-gate factoring knobs (same study; independent arm).
    if let Some(v) = env_bool("NIXIE_ANDGATE") {
        config.enable_mid_andgate = v;
    }
    if std::env::var("NIXIE_ANDGATE_NULL").is_ok() {
        config.enable_mid_andgate = true;
        config.mid_andgate_null = true;
    }
    if let Some(v) = env_u64("INPROC_INTERVAL") {
        config.inprocessing_interval = if v == 0 { u64::MAX } else { v };
    }
    // ELS arm knobs for the 2026-09-05 study follow-up: ELS=1 enables the
    // pass (preset keeps it off); ELS_PRE=1 additionally moves the
    // extraction pre-search at full fixpoint effort (consumes the
    // mid-search one-shot).
    if let Some(v) = env_bool("ELS") {
        config.enable_equiv_substitution = v;
    }
    // Binary-chain factoring arm (2026-09-05 factor port A/B).
    if let Some(v) = env_bool("FACTOR") {
        config.enable_factoring = v;
    }
    if let Some(v) = env_bool("ELS_PRE") {
        config.enable_equiv_substitution = v;
        config.els_presearch = v;
    }
    // Diagnostic `NO_*` arms: switch knobs back off after everything
    // above, so e.g. `ELS=1 NO_BVE=1` runs with ELS off (stats_solve
    // semantics).
    if std::env::var("NO_REDUCE").is_ok() {
        config.clause_deletion_threshold = usize::MAX;
    }
    if std::env::var("NO_PROBE").is_ok() {
        config.enable_failed_literal_probing = false;
        config.enable_hyper_binary_probing = false;
    }
    if std::env::var("NO_BVE").is_ok() {
        config.enable_bve = false;
        config.enable_equiv_substitution = false;
    }
    if std::env::var("NO_ELIM").is_ok() {
        // Diagnostic arm: keep the pre-search elimination fixpoint, disable
        // the *scheduled* mid-search rounds (memory-composition studies).
        config.elim_interval = u64::MAX;
    }
    if std::env::var("NO_STAB").is_ok() {
        config.enable_stabilize = false;
    }
    config
}

/// Former `cnf_instrumented` output: solver counters and rates on stderr,
/// used to separate *search quality* (conflicts needed) from *raw speed*
/// (propagations/sec). Informational only — wall time is never a policy
/// input (see docs/BENCHMARKING.md).
fn print_stats_block(solver: &Solver, dt: f64) {
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
    // Sweep-port counters (kitten sweep A/B; see solver/sweep.rs).
    if s.kitten_solved > 0 || s.sweep_rounds > 0 {
        eprintln!(
            "sweep rounds={} swept={} solved={} kitten_solved={} ticks={} eq={} units={} \
             merged-vars(env)={} lemmas_dropped={}",
            s.sweep_rounds,
            s.sweep_swept,
            s.sweep_solved,
            s.kitten_solved,
            s.kitten_ticks,
            s.sweep_equivalences,
            s.sweep_units,
            s.sweep_variables,
            s.sweep_lemmas_dropped,
        );
    }
}

/// Former `stats_solve` output: the search-shape diagnostics block the
/// studies in `docs/studies/` compare (conflicts, decisions,
/// propagations, restarts, LBD average, per-mode ticks, stabilization
/// switches, reason origins). Byte-compatible with the former harness.
fn print_diag_block(solver: &Solver, result: SolverResult) {
    let s = solver.stats();
    {
        let w = solver.walk_counters();
        println!(
            "walk: count={} flips={} minimum={} broken={} ticks={}",
            w.count, w.flips, w.minimum, w.broken, w.ticks
        );
    }
    println!("result={result:?}");
    if std::env::var("NIXIE_MEM_STATS").is_ok() {
        let mc = solver.memory_composition();
        println!(
            "memstat arena={}/{}B waste={}B refs={}B watch={}/{}B moves={}B big={}/{}B compactions={}",
            mc.arena_used_bytes,
            mc.arena_capacity_bytes,
            mc.arena_wasted_bytes,
            mc.refs_bytes,
            mc.watch_bytes,
            mc.watch_capacity_bytes,
            mc.watch_move_capacity_bytes,
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
        "avg_lbd={avg_lbd:.2} chrono_bt={} non_chrono_bt={}",
        s.chrono_backtracks, s.non_chrono_backtracks
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

/// `v <lit> ...` line (DIMACS order), for external model validation in
/// the A/B harnesses.
fn print_model_line(solver: &Solver) {
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

fn main() {
    let path = std::env::args().nth(1).unwrap_or_else(|| {
        eprintln!("usage: cnf_solve <file.cnf>");
        std::process::exit(2);
    });

    // Output modes (see module docs). In DIAG mode the `s <VERDICT>` line
    // is suppressed so stdout stays byte-compatible with the former
    // stats_solve harness (registered suites diff against pinned stdout).
    let stats_mode = env_bool("STATS").unwrap_or(false);
    let diag_mode = env_bool("DIAG").unwrap_or(false);

    let config = config_from_env();

    // Study-A gate (2026-09-06, docs/studies/2026-09-06-els-gate-density-study.md):
    // "ELS fires iff a per-instance scalar crosses K". The scalar's source
    // is the semantic content under test: `gates` (congruence-gate count,
    // the treatment) or `hash` (sha256 of the instance file, the matched
    // null). K is chosen so both arms fire on the same number of corpus
    // files. The decision is made after parse (the gate count needs the
    // formula); requires `ELS=1` to arm the pass.
    let els_gate: Option<(String, u32)> =
        match (std::env::var("ELS_GATE_SRC"), std::env::var("ELS_GATE_K")) {
            (Ok(src), Ok(k)) => match k.parse::<u32>() {
                Ok(k) => Some((src, k)),
                Err(_) => {
                    eprintln!("ELS_GATE_K not a u32");
                    std::process::exit(2);
                }
            },
            _ => None,
        };

    let use_relations = match std::env::var("NIXIE_RELATION_FACTOR") {
        Ok(value) if value == "1" => true,
        Ok(value) if value == "0" => false,
        Err(std::env::VarError::NotPresent) => false,
        Ok(_) | Err(std::env::VarError::NotUnicode(_)) => {
            eprintln!("NIXIE_RELATION_FACTOR must be 0 or 1");
            std::process::exit(2);
        }
    };

    // Portfolio mode (see module docs).
    let parse_arm = |t: &str| -> (Option<u64>, bool, bool) {
        let t = t.trim();
        if t.is_empty() || t == "default" {
            return (None, false, false);
        }
        if let Some(rest) = t.strip_prefix("chrono") {
            let seed = rest
                .strip_prefix(':')
                .and_then(|s| s.trim().parse::<u64>().ok());
            return (seed, true, false);
        }
        if let Some(rest) = t.strip_prefix("els") {
            // ELS portfolio arm (2026-09-07 campaign, T3 portfolio
            // conversion): default config + the scheduled equivalence-
            // literal-substitution one-shot (`ELS=1` semantics) — the arm
            // measured 0.349x conflicts on 6s167-opt whose static gates
            // are falsified four ways. Optional seed suffix `els:<n>`.
            let seed = rest
                .strip_prefix(':')
                .and_then(|s| s.trim().parse::<u64>().ok());
            return (seed, false, true);
        }
        (t.parse::<u64>().ok(), false, false)
    };
    let arms: Vec<(Option<u64>, bool, bool)> = match std::env::var("SEEDS") {
        Ok(v) if !v.trim().is_empty() => v.split(',').map(&parse_arm).collect(),
        _ => vec![(None, false, false)],
    };
    let arm_budgets: Vec<Option<u64>> = match std::env::var("ARM_CONFLICTS") {
        Ok(v) if v.contains(',') => v.split(',').map(|t| t.trim().parse().ok()).collect(),
        Ok(v) => {
            let n = v.parse().ok();
            arms.iter().map(|_| n).collect()
        }
        Err(_) => arms.iter().map(|_| None).collect(),
    };

    // Global conflict budget and per-invocation seed: hard errors on
    // non-numbers (see env_u64_strict).
    let maxc = env_u64_strict("MAXC");
    let env_seed = env_u64_strict("SEED");

    for (arm, (seed_token, chrono, els_arm)) in arms.iter().enumerate() {
        let mut arm_config = config.clone();
        if *chrono {
            arm_config.chrono_reuse = true;
            arm_config.chrono_reuse_after = 0;
        }
        if *els_arm {
            arm_config.enable_equiv_substitution = true;
        }
        let mut solver = Solver::with_config(arm_config);
        if let Some(n) = maxc {
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
        // Arm seed precedence: the arm token's explicit seed (e.g. `els:1`),
        // else the `SEED` env (per-invocation seed for single-arm runs and
        // for portfolio arms that do not pin one), else the solver default.
        let seed = (*seed_token).or(env_seed);
        if let Some(sd) = seed {
            solver.set_random_seed(sd);
        }

        // Sampled instrumentation is armed before the formula is loaded
        // (clause traffic / watch groups observe the whole run).
        #[cfg(feature = "clause-traffic")]
        let observe_traffic = match std::env::var("NIXIE_CLAUSE_TRAFFIC") {
            Ok(value) => match value.parse::<std::num::NonZeroU64>() {
                Ok(stride) => {
                    solver.enable_clause_traffic(stride);
                    true
                }
                Err(error) => {
                    eprintln!("invalid NIXIE_CLAUSE_TRAFFIC: {error}");
                    std::process::exit(2);
                }
            },
            Err(std::env::VarError::NotPresent) => false,
            Err(error) => {
                eprintln!("invalid NIXIE_CLAUSE_TRAFFIC: {error}");
                std::process::exit(2);
            }
        };
        #[cfg(feature = "bcp-groups")]
        let observe_groups = match std::env::var("NIXIE_WATCH_GROUPS") {
            Ok(value) => match value.parse::<std::num::NonZeroU64>() {
                Ok(stride) => {
                    solver.enable_watch_group_stats(stride);
                    true
                }
                Err(error) => {
                    eprintln!("invalid NIXIE_WATCH_GROUPS: {error}");
                    std::process::exit(2);
                }
            },
            Err(std::env::VarError::NotPresent) => false,
            Err(error) => {
                eprintln!("invalid NIXIE_WATCH_GROUPS: {error}");
                std::process::exit(2);
            }
        };

        // Load: either the checked relation-factorized form (validated
        // against the original CNF after a SAT verdict), or plain DIMACS.
        let original_for_validation = if use_relations {
            match relation_solve::load_file(&path, &mut solver) {
                Ok(prepared) => {
                    eprintln!(
                        "relation_factor: groups={} fallback={} input_clauses={} clauses={} literals={}",
                        prepared.groups,
                        prepared.fallback,
                        prepared.original_clauses(),
                        prepared.clauses,
                        prepared.literals
                    );
                    Some(prepared)
                }
                Err(error) => {
                    eprintln!("relation factorization failed: {error}");
                    std::process::exit(2);
                }
            }
        } else {
            let mut parser = DimacsParser::new();
            if let Err(e) = parser.parse_file(&path, &mut solver) {
                eprintln!("parse error: {e}");
                std::process::exit(2);
            }
            None
        };

        // Region snapshots need the loaded formula.
        #[cfg(feature = "bcp-regions")]
        let observe_regions = match std::env::var("NIXIE_REGION_STATS") {
            Ok(value) => match value.parse::<std::num::NonZeroU64>() {
                Ok(stride) => match solver.enable_region_stats(stride) {
                    Ok(()) => true,
                    Err(error) => {
                        eprintln!("region snapshot failed: {error}");
                        std::process::exit(2);
                    }
                },
                Err(error) => {
                    eprintln!("invalid NIXIE_REGION_STATS: {error}");
                    std::process::exit(2);
                }
            },
            Err(std::env::VarError::NotPresent) => false,
            Err(error) => {
                eprintln!("invalid NIXIE_REGION_STATS: {error}");
                std::process::exit(2);
            }
        };

        if let Some((src, k)) = &els_gate {
            // The gate scalar: congruence-gate count (treatment) or the
            // instance content hash (matched null — same threshold shape,
            // same firing count, no structural information).
            let scalar: u32 = match src.as_str() {
                "gates" => solver.detected_gate_count() as u32,
                "hash" => {
                    let mut h = 0u32;
                    if let Ok(bytes) = std::fs::read(&path) {
                        for b in bytes.iter().take(8) {
                            h = h.wrapping_mul(31).wrapping_add(*b as u32);
                        }
                    }
                    h % 1_000_000
                }
                other => {
                    eprintln!("unknown ELS_GATE_SRC {other}");
                    std::process::exit(2);
                }
            };
            let fires = scalar >= *k;
            solver.set_enable_equiv_substitution(fires);
            eprintln!("els_gate src={src} scalar={scalar} k={k} fires={fires}");
        }
        if std::env::var("GATE_COUNT").is_ok() {
            // Structural telemetry (2026-09-05 gate-gating study): gates found in
            // the parsed formula, before any preprocessing.  Print and exit —
            // the metric is available before any search.
            println!("gates={}", solver.detected_gate_count());
            return;
        }
        if std::env::var("SCC_MASS").is_ok() {
            // Structural telemetry (2026-09-07 ELS SCC-gate study): the
            // equivalence mass of the parse-time binary-implication graph.
            // The DIMACS bulk load defers BIG edges; materialize exactly what
            // `solve()` would build (deterministic, no pass execution), then
            // measure read-only.
            solver.finish_deferred_big();
            let (mass, mass3, largest) = solver.binary_scc_mass();
            println!(
                "scc_mass={mass} scc_mass3={mass3} scc_largest={largest} big_edges={} vars={}",
                solver.big_edge_count(),
                solver.num_vars()
            );
            return;
        }
        if let Ok(hint_path) = std::env::var("PHASE_HINT") {
            // cadical model file: `v 1 -2 3 ...` lines.  Index 0 unused.
            if let Ok(txt) = std::fs::read_to_string(&hint_path) {
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

        let t0 = Instant::now();
        let result = solver.solve();
        let dt = t0.elapsed().as_secs_f64();

        if let Some(original) = &original_for_validation
            && result == SolverResult::Sat
            && let Err(error) = original.verify_model(solver.model())
        {
            eprintln!("{error}");
            std::process::exit(2);
        }

        #[cfg(feature = "clause-traffic")]
        if observe_traffic && let Err(error) = solver.write_clause_traffic(std::io::stderr().lock())
        {
            eprintln!("writing clause traffic failed: {error}");
            std::process::exit(2);
        }
        #[cfg(feature = "bcp-regions")]
        if observe_regions && let Err(error) = solver.write_region_report(std::io::stderr().lock())
        {
            eprintln!("writing region observations failed: {error}");
            std::process::exit(2);
        }
        #[cfg(feature = "bcp-groups")]
        if observe_groups
            && let Err(error) = solver.write_watch_group_report(std::io::stderr().lock())
        {
            eprintln!("writing watch group observations failed: {error}");
            std::process::exit(2);
        }
        #[cfg(feature = "bcp-work")]
        {
            let work = &solver.stats().propagation_work;
            eprintln!(
                "bcp-work: {work:?} blocker_hits={} estimated_ticks={}",
                work.blocker_hits(),
                work.estimated_ticks()
            );
        }
        #[cfg(feature = "bcp-stats")]
        if nixie_sat::diag_bcp::enabled() {
            nixie_sat::diag_bcp::dump();
        }

        if result == SolverResult::Sat && std::env::var("PRINT_MODEL").is_ok() {
            print_model_line(&solver);
        }
        if stats_mode {
            print_stats_block(&solver, dt);
        }
        if diag_mode {
            print_diag_block(&solver, result);
        }
        if arms.len() > 1 {
            eprintln!(
                "c arm {arm} seed {} chrono={} els={} -> {result:?} (conflicts {})",
                seed.map_or_else(|| "default".to_string(), |s| s.to_string()),
                chrono,
                els_arm,
                solver.stats().conflicts,
            );
        }
        match result {
            SolverResult::Sat => {
                if !diag_mode {
                    println!("s SATISFIABLE");
                }
                return;
            }
            SolverResult::Unsat => {
                if !diag_mode {
                    println!("s UNSATISFIABLE");
                }
                return;
            }
            SolverResult::Unknown => continue,
        }
    }
    if !diag_mode {
        println!("s UNKNOWN");
    }
}
