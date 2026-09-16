//! `Solver::set_rng_seed` — reproducibility and variation guarantees.
//!
//! The benchmarking discipline (docs/BENCHMARKING.md) treats a single solve
//! of a chaotic CDCL system as one sample; seed replication needs a seed
//! knob, which was missing (a doc comment referenced a `set_rng_seed` that
//! did not exist). These tests pin the two properties the knob promises:
//!
//! * same seed ⇒ bit-identical trajectory (counters equal);
//! * different seeds ⇒ different trajectories (counters move), verdict
//!   unchanged on an instance both can decide.
//!
//! The instance is a deterministic in-test 3-CNF (LCG-generated), sized to
//! decide in milliseconds.

use nixie_sat::{DimacsParser, Solver, SolverConfig, SolverResult};
use std::io::Cursor;

/// Deterministic LCG 3-CNF: `vars` variables, `cls` clauses, ratio 4.0 —
/// inside the searchable band: real conflict work (~0.4 k conflicts) at
/// ~0.1 s per solve, and seed-sensitive (verified: seeds 1/2/3 give
/// 387/395/766 conflicts).  Sized deliberately below the phase-transition
/// blow-up so the pair of solves here stays milliseconds-scale.
fn lcg_cnf(seed: u64, vars: usize, cls: usize) -> String {
    let mut s = String::new();
    s.push_str(&format!("p cnf {vars} {cls}\n"));
    let mut x = seed
        .wrapping_mul(6364136223846793005)
        .wrapping_add(1442695040888963407);
    let mut next = |range: u64| {
        x = x
            .wrapping_mul(6364136223846793005)
            .wrapping_add(1442695040888963407);
        (x >> 33) % range
    };
    for _ in 0..cls {
        let a = next(vars as u64) as i64 + 1;
        let b = next(vars as u64) as i64 + 1;
        let c = next(vars as u64) as i64 + 1;
        let sa = if next(2) == 0 { 1 } else { -1 };
        let sb = if next(2) == 0 { 1 } else { -1 };
        let sc = if next(2) == 0 { 1 } else { -1 };
        s.push_str(&format!("{} {} {} 0\n", sa * a, sb * b, sc * c));
    }
    s
}

fn solve_with(seed: u64, text: &str) -> (SolverResult, u64, u64, u64) {
    let mut sat = Solver::with_config(SolverConfig::default());
    let mut parser = DimacsParser::new();
    parser
        .parse_reader(Cursor::new(text.as_bytes()), &mut sat)
        .unwrap_or_else(|e| panic!("parse: {e}"));
    sat.set_rng_seed(seed);
    let result = sat.solve();
    let st = sat.stats();
    (result, st.decisions, st.conflicts, st.propagations)
}

#[test]
fn same_seed_reproduces_the_same_trajectory() {
    let text = lcg_cnf(0x5DEECE66D, 160, 640);
    let a = solve_with(42, &text);
    let b = solve_with(42, &text);
    assert_eq!(a, b, "same seed must give bit-identical counters");
}

#[test]
fn different_seeds_move_the_trajectory() {
    let text = lcg_cnf(0x5DEECE66D, 160, 640);
    // Two seeds *occasionally* coincide on one formula (chaotic, not
    // bijective) — require that some pair from a small set differs.
    let mut any_differs = false;
    for (s1, s2) in [(1u64, 2u64), (3, 5), (7, 11), (13, 17)] {
        let a = solve_with(s1, &text);
        let b = solve_with(s2, &text);
        assert_eq!(a.0, b.0, "verdict must not depend on the seed here");
        if (a.1, a.2, a.3) != (b.1, b.2, b.3) {
            any_differs = true;
        }
    }
    assert!(
        any_differs,
        "seeds are supposed to reshape the trajectory — a knob that never \
         moves the counters cannot support seed replication"
    );
}

#[test]
fn restart_strategy_is_live_under_stabilization() {
    // 2026-09-16 wiring regression: `restart_strategy` was unreachable under
    // `enable_stabilize` (every preset sets it), making the whole knob facade.
    // It now selects the focused-mode firing rule. Glucose is the config
    // default and must keep the EMA rule; Luby must produce a *different*
    // trajectory (the legacy cadence) — identical counters would mean the
    // knob went inert again.
    // 300 vars / 1200 clauses (ratio 4.0): ~2-5 k conflicts — enough
    // restart activity for the strategies to diverge (verified: Glucose
    // 5516 vs Luby 2114 conflicts), solves in ~0.1 s.  The 160-var
    // instance above finishes in 25 conflicts without ever restarting.
    let text = lcg_cnf(99, 300, 1200);
    let glucose = solve_with_config_strategy(&text, nixie_sat::RestartStrategy::Glucose);
    let luby = solve_with_config_strategy(&text, nixie_sat::RestartStrategy::Luby);
    assert_eq!(
        glucose.0, luby.0,
        "verdict must not depend on the restart strategy here"
    );
    assert_ne!(
        (glucose.1, glucose.2),
        (luby.1, luby.2),
        "Luby vs Glucose must reshape the trajectory under stabilization — \
         identical counters mean `restart_strategy` is inert again"
    );
}

fn solve_with_config_strategy(
    text: &str,
    strategy: nixie_sat::RestartStrategy,
) -> (SolverResult, u64, u64) {
    use nixie_sat::{DimacsParser, Solver, SolverConfig};
    use std::io::Cursor;
    let cfg = SolverConfig {
        restart_strategy: strategy,
        ..SolverConfig::default()
    };
    let mut sat = Solver::with_config(cfg);
    let mut parser = DimacsParser::new();
    parser
        .parse_reader(Cursor::new(text.as_bytes()), &mut sat)
        .unwrap_or_else(|e| panic!("parse: {e}"));
    let result = sat.solve();
    let st = sat.stats();
    (result, st.decisions, st.conflicts)
}
