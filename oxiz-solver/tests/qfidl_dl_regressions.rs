//! QF_IDL difference-logic regressions (2026-08 phantom-edge / scope-mark /
//! 1-UIP sweep).
//!
//! Each test pins one of the four defects fixed together in that sweep, on
//! the exact SMT-LIB instance that exposed it:
//!
//! 1. **Phantom dense edges** — the dense core was created lazily on first
//!    feed, so decision levels that preceded its creation never recorded a
//!    scope mark; a backtrack past that point hit `DenseDlCore::pop`'s
//!    no-mark early return and stranded every live edge as a permanent
//!    phantom constraint.  Symptom: unexplainable dense conflicts → the pure
//!    DL route broke purity and replayed into the simplex (DTP/queens:
//!    10s–2s where Z3 answers in 20–80ms).  Fix: eager creation in
//!    `DiffLogicSolver::with_config`.
//! 2. **Constraint wipe on routine backtrack** — `ConstraintGraph::push`
//!    initialized the new level's rollback mark to `0` instead of the
//!    current constraint count, so a pop to an add-less level truncated
//!    EVERYTHING, including level-0 facts.  Symptom: false `sat` on
//!    `qlock-4-10-11.base` once the sparse engine could own a verdict.
//!    Fix: mark starts at `constraints.len()`.
//! 3. **Scope-leak across push/pop** — `DiffLogicSolver::reset` did not
//!    clear the dense term map / sparse scratch together with the graph.
//! 4. **1-UIP under chronological backtracking** — the theory-conflict
//!    analysis walked the trail discharging its counter on ANY seen literal,
//!    not only conflict-level ones (the Boolean `analyze`'s
//!    `analyze_scan_pivot` guard exists for exactly this).  On non-level-
//!    sorted trails it terminated early and emitted an asserting literal at
//!    the backtrack level — `backtrack_level == uip level`, tripping the
//!    debug assert on `qlock-4-10-11.base` (debug) and corrupting the trail
//!    in release.  Fix: port the guard.
//!
//! These tests assert *verdicts against z3* and *time budgets* loose enough
//! for a loaded machine but far below the defective behavior (the defects
//! measured 10s timeout / wrong verdict).

use oxiz_solver::{Context, SolverResult};
use std::time::Instant;

fn solve_file(rel: &str, timeout_ms: u64) -> (SolverResult, std::time::Duration) {
    let path = concat!(env!("CARGO_MANIFEST_DIR"), "/../");
    let full = format!("{path}{rel}");
    let start = Instant::now();
    let Ok(script) = std::fs::read_to_string(&full) else {
        eprintln!("skipping {rel}: file not present (smt-lib not checked out?)");
        return (SolverResult::Unknown, start.elapsed());
    };
    let mut ctx = Context::new();
    ctx.set_timeout_ms(timeout_ms);
    let outputs = ctx.execute_script(&script).unwrap_or_default();
    let verdict = outputs
        .iter()
        .rev()
        .find_map(|tok| match tok.trim() {
            "sat" => Some(SolverResult::Sat),
            "unsat" => Some(SolverResult::Unsat),
            "unknown" => Some(SolverResult::Unknown),
            _ => None,
        })
        .unwrap_or(SolverResult::Unknown);
    (verdict, start.elapsed())
}

/// DTP family: 35 constants / 210 clauses — the dense-core route's home turf.
/// The phantom-edge defect timed this out (>10s); Z3 answers in 50ms.
/// Budget: 5s (≈100× headroom over the fixed ~30ms).
#[test]
fn qfidl_dtp_s1_dense_route_is_fast_and_correct() {
    let (res, elapsed) = solve_file(
        "smt-lib/non-incremental/QF_IDL/DTP/DTP_k2_n35_c210_s1.smt2",
        5_000,
    );
    assert_eq!(res, SolverResult::Sat, "z3 says sat");
    assert!(
        elapsed.as_secs() < 5,
        "dense route must solve DTP_s1 well inside the budget, took {elapsed:?}"
    );
}

/// Same family, UNSAT member (Z3: unsat in 49ms).
#[test]
fn qfidl_dtp_s14_unsat_is_fast_and_correct() {
    let (res, elapsed) = solve_file(
        "smt-lib/non-incremental/QF_IDL/DTP/DTP_k2_n35_c210_s14.smt2",
        5_000,
    );
    assert_eq!(res, SolverResult::Unsat, "z3 says unsat");
    assert!(
        elapsed.as_secs() < 5,
        "dense route must solve DTP_s14 well inside the budget, took {elapsed:?}"
    );
}

/// queens_bench: the eager-atom-interning regression (before it, CDCL
/// decided every atom by hand — 35k decisions where Z3's eagerly
/// internalized closure needs 66).  Z3: 78ms sat.
#[test]
fn qfidl_super_queen38_is_fast_and_correct() {
    let (res, elapsed) = solve_file(
        "smt-lib/non-incremental/QF_IDL/queens_bench/super_queen/super_queen38-1.smt2",
        10_000,
    );
    assert_eq!(res, SolverResult::Sat, "z3 says sat");
    assert!(
        elapsed.as_secs() < 10,
        "eager interning must keep super_queen38 inside the budget, took {elapsed:?}"
    );
}

/// qlock-4-10-11.base: the constraint-wipe false-`sat` regression.  Z3:
/// unsat in 281ms; the wipe made the pure sparse route answer `sat` on it.
/// Verdict-only (no time pin): the interest here is the UNSAT, not speed.
#[test]
fn qfidl_qlock_11_base_is_unsat() {
    let (res, _) = solve_file(
        "smt-lib/non-incremental/QF_IDL/qlock/qlock-4-10-11.base.cvc.smt2",
        20_000,
    );
    assert_ne!(
        res,
        SolverResult::Sat,
        "constraint-wipe regression: answered sat on a z3-UNSAT instance"
    );
    assert_eq!(
        res,
        SolverResult::Unsat,
        "qlock-4-10-11.base is unsat (z3); unknown/timeout is acceptable but weak"
    );
}

/// qlock-4-10-11.induction (Z3: sat): the sat-side member of the same
/// family — pins that the fixes did not overcorrect into a wrong `unsat`.
#[test]
fn qfidl_qlock_11_induction_is_sat() {
    let (res, _) = solve_file(
        "smt-lib/non-incremental/QF_IDL/qlock/qlock-4-10-11.induction.cvc.smt2",
        20_000,
    );
    assert_eq!(res, SolverResult::Sat, "z3 says sat");
}
