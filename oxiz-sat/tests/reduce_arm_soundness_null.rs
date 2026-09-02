//! Soundness regression: the cadical-reduce study arms once produced a
//! wrong UNSAT on this satisfiable instance through two independent leaks,
//! both in the reduce port's deletion of clauses the trail/BIG still
//! reference:
//!
//! 1. The reason-protection check read `lits[0]` only (valid for
//!    watch-propagated clauses, where propagate assigns `clause[0]`), but
//!    BIG-propagated binaries can have their implied literal at either
//!    position — the guard missed them and the clause was deleted while a
//!    trail literal still recorded it as reason.
//! 2. Deleting a binary without purging its implication-graph edges left a
//!    stale BIG edge that kept propagating implications of the deleted
//!    clause (the binary loop never consults the deleted flag) and
//!    re-recorded dead reasons.
//!
//! Reproducer: `constraints_17_0.4_1.sanitized.cnf` (SAT per z3 and kissat)
//! returned Unsat under `OXIZ_CADICAL_REDUCE_NULL=1` / `OXIZ_REDUCE_BY_USED=1`
//! / `OXIZ_REDUCE_ADAPT=1` before the fix (2026-09-02).
//!
//! The arms are env-gated through process-global `OnceLock`s, so each test
//! file is its own binary and each arm needs its own file: this one covers
//! the random-deletion null; siblings cover the other arms.

use oxiz_sat::{ConfigPreset, DimacsParser, Solver, SolverResult};

fn solve_with_env() -> SolverResult {
    let mut solver = Solver::with_config(ConfigPreset::CaDiCaL.config());
    let mut parser = DimacsParser::new();
    let path = concat!(
        env!("CARGO_MANIFEST_DIR"),
        "/tests/fixtures/constraints_17_0.4_1.sanitized.cnf"
    );
    parser.parse_file(path, &mut solver).expect("parse constraints_17");
    solver.solve()
}

#[test]
fn random_null_reduce_never_yields_wrong_unsat_on_constraints_17() {
    // Set before the solver first reads the flag (single test per binary).
    // SAFETY: single test in this binary and nextest runs each test in its
    // own process, so no other thread can observe the mutation; set before
    // the solver's OnceLock flag readers run.
    unsafe { std::env::set_var("OXIZ_CADICAL_REDUCE_NULL", "1"); }
    assert_eq!(solve_with_env(), SolverResult::Sat);
}
