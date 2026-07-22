//! Always-on differential-testing smoke test.
//!
//! Fixed seed, ~25 generated cases per logic (QF_LIA / QF_LRA / QF_BV /
//! QF_UF). Self-skips -- exactly like the plain OxiZ-vs-Z3 tests in
//! `src/z3_runner.rs` -- when no `z3` binary is reachable on `PATH`, so a
//! normal `cargo test` never fails in an environment without Z3. Whenever
//! Z3 *is* present (a dev machine, or a CI image that happens to bundle
//! it), this runs as a real regression check with no extra flags or
//! `--ignored` required.
//!
//! For a much larger sweep, opt into `tests/difftest_full.rs` via
//! `OXIZ_DIFFTEST=1`.

use oxiz_z3_parity::difftest::{format_mismatch_report, run_cases, summarize};
use oxiz_z3_parity::generator::Logic;
use oxiz_z3_parity::z3_runner::is_z3_available;

/// Fixed base seed for the smoke corpus: every case is fully reproducible
/// from `(logic, this seed's derivation)`, no wall-clock randomness.
const SMOKE_BASE_SEED: u64 = 0xC0FFEE;
const SMOKE_CASES_PER_LOGIC: u64 = 25;

fn run_smoke(logic: Logic, seed_offset: u64) {
    if !is_z3_available() {
        eprintln!(
            "skipping differential smoke test for {logic}: z3 not found on PATH (install Z3 to run this test)"
        );
        return;
    }

    let base_seed = SMOKE_BASE_SEED ^ seed_offset;
    let outcomes = run_cases(logic, base_seed, SMOKE_CASES_PER_LOGIC)
        .unwrap_or_else(|e| panic!("failed to run differential cases for {logic}: {e:#}"));
    let summary = summarize(outcomes);

    eprintln!(
        "{logic}: {} agreed, {} skipped (unknown/timeout/error), {} mismatch(es)",
        summary.agreed,
        summary.skipped,
        summary.mismatches.len()
    );

    if !summary.mismatches.is_empty() {
        panic!("{}", format_mismatch_report(&summary.mismatches));
    }
}

#[test]
fn difftest_smoke_qf_lia() {
    run_smoke(Logic::QfLia, 1);
}

#[test]
fn difftest_smoke_qf_lra() {
    run_smoke(Logic::QfLra, 2);
}

#[test]
fn difftest_smoke_qf_bv() {
    run_smoke(Logic::QfBv, 3);
}

#[test]
fn difftest_smoke_qf_uf() {
    run_smoke(Logic::QfUf, 4);
}
