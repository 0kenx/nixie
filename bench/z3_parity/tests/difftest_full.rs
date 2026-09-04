//! Full differential-testing sweep entry point.
//!
//! Not run by a plain `cargo test` -- this keeps normal test runs fast and
//! keeps CI independent of having Z3 installed. Opt in explicitly:
//!
//! ```text
//! NIXIE_DIFFTEST=1 cargo test --test difftest_full -- --nocapture
//! ```
//!
//! Optional environment variables:
//!
//! - `NIXIE_DIFFTEST_CASES` (default `200`): number of generated cases per
//!   logic.
//! - `NIXIE_DIFFTEST_SEED` (default `42`): base PRNG seed. Each logic gets a
//!   distinct derived seed so the four sweeps don't share a case stream.
//!
//! This test self-skips (does not fail) both when `NIXIE_DIFFTEST` is unset
//! and when no `z3` binary is reachable on `PATH`, so it can never turn a
//! plain `cargo test` red and never requires Z3 to be present in CI.
//!
//! On a mismatch, the reproducing `.smt2` script for every failing case is
//! written under `std::env::temp_dir()/nixie_difftest_repro/` and its path
//! is printed in the panic message.

use nixie_z3_parity::difftest::{format_mismatch_report, run_cases, summarize};
use nixie_z3_parity::generator::Logic;
use nixie_z3_parity::z3_runner::is_z3_available;

fn env_u64(name: &str, default: u64) -> u64 {
    std::env::var(name)
        .ok()
        .and_then(|s| s.parse().ok())
        .unwrap_or(default)
}

#[test]
fn difftest_full_all_logics() {
    if std::env::var("NIXIE_DIFFTEST").ok().as_deref() != Some("1") {
        eprintln!(
            "skipping: set NIXIE_DIFFTEST=1 to run the full differential-testing sweep \
             (see tests/difftest_full.rs for details)"
        );
        return;
    }
    if !is_z3_available() {
        eprintln!("skipping: NIXIE_DIFFTEST=1 is set but no z3 binary was found on PATH");
        return;
    }

    let cases_per_logic = env_u64("NIXIE_DIFFTEST_CASES", 200);
    let base_seed = env_u64("NIXIE_DIFFTEST_SEED", 42);

    let mut total_agreed = 0usize;
    let mut total_skipped = 0usize;
    let mut all_mismatches = Vec::new();

    for (i, logic) in Logic::ALL.into_iter().enumerate() {
        // Derive a distinct per-logic seed from the shared base seed so the
        // four sweeps don't replay identical PRNG streams against
        // structurally different generators.
        let logic_seed = base_seed ^ ((i as u64 + 1).wrapping_mul(0x1000_0000_01B3));
        let outcomes = run_cases(logic, logic_seed, cases_per_logic)
            .unwrap_or_else(|e| panic!("failed to run differential cases for {logic}: {e:#}"));
        let summary = summarize(outcomes);
        println!(
            "{logic}: {} agreed, {} skipped (unknown/timeout/error), {} mismatch(es)",
            summary.agreed,
            summary.skipped,
            summary.mismatches.len()
        );
        total_agreed += summary.agreed;
        total_skipped += summary.skipped;
        all_mismatches.extend(summary.mismatches);
    }

    println!(
        "TOTAL: {total_agreed} agreed, {total_skipped} skipped, {} mismatch(es) across {} logics x {cases_per_logic} cases",
        all_mismatches.len(),
        Logic::ALL.len()
    );

    if !all_mismatches.is_empty() {
        panic!("{}", format_mismatch_report(&all_mismatches));
    }
}
