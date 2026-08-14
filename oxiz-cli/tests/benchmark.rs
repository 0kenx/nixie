//! Benchmark tests for oxiz CLI
//!
//! These tests measure performance characteristics of the CLI

mod common;

use std::env;
use std::fs;
use std::path::PathBuf;
use std::process::Command;
use std::time::Instant;

/// Get the path to the oxiz binary
fn oxiz_bin() -> PathBuf {
    PathBuf::from(env!("CARGO_BIN_EXE_oxiz"))
}

/// Create a temporary SMT2 file for testing.
///
/// See `tests/common/mod.rs` for why this is collision-proof by
/// construction (pid + per-process counter) rather than the fixed,
/// name-only path this used to build -- two concurrent runs of this same
/// binary (e.g. a debug and a release `cargo test` invocation overlapping)
/// previously raced on the identical path -- and why it cleans up on
/// `Drop` (including on panic).
fn create_temp_smt2(content: &str, name: &str) -> common::TempPath {
    common::TempPath::write(&format!("bench_{name}"), "smt2", content)
}

/// Wall-clock duration assertions in this file are flaky under shared-machine /
/// CI load (a loaded box can easily blow a 5s budget on an otherwise-instant
/// solve, with no bug involved). Gate them behind `OXIZ_TIMING_TESTS=1` so the
/// solve itself is still exercised by default; only opt in to the timing
/// assertion when explicitly requested (e.g. a dedicated perf-check CI job).
fn timing_asserts_enabled() -> bool {
    env::var("OXIZ_TIMING_TESTS").as_deref() == Ok("1")
}

/// Assert `elapsed` is under `budget_ms` when `enabled` is `true`; otherwise
/// a no-op except for always printing the elapsed time. Parameterized
/// (rather than reading the gate internally) so the gate's on/off behavior
/// can be unit-tested without mutating process-global environment state --
/// see `assert_within_budget` below and the tests at the bottom of this
/// file for why that mutation used to be a second, independent race.
fn assert_budget_gated(elapsed: std::time::Duration, budget_ms: u128, label: &str, enabled: bool) {
    println!("{label}: {elapsed:?} (budget {budget_ms}ms, timing asserts enabled: {enabled})");
    if enabled {
        assert!(
            elapsed.as_millis() < budget_ms,
            "{label} took too long: {elapsed:?}"
        );
    }
}

/// Assert `elapsed` is under `budget_ms`, but only when timing assertions are
/// enabled via `OXIZ_TIMING_TESTS=1`. Always prints the elapsed time either way.
fn assert_within_budget(elapsed: std::time::Duration, budget_ms: u128, label: &str) {
    assert_budget_gated(elapsed, budget_ms, label, timing_asserts_enabled());
}

#[test]
fn bench_simple_sat_problem() {
    let smt2_content = r#"
(set-logic QF_LIA)
(declare-const x Int)
(assert (= x 42))
(check-sat)
"#;

    let temp_file = create_temp_smt2(smt2_content, "simple_sat");

    let start = Instant::now();
    let output = Command::new(oxiz_bin())
        .arg(temp_file.to_str().unwrap())
        .arg("--quiet")
        .output()
        .expect("Failed to execute oxiz");
    let elapsed = start.elapsed();

    fs::remove_file(temp_file).ok();

    println!("Simple SAT problem took: {:?}", elapsed);
    assert!(output.status.success() || output.status.code() == Some(1));
    assert_within_budget(elapsed, 5000, "Simple SAT problem");
}

#[test]
fn bench_simple_unsat_problem() {
    let smt2_content = r#"
(set-logic QF_LIA)
(declare-const x Int)
(assert (= x 42))
(assert (= x 43))
(check-sat)
"#;

    let temp_file = create_temp_smt2(smt2_content, "simple_unsat");

    let start = Instant::now();
    let output = Command::new(oxiz_bin())
        .arg(temp_file.to_str().unwrap())
        .arg("--quiet")
        .output()
        .expect("Failed to execute oxiz");
    let elapsed = start.elapsed();

    fs::remove_file(temp_file).ok();

    println!("Simple UNSAT problem took: {:?}", elapsed);
    assert!(output.status.success() || output.status.code() == Some(1));
    assert_within_budget(elapsed, 5000, "Simple UNSAT problem");
}

#[test]
fn bench_boolean_logic() {
    let smt2_content = r#"
(set-logic QF_UF)
(declare-const p Bool)
(declare-const q Bool)
(declare-const r Bool)
(assert (or (and p q) (and (not p) r)))
(assert (not (and p r)))
(check-sat)
"#;

    let temp_file = create_temp_smt2(smt2_content, "boolean_logic");

    let start = Instant::now();
    let output = Command::new(oxiz_bin())
        .arg(temp_file.to_str().unwrap())
        .arg("--quiet")
        .output()
        .expect("Failed to execute oxiz");
    let elapsed = start.elapsed();

    fs::remove_file(temp_file).ok();

    println!("Boolean logic problem took: {:?}", elapsed);
    assert!(output.status.success() || output.status.code() == Some(1));
    assert_within_budget(elapsed, 5000, "Boolean logic problem");
}

#[test]
fn bench_multiple_assertions() {
    let smt2_content = r#"
(set-logic QF_LIA)
(declare-const x Int)
(declare-const y Int)
(declare-const z Int)
(assert (> x 0))
(assert (> y 0))
(assert (> z 0))
(assert (< (+ x y) 10))
(assert (< (+ y z) 10))
(assert (< (+ x z) 10))
(check-sat)
"#;

    let temp_file = create_temp_smt2(smt2_content, "multiple_assertions");

    let start = Instant::now();
    let output = Command::new(oxiz_bin())
        .arg(temp_file.to_str().unwrap())
        .arg("--quiet")
        .output()
        .expect("Failed to execute oxiz");
    let elapsed = start.elapsed();

    fs::remove_file(temp_file).ok();

    println!("Multiple assertions problem took: {:?}", elapsed);
    assert!(output.status.success() || output.status.code() == Some(1));
    assert_within_budget(elapsed, 5000, "Multiple assertions problem");
}

#[test]
fn bench_stats_output() {
    let smt2_content = r#"
(set-logic QF_LIA)
(declare-const x Int)
(assert (= x 42))
(check-sat)
"#;

    let temp_file = create_temp_smt2(smt2_content, "stats");

    let start = Instant::now();
    let output = Command::new(oxiz_bin())
        .arg(temp_file.to_str().unwrap())
        .arg("--stats")
        .arg("--time")
        .output()
        .expect("Failed to execute oxiz");
    let elapsed = start.elapsed();

    fs::remove_file(temp_file).ok();

    let stdout = String::from_utf8_lossy(&output.stdout);
    println!("Stats output problem took: {:?}", elapsed);
    println!("Stats output: {}", stdout);

    assert!(output.status.success() || output.status.code() == Some(1));
    assert!(
        stdout.contains("Statistics") || stdout.contains("Decisions"),
        "Expected statistics in output"
    );
}

#[test]
fn bench_json_output() {
    let smt2_content = r#"
(set-logic QF_LIA)
(declare-const x Int)
(assert (= x 42))
(check-sat)
"#;

    let temp_file = create_temp_smt2(smt2_content, "json");

    let start = Instant::now();
    let output = Command::new(oxiz_bin())
        .arg(temp_file.to_str().unwrap())
        .arg("--format")
        .arg("json")
        .output()
        .expect("Failed to execute oxiz");
    let elapsed = start.elapsed();

    fs::remove_file(temp_file).ok();

    let stdout = String::from_utf8_lossy(&output.stdout);
    println!("JSON output problem took: {:?}", elapsed);

    assert!(output.status.success() || output.status.code() == Some(1));
    assert!(stdout.contains("{") && stdout.contains("}"));
}

/// Regression test for the `OXIZ_TIMING_TESTS` gate: when disabled, a
/// wildly-over-budget duration must NOT panic – only the solve/output
/// assertions run.
///
/// This used to set/remove the real `OXIZ_TIMING_TESTS` process environment
/// variable via `env::set_var`/`env::remove_var` (`unsafe` as of the 2024
/// edition) to drive `timing_asserts_enabled()`. That variable is
/// process-global: under plain `cargo test` (as opposed to `cargo-nextest`,
/// which the old comment here assumed but which is not guaranteed for every
/// invocation of this suite), every `#[test]` in this binary runs as a
/// thread in one process, so this test toggling the var raced against every
/// other thread reading it -- including the benchmark tests above, whose
/// hardcoded timing budgets would then flip from advisory to enforced mid-run
/// under load. Testing the pure, parameterized `assert_budget_gated` directly
/// exercises the exact same gate logic without touching global state at all.
#[test]
fn timing_budget_is_opt_in_by_default() {
    // An absurdly long "elapsed" must not panic when the gate is off.
    let huge = std::time::Duration::from_secs(3600);
    assert_budget_gated(huge, 5000, "should not panic with gate off", false);
}

/// Regression test: when the gate is enabled, an over-budget duration DOES
/// panic, so the gate is not a no-op. See
/// `timing_budget_is_opt_in_by_default` above for why this no longer
/// mutates the real `OXIZ_TIMING_TESTS` environment variable.
#[test]
fn timing_budget_enforced_when_opted_in() {
    let huge = std::time::Duration::from_secs(3600);
    let result = std::panic::catch_unwind(|| {
        assert_budget_gated(huge, 5000, "over-budget duration", true);
    });
    assert!(
        result.is_err(),
        "assert_budget_gated should panic when over budget and the gate is on"
    );
}
