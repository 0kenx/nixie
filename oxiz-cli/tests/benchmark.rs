//! Benchmark tests for oxiz CLI
//!
//! These tests measure performance characteristics of the CLI

use std::env;
use std::fs;
use std::path::PathBuf;
use std::process::Command;
use std::time::Instant;

/// Get the path to the oxiz binary
fn oxiz_bin() -> PathBuf {
    PathBuf::from(env!("CARGO_BIN_EXE_oxiz"))
}

/// Create a temporary SMT2 file for testing
fn create_temp_smt2(content: &str, name: &str) -> PathBuf {
    let temp_dir = env::temp_dir();
    let file_path = temp_dir.join(format!("bench_{}.smt2", name));
    fs::write(&file_path, content).expect("Failed to write temp file");
    file_path
}

/// Wall-clock duration assertions in this file are flaky under shared-machine /
/// CI load (a loaded box can easily blow a 5s budget on an otherwise-instant
/// solve, with no bug involved). Gate them behind `OXIZ_TIMING_TESTS=1` so the
/// solve itself is still exercised by default; only opt in to the timing
/// assertion when explicitly requested (e.g. a dedicated perf-check CI job).
fn timing_asserts_enabled() -> bool {
    env::var("OXIZ_TIMING_TESTS").as_deref() == Ok("1")
}

/// Assert `elapsed` is under `budget_ms`, but only when timing assertions are
/// enabled via `OXIZ_TIMING_TESTS=1`. Always prints the elapsed time either way.
fn assert_within_budget(elapsed: std::time::Duration, budget_ms: u128, label: &str) {
    if timing_asserts_enabled() {
        assert!(
            elapsed.as_millis() < budget_ms,
            "{label} took too long: {elapsed:?}"
        );
    }
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

/// Regression test for the `OXIZ_TIMING_TESTS` gate: by default (unset), a
/// wildly-over-budget duration must NOT panic — only the solve/output
/// assertions run. `cargo-nextest` isolates each test in its own process, so
/// mutating the environment here does not leak into other tests in this file.
#[test]
fn timing_budget_is_opt_in_by_default() {
    // SAFETY: nextest runs each test in its own process; no other thread in
    // this process reads/writes OXIZ_TIMING_TESTS concurrently.
    unsafe {
        env::remove_var("OXIZ_TIMING_TESTS");
    }
    assert!(
        !timing_asserts_enabled(),
        "timing asserts must default to disabled"
    );

    // An absurdly long "elapsed" must not panic when the gate is off.
    let huge = std::time::Duration::from_secs(3600);
    assert_within_budget(huge, 5000, "should not panic with gate off");
}

/// Regression test: when explicitly opted in via `OXIZ_TIMING_TESTS=1`, an
/// over-budget duration DOES panic, so the gate is not a no-op.
#[test]
fn timing_budget_enforced_when_opted_in() {
    // SAFETY: see note above.
    unsafe {
        env::set_var("OXIZ_TIMING_TESTS", "1");
    }
    assert!(
        timing_asserts_enabled(),
        "timing asserts must be enabled once OXIZ_TIMING_TESTS=1 is set"
    );

    let huge = std::time::Duration::from_secs(3600);
    let result = std::panic::catch_unwind(|| {
        assert_within_budget(huge, 5000, "over-budget duration");
    });
    assert!(
        result.is_err(),
        "assert_within_budget should panic when over budget and the gate is on"
    );

    // Clean up so this process's env doesn't affect anything else that
    // might run after this test within the same process.
    unsafe {
        env::remove_var("OXIZ_TIMING_TESTS");
    }
}
