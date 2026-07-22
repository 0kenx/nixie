//! Regression tests for `--enumerate-models`/`--max-models`.
//!
//! `--max-models` used to be parsed by clap and never read anywhere in
//! `oxiz-cli`, and `--enumerate-models` printed a "not yet implemented"
//! warning and reported only the first model. Both flags are now wired
//! into a real bounded blocking-clause enumeration
//! (`enumerate_additional_models` in `src/main.rs`).

use std::env;
use std::fs;
use std::path::PathBuf;
use std::process::Command;

/// Get the path to the oxiz binary.
fn oxiz_bin() -> PathBuf {
    PathBuf::from(env!("CARGO_BIN_EXE_oxiz"))
}

/// Create a temporary SMT2 file for testing.
fn create_temp_smt2(content: &str) -> PathBuf {
    let temp_dir = env::temp_dir();
    let file_path = temp_dir.join(format!("test_max_models_{}.smt2", rand_string()));
    fs::write(&file_path, content).expect("Failed to write temp file");
    file_path
}

/// Generate a random string for unique filenames.
fn rand_string() -> String {
    use std::time::SystemTime;
    let duration = SystemTime::now()
        .duration_since(SystemTime::UNIX_EPOCH)
        .expect("Time went backwards");
    format!("{}{}", duration.as_secs(), duration.subsec_nanos())
}

/// `p XOR q` (encoded as two clauses) has exactly two models: `(p, q)` in
/// `{(true, false), (false, true)}`. `--enumerate-models --max-models 5`
/// must report both `(model ...)` blocks (the cap is above the true count,
/// so enumeration should stop because the solver reports `unsat` on the
/// third attempt, not because the cap was hit).
fn xor_script() -> &'static str {
    "(declare-const p Bool)\n(declare-const q Bool)\n\
     (assert (or p q))\n(assert (or (not p) (not q)))\n(check-sat)\n"
}

#[test]
fn enumerate_models_finds_both_xor_models() {
    let temp_file = create_temp_smt2(xor_script());

    let output = Command::new(oxiz_bin())
        .arg("--enumerate-models")
        .arg("--max-models")
        .arg("5")
        .arg(temp_file.to_str().unwrap())
        .output()
        .expect("Failed to execute oxiz");

    fs::remove_file(&temp_file).ok();

    let stdout = String::from_utf8_lossy(&output.stdout);
    let stderr = String::from_utf8_lossy(&output.stderr);

    assert!(
        stdout.lines().any(|line| line.trim() == "sat"),
        "expected a 'sat' result line: stdout={stdout}, stderr={stderr}"
    );
    let model_count = stdout.matches("(model").count();
    assert_eq!(
        model_count, 2,
        "p XOR q has exactly 2 models: stdout={stdout}, stderr={stderr}"
    );
    assert!(
        stdout.contains("no further"),
        "enumeration should report it exhausted every model, not hit the cap: stdout={stdout}"
    );
}

/// `--max-models` must actually bound how many models are found: with a
/// cap of 1, exactly one `(model ...)` block is reported (no blocking-clause
/// enumeration round ever runs), and the CLI says honestly that it stopped
/// because of the cap.
#[test]
fn max_models_one_reports_only_the_first_model() {
    let temp_file = create_temp_smt2(xor_script());

    let output = Command::new(oxiz_bin())
        .arg("--enumerate-models")
        .arg("--max-models")
        .arg("1")
        .arg(temp_file.to_str().unwrap())
        .output()
        .expect("Failed to execute oxiz");

    fs::remove_file(&temp_file).ok();

    let stdout = String::from_utf8_lossy(&output.stdout);
    assert!(
        stdout.lines().any(|line| line.trim() == "sat"),
        "expected a 'sat' result line: stdout={stdout}"
    );
    let model_count = stdout.matches("(model").count();
    assert_eq!(
        model_count, 1,
        "--max-models 1 must report exactly the one model: stdout={stdout}"
    );
    assert!(
        stdout.contains("--max-models 1"),
        "hitting the cap should be reported honestly: stdout={stdout}"
    );
}

/// `--max-models` with a cap strictly between 1 and the true model count
/// must stop exactly at the cap and say so, honoring the bound instead of
/// silently ignoring it (the original bug: the flag was parsed but never
/// read).
#[test]
fn max_models_caps_enumeration_below_true_count() {
    // Two independent XOR pairs (p1/q1 and p2/q2) have exactly 2*2=4
    // models, all four variables genuinely constrained; cap at 2.
    let smt2 = "(declare-const p1 Bool)\n(declare-const q1 Bool)\n\
                (declare-const p2 Bool)\n(declare-const q2 Bool)\n\
                (assert (or p1 q1))\n(assert (or (not p1) (not q1)))\n\
                (assert (or p2 q2))\n(assert (or (not p2) (not q2)))\n\
                (check-sat)\n";
    let temp_file = create_temp_smt2(smt2);

    let output = Command::new(oxiz_bin())
        .arg("--enumerate-models")
        .arg("--max-models")
        .arg("2")
        .arg(temp_file.to_str().unwrap())
        .output()
        .expect("Failed to execute oxiz");

    fs::remove_file(&temp_file).ok();

    let stdout = String::from_utf8_lossy(&output.stdout);
    let model_count = stdout.matches("(model").count();
    assert_eq!(
        model_count, 2,
        "--max-models 2 must stop after exactly 2 models: stdout={stdout}"
    );
    assert!(
        stdout.contains("--max-models 2"),
        "hitting the cap should be reported honestly: stdout={stdout}"
    );
}

/// `--max-models` without `--enumerate-models` has no effect (matching
/// its documented `--enumerate-models`-only semantics); the CLI must warn
/// about the combination instead of silently discarding the flag.
#[test]
fn max_models_without_enumerate_models_warns() {
    let smt2 = "(declare-const p Bool)\n(check-sat)\n";
    let temp_file = create_temp_smt2(smt2);

    let output = Command::new(oxiz_bin())
        .arg("--max-models")
        .arg("3")
        .arg(temp_file.to_str().unwrap())
        .output()
        .expect("Failed to execute oxiz");

    fs::remove_file(&temp_file).ok();

    let stdout = String::from_utf8_lossy(&output.stdout);
    let stderr = String::from_utf8_lossy(&output.stderr);
    assert!(
        stdout.lines().any(|line| line.trim() == "sat"),
        "solving must still succeed normally: stdout={stdout}"
    );
    assert!(
        stderr.contains("--max-models") && stderr.contains("--enumerate-models"),
        "expected a warning that --max-models has no effect without --enumerate-models: \
         stderr={stderr}"
    );
}

/// An `unsat` result has no model to enumerate; `--enumerate-models` must
/// not attempt to run additional rounds against it.
#[test]
fn enumerate_models_no_op_on_unsat() {
    let smt2 = "(declare-const p Bool)\n(assert p)\n(assert (not p))\n(check-sat)\n";
    let temp_file = create_temp_smt2(smt2);

    let output = Command::new(oxiz_bin())
        .arg("--enumerate-models")
        .arg("--max-models")
        .arg("5")
        .arg(temp_file.to_str().unwrap())
        .output()
        .expect("Failed to execute oxiz");

    fs::remove_file(&temp_file).ok();

    let stdout = String::from_utf8_lossy(&output.stdout);
    assert!(
        stdout.lines().any(|line| line.trim() == "unsat"),
        "expected an 'unsat' result line: stdout={stdout}"
    );
    assert!(
        !stdout.contains("model enumeration"),
        "unsat has no model to enumerate from: stdout={stdout}"
    );
}
