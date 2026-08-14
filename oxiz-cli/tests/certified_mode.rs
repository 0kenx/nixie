//! End-to-end coverage for the externally enforced certification policy.

mod common;

use std::path::PathBuf;
use std::process::Command;

fn oxiz_bin() -> PathBuf {
    PathBuf::from(env!("CARGO_BIN_EXE_oxiz"))
}

#[test]
fn certified_mode_is_off_by_default() {
    let script = common::TempPath::write(
        "certified_default_off",
        "smt2",
        "(get-option :certified-mode)\n(declare-const x Int)\n(assert (< x 0))\n(assert (>= x 0))\n(check-sat)\n",
    );
    let output = Command::new(oxiz_bin())
        .args(["--quiet", script.to_str().unwrap_or("")])
        .output()
        .expect("run oxiz without certified mode");

    assert!(output.status.success());
    assert_eq!(
        String::from_utf8_lossy(&output.stdout)
            .lines()
            .collect::<Vec<_>>(),
        vec!["false", "unsat"]
    );
}

#[test]
fn certified_mode_verifies_a_boolean_unsat_result() {
    let script = common::TempPath::write(
        "certified_boolean_unsat",
        "smt2",
        "(declare-const p Bool)\n(assert p)\n(assert (not p))\n(check-sat)\n",
    );
    let output = Command::new(oxiz_bin())
        .args(["--certified-mode", "--quiet", script.to_str().unwrap_or("")])
        .output()
        .expect("run oxiz in certified mode");

    assert!(output.status.success());
    assert_eq!(String::from_utf8_lossy(&output.stdout).trim(), "unsat");
}

#[test]
fn certified_mode_fails_closed_for_unsupported_theory_unsat() {
    let script = common::TempPath::write(
        "certified_theory_unsat",
        "smt2",
        "(declare-const x Int)\n(assert (< x 0))\n(assert (>= x 0))\n(check-sat)\n",
    );
    let output = Command::new(oxiz_bin())
        .args(["--certified-mode", "--quiet", script.to_str().unwrap_or("")])
        .output()
        .expect("run oxiz in certified mode");

    assert!(output.status.success());
    assert_eq!(String::from_utf8_lossy(&output.stdout).trim(), "unknown");
}

#[test]
fn certified_cli_policy_cannot_be_disabled_by_the_script() {
    let script = common::TempPath::write(
        "certified_not_downgradable",
        "smt2",
        "(set-option :certified-mode false)\n(reset)\n(get-option :certified-mode)\n(declare-const p Bool)\n(assert p)\n(assert (not p))\n(check-sat)\n",
    );
    let output = Command::new(oxiz_bin())
        .args(["--certified-mode", "--quiet", script.to_str().unwrap_or("")])
        .output()
        .expect("run oxiz in certified mode");

    assert!(output.status.success());
    let stdout = String::from_utf8_lossy(&output.stdout);
    assert_eq!(stdout.lines().collect::<Vec<_>>(), vec!["true", "unsat"]);
}
