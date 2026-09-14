//! The `nixie-tla` command line, which exists to be a drop-in.
//!
//! The tools that consume TLA+ counterexamples already call Apalache:
//! `tla-connect`, the model-based testing harness for Rust, runs
//! `apalache-mc check --inv=… --length=… --out-dir=…`, collects `*.itf.json`,
//! and replays each trace against a driver. These pin the parts of that
//! contract a caller depends on — the command line, the exit codes, and the
//! file that appears in the output directory — because a caller will branch on
//! them without asking us anything.

use std::path::{Path, PathBuf};
use std::process::Command;

fn scratch(name: &str) -> PathBuf {
    let dir = std::env::temp_dir().join(format!("nixie-tla-cli-{name}-{}", std::process::id()));
    let _ = std::fs::remove_dir_all(&dir);
    std::fs::create_dir_all(&dir).expect("a scratch directory");
    dir
}

fn write_spec(dir: &Path, name: &str, body: &str) -> PathBuf {
    let p = dir.join(format!("{name}.tla"));
    std::fs::write(&p, body).expect("writes the specification");
    p
}

struct Run {
    code: i32,
    out: String,
    err: String,
}

fn run(args: &[&str]) -> Run {
    let o = Command::new(env!("CARGO_BIN_EXE_nixie-tla"))
        .args(args)
        .output()
        .expect("the binary runs");
    Run {
        code: o.status.code().unwrap_or(-1),
        out: String::from_utf8_lossy(&o.stdout).into_owned(),
        err: String::from_utf8_lossy(&o.stderr).into_owned(),
    }
}

const COUNTER: &str = r"
---- MODULE Counter ----
EXTENDS Integers
VARIABLE x
Init == x = 0
Next == x' = x + 1
Inv  == x < 3
====
";

/// The headline contract: a counterexample is exit **12** and one
/// `violation1.itf.json` in the output directory. `tla-connect` accepts 0 and
/// 12 and treats anything else as a failure of the tool.
#[test]
fn a_counterexample_is_exit_12_and_an_itf_file() {
    let dir = scratch("violation");
    let spec = write_spec(&dir, "Counter", COUNTER);
    let out = dir.join("out");
    let r = run(&[
        "check",
        "--inv=Inv",
        "--length=6",
        &format!("--out-dir={}", out.display()),
        spec.to_str().expect("a path"),
    ]);
    assert_eq!(r.code, 12, "stdout: {}\nstderr: {}", r.out, r.err);
    let file = out.join("violation1.itf.json");
    let text = std::fs::read_to_string(&file).expect("an ITF file");
    let doc: serde_json::Value = serde_json::from_str(&text).expect("valid JSON");
    assert_eq!(doc["vars"], serde_json::json!(["x"]));
    assert_eq!(
        doc["states"].as_array().expect("states").len(),
        4,
        "0, 1, 2, 3"
    );
    // And the counterexample was confirmed against the evaluator, not just
    // taken from the solver.
    assert!(r.out.contains("independently replayed: yes"), "{}", r.out);
    let _ = std::fs::remove_dir_all(&dir);
}

/// No counterexample within the bound is exit **0** — and the message says the
/// bound out loud, because a bounded search that finds nothing is not a proof.
#[test]
fn no_counterexample_is_exit_0() {
    let dir = scratch("clean");
    let spec = write_spec(&dir, "Counter", COUNTER);
    let r = run(&[
        "check",
        "--inv=Inv",
        "--length=2",
        spec.to_str().expect("a path"),
    ]);
    assert_eq!(r.code, 0, "stderr: {}", r.err);
    assert!(r.out.contains("2 step(s) or fewer"), "{}", r.out);
    let _ = std::fs::remove_dir_all(&dir);
}

/// A specification that does not type check is **120**, and one that does not
/// parse is **150** — Apalache's codes, which a caller may branch on to tell
/// "your spec is wrong" from "the checker fell over".
#[test]
fn the_failure_exit_codes_are_apalaches() {
    let dir = scratch("codes");
    let bad_types = write_spec(
        &dir,
        "BadTypes",
        r"
---- MODULE BadTypes ----
EXTENDS Integers
VARIABLE x
Init == x = 1 /\ x = TRUE
Next == UNCHANGED x
Inv  == x = 1
====
",
    );
    let r = run(&["check", "--inv=Inv", bad_types.to_str().expect("a path")]);
    assert_eq!(r.code, 120, "stderr: {}", r.err);

    let bad_syntax = write_spec(&dir, "BadSyntax", "---- MODULE BadSyntax ----\nInit ==\n");
    let r = run(&["check", "--inv=Inv", bad_syntax.to_str().expect("a path")]);
    assert_eq!(r.code, 150, "stderr: {}", r.err);
    let _ = std::fs::remove_dir_all(&dir);
}

/// A missing invariant is refused rather than defaulted. Checking a
/// specification against an invariant nobody named would answer a question
/// nobody asked.
#[test]
fn a_missing_invariant_is_refused() {
    let dir = scratch("noinv");
    let spec = write_spec(&dir, "Counter", COUNTER);
    let r = run(&["check", spec.to_str().expect("a path")]);
    assert_ne!(r.code, 0);
    assert!(r.err.contains("--inv"), "{}", r.err);
    let _ = std::fs::remove_dir_all(&dir);
}

/// Apalache spells every option `--name=value`, so that is the only form
/// accepted: `--inv Inv` would otherwise leave the invariant unset and check
/// something else.
#[test]
fn a_separated_option_value_is_refused() {
    let dir = scratch("sep");
    let spec = write_spec(&dir, "Counter", COUNTER);
    let r = run(&["check", "--inv", "Inv", spec.to_str().expect("a path")]);
    assert_ne!(r.code, 0);
    assert!(r.err.contains("needs a value"), "{}", r.err);
    let _ = std::fs::remove_dir_all(&dir);
}

#[test]
fn an_unknown_option_is_refused() {
    let dir = scratch("unknown");
    let spec = write_spec(&dir, "Counter", COUNTER);
    let r = run(&[
        "check",
        "--inv=Inv",
        "--nonsense=1",
        spec.to_str().expect("a path"),
    ]);
    assert_ne!(r.code, 0);
    assert!(r.err.contains("nonsense"), "{}", r.err);
    let _ = std::fs::remove_dir_all(&dir);
}

/// What this checker cannot do is said out loud rather than silently ignored:
/// `simulate` is a bounded exhaustive check here, `--view` is not used, and
/// `--max-error` above one delivers one.
#[test]
fn the_differences_from_apalache_are_reported() {
    let dir = scratch("notes");
    let spec = write_spec(&dir, "Counter", COUNTER);
    let r = run(&[
        "simulate",
        "--inv=Inv",
        "--max-run=10",
        "--length=6",
        "--view=V",
        spec.to_str().expect("a path"),
    ]);
    assert_eq!(r.code, 12, "stderr: {}", r.err);
    assert!(r.err.contains("not random simulation"), "{}", r.err);
    assert!(r.err.contains("--view=V` is not used"), "{}", r.err);
    assert!(r.err.contains("shortest counterexample only"), "{}", r.err);
    let _ = std::fs::remove_dir_all(&dir);
}

/// The `.cfg` supplies `CONSTANT` values; the command line keeps the roles.
/// Without the file `0 .. N-1` has no candidate list at all.
#[test]
fn a_cfg_supplies_constants_and_the_cli_keeps_the_roles() {
    let dir = scratch("cfg");
    let spec = write_spec(
        &dir,
        "Ring",
        r"
---- MODULE Ring ----
EXTENDS Integers
CONSTANT N
VARIABLE x
Init == x = 0
Next == x' = (x + 1) % N
Inv  == x \in 0 .. N - 1
====
",
    );
    std::fs::write(dir.join("Ring.cfg"), "CONSTANTS\n    N = 4\n").expect("writes the cfg");

    let with = run(&[
        "check",
        "--inv=Inv",
        "--length=3",
        spec.to_str().expect("a path"),
    ]);
    assert_eq!(with.code, 0, "stderr: {}", with.err);
    assert!(with.err.contains("Ring.cfg"), "{}", with.err);

    // And `--no-cfg` genuinely ignores it, leaving `N` arbitrary — which is a
    // strictly harder question that this encoding declines rather than
    // guessing at.
    let without = run(&[
        "check",
        "--inv=Inv",
        "--length=3",
        "--no-cfg",
        spec.to_str().expect("a path"),
    ]);
    assert_ne!(without.code, 0, "an arbitrary `N` must not pass silently");
    assert!(!without.err.contains("Ring.cfg"), "{}", without.err);
    let _ = std::fs::remove_dir_all(&dir);
}
