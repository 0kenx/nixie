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
/// `--inv` is optional exactly when deadlock checking is on (issue #26):
/// a deadlock-only check is a complete question. With `--no-deadlock` and
/// no invariant there is nothing to check at all, and that is still
/// refused — loudly, naming what to give.
#[test]
fn a_missing_invariant_is_refused_only_without_deadlock_checking() {
    let dir = scratch("noinv");
    let spec = write_spec(&dir, "Counter", COUNTER);
    // Deadlock checking on by default: a legal (and complete) question.
    let r = run(&["check", spec.to_str().expect("a path")]);
    assert_eq!(r.code, 0, "stdout: {}\nstderr: {}", r.out, r.err);
    // Both off: nothing to check.
    let r = run(&["check", "--no-deadlock", spec.to_str().expect("a path")]);
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
/// `simulate` is a bounded exhaustive check here and `--view` is not used.
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
    let _ = std::fs::remove_dir_all(&dir);
}

// ---- --max-error ----

const CHOICE: &str = r"
---- MODULE Choice ----
EXTENDS Integers
VARIABLE x
Init == x \in 0 .. 5
Next == UNCHANGED x
Inv  == x < 3
====
";

/// `--max-error=N` means N *different* counterexamples. A bounded query has
/// one shortest counterexample, so each is ruled out before the next is asked
/// for; without that the same trace comes back forever.
#[test]
fn max_error_yields_distinct_counterexamples() {
    let dir = scratch("many");
    let spec = write_spec(&dir, "Choice", CHOICE);
    let out = dir.join("out");
    let r = run(&[
        "check",
        "--inv=Inv",
        "--length=1",
        "--max-error=5",
        &format!("--out-dir={}", out.display()),
        spec.to_str().expect("a path"),
    ]);
    assert_eq!(r.code, 12, "stderr: {}", r.err);
    // Exactly the three states of `0..5` that break `x < 3`, each in its own
    // file, and every one of them independently replayed.
    let mut seen: Vec<String> = Vec::new();
    for n in 1..=3 {
        let text = std::fs::read_to_string(out.join(format!("violation{n}.itf.json")))
            .unwrap_or_else(|e| panic!("violation{n}.itf.json: {e}"));
        let doc: serde_json::Value = serde_json::from_str(&text).expect("valid JSON");
        seen.push(
            doc["states"][0]["x"]["#bigint"]
                .as_str()
                .expect("an x")
                .to_string(),
        );
    }
    assert!(
        !out.join("violation4.itf.json").exists(),
        "there are only three"
    );
    seen.sort();
    assert_eq!(seen, ["3", "4", "5"]);
    assert_eq!(r.out.matches("independently replayed: yes").count(), 3);
    // The search is exhaustive, so three is all there are — and it says so
    // rather than quietly delivering fewer than asked.
    assert!(r.err.contains("asked for more"), "{}", r.err);
    let _ = std::fs::remove_dir_all(&dir);
}

/// A deterministic specification has one behaviour, so one counterexample is
/// the whole answer however many are asked for.
#[test]
fn a_deterministic_spec_has_one_counterexample() {
    let dir = scratch("det");
    let spec = write_spec(&dir, "Counter", COUNTER);
    let out = dir.join("out");
    let r = run(&[
        "check",
        "--inv=Inv",
        "--length=8",
        "--max-error=5",
        &format!("--out-dir={}", out.display()),
        spec.to_str().expect("a path"),
    ]);
    assert_eq!(r.code, 12, "stderr: {}", r.err);
    assert!(out.join("violation1.itf.json").exists());
    assert!(!out.join("violation2.itf.json").exists());
    let _ = std::fs::remove_dir_all(&dir);
}

// ---- the `.cfg` divergences (issue #11) ----

const RING: &str = r"
---- MODULE Ring ----
EXTENDS Integers
CONSTANT N
VARIABLE x
Init == x = 0
Next == x' = (x + 1) % N
Inv  == x \in 0 .. N - 1
====
";

/// A `<Spec>.cfg` next to the specification is **not** read: Apalache's own
/// default since 0.25.0. Instead a hint names the file and the flag that
/// enables it — silently reading it applied its `CONSTRAINT`/`CONSTANTS`
/// without anyone asking, which changes the verdict.
#[test]
fn a_cfg_beside_the_spec_is_not_read_and_says_so() {
    let dir = scratch("cfg-hint");
    let spec = write_spec(&dir, "Ring", RING);
    std::fs::write(dir.join("Ring.cfg"), "CONSTANTS\n    N = 4\n").expect("writes the cfg");

    let r = run(&[
        "check",
        "--inv=Inv",
        "--length=3",
        spec.to_str().expect("a path"),
    ]);
    // Without the file, `N` is arbitrary and `0 .. N - 1` has no members: the
    // checker declines rather than guessing — and the hint says how to enable.
    assert_ne!(r.code, 0, "an arbitrary `N` must not pass silently");
    assert!(
        r.err.contains("TLC config file found"),
        "the hint should point at the file: {}",
        r.err
    );
    assert!(
        r.err.contains("--config=Ring.cfg"),
        "the hint should name the flag: {}",
        r.err
    );
    let _ = std::fs::remove_dir_all(&dir);
}

/// `--config=FILE` reads the file: `CONSTANTS` pin `N`, and the roles come
/// from `INIT`/`NEXT`/`INVARIANT` when the command line does not say. A
/// command-line value overrides the file's, with a warning naming both.
#[test]
fn config_loads_constants_and_roles_with_cli_precedence() {
    let dir = scratch("cfg-load");
    let spec = write_spec(
        &dir,
        "Roles",
        r"
---- MODULE Roles ----
EXTENDS Integers
CONSTANT N
VARIABLE x
Init == x = 0
Next == x' = (x + 1) % N
Inv  == x \in 0 .. N - 1
TypeInv == x >= 0
====
",
    );
    std::fs::write(
        dir.join("roles.cfg"),
        "CONSTANTS\n    N = 4\nINIT Init\nNEXT Next\nINVARIANT Inv\n",
    )
    .expect("writes the cfg");

    // Roles from the file, constants from the file: no --init/--next/--inv.
    let r = run(&[
        "check",
        "--length=3",
        &format!("--config={}", dir.join("roles.cfg").display()),
        spec.to_str().expect("a path"),
    ]);
    assert_eq!(r.code, 0, "stdout: {}\nstderr: {}", r.out, r.err);

    // The command line wins, and says so: `--inv=TypeInv` overrides the
    // file's `INVARIANT Inv`.
    let r = run(&[
        "check",
        "--length=3",
        "--inv=TypeInv",
        &format!("--config={}", dir.join("roles.cfg").display()),
        spec.to_str().expect("a path"),
    ]);
    assert_eq!(r.code, 0, "stdout: {}\nstderr: {}", r.out, r.err);
    assert!(
        r.err.contains("--inv=TypeInv overrides"),
        "the override should warn: {}",
        r.err
    );
    let _ = std::fs::remove_dir_all(&dir);
}

/// **The dangerous direction:** a `.cfg` `CONSTRAINT` prunes states. Reading
/// it unasked made Nixie say "no error" (exit 0) on exactly the command where
/// Apalache finds a violation (exit 12). Without `--config` the constraint is
/// not applied and the violation is found.
#[test]
fn a_cfg_constraint_is_applied_only_when_configured() {
    let dir = scratch("cfg-constraint");
    let spec = write_spec(
        &dir,
        "Pruned",
        r"
---- MODULE Pruned ----
EXTENDS Integers
VARIABLE x
Init == x \in {0, 5}
Next == UNCHANGED x
Inv  == x < 3
NoBig == x < 3
====
",
    );
    // The constraint removes the state that violates the invariant.
    std::fs::write(dir.join("pruned.cfg"), "CONSTRAINT\n    NoBig\n").expect("writes the cfg");

    let without = run(&["check", "--inv=Inv", spec.to_str().expect("a path")]);
    assert_eq!(without.code, 12, "stderr: {}", without.err);

    let with = run(&[
        "check",
        "--inv=Inv",
        &format!("--config={}", dir.join("pruned.cfg").display()),
        spec.to_str().expect("a path"),
    ]);
    assert_eq!(with.code, 0, "stderr: {}", with.err);
    let _ = std::fs::remove_dir_all(&dir);
}

/// `--max-run` is the number of **simulation** runs in Apalache, not an alias
/// for `--max-error`. Under `check` it is refused; reinterpreting it silently
/// changed how many counterexamples a caller asked for.
#[test]
fn max_run_is_refused_under_check() {
    let dir = scratch("maxrun");
    let spec = write_spec(&dir, "Counter", COUNTER);
    let r = run(&[
        "check",
        "--inv=Inv",
        "--max-run=5",
        spec.to_str().expect("a path"),
    ]);
    assert_eq!(r.code, 255, "stderr: {}", r.err);
    assert!(
        r.err.contains("--max-error"),
        "the refusal should point at the right flag: {}",
        r.err
    );
    let _ = std::fs::remove_dir_all(&dir);
}

/// `--inv=A,B` is a list: every invariant is checked, the one that broke is
/// named on stdout and in the ITF `#meta`, and a name that does not resolve
/// refuses the whole list — never a silent subset.
#[test]
fn inv_takes_a_comma_separated_list() {
    let dir = scratch("invlist");
    let spec = write_spec(
        &dir,
        "TwoInvs",
        r"
---- MODULE TwoInvs ----
EXTENDS Integers
VARIABLE x
Init == x = 0
Next == x' = x + 1
Low  == x > 2
High == x < 10
====
",
    );
    let out = dir.join("out");
    let r = run(&[
        "check",
        "--inv=Low,High",
        "--length=6",
        &format!("--out-dir={}", out.display()),
        spec.to_str().expect("a path"),
    ]);
    assert_eq!(r.code, 12, "stdout: {}\nstderr: {}", r.out, r.err);
    assert!(
        r.out.contains("invariant Low"),
        "stdout should name the broken invariant: {}",
        r.out
    );
    let doc: serde_json::Value = serde_json::from_str(
        &std::fs::read_to_string(out.join("violation1.itf.json")).expect("an ITF file"),
    )
    .expect("valid JSON");
    assert_eq!(doc["#meta"]["violated"], serde_json::json!(["Low"]));

    // An unresolvable name refuses everything: checking the other two would
    // answer a narrower question than the caller asked.
    let r = run(&[
        "check",
        "--inv=Low,NoSuchInvariant,High",
        "--length=6",
        spec.to_str().expect("a path"),
    ]);
    assert_eq!(r.code, 75, "stderr: {}", r.err);
    assert!(r.err.contains("NoSuchInvariant"), "{}", r.err);
    let _ = std::fs::remove_dir_all(&dir);
}

/// A missing file or a foreign extension is exit **255**, not 150: Apalache
/// distinguishes "you pointed me at the wrong thing" from "your spec does not
/// parse", and so does a wrapper.
#[test]
fn a_missing_or_foreign_file_is_255() {
    let dir = scratch("missing");
    let r = run(&[
        "check",
        "--inv=Inv",
        &dir.join("Nope.tla").to_string_lossy(),
    ]);
    assert_eq!(r.code, 255, "stderr: {}", r.err);
    assert!(r.err.contains("no such file"), "{}", r.err);

    let other = dir.join("spec.mc");
    std::fs::write(&other, "not a spec").expect("writes");
    let r = run(&["check", "--inv=Inv", &other.to_string_lossy()]);
    assert_eq!(r.code, 255, "stderr: {}", r.err);
    assert!(r.err.contains(".tla"), "{}", r.err);

    // And a `.cfg` that does not exist is refused too, not silently skipped.
    let spec = write_spec(&dir, "Counter", COUNTER);
    let r = run(&[
        "check",
        "--inv=Inv",
        &format!("--config={}", dir.join("absent.cfg").display()),
        spec.to_str().expect("a path"),
    ]);
    assert_eq!(r.code, 255, "stderr: {}", r.err);
    let _ = std::fs::remove_dir_all(&dir);
}

/// A `.cfg` naming `SPECIFICATION` is refused by name: that is a temporal
/// behaviour spec, and a bounded Init/Next unrolling would silently check
/// something weaker than what the file says.
#[test]
fn a_cfg_with_specification_is_refused() {
    let dir = scratch("cfg-spec");
    let spec = write_spec(&dir, "Counter", COUNTER);
    std::fs::write(dir.join("temporal.cfg"), "SPECIFICATION Spec\n").expect("writes the cfg");
    let r = run(&[
        "check",
        "--inv=Inv",
        &format!("--config={}", dir.join("temporal.cfg").display()),
        spec.to_str().expect("a path"),
    ]);
    assert_eq!(r.code, 255, "stderr: {}", r.err);
    assert!(r.err.contains("SPECIFICATION"), "{}", r.err);
    let _ = std::fs::remove_dir_all(&dir);
}
