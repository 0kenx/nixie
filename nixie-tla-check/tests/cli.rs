//! The `nixie-tla` command line, which exists to be a drop-in.
//!
//! The tools that consume TLA+ counterexamples already call Apalache:
//! `tla-connect`, the model-based testing harness for Rust, runs
//! `apalache-mc check --inv=… --length=… --out-dir=…`, collects `*.itf.json`,
//! and replays each trace against a driver. These pin the parts of that
//! contract a caller depends on – the command line, the exit codes, and the
//! file that appears in the output directory – because a caller will branch on
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
View == <<x>>
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

/// No counterexample within the bound is exit **0** – and the message says the
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
/// parse is **150** – Apalache's codes, which a caller may branch on to tell
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
/// refused – loudly, naming what to give.
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

/// `simulate` samples behaviours (issue #28): even a deterministic
/// specification's violation is found by the first run, as a replayed
/// counterexample with Apalache's exit code.
#[test]
fn the_differences_from_apalache_are_reported() {
    let dir = scratch("notes");
    let spec = write_spec(&dir, "Counter", COUNTER);
    let r = run(&[
        "simulate",
        "--inv=Inv",
        "--max-run=10",
        "--length=6",
        spec.to_str().expect("a path"),
    ]);
    assert_eq!(r.code, 12, "stderr: {}", r.err);
    assert!(r.out.contains("counterexample in run 1"), "{}", r.out);
    assert!(r.out.contains("independently replayed: yes"), "{}", r.out);
    let _ = std::fs::remove_dir_all(&dir);
}

// ======== --max-error ========

const CHOICE: &str = r"
---- MODULE Choice ----
EXTENDS Integers
VARIABLE x
Init == x \in 0 .. 5
Next == UNCHANGED x
Inv  == x < 3
View == <<x>>
====
";

/// `--max-error=N` means N counterexamples distinct **under the view** –
/// Apalache's semantics, including its refusal of `--max-error > 1` without
/// one (`ApalacheConfigResolver`). Each reported trace is ruled out at its
/// view's value, so the next must differ where the author looks.
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
        "--view=View",
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
    // The search is exhaustive, so three is all there are – and it says so
    // rather than quietly delivering fewer than asked.
    assert!(r.err.contains("asked for more"), "{}", r.err);
    let _ = std::fs::remove_dir_all(&dir);
}

/// A view that names no definition is refused with exit 255 – an honest
/// refusal rather than a note that would silently mean "no view".
#[test]
fn a_view_that_names_nothing_is_refused() {
    let dir = scratch("badview");
    let spec = write_spec(&dir, "Counter", COUNTER);
    let r = run(&[
        "check",
        "--inv=Inv",
        "--length=6",
        "--view=Nope",
        spec.to_str().expect("a path"),
    ]);
    assert_eq!(r.code, 255, "stderr: {}", r.err);
    assert!(r.err.contains("--view=Nope"), "{}", r.err);
    let _ = std::fs::remove_dir_all(&dir);
}

/// `--max-error > 1` without `--view` is refused with exit 255, exactly as
/// Apalache refuses it: without a view, further counterexamples are
/// near-duplicates of the first, and the combination promises a diversity
/// no one can deliver.
#[test]
fn max_error_without_a_view_is_refused() {
    let dir = scratch("noview");
    let spec = write_spec(&dir, "Choice", CHOICE);
    let r = run(&[
        "check",
        "--inv=Inv",
        "--length=1",
        "--max-error=2",
        spec.to_str().expect("a path"),
    ]);
    assert_eq!(r.code, 255, "stderr: {}", r.err);
    assert!(r.err.contains("requires --view"), "{}", r.err);
    let _ = std::fs::remove_dir_all(&dir);
}

/// A view blocks at the view's *value*, not the whole state: two traces the
/// view cannot tell apart count as one, so asking for several returns
/// traces that differ in the viewed component. `y` varies where `x` does
/// not, and the view is `<<x>>`.
#[test]
fn view_blocking_blocks_the_views_value() {
    let spec = r"
---- MODULE Viewed ----
EXTENDS Integers
VARIABLE x, y
Init == /\ x = 0 /\ y = 0
Next == /\/ /\ x' = x + 1 /\ y' = y
        \/ /\ x' = x /\ y' = y + 1
Inv  == x + y < 3
View == <<x>>
====
";
    let dir = scratch("view");
    let p = write_spec(&dir, "Viewed", spec);
    let out = dir.join("out");
    let r = run(&[
        "check",
        "--inv=Inv",
        "--length=5",
        "--max-error=3",
        "--view=View",
        &format!("--out-dir={}", out.display()),
        p.to_str().expect("a path"),
    ]);
    assert_eq!(r.code, 12, "stderr: {}", r.err);
    // Three traces, pairwise distinct in their `x` histories (the view),
    // however their `y`s scatter.
    let mut xs: Vec<String> = Vec::new();
    for n in 1..=3 {
        let text = std::fs::read_to_string(out.join(format!("violation{n}.itf.json")))
            .unwrap_or_else(|e| panic!("violation{n}.itf.json: {e}"));
        let doc: serde_json::Value = serde_json::from_str(&text).expect("valid JSON");
        let seq: Vec<String> = doc["states"]
            .as_array()
            .expect("states")
            .iter()
            .map(|s| s["x"]["#bigint"].as_str().expect("an x").to_string())
            .collect();
        xs.push(seq.join(","));
    }
    xs.sort();
    xs.dedup();
    assert_eq!(xs.len(), 3, "the three traces are distinct under the view");
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
        "--view=View",
        &format!("--out-dir={}", out.display()),
        spec.to_str().expect("a path"),
    ]);
    assert_eq!(r.code, 12, "stderr: {}", r.err);
    assert!(out.join("violation1.itf.json").exists());
    assert!(!out.join("violation2.itf.json").exists());
    let _ = std::fs::remove_dir_all(&dir);
}

// ======== the `.cfg` divergences (issue #11) ========

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
/// enables it – silently reading it applied its `CONSTRAINT`/`CONSTANTS`
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
    // checker declines rather than guessing – and the hint says how to enable.
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
/// refuses the whole list – never a silent subset.
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

// ======== `SPECIFICATION` in the configuration (issue #46) ========

/// The issue's own reproducer. `SPECIFICATION Spec`, with
/// `Spec == Init /\ [][Next]_x`, is checked exactly as `INIT Init` /
/// `NEXT Next` are: `[Next]_x` is `Next` or a stuttering step, and a
/// stuttering step reaches no state the invariant was not already checked
/// in. Before this, the configuration was refused: more than half of the
/// corpus's `.cfg` files name the system this way.
#[test]
fn a_cfg_with_the_canonical_specification_checks_like_init_next() {
    let dir = scratch("cfg-spec-ok");
    let spec = write_spec(
        &dir,
        "SpecRepro",
        r"
---- MODULE SpecRepro ----
VARIABLE x
Init == x = FALSE
Next == x' = x
Spec == Init /\ [][Next]_x
Inv == x = FALSE
Nope == x = TRUE
====
",
    );
    std::fs::write(dir.join("spec.cfg"), "SPECIFICATION Spec\nINVARIANT Inv\n").expect("cfg");
    let r = run(&[
        "check",
        &format!("--config={}", dir.join("spec.cfg").display()),
        "--length=0",
        "--out-dir=out",
        spec.to_str().expect("a path"),
    ]);
    assert_eq!(r.code, 0, "stdout: {}\nstderr: {}", r.out, r.err);
    assert!(
        r.out.contains("no counterexample of 0 step(s) or fewer"),
        "{}",
        r.out
    );
    // Apalache's own three lines, in its own words.
    assert!(
        r.out.contains("> spec.cfg: Using SPECIFICATION Spec"),
        "{}",
        r.out
    );
    assert!(
        r.out.contains("> Set the initialization predicate to Init")
            && r.out.contains("> Set the transition predicate to Next"),
        "{}",
        r.out
    );

    // The same specification with the roles named the other way round gives
    // the same answer, and a violated invariant is found the same way too.
    std::fs::write(
        dir.join("spec.cfg"),
        "CONSTANTS\nINVARIANT Nope\nSPECIFICATION Spec\n",
    )
    .expect("cfg");
    let r = run(&[
        "check",
        &format!("--config={}", dir.join("spec.cfg").display()),
        "--length=2",
        spec.to_str().expect("a path"),
    ]);
    assert_eq!(r.code, 12, "stdout: {}\nstderr: {}", r.out, r.err);
    assert!(
        r.out
            .contains("counterexample 1: 0 step(s), invariant Nope"),
        "{}",
        r.out
    );
    assert!(r.out.contains("independently replayed: yes"), "{}", r.out);
    let _ = std::fs::remove_dir_all(&dir);
}

/// Under `SPECIFICATION Spec` the deadlock question is the one TLC and
/// Apalache ask under it: a state with no `Next`-successor is a deadlock,
/// even though `[Next]_vars` permits stuttering – and `CHECK_DEADLOCK FALSE`
/// is what turns that off, in the file, as for TLC.
#[test]
fn the_deadlock_question_is_the_same_under_a_specification() {
    let dir = scratch("cfg-spec-deadlock");
    let spec = write_spec(
        &dir,
        "Stopper",
        r"
---- MODULE Stopper ----
EXTENDS Integers
VARIABLE x
Init == x = 0
Next == x < 2 /\ x' = x + 1
Spec == Init /\ [][Next]_x
Inv == x >= 0
====
",
    );
    std::fs::write(
        dir.join("Stopper.cfg"),
        "SPECIFICATION Spec\nINVARIANT Inv\n",
    )
    .expect("cfg");
    let r = run(&[
        "check",
        &format!("--config={}", dir.join("Stopper.cfg").display()),
        "--length=4",
        spec.to_str().expect("a path"),
    ]);
    assert_eq!(r.code, 12, "stdout: {}\nstderr: {}", r.out, r.err);
    assert!(r.out.contains("The outcome is: Deadlock"), "{}", r.out);
    std::fs::write(
        dir.join("Stopper.cfg"),
        "SPECIFICATION Spec\nINVARIANT Inv\nCHECK_DEADLOCK FALSE\n",
    )
    .expect("cfg");
    let r = run(&[
        "check",
        &format!("--config={}", dir.join("Stopper.cfg").display()),
        "--length=4",
        spec.to_str().expect("a path"),
    ]);
    assert_eq!(r.code, 0, "stdout: {}\nstderr: {}", r.out, r.err);
    let _ = std::fs::remove_dir_all(&dir);
}

/// What stands inside the brackets is the next-state action even when it is
/// not a definition's name – TLC's reading (`TerminatingSpec == Init /\
/// [][Next \/ Terminate]_v` is the dag-consensus specs' shape) – and a
/// state-level conjunct that is not a name is an initial predicate
/// (`PrintT(R) /\ Spec` is MCEcho's). Both are read where the formula was
/// written.
#[test]
fn roles_written_inline_in_the_specification_are_checked() {
    let dir = scratch("cfg-spec-inline");
    let spec = write_spec(
        &dir,
        "Inline",
        r"
---- MODULE Inline ----
EXTENDS Integers
VARIABLE x
Init == x = 0
Next == x < 3 /\ x' = x + 1
Terminate == x' = x
StopSpec == x <= 0 /\ Init /\ [][Next \/ Terminate]_x
RunSpec == x <= 0 /\ Init /\ [][Next]_x
Inv == x <= 3
====
",
    );
    std::fs::write(
        dir.join("Stop.cfg"),
        "SPECIFICATION StopSpec\nINVARIANT Inv\n",
    )
    .expect("cfg");
    let r = run(&[
        "check",
        &format!("--config={}", dir.join("Stop.cfg").display()),
        "--length=5",
        spec.to_str().expect("a path"),
    ]);
    assert_eq!(r.code, 0, "stdout: {}\nstderr: {}", r.out, r.err);
    assert!(
        r.out
            .contains("Set the initialization predicate to x <= 0 (written inline) /\\ Init"),
        "{}",
        r.out
    );
    assert!(
        r.out
            .contains("Set the transition predicate to Next \\/ Terminate (written inline)"),
        "{}",
        r.out
    );
    // Without `Terminate`, the state x = 3 has no successor: a deadlock,
    // as under `NEXT Next`.
    std::fs::write(
        dir.join("Run.cfg"),
        "SPECIFICATION RunSpec\nINVARIANT Inv\n",
    )
    .expect("cfg");
    let r = run(&[
        "check",
        &format!("--config={}", dir.join("Run.cfg").display()),
        "--length=5",
        spec.to_str().expect("a path"),
    ]);
    assert_eq!(r.code, 12, "stdout: {}\nstderr: {}", r.out, r.err);
    assert!(r.out.contains("The outcome is: Deadlock"), "{}", r.out);
    // And an initial predicate written as an action is refused before the
    // formula is checked, as TLC refuses an action-level conjunct.
    std::fs::write(
        dir.join("Inline.tla"),
        r"
---- MODULE Inline ----
EXTENDS Integers
VARIABLE x
Init == x = 0
Next == x' = x + 1
BadSpec == x' = 1 /\ Init /\ [][Next]_x
Inv == x <= 3
====
",
    )
    .expect("spec");
    std::fs::write(
        dir.join("Bad.cfg"),
        "SPECIFICATION BadSpec\nINVARIANT Inv\n",
    )
    .expect("cfg");
    let r = run(&[
        "check",
        &format!("--config={}", dir.join("Bad.cfg").display()),
        "--length=5",
        spec.to_str().expect("a path"),
    ]);
    assert_eq!(r.code, 75, "stdout: {}\nstderr: {}", r.out, r.err);
    assert!(r.err.contains("the conjunct `x' = 1`"), "{}", r.err);
    let _ = std::fs::remove_dir_all(&dir);
}

/// A `.cfg` naming a definition the module does not have is refused by name
/// – exit 75, the "could not be evaluated" bucket an `INIT Nope` lands in,
/// not a usage error.
#[test]
fn a_cfg_with_specification_naming_nothing_is_refused_by_name() {
    let dir = scratch("cfg-spec");
    let spec = write_spec(&dir, "Counter", COUNTER);
    std::fs::write(dir.join("temporal.cfg"), "SPECIFICATION Spec\n").expect("writes the cfg");
    let r = run(&[
        "check",
        "--inv=Inv",
        &format!("--config={}", dir.join("temporal.cfg").display()),
        spec.to_str().expect("a path"),
    ]);
    assert_eq!(r.code, 75, "stdout: {}\nstderr: {}", r.out, r.err);
    assert!(
        r.err.contains("no zero-argument definition named `Spec`"),
        "{}",
        r.err
    );
    let _ = std::fs::remove_dir_all(&dir);
}

/// A fairness conjunct restricts behaviours by their infinite tails. For an
/// invariant that changes nothing a bounded check sees – TLC checks
/// invariants on the states `Init`/`Next` reach whatever the fairness, and
/// Apalache warns and ignores it – so the invariants are checked and the
/// clause is **said out loud**. For a liveness property it is the difference
/// between a counterexample and an unfair behaviour, so a liveness check
/// **assumes** it (issue #47), and says so: a lasso is a counterexample only
/// when it is a behaviour of the full specification.
#[test]
fn fairness_in_a_specification_is_announced_for_invariants_and_assumed_for_liveness() {
    let dir = scratch("cfg-spec-fair");
    let spec = write_spec(
        &dir,
        "Fair",
        r"
---- MODULE Fair ----
VARIABLE x
Node == {1}
A(p) == x' = x + 1
Next == \E p \in Node : A(p)
Init == x = 0
Spec4 == (Init /\ [][Next]_x) /\ WF_x(Next)
Spec5 == Init /\ ([][Next]_x /\ SF_x(Next))
Spec6 == Init /\ [][Next]_x /\ \A p \in Node : WF_x(A(p))
Inv == x < 3
====
",
    );
    for (spec_name, clause) in [
        ("Spec4", "WF_x(Next)"),
        ("Spec5", "SF_x(Next)"),
        ("Spec6", r"\A … : WF_x(A(p))"),
    ] {
        std::fs::write(
            dir.join("Fair.cfg"),
            format!("SPECIFICATION {spec_name}\nINVARIANT Inv\n"),
        )
        .expect("cfg");
        // `x < 3` holds through two steps of `x' = x + 1` from 0: checked,
        // answered, and the fairness clause announced on the way.
        let r = run(&[
            "check",
            &format!("--config={}", dir.join("Fair.cfg").display()),
            "--length=2",
            spec.to_str().expect("a path"),
        ]);
        assert_eq!(
            r.code, 0,
            "{spec_name}: stdout: {}\nstderr: {}",
            r.out, r.err
        );
        assert!(
            r.out.contains("no counterexample of 2 step(s) or fewer"),
            "{spec_name}: {}",
            r.out
        );
        assert!(
            r.err.contains(&format!(
                "warning: the specification states fairness (`{clause}`)"
            )),
            "{spec_name}: {}",
            r.err
        );
        assert!(
            r.err.contains("where TLC and Apalache check them"),
            "{spec_name}: {}",
            r.err
        );
        // A liveness property under it is checked with the clause assumed:
        // every lasso the search would otherwise find may be unfair, and an
        // unfair lasso is not a counterexample to the specification.
        std::fs::write(dir.join("live.cfg"), format!("SPECIFICATION {spec_name}\n")).expect("cfg");
        let r = run(&[
            "check",
            &format!("--config={}", dir.join("live.cfg").display()),
            "--temporal=Inv",
            "--length=3",
            // The property alone: with the deadlock question on too, the run
            // is two passes and the outcome line is the run's, not the
            // pass's.
            "--no-deadlock",
            spec.to_str().expect("a path"),
        ]);
        assert_eq!(
            r.code, 0,
            "{spec_name}: stdout: {}\nstderr: {}",
            r.out, r.err
        );
        assert!(
            r.out.contains(&format!(
                "Assuming fairness of the temporal property: `{clause}`"
            )),
            "{spec_name}: {}",
            r.out
        );
        assert!(
            r.out
                .contains("no lasso of 3 step(s) or fewer violates `Inv`"),
            "{spec_name}: {}",
            r.out
        );
        assert!(
            r.out.contains(
                "NoError (no violating lasso within the bound satisfies the specification's \
                 fairness assumptions)"
            ),
            "{spec_name}: {}",
            r.out
        );
    }
    let _ = std::fs::remove_dir_all(&dir);
}

/// Any other temporal conjunct is declined by name too: `[]P` in the
/// formula is a property of behaviours, and a bounded `Init`/`Next`
/// unrolling would answer a different question than the one asked.
#[test]
fn a_cfg_with_a_temporal_clause_is_declined_by_name() {
    let dir = scratch("cfg-spec-temporal");
    let spec = write_spec(
        &dir,
        "Temporal",
        r"
---- MODULE Temporal ----
EXTENDS Integers
VARIABLE x
Init == x = 0
Next == x' = x + 1
Spec == Init /\ [][Next]_x /\ [](x >= 0)
Inv == x < 3
====
",
    );
    std::fs::write(
        dir.join("Temporal.cfg"),
        "SPECIFICATION Spec\nINVARIANT Inv\n",
    )
    .expect("cfg");
    let r = run(&[
        "check",
        &format!("--config={}", dir.join("Temporal.cfg").display()),
        "--length=3",
        spec.to_str().expect("a path"),
    ]);
    assert_eq!(r.code, 75, "stdout: {}\nstderr: {}", r.out, r.err);
    assert!(r.err.contains("the conjunct `[](x >= 0)`"), "{}", r.err);
    let _ = std::fs::remove_dir_all(&dir);
}

/// `--init`/`--next` next to a `SPECIFICATION`: refused rather than applied
/// (half the formula would be overridden) or ignored (a silent no-op).
#[test]
fn init_and_next_are_refused_next_to_a_specification() {
    let dir = scratch("cfg-spec-override");
    let spec = write_spec(
        &dir,
        "SpecRepro",
        r"
---- MODULE SpecRepro ----
VARIABLE x
Init == x = FALSE
Next == x' = x
Spec == Init /\ [][Next]_x
Inv == x = FALSE
====
",
    );
    std::fs::write(
        dir.join("SpecRepro.cfg"),
        "SPECIFICATION Spec\nINVARIANT Inv\n",
    )
    .expect("cfg");
    let r = run(&[
        "check",
        &format!("--config={}", dir.join("SpecRepro.cfg").display()),
        "--init=Init",
        "--length=0",
        spec.to_str().expect("a path"),
    ]);
    assert_eq!(r.code, 255, "stdout: {}\nstderr: {}", r.out, r.err);
    assert!(
        r.err.contains("--init/--next cannot be combined"),
        "{}",
        r.err
    );
    let _ = std::fs::remove_dir_all(&dir);
}

/// The Toolbox's model-file shape: `MC.tla` EXTENDS the specification and
/// `MC.cfg` says `SPECIFICATION Spec`. The formula and both roles live in
/// the extended module. And the roles are read **there**: `MC.tla`'s own
/// `Init` override does not change what `Spec` says (TLC reads the formula
/// in its own module), while `INIT Init` names the override – the two
/// configurations are different specifications, and the difference shows.
#[test]
fn a_specification_in_an_extended_module_is_read_in_its_own_module() {
    let dir = scratch("cfg-spec-extends");
    std::fs::write(
        dir.join("Base.tla"),
        r#"
---- MODULE Base ----
EXTENDS Integers
CONSTANT N
VARIABLE x
Init == x = 0
Next == x < N /\ x' = x + 1
Spec == Init /\ [][Next]_x
====
"#,
    )
    .expect("Base");
    let spec = std::fs::write(
        dir.join("MC.tla"),
        r#"
---- MODULE MC ----
EXTENDS Base, TLC
CONSTANT N
ASSUME N \in Nat
Init == x = 100
NoHundred == x # 100
====
"#,
    )
    .map(|_| dir.join("MC.tla"))
    .expect("MC");
    // `SPECIFICATION Spec`: Base's `Init` (x = 0) – the override is not read.
    std::fs::write(
        dir.join("MC.cfg"),
        "CONSTANT N = 3\nSPECIFICATION Spec\nINVARIANT NoHundred\n",
    )
    .expect("cfg");
    let r = run(&[
        "check",
        &format!("--config={}", dir.join("MC.cfg").display()),
        "--length=2",
        spec.to_str().expect("a path"),
    ]);
    assert_eq!(r.code, 0, "stdout: {}\nstderr: {}", r.out, r.err);
    assert!(
        r.out.contains("no counterexample of 2 step(s) or fewer"),
        "{}",
        r.out
    );
    // `INIT Init`: MC's own override (x = 100) – a violation at step 0.
    std::fs::write(
        dir.join("MC.cfg"),
        "CONSTANT N = 3\nINIT Init\nNEXT Next\nINVARIANT NoHundred\n",
    )
    .expect("cfg");
    let r = run(&[
        "check",
        &format!("--config={}", dir.join("MC.cfg").display()),
        "--length=2",
        spec.to_str().expect("a path"),
    ]);
    assert_eq!(r.code, 12, "stdout: {}\nstderr: {}", r.out, r.err);
    assert!(r.out.contains("counterexample 1: 0 step(s)"), "{}", r.out);
    let _ = std::fs::remove_dir_all(&dir);
}

// ======== the option table and subcommands (issue #27) ========

/// Performance-only knobs are accepted with a note; verdict-changing ones
/// are implemented or refused with the reason; unknown stays fatal.
#[test]
fn the_option_table_classes() {
    let dir = scratch("opts");
    let spec = write_spec(&dir, "Counter", COUNTER);

    // AcceptedNoEffect: a script from Apalache runs unchanged.
    let r = run(&[
        "check",
        "--inv=Inv",
        "--length=1",
        "--algo=incremental",
        "--smt-solver=z3",
        "--debug",
        spec.to_str().expect("a path"),
    ]);
    assert_eq!(r.code, 0, "stdout: {}\nstderr: {}", r.out, r.err);
    assert!(r.err.contains("--algo"), "{}", r.err);

    // Refused, with the reason said out loud: a wall-clock timeout would
    // make verdicts machine-load-dependent, which this checker refuses on
    // principle.
    let r = run(&[
        "check",
        "--inv=Inv",
        "--timeout-smt=10",
        spec.to_str().expect("a path"),
    ]);
    assert_eq!(r.code, 255, "stderr: {}", r.err);
    assert!(r.err.contains("deterministic"), "{}", r.err);

    // Temporal properties are implemented (issue #29): a property the
    // module does not define is refused by name, as `--inv`'s is.
    let r = run(&["check", "--temporal=Always", spec.to_str().expect("a path")]);
    assert_eq!(r.code, 75, "stdout: {}\nstderr: {}", r.out, r.err);
    assert!(
        r.err.contains("no zero-argument definition named `Always`"),
        "{}",
        r.err
    );

    // Unknown stays fatal.
    let r = run(&[
        "check",
        "--inv=Inv",
        "--nonsense",
        spec.to_str().expect("a path"),
    ]);
    assert_eq!(r.code, 255, "stderr: {}", r.err);
    let _ = std::fs::remove_dir_all(&dir);
}

/// Apalache's stdout contract: `Output directory:`, `The outcome is:`, and
/// the final `EXITCODE:` line, which scripts grep.
#[test]
fn the_stdout_contract_is_apalaches() {
    let dir = scratch("stdout");
    let spec = write_spec(&dir, "Counter", COUNTER);
    let out = dir.join("out");
    let r = run(&[
        "check",
        "--inv=Inv",
        "--length=2",
        &format!("--out-dir={}", out.display()),
        spec.to_str().expect("a path"),
    ]);
    assert_eq!(r.code, 0, "stdout: {}\nstderr: {}", r.out, r.err);
    assert!(r.out.contains("Output directory:"), "{}", r.out);
    assert!(r.out.contains("The outcome is: NoError"), "{}", r.out);
    assert!(r.out.contains("EXITCODE: OK"), "{}", r.out);

    let r = run(&[
        "check",
        "--inv=Inv",
        "--length=6",
        &format!("--out-dir={}", out.display()),
        spec.to_str().expect("a path"),
    ]);
    assert_eq!(r.code, 12, "stdout: {}\nstderr: {}", r.out, r.err);
    assert!(r.out.contains("The outcome is: Error"), "{}", r.out);
    assert!(r.out.contains("EXITCODE: ERROR (12)"), "{}", r.out);
    let _ = std::fs::remove_dir_all(&dir);
}

/// `parse` and `typecheck` are their own subcommands with their own codes:
/// 150 for a file that does not parse, 120 for one that does not type
/// check, 0 otherwise – Apalache's cheap syntax gates.
#[test]
fn parse_and_typecheck_are_subcommands() {
    let dir = scratch("subcmd");
    let good = write_spec(&dir, "Good", COUNTER);
    let bad = write_spec(&dir, "BadSyntax", "---- MODULE BadSyntax ----\nInit ==\n");
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

    let r = run(&["parse", good.to_str().expect("a path")]);
    assert_eq!(r.code, 0, "stdout: {}\nstderr: {}", r.out, r.err);
    assert!(r.out.contains("Parser has found no errors"), "{}", r.out);

    let r = run(&["parse", bad.to_str().expect("a path")]);
    assert_eq!(r.code, 150, "stdout: {}\nstderr: {}", r.out, r.err);
    assert!(r.out.contains("Parser has found an error"), "{}", r.out);
    assert!(r.out.contains("EXITCODE: ERROR (150)"), "{}", r.out);

    let r = run(&["typecheck", good.to_str().expect("a path")]);
    assert_eq!(r.code, 0, "stdout: {}\nstderr: {}", r.out, r.err);
    assert!(r.out.contains("no errors"), "{}", r.out);

    let r = run(&["typecheck", bad_types.to_str().expect("a path")]);
    assert_eq!(r.code, 120, "stdout: {}\nstderr: {}", r.out, r.err);
    assert!(
        r.out.contains("Type checker has found an error"),
        "{}",
        r.out
    );
    let _ = std::fs::remove_dir_all(&dir);
}

/// The unsupported subcommands refuse with the reason, not a usage dump.
#[test]
fn unsupported_subcommands_refuse_with_reasons() {
    let dir = scratch("refuse");
    let spec = write_spec(&dir, "Counter", COUNTER);
    for (mode, needle) in [
        ("server", "Quint"),
        ("transpile", "intermediate-format"),
        ("config", "not supported"),
    ] {
        let r = run(&[mode, spec.to_str().expect("a path")]);
        assert_eq!(r.code, 255, "{mode}: stdout: {}\nstderr: {}", r.out, r.err);
        assert!(r.err.contains(needle), "{mode}: {}", r.err);
    }
    let _ = std::fs::remove_dir_all(&dir);
}

// ======== simulate: sampled behaviours (issue #28) ========

const WALK: &str = r"
---- MODULE Walk ----
EXTENDS Integers
VARIABLE x
Init == x = 0
Next == \/ /\ x < 6 /\ x' = x + 1
        \/ /\ x > 2 /\ x' = x - 2
Inv == x < 6
View == <<x>>
====
";

/// `simulate` samples: at each step one *enabled* disjunct is taken, and a
/// violation found in a run is a real counterexample – exit 12, replayed,
/// with its `example<r>.itf.json` when `--output-traces` says so.
#[test]
fn simulate_reports_a_sampled_violation() {
    let dir = scratch("simviol");
    let spec = write_spec(&dir, "Walk", WALK);
    let out = dir.join("out");
    let r = run(&[
        "simulate",
        "--inv=Inv",
        "--length=10",
        "--max-run=5",
        "--seed=0",
        "--output-traces",
        &format!("--out-dir={}", out.display()),
        spec.to_str().expect("a path"),
    ]);
    assert_eq!(r.code, 12, "stderr: {}", r.err);
    assert!(r.out.contains("counterexample in run"), "{}", r.out);
    assert!(r.out.contains("independently replayed: yes"), "{}", r.out);
    // Whichever run found it, its example file is there (a run that never
    // violates writes no file of its own unless it completes the length).
    let wrote_one = std::fs::read_dir(&out)
        .map(|entries| {
            entries
                .filter_map(|e| e.ok())
                .any(|e| e.file_name().to_string_lossy().starts_with("example"))
        })
        .unwrap_or(false);
    assert!(wrote_one, "an example file");
    let _ = std::fs::remove_dir_all(&dir);
}

/// A sampler never claims absence of errors beyond its runs, and its "no
/// error" message says exactly that.
#[test]
fn simulate_no_error_is_about_the_sampled_runs() {
    let dir = scratch("simok");
    let spec = write_spec(&dir, "Walk", WALK);
    let r = run(&[
        "simulate",
        "--inv=Inv",
        "--length=4",
        "--max-run=3",
        "--seed=1",
        spec.to_str().expect("a path"),
    ]);
    assert_eq!(r.code, 0, "stderr: {}", r.err);
    assert!(r.out.contains("NoError in 3 sampled run(s)"), "{}", r.out);
    assert!(r.out.contains("not an exhaustive search"), "{}", r.out);
    let _ = std::fs::remove_dir_all(&dir);
}

/// The same seed gives byte-identical sampled behaviour – where Apalache's
/// simulation is not reproducible, this one is a deterministic function of
/// `--seed`, and a reported bug must replay from the seed alone.
#[test]
fn simulate_is_seed_deterministic() {
    let dir = scratch("simseed");
    let spec = write_spec(&dir, "Walk", WALK);
    let mut outs = Vec::new();
    for _ in 0..2 {
        let out = dir.join(format!("o{}", outs.len()));
        let r = run(&[
            "simulate",
            "--inv=Inv",
            "--length=4",
            "--max-run=5",
            "--seed=7",
            "--output-traces",
            &format!("--out-dir={}", out.display()),
            spec.to_str().expect("a path"),
        ]);
        assert_eq!(r.code, 0, "stderr: {}", r.err);
        let mut files: Vec<(String, String)> = Vec::new();
        for e in std::fs::read_dir(&out).expect("the output dir") {
            let p = e.expect("entry").path();
            if p.extension().and_then(|e| e.to_str()) == Some("json") {
                files.push((
                    p.file_name().unwrap().to_string_lossy().into_owned(),
                    std::fs::read_to_string(&p).expect("the trace"),
                ));
            }
        }
        files.sort();
        outs.push(files);
    }
    assert_eq!(outs[0], outs[1], "byte-identical across identical seeds");
    let _ = std::fs::remove_dir_all(&dir);
}

/// A role may name a member of an **unnamed** instance – `INSTANCE y2k
/// WITH …` makes `Init`, `Next` and `Safety` visible unprefixed – which is
/// the y2k simulate cell's very shape.
#[test]
fn a_role_may_name_an_open_instance_member() {
    let dir = scratch("siminst");
    let spec = write_spec(
        &dir,
        "y2k_instance",
        r"
---------------------------- MODULE y2k_instance ----------------------------
VARIABLE
    \* @type: Int;
    year,
    \* @type: Bool;
    hasLicense

INSTANCE y2k WITH BIRTH_YEAR <- 80, LICENSE_AGE <- 18
=============================================================================
",
    );
    write_spec(
        &dir,
        "y2k",
        r"
---- MODULE y2k ----
EXTENDS Integers
CONSTANT BIRTH_YEAR, LICENSE_AGE
VARIABLE year, hasLicense
Init == year = 0 /\ hasLicense = FALSE
Next == year' = year + 1 /\ hasLicense' = hasLicense
Safety == year < 100
====
",
    );
    let r = run(&[
        "simulate",
        "--inv=Safety",
        "--length=10",
        "--max-run=2",
        "--seed=0",
        spec.to_str().expect("a path"),
    ]);
    assert_eq!(r.code, 0, "stderr: {}", r.err);
    assert!(r.out.contains("NoError in 2 sampled run(s)"), "{}", r.out);
    let _ = std::fs::remove_dir_all(&dir);
}

// ---- issue #29: `--temporal` ----

const CYCLE: &str = r"
---- MODULE Cycle ----
EXTENDS Integers
VARIABLE x
Init == x = 0
Next == x' = IF x = 0 THEN 1 ELSE 0
Never == [](x = 1)
Always == [](x < 2)
Fair == WF_x(x' # x)
Inv == x < 2
Bad == x = 0
View == <<x>>
====
";

/// A violating lasso is exit **12** with a `violation1.itf.json` whose
/// `loop` field names the loop's start state (ADR-015), and the outcome
/// line says it is a lasso.
#[test]
fn a_violating_lasso_is_exit_12_with_a_loop_field() {
    let dir = scratch("lasso");
    let spec = write_spec(&dir, "Cycle", CYCLE);
    let r = run(&[
        "check",
        "--temporal=Never",
        "--length=6",
        &format!("--out-dir={}", dir.display()),
        spec.to_str().expect("a path"),
    ]);
    assert_eq!(r.code, 12, "stderr: {}", r.err);
    assert!(r.out.contains("a lasso of"), "{}", r.out);
    let file = std::fs::read_to_string(dir.join("violation1.itf.json")).expect("the ITF file");
    let doc: serde_json::Value = serde_json::from_str(&file).expect("JSON");
    // The shortest lasso: `s0 -> s1 -> s0`, the loop starting in the first
    // state (`__InLoop` turns true on the step into it). It used to be
    // found one step longer, rotated to start in `s1`: the tableau fixed
    // `unroll` at `Init` as well as by its step-0 equation, and for a loop
    // starting in the first state the two contradict each other whenever
    // a `[]` argument is false there (`temporal.rs`).
    assert_eq!(doc["loop"], serde_json::json!(1), "{doc}");
    // The spec's variables and `__InLoop` are shown; the tableau's
    // bookkeeping is not.
    let vars: Vec<&str> = doc["vars"]
        .as_array()
        .expect("vars")
        .iter()
        .map(|v| v.as_str().expect("a name"))
        .collect();
    assert!(
        vars.contains(&"x") && vars.contains(&"__InLoop"),
        "{vars:?}"
    );
    assert!(
        vars.iter().all(|v| !v.starts_with("__temporal_")),
        "{vars:?}"
    );
    let _ = std::fs::remove_dir_all(&dir);
}

/// No violating lasso within the bound is exit **0**, and the message says
/// it is a bound – never that the property holds.
#[test]
fn no_violating_lasso_is_exit_0_and_says_bound() {
    let dir = scratch("lasso-ok");
    let spec = write_spec(&dir, "Cycle", CYCLE);
    let r = run(&[
        "check",
        "--temporal=Always",
        "--length=6",
        spec.to_str().expect("a path"),
    ]);
    assert_eq!(r.code, 0, "stderr: {}", r.err);
    assert!(r.out.contains("this is a bound, not a proof"), "{}", r.out);
    // And never the affirmative: every mention of "the property holds"
    // is inside the disclaimer.
    for line in r.out.lines().filter(|l| l.contains("the property holds")) {
        assert!(line.contains("not a proof"), "an unqualified claim: {line}");
    }
    let _ = std::fs::remove_dir_all(&dir);
}

/// `--inv=<a temporal formula>` is exit **255** – Apalache's integration
/// corpus has this exact cell (`check --inv=FalseLiveness LongPrefix.tla`
/// → `EXITCODE: ERROR (255)`). A temporal formula asked for as an invariant
/// is refused before any pass runs, under `--temporal` too.
#[test]
fn inv_naming_a_temporal_formula_is_exit_255() {
    let dir = scratch("inv-temporal");
    let spec = write_spec(&dir, "Cycle", CYCLE);
    let r = run(&[
        "check",
        "--inv=Never",
        "--length=4",
        spec.to_str().expect("a path"),
    ]);
    assert_eq!(r.code, 255, "stderr: {}", r.err);
    assert!(r.err.contains("temporal"), "{}", r.err);
    let r = run(&[
        "check",
        "--temporal=Never",
        "--inv=Always",
        "--length=4",
        spec.to_str().expect("a path"),
    ]);
    assert_eq!(r.code, 255, "stdout: {}\nstderr: {}", r.out, r.err);
    assert!(r.err.contains("temporal"), "{}", r.err);
    let _ = std::fs::remove_dir_all(&dir);
}

// ======== `PROPERTY` in the configuration, and passes (issues #29, #31) ========

/// `PROPERTY` in a `.cfg` is a temporal property, and Apalache checks it
/// beside the invariants. Until it was read here the line was parsed and
/// dropped: a configuration could report `NoError` with a liveness property
/// in it unexamined. A `check` is now one pass for the invariants and the
/// deadlock question, then one per property; the outcome is the worst of
/// them, and each counterexample is written and numbered across the run.
#[test]
fn a_cfg_property_is_checked_beside_the_invariants() {
    let dir = scratch("cfg-property");
    let spec = write_spec(&dir, "Cycle", CYCLE);
    std::fs::write(dir.join("Cycle.cfg"), "INVARIANT Inv\nPROPERTY Never\n").expect("cfg");
    let out = dir.join("out");
    let r = run(&[
        "check",
        &format!("--config={}", dir.join("Cycle.cfg").display()),
        "--length=4",
        &format!("--out-dir={}", out.display()),
        spec.to_str().expect("a path"),
    ]);
    assert_eq!(r.code, 12, "stdout: {}\nstderr: {}", r.out, r.err);
    // Two passes, each with its heading and its own result.
    let lines: Vec<&str> = r.out.lines().collect();
    assert!(lines.contains(&"checking invariant(s) Inv"), "{}", r.out);
    assert!(
        lines.contains(&"checking temporal property `Never`"),
        "{}",
        r.out
    );
    assert!(
        r.out.contains("  no counterexample of 4 step(s) or fewer"),
        "{}",
        r.out
    );
    assert!(
        r.out.contains("  counterexample 1: a lasso of"),
        "{}",
        r.out
    );
    // One outcome line, for the whole run.
    assert_eq!(r.out.matches("The outcome is:").count(), 1, "{}", r.out);
    assert!(r.out.contains("The outcome is: Error"), "{}", r.out);
    let doc: serde_json::Value = serde_json::from_str(
        &std::fs::read_to_string(out.join("violation1.itf.json")).expect("the ITF file"),
    )
    .expect("JSON");
    assert_eq!(doc["loop"], serde_json::json!(1), "{doc}");
    let _ = std::fs::remove_dir_all(&dir);
}

/// The other order of bad news: the invariant breaks first, `--max-error`
/// is reached, and the property pass is not run – said out loud, never
/// reported as if it had held. With two errors asked for, both passes run
/// and the two traces are numbered across the run.
#[test]
fn max_error_stops_before_a_later_pass_and_says_so() {
    let dir = scratch("cfg-property-max");
    let spec = write_spec(&dir, "Cycle", CYCLE);
    std::fs::write(dir.join("Cycle.cfg"), "INVARIANT Bad\nPROPERTY Never\n").expect("cfg");
    let r = run(&[
        "check",
        &format!("--config={}", dir.join("Cycle.cfg").display()),
        "--length=4",
        spec.to_str().expect("a path"),
    ]);
    assert_eq!(r.code, 12, "stdout: {}\nstderr: {}", r.out, r.err);
    assert!(
        r.out.contains("counterexample 1: 1 step(s), invariant Bad"),
        "{}",
        r.out
    );
    assert!(
        !r.out.contains("temporal property"),
        "the pass did not run: {}",
        r.out
    );
    assert!(
        r.err
            .contains("--max-error=1 reached; the remaining passes are not run"),
        "{}",
        r.err
    );
    let out = dir.join("out");
    let r = run(&[
        "check",
        &format!("--config={}", dir.join("Cycle.cfg").display()),
        "--length=4",
        "--max-error=2",
        "--view=View",
        &format!("--out-dir={}", out.display()),
        spec.to_str().expect("a path"),
    ]);
    assert_eq!(r.code, 12, "stdout: {}\nstderr: {}", r.out, r.err);
    assert!(
        r.out.contains("counterexample 1: 1 step(s), invariant Bad"),
        "{}",
        r.out
    );
    assert!(r.out.contains("counterexample 2: a lasso of"), "{}", r.out);
    assert!(out.join("violation2.itf.json").exists(), "{}", r.out);
    let _ = std::fs::remove_dir_all(&dir);
}

/// A configuration with only a `PROPERTY` is one temporal pass, with the
/// same words `--temporal` uses; and `--temporal` on the command line
/// overrides the file's property, with a warning, as `--inv` does.
#[test]
fn a_property_only_config_is_a_temporal_pass_and_the_cli_overrides() {
    let dir = scratch("cfg-property-only");
    let spec = write_spec(&dir, "Cycle", CYCLE);
    // Deadlock checking is on by default, so this is two passes: the
    // deadlock question, then the property – each under its heading.
    std::fs::write(dir.join("Cycle.cfg"), "PROPERTY Always\n").expect("cfg");
    let r = run(&[
        "check",
        &format!("--config={}", dir.join("Cycle.cfg").display()),
        "--length=4",
        spec.to_str().expect("a path"),
    ]);
    assert_eq!(r.code, 0, "stdout: {}\nstderr: {}", r.out, r.err);
    assert!(r.out.contains("checking deadlocks"), "{}", r.out);
    assert!(
        r.out
            .contains("  no lasso of 4 step(s) or fewer violates `Always`; this is a bound"),
        "{}",
        r.out
    );
    assert_eq!(r.out.matches("The outcome is:").count(), 1, "{}", r.out);
    // With the deadlock question off it is one temporal pass, with the same
    // words `--temporal` uses.
    std::fs::write(
        dir.join("Cycle.cfg"),
        "PROPERTY Always\nCHECK_DEADLOCK FALSE\n",
    )
    .expect("cfg");
    let r = run(&[
        "check",
        &format!("--config={}", dir.join("Cycle.cfg").display()),
        "--length=4",
        spec.to_str().expect("a path"),
    ]);
    assert_eq!(r.code, 0, "stdout: {}\nstderr: {}", r.out, r.err);
    assert!(
        r.out
            .contains("no lasso of 4 step(s) or fewer violates `Always`; this is a bound"),
        "{}",
        r.out
    );
    assert!(
        r.out
            .contains("The outcome is: NoError (no violating lasso within the bound)"),
        "{}",
        r.out
    );
    assert_eq!(r.out.matches("The outcome is:").count(), 1, "{}", r.out);
    // And `--temporal` on the command line overrides the file's property,
    // with a warning, as `--inv` does over `INVARIANT`.
    let r = run(&[
        "check",
        &format!("--config={}", dir.join("Cycle.cfg").display()),
        "--temporal=Never",
        "--length=4",
        spec.to_str().expect("a path"),
    ]);
    assert_eq!(r.code, 12, "stdout: {}\nstderr: {}", r.out, r.err);
    assert!(
        r.err
            .contains("--temporal=Never overrides PROPERTY from the config (Always)"),
        "{}",
        r.err
    );
    assert!(r.out.contains("a lasso of"), "{}", r.out);
    let _ = std::fs::remove_dir_all(&dir);
}

/// Sampling does not check properties; it says so rather than dropping them.
#[test]
fn simulate_announces_the_properties_it_does_not_check() {
    let dir = scratch("cfg-property-sim");
    let spec = write_spec(&dir, "Cycle", CYCLE);
    std::fs::write(dir.join("Cycle.cfg"), "PROPERTY Always\n").expect("cfg");
    let r = run(&[
        "simulate",
        &format!("--config={}", dir.join("Cycle.cfg").display()),
        "--max-run=2",
        "--length=3",
        spec.to_str().expect("a path"),
    ]);
    assert_eq!(r.code, 0, "stdout: {}\nstderr: {}", r.out, r.err);
    assert!(
        r.err
            .contains("simulate does not check temporal properties; `Always` not checked"),
        "{}",
        r.err
    );
    let _ = std::fs::remove_dir_all(&dir);
}

/// A fairness construct is **declined by name** (exit 75, the lowering
/// bucket), never dropped: a dropped fairness conjunct invents
/// counterexamples.
#[test]
fn fairness_in_a_temporal_property_is_declined_by_name() {
    let dir = scratch("lasso-fair");
    let spec = write_spec(&dir, "Cycle", CYCLE);
    let r = run(&[
        "check",
        "--temporal=Fair",
        "--length=4",
        spec.to_str().expect("a path"),
    ]);
    assert_eq!(r.code, 75, "stderr: {}", r.err);
    assert!(r.err.contains("fairness"), "{}", r.err);
    let _ = std::fs::remove_dir_all(&dir);
}

/// Issue #44: a temporal check does not look for deadlocks unless asked.
/// The lasso encoding's "state with no successor" is a question about the
/// encoding's variables – and on a spec with a ranged variable the search
/// for one is the hardest query of the run (seconds to minutes per depth
/// against microseconds for the property itself). `--deadlock` turns it
/// back on.
#[test]
fn a_temporal_check_skips_the_deadlock_search_unless_asked() {
    let dir = scratch("lasso-nodeadlock");
    let spec = write_spec(
        &dir,
        "Cycle",
        r"
---- MODULE Cycle ----
EXTENDS Integers
VARIABLE x
Init == x = 0
Next == x' = IF x = 0 THEN 1 ELSE 0
Never == [](x = 1)
====
",
    );
    let r = run(&[
        "check",
        "--temporal=Never",
        "--length=6",
        spec.to_str().expect("a path"),
    ]);
    assert_eq!(r.code, 12, "stderr: {}", r.err);
    // The run never asked the deadlock question (no `Deadlock` outcome).
    assert!(r.out.contains("a lasso of"), "{}", r.out);
    assert!(!r.out.contains("Deadlock"), "{}", r.out);
    // Explicitly asked for, the search runs – and finds none on a lasso
    // whose loop state has a successor by construction.
    let r = run(&[
        "check",
        "--temporal=Never",
        "--deadlock",
        "--length=6",
        spec.to_str().expect("a path"),
    ]);
    assert_eq!(r.code, 12, "stderr: {}", r.err);
    let _ = std::fs::remove_dir_all(&dir);
}
