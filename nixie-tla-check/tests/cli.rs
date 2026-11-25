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

    // Temporal properties: refused, pointing at what exists today.
    let r = run(&[
        "check",
        "--inv=Inv",
        "--temporal=Always",
        spec.to_str().expect("a path"),
    ]);
    assert_eq!(r.code, 255, "stderr: {}", r.err);
    assert!(r.err.contains("--temporal"), "{}", r.err);

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
