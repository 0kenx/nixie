//! Deadlock checking (issue #26).
//!
//! Apalache's `check` looks for deadlocks **by default**: a reachable state
//! no transition leaves. The no-successor half is a *proof* – the `Next`
//! query at a step comes back `Unsat` over every state that has a successor
//! – never a sample; an undecided query anywhere makes the whole verdict
//! `Unknown`. `--no-deadlock` (and `CHECK_DEADLOCK FALSE`) turns it off, and
//! then a search that finds nothing must also say whether any behaviour ran
//! the full length: `ExecutionsTooShort`, not a silent "no error".

use nixie_core::TermManager;
use nixie_tla_check::bmc::{Bmc, Outcome, Roles};
use std::path::{Path, PathBuf};
use std::process::Command;

fn scratch(name: &str) -> PathBuf {
    let dir = std::env::temp_dir().join(format!("nixie-tla-dl-{name}-{}", std::process::id()));
    let _ = std::fs::remove_dir_all(&dir);
    std::fs::create_dir_all(&dir).expect("a scratch directory");
    dir
}

/// A counter that stops: after three increments no transition is enabled.
const STUCK: &str = r#"
---- MODULE Stuck ----
EXTENDS Integers
VARIABLE x
Init == x = 0
Next == x < 3 /\ x' = x + 1
====
"#;

/// The same specification with an invariant that never fails.
const STUCK_INV: &str = r#"
---- MODULE StuckInv ----
EXTENDS Integers
VARIABLE x
Init == x = 0
Next == x < 3 /\ x' = x + 1
Inv == x < 9
====
"#;

/// An invariant that *does* fail, one step before the deadlock.
const STUCK_BAD: &str = r#"
---- MODULE StuckBad ----
EXTENDS Integers
VARIABLE x
Init == x = 0
Next == x < 3 /\ x' = x + 1
Inv == x # 2
====
"#;

fn claim(src: &str, depth: u32, deadlocks: bool) -> Outcome {
    let parsed = nixie_tla_syntax::parse_file(src).expect("parses");
    let spec = nixie_tla_syntax::LoadedSpec::single(parsed);
    let module = spec.root_module().expect("has a root module");
    let mut tm = TermManager::new();
    let invs: &[&str] = if src.contains("Inv ==") {
        &["Inv"]
    } else {
        &[]
    };
    let mut bmc = Bmc::prepare_with_config(
        &spec,
        module,
        Roles {
            init: "Init",
            next: "Next",
            inv: invs,
            constraints: &[],
        },
        &nixie_tla_syntax::TlcConfig::default(),
        &mut tm,
    )
    .expect("prepares");
    bmc.set_check_deadlocks(deadlocks);
    bmc.check(depth, &mut tm).expect("checks")
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

fn write_spec(dir: &Path, name: &str, body: &str) -> PathBuf {
    let p = dir.join(format!("{name}.tla"));
    std::fs::write(&p, body).expect("writes the specification");
    p
}

// ======== the deadlock itself ========

/// The counter stops at `x = 3`: no transition leaves it, and the search
/// says **Deadlock** at exactly step 3 – the earliest step whose every
/// reachable state is stuck.
#[test]
fn a_deadlock_is_found_at_the_step_it_happens() {
    assert_eq!(claim(STUCK, 4, true), Outcome::Deadlock { step: 3 });
}

/// With the deadlock check off and an invariant that holds, a bound the
/// behaviours cannot reach is not "no error" – it is `ExecutionsTooShort`.
#[test]
fn executions_too_short_when_nothing_reaches_the_bound() {
    assert_eq!(claim(STUCK_INV, 4, false), Outcome::ExecutionsTooShort);
    // ...and a bound within reach is the ordinary clean verdict.
    assert_eq!(claim(STUCK_INV, 2, false), Outcome::NoViolationWithin(2));
}

/// A counterexample outranks the deadlock at the same step – the invariant
/// is checked first, per step, which is Apalache's order and the order a
/// user reading a report wants: the bug before the liveness footnote.
#[test]
fn an_invariant_violation_wins_over_the_deadlock() {
    assert_eq!(claim(STUCK_BAD, 4, true), Outcome::Violation { step: 2 });
}

// ======== the CLI surface ========

/// The whole matrix on one specification: default finds the deadlock (12),
/// `--no-deadlock` finds nothing to run the length (0, ExecutionsTooShort),
/// and a `CHECK_DEADLOCK FALSE` config behaves as the flag.
#[test]
fn the_cli_deadlock_matrix() {
    let dir = scratch("matrix");
    let spec = write_spec(&dir, "StuckInv", STUCK_INV);

    // Default: deadlock on, found, exit 12, Apalache's outcome line.
    let r = run(&[
        "check",
        "--inv=Inv",
        "--length=4",
        spec.to_str().expect("a path"),
    ]);
    assert_eq!(r.code, 12, "stdout: {}\nstderr: {}", r.out, r.err);
    assert!(r.out.contains("The outcome is: Deadlock"), "{}", r.out);

    // `--no-deadlock`: no full-length behaviour, exit 0 with the
    // distinction in the message.
    let r = run(&[
        "check",
        "--inv=Inv",
        "--length=4",
        "--no-deadlock",
        spec.to_str().expect("a path"),
    ]);
    assert_eq!(r.code, 0, "stdout: {}\nstderr: {}", r.out, r.err);
    assert!(
        r.out.contains("The outcome is: ExecutionsTooShort"),
        "{}",
        r.out
    );

    // `CHECK_DEADLOCK FALSE` from a config: same behaviour as the flag,
    // and the precedence note is printed.
    std::fs::write(
        dir.join("nodl.cfg"),
        "CHECK_DEADLOCK FALSE\nINVARIANT Inv\n",
    )
    .expect("writes the cfg");
    let r = run(&[
        "check",
        "--length=4",
        &format!("--config={}", dir.join("nodl.cfg").display()),
        spec.to_str().expect("a path"),
    ]);
    assert_eq!(r.code, 0, "stdout: {}\nstderr: {}", r.out, r.err);
    assert!(r.out.contains("ExecutionsTooShort"), "{}", r.out);
    assert!(r.err.contains("Using CHECK_DEADLOCK=false"), "{}", r.err);
    let _ = std::fs::remove_dir_all(&dir);
}

/// A deadlock-only check, with no invariant named: a complete question on
/// its own, and `--inv` is optional exactly when the deadlock check is on.
#[test]
fn a_deadlock_only_check_needs_no_invariant() {
    let dir = scratch("only");
    let spec = write_spec(&dir, "Stuck", STUCK);
    let r = run(&["check", "--length=4", spec.to_str().expect("a path")]);
    assert_eq!(r.code, 12, "stdout: {}\nstderr: {}", r.out, r.err);
    assert!(r.out.contains("Deadlock"), "{}", r.out);
    // ...but with the deadlock check off too, there is nothing to check.
    let r = run(&[
        "check",
        "--length=4",
        "--no-deadlock",
        spec.to_str().expect("a path"),
    ]);
    assert_eq!(r.code, 255, "stderr: {}", r.err);
    let _ = std::fs::remove_dir_all(&dir);
}

// ======== action invariants ========

/// An action invariant constrains a step pair; `ActionInv.tla` in
/// Apalache's own suite is the acceptance shape, checked here inline.
#[test]
fn an_action_invariant_is_checked_over_step_pairs() {
    let src = r#"
---- MODULE ActionClaim ----
EXTENDS Integers
VARIABLE n
Init == n = 0
Next == n' = n + 1
IncreaseInv == n' > n
WrongInv == n' > n + 1
====
"#;
    let parsed = nixie_tla_syntax::parse_file(src).expect("parses");
    let spec = nixie_tla_syntax::LoadedSpec::single(parsed);
    let module = spec.root_module().expect("has a root module");
    let mut tm = TermManager::new();
    let mut bmc = Bmc::prepare_with_config(
        &spec,
        module,
        Roles {
            init: "Init",
            next: "Next",
            inv: &["IncreaseInv"],
            constraints: &[],
        },
        &nixie_tla_syntax::TlcConfig::default(),
        &mut tm,
    )
    .expect("prepares");
    assert_eq!(
        bmc.check(2, &mut tm).expect("checks"),
        Outcome::NoViolationWithin(2),
        "n strictly increases"
    );

    let mut tm = TermManager::new();
    let mut bmc = Bmc::prepare_with_config(
        &spec,
        module,
        Roles {
            init: "Init",
            next: "Next",
            inv: &["WrongInv"],
            constraints: &[],
        },
        &nixie_tla_syntax::TlcConfig::default(),
        &mut tm,
    )
    .expect("prepares");
    assert_eq!(
        bmc.check(2, &mut tm).expect("checks"),
        Outcome::Violation { step: 1 },
        "n' is n + 1, never n + 2 – the pair query refutes it"
    );
}

/// A temporal formula named by `--inv` is refused: it is a lasso question,
/// not a state property, and Apalache's exit code for it is the same 255.
#[test]
fn a_temporal_invariant_is_refused() {
    let src = r#"
---- MODULE TemporalInv ----
EXTENDS Integers
VARIABLE n
Init == n = 0
Next == n' = n + 1
Always == [](n < 5)
====
"#;
    let parsed = nixie_tla_syntax::parse_file(src).expect("parses");
    let spec = nixie_tla_syntax::LoadedSpec::single(parsed);
    let module = spec.root_module().expect("has a root module");
    let mut tm = TermManager::new();
    let err = match Bmc::prepare_with_config(
        &spec,
        module,
        Roles {
            init: "Init",
            next: "Next",
            inv: &["Always"],
            constraints: &[],
        },
        &nixie_tla_syntax::TlcConfig::default(),
        &mut tm,
    ) {
        Ok(_) => panic!("a temporal invariant must be refused"),
        Err(e) => e,
    };
    assert!(
        err.to_string().contains("temporal"),
        "the refusal should name the kind: {err}"
    );
}
