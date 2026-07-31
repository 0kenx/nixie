//! Regression tests for the cli-p2 audit findings:
//!
//! 1. `oxiz-cli/src/model_counter.rs` — `--count-models` used to always
//!    report "Exact count: 0" (exact mode) or a fabricated statistical
//!    estimate derived from text heuristics alone (approximate mode),
//!    never actually invoking the solver.
//! 2. `oxiz-cli/src/main.rs` — `--timeout` (and the config-file timeout)
//!    were never enforced on the normal (non-portfolio) solving path, so
//!    a hard instance could hang the CLI forever despite an explicit
//!    user-supplied limit.

mod common;

use std::fs;
use std::path::PathBuf;
use std::process::{Command, Stdio};
use std::time::{Duration, Instant};

/// Get the path to the oxiz binary
fn oxiz_bin() -> PathBuf {
    PathBuf::from(env!("CARGO_BIN_EXE_oxiz"))
}

/// Wall-clock duration assertions in this file (how *quickly* a subprocess
/// returns, as opposed to whether it returns the right honest answer within
/// the hard-kill safety net) are flaky under shared-machine / CI load -- a
/// heavily loaded box can easily blow a tight "must be fast" budget on an
/// otherwise-correct run, with no bug involved. Gate them behind
/// `OXIZ_TIMING_TESTS=1`, matching the convention already established in
/// `tests/benchmark.rs`; the subprocess and its honesty (exit code, stdout
/// content) are still exercised and checked by default either way.
fn timing_asserts_enabled() -> bool {
    std::env::var("OXIZ_TIMING_TESTS").as_deref() == Ok("1")
}

/// Assert `elapsed` is under `budget`, but only when timing assertions are
/// enabled via `OXIZ_TIMING_TESTS=1`. Always prints the elapsed time either way.
fn assert_prompt(elapsed: Duration, budget: Duration, label: &str) {
    let enabled = timing_asserts_enabled();
    println!("{label}: {elapsed:?} (budget {budget:?}, timing asserts enabled: {enabled})");
    if enabled {
        assert!(elapsed < budget, "{label} took too long: {elapsed:?}");
    }
}

/// Create a unique temp `.smt2` script.
///
/// See `tests/common/mod.rs` for why this is collision-proof by
/// construction (pid + per-process counter) rather than timestamp-based,
/// and why it cleans up on `Drop` (including on panic).
fn write_temp_smt2(label: &str, content: &str) -> common::TempPath {
    common::TempPath::write(&format!("audit_cli_p2_{label}"), "smt2", content)
}

/// Build a pigeonhole-principle CNF (as SMT-LIB2) with `holes` holes and
/// `holes + 1` pigeons. PHP is UNSAT and, at this size, is hard enough for a
/// plain CDCL search (no dedicated pigeonhole reasoning) to run well past a
/// few seconds -- a real, not contrived, "hang forever without --timeout"
/// instance.
fn pigeonhole_script(holes: usize) -> String {
    let pigeons = holes + 1;
    let mut s = String::new();
    for i in 1..=pigeons {
        for j in 1..=holes {
            s.push_str(&format!("(declare-const p_{i}_{j} Bool)\n"));
        }
    }
    for i in 1..=pigeons {
        let disj: Vec<String> = (1..=holes).map(|j| format!("p_{i}_{j}")).collect();
        s.push_str(&format!("(assert (or {}))\n", disj.join(" ")));
    }
    for j in 1..=holes {
        for i1 in 1..=pigeons {
            for i2 in (i1 + 1)..=pigeons {
                s.push_str(&format!(
                    "(assert (or (not p_{i1}_{j}) (not p_{i2}_{j})))\n"
                ));
            }
        }
    }
    s.push_str("(check-sat)\n");
    s
}

/// Run `oxiz` with `args`, killing it if it hasn't finished within
/// `hard_kill_after` (a generous safety net so a regression in the timeout
/// watchdog cannot hang the test suite forever).
fn run_with_hard_kill(
    args: &[&str],
    hard_kill_after: Duration,
) -> (std::process::Output, Duration) {
    let mut child = Command::new(oxiz_bin())
        .args(args)
        .stdout(Stdio::piped())
        .stderr(Stdio::piped())
        .spawn()
        .expect("failed to spawn oxiz");

    let start = Instant::now();
    loop {
        if let Some(_status) = child.try_wait().expect("failed to poll child") {
            let elapsed = start.elapsed();
            let output = child
                .wait_with_output()
                .expect("failed to collect child output");
            return (output, elapsed);
        }
        if start.elapsed() > hard_kill_after {
            let _ = child.kill();
            let _ = child.wait();
            panic!(
                "oxiz did not exit within the hard-kill safety window ({:?}); \
                 --timeout is not being enforced",
                hard_kill_after
            );
        }
        std::thread::sleep(Duration::from_millis(50));
    }
}

// ---------------------------------------------------------------------
// Finding 1: --count-models must invoke the solver honestly.
// ---------------------------------------------------------------------

#[test]
fn count_models_exact_reports_real_count_not_zero() {
    let script = write_temp_smt2(
        "count_exact",
        r#"
            (declare-const x Bool)
            (declare-const y Bool)
            (assert (or x y))
        "#,
    );

    let output = Command::new(oxiz_bin())
        .args([
            "--count-models",
            "--count-method",
            "exact",
            script.to_str().unwrap(),
        ])
        .output()
        .expect("failed to execute oxiz");

    let stdout = String::from_utf8_lossy(&output.stdout);
    let _ = fs::remove_file(&script);

    // The original bug: this always printed "Exact count: 0" regardless of
    // the formula. `(or x y)` has exactly 3 models (all assignments except
    // x=y=false).
    assert!(
        stdout.contains("Exact count: 3"),
        "expected the real exact count (3), got:\n{stdout}"
    );
    assert!(
        !stdout.contains("Exact count: 0"),
        "must not fabricate a zero count for a satisfiable formula:\n{stdout}"
    );
}

#[test]
fn count_models_exact_unsat_is_genuinely_zero() {
    let script = write_temp_smt2(
        "count_exact_unsat",
        r#"
            (declare-const x Bool)
            (assert x)
            (assert (not x))
        "#,
    );

    let output = Command::new(oxiz_bin())
        .args([
            "--count-models",
            "--count-method",
            "exact",
            script.to_str().unwrap(),
        ])
        .output()
        .expect("failed to execute oxiz");

    let stdout = String::from_utf8_lossy(&output.stdout);
    let _ = fs::remove_file(&script);

    assert!(
        stdout.contains("Exact count: 0"),
        "an UNSAT formula genuinely has 0 models:\n{stdout}"
    );
}

#[test]
fn count_models_approximate_invokes_solver_not_text_heuristic() {
    let script = write_temp_smt2(
        "count_approx",
        r#"
            (declare-const x Bool)
            (declare-const y Bool)
            (declare-const z Bool)
            (assert (or x y z))
        "#,
    );

    let output = Command::new(oxiz_bin())
        .args([
            "--count-models",
            "--count-method",
            "approximate",
            script.to_str().unwrap(),
        ])
        .output()
        .expect("failed to execute oxiz");

    let stdout = String::from_utf8_lossy(&output.stdout);
    let _ = fs::remove_file(&script);

    // The original bug always printed a fabricated "Samples used: 1000" and
    // a fake 95% confidence interval, no matter the formula, without ever
    // solving anything. `(or x y z)` has a small variable space, so an
    // honest implementation falls back to full enumeration and reports the
    // *exact* count (7 out of 8 assignments), not a heuristic guess.
    assert!(
        stdout.contains("Exact count: 7") || stdout.contains("At least 7"),
        "expected the real model count derived from actually solving, got:\n{stdout}"
    );
    assert!(
        output.status.success(),
        "approximate counting should succeed on a small satisfiable formula:\n{stdout}"
    );
}

// ---------------------------------------------------------------------
// Finding 2: --timeout must actually bound the normal solving path.
// ---------------------------------------------------------------------

#[test]
fn timeout_bounds_a_hard_instance_and_reports_unknown() {
    // 11 pigeons into 10 holes: UNSAT, and hard enough for plain CDCL that
    // it does not finish quickly (verified empirically while writing this
    // test: it did not complete within 15s with no --timeout at all).
    let script = write_temp_smt2("timeout_hard", &pigeonhole_script(10));

    // Give the CLI a small, explicit timeout and an extremely generous
    // hard-kill safety net so a regression cannot hang the test suite. This
    // is deliberately huge (not just "a few times the --timeout"): unrelated
    // trivial CLI invocations elsewhere in this same test binary have been
    // observed to stall in lockstep for over 1200s on a heavily
    // oversubscribed/memory-pressured shared machine (many concurrent
    // solves/builds competing for the same cores and RAM), then all resume
    // and pass together -- i.e. the whole test process, not this specific
    // code, was starved. Since that kind of stall always eventually resolves
    // (unlike a genuine infinite hang), the safety net only needs to be
    // larger than any such stall, not tight -- it exists purely to catch a
    // regression that truly never returns.
    let (output, elapsed) = run_with_hard_kill(
        &["--timeout", "3", script.to_str().unwrap()],
        Duration::from_secs(1800),
    );
    let _ = fs::remove_file(&script);

    let stdout = String::from_utf8_lossy(&output.stdout);

    // The core, in-scope property of this fix: the CLI must never hang past
    // the configured deadline, no matter how the underlying solve is going.
    // (The 180s hard-kill above would have already panicked otherwise.) This
    // is a tighter, opt-in (see `assert_prompt`) check that the supervisor is
    // actually prompt under normal, non-pathological load.
    assert_prompt(
        elapsed,
        Duration::from_secs(60),
        "--timeout 3 pigeonhole run",
    );

    // If the CLI's own watchdog is what ended the run (exit code 124), it
    // must have reported the timeout honestly as "unknown" -- never a
    // fabricated sat/unsat. If instead the solve itself finished first
    // (e.g. a very fast machine, or scheduling luck under heavy concurrent
    // CI load), that is also acceptable: the fix is about not hanging
    // forever, not about forcing every hard instance to time out.
    if output.status.code() == Some(124) {
        assert!(
            stdout.contains("unknown"),
            "a timed-out solve must be reported honestly as 'unknown', not fabricated \
             sat/unsat, got:\n{stdout}"
        );
    }
}

/// Same regression as [`timeout_bounds_a_hard_instance_and_reports_unknown`],
/// with THEIRS's original tighter, non-gated timing bounds (30s hard-kill,
/// must return within 20s) kept as a separate test rather than dropped, since
/// it exercises a stricter promptness bound than the opt-in `assert_prompt`
/// check above.
#[test]
fn timeout_bounds_a_hard_instance_and_reports_unknown_b() {
    // 11 pigeons into 10 holes: UNSAT, and hard enough for plain CDCL that
    // it does not finish quickly (verified empirically while writing this
    // test: it did not complete within 15s with no --timeout at all).
    let script = write_temp_smt2("timeout_hard", &pigeonhole_script(10));

    // Give the CLI a small, explicit timeout and a generous hard-kill safety
    // net so a regression cannot hang the test suite.
    let (output, elapsed) = run_with_hard_kill(
        &["--timeout", "3", script.to_str().unwrap()],
        Duration::from_secs(30),
    );
    let _ = fs::remove_file(&script);

    let stdout = String::from_utf8_lossy(&output.stdout);

    // The core, in-scope property of this fix: the CLI must never hang past
    // the configured deadline, no matter how the underlying solve is going.
    // (The 30s hard-kill above would have already panicked otherwise; this
    // is a tighter, still generous, bound that also tolerates a heavily
    // loaded shared CI/dev machine.)
    assert!(
        elapsed < Duration::from_secs(20),
        "--timeout 3 should make the CLI return well before the 30s hard-kill \
         window; it took {elapsed:?}. Output was:\n{stdout}"
    );

    // If the CLI's own watchdog is what ended the run (exit code 124), it
    // must have reported the timeout honestly as "unknown" -- never a
    // fabricated sat/unsat. If instead the solve itself finished first
    // (e.g. a very fast machine, or scheduling luck under heavy concurrent
    // CI load), that is also acceptable: the fix is about not hanging
    // forever, not about forcing every hard instance to time out.
    if output.status.code() == Some(124) {
        assert!(
            stdout.contains("unknown"),
            "a timed-out solve must be reported honestly as 'unknown', not fabricated \
             sat/unsat, got:\n{stdout}"
        );
    }
}

#[test]
fn zero_timeout_still_solves_normally() {
    // Default (`--timeout 0` / omitted) must remain fully unbounded and
    // must not regress ordinary fast solves.
    let script = write_temp_smt2(
        "no_timeout_easy",
        r#"
            (declare-const x Int)
            (assert (> x 5))
            (assert (< x 10))
            (check-sat)
        "#,
    );

    let output = Command::new(oxiz_bin())
        .arg(script.to_str().unwrap())
        .output()
        .expect("failed to execute oxiz");

    let stdout = String::from_utf8_lossy(&output.stdout);
    let _ = fs::remove_file(&script);

    assert!(
        stdout.contains("sat"),
        "an easy satisfiable formula should still solve normally, got:\n{stdout}"
    );
    assert_ne!(
        output.status.code(),
        Some(124),
        "an easy, fast solve must not be mistaken for a timeout:\n{stdout}"
    );
}

#[test]
fn timeout_with_generous_budget_solves_normally() {
    // A large --timeout paired with an easy formula must behave exactly
    // like no timeout at all (the watchdog thread must not itself change
    // results).
    let script = write_temp_smt2(
        "timeout_easy",
        r#"
            (declare-const x Bool)
            (declare-const y Bool)
            (assert (and x (not y)))
            (check-sat)
        "#,
    );

    let output = Command::new(oxiz_bin())
        .args(["--timeout", "60", script.to_str().unwrap()])
        .output()
        .expect("failed to execute oxiz");

    let stdout = String::from_utf8_lossy(&output.stdout);
    let _ = fs::remove_file(&script);

    assert!(stdout.contains("sat"), "expected sat, got:\n{stdout}");
    assert!(
        output.status.success(),
        "a generous --timeout on an easy formula must not fail:\n{stdout}"
    );
}
