//! Unified-path blast deferral (`NIXIE_BV_DEFER_BLAST=1`) regressions.
//!
//! Pure-BV fragment assertions postpone clause emission and circuit
//! linking to the next `check`, where the preprocessor's rewritten set
//! becomes the *only* circuit source (menu item 4, "blast rewritten-only").
//! The flag is net-negative on the 509-file corpus (301 vs 308 parallel,
//! zero flips) but structurally closes `s3_srvr_1_alt` — the last
//! parser-macro cell — which no other mechanism reaches.
//!
//! These tests pin the three model-path invariants the prototype needed:
//!
//! 1. **Multi-check sequences** (assert/check/assert/check/push/assert/
//!    check/pop/check) — the deferral flush, the stage-4 re-emission, and
//!    the push/pop pending-flush must produce the same verdict sequence as
//!    the assert-time path.
//! 2. **Eliminated variables in `Sat` models** — the rewritten-only core
//!    leaves solve-eqs-eliminated variables unconstrained; their values
//!    must be *replayed* from the recorded eliminations before the
//!    model-validation gate (otherwise the gate refutes the ORIGINAL
//!    assertions with defaulted values and blocks into `Unknown`), and the
//!    replay must clear the sort-default completion `build_model` installs
//!    first.
//! 3. **Model records win over defaulted bits** — an explicit model entry
//!    (a replayed definition) must not be shadowed by "determined" bits
//!    that are merely the adopted assignment's all-false default for a
//!    never-constrained variable.

use nixie_solver::Context;

fn defer_on() {
    #[cfg(feature = "std")]
    // SAFETY: per-test processes under `cargo nextest`; every test in this
    // binary sets the same value before constructing a solver.
    unsafe {
        std::env::set_var("NIXIE_BV_DEFER_BLAST", "1")
    };
}

fn verdicts(script: &str) -> Vec<String> {
    let mut ctx = Context::new();
    let out = ctx.execute_script(script).expect("script executes");
    out.iter()
        .filter(|t| !t.trim().is_empty())
        .cloned()
        .collect()
}

/// The full incremental sequence from the prototype's first failure: every
/// verdict must match the assert-time path's.
#[test]
fn deferred_incremental_sequence_matches() {
    defer_on();
    let v = verdicts(
        r#"
        (set-logic QF_BV)
        (declare-const x (_ BitVec 32))
        (declare-const y (_ BitVec 32))
        (assert (= (bvadd x (_ bv1 32)) (bvadd y (_ bv2 32))))
        (check-sat)
        (assert (= x (bvadd y (_ bv3 32))))
        (check-sat)
        (push 1)
        (assert (= x (bvadd y (_ bv9 32))))
        (check-sat)
        (pop 1)
        (check-sat)
    "#,
    );
    let v: Vec<&str> = v.iter().map(String::as_str).collect();
    assert_eq!(v, vec!["sat", "unsat", "unsat", "unsat"], "verdicts: {v:?}");
}

/// A solve-eqs-eliminated variable (`x := 7`): the deferred `sat` must
/// survive the model-validation gate via the elimination replay, and
/// `get-value` must report the replayed definition value — not the sort
/// default.
#[test]
fn deferred_sat_replays_eliminated_variable() {
    defer_on();
    let v = verdicts(
        r#"
        (set-logic QF_BV)
        (declare-const x (_ BitVec 32))
        (assert (= x (_ bv7 32)))
        (check-sat)
        (get-value (x))
    "#,
    );
    assert_eq!(v[0], "sat", "verdicts: {v:?}");
    assert!(
        v[1].contains("#x00000007") || v[1].contains("7"),
        "replayed value: {}",
        v[1]
    );
}

/// Chained eliminations (`x := y+1`, `y := 7`) replay transitively.
#[test]
fn deferred_sat_replays_elimination_chain() {
    defer_on();
    let v = verdicts(
        r#"
        (set-logic QF_BV)
        (declare-const x (_ BitVec 32))
        (declare-const y (_ BitVec 32))
        (assert (= y (_ bv7 32)))
        (assert (= x (bvadd y (_ bv1 32))))
        (check-sat)
        (get-value (x))
    "#,
    );
    assert_eq!(v[0], "sat", "verdicts: {v:?}");
    assert!(
        v[1].contains("#x00000008") || v[1].contains("8"),
        "chained replay: {}",
        v[1]
    );
}

/// A `sat` whose model needs the record-priority fix: the eliminated
/// variable's replayed entry must win over the never-constrained bits'
/// all-false default, or the validation gate refutes `x = 7` as `x = 0`.
#[test]
fn deferred_record_wins_over_defaulted_bits() {
    defer_on();
    let v = verdicts(
        r#"
        (set-logic QF_BV)
        (declare-const x (_ BitVec 8))
        (declare-const w (_ BitVec 8))
        (assert (= x (_ bv42 8)))
        (assert (bvult w (_ bv200 8)))
        (check-sat)
    "#,
    );
    assert_eq!(v[0], "sat", "verdicts: {v:?}");
}
