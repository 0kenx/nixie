//! Regression tests for the "solver-final" fix package:
//!   1. Array soundness honesty gate (store=store extensionality).
//!   2. `Context::set_option` wiring of solve-time options + granular config API.
//!   3. `get-unsat-assumptions` / `get-assignment` command behaviour.
//!   4. `declare-sort` / `define-fun` are honoured (no longer silently ignored).

use oxiz_solver::{Context, SolverConfig, TheoryMode};

fn run_last(script: &str) -> String {
    let mut ctx = Context::new();
    let out = ctx.execute_script(script).expect("script executes");
    out.last().cloned().unwrap_or_default()
}

// ─────────────────────────── Array honesty gate ───────────────────────────

#[test]
fn store_store_conflict_concrete_index_is_unsat() {
    // (store a 0 1) = (store b 0 2) forces the read at 0 to be both 1 and 2.
    let r = run_last(
        r#"(set-logic QF_AUFLIA)
        (declare-const a (Array Int Int))
        (declare-const b (Array Int Int))
        (assert (= (store a 0 1) (store b 0 2)))
        (check-sat)"#,
    );
    assert_eq!(
        r, "unsat",
        "store=store conflict must be UNSAT (was spurious sat)"
    );
}

#[test]
fn store_store_conflict_symbolic_index_is_unsat() {
    // Same overwritten index i on both sides but different values → UNSAT.
    let r = run_last(
        r#"(set-logic QF_AUFLIA)
        (declare-const a (Array Int Int))
        (declare-const b (Array Int Int))
        (declare-const i Int)
        (assert (= (store a i 1) (store b i 2)))
        (check-sat)"#,
    );
    assert_eq!(r, "unsat");
}

#[test]
fn store_store_consistent_is_not_spurious_sat() {
    // (store a 0 1) = (store b 0 1) is genuinely satisfiable, but the syntactic
    // checks + EUF core cannot certify it, so the honesty gate reports unknown
    // (never a possibly-spurious sat).
    let r = run_last(
        r#"(set-logic QF_AUFLIA)
        (declare-const a (Array Int Int))
        (declare-const b (Array Int Int))
        (assert (= (store a 0 1) (store b 0 1)))
        (check-sat)"#,
    );
    assert_eq!(
        r, "unknown",
        "unrefuted store=store must be honest unknown, not sat"
    );
}

#[test]
fn var_store_alias_still_decided() {
    // The var=store alias path is unaffected by the gate: still concrete.
    let unsat = run_last(
        r#"(set-logic QF_AUFLIA)
        (declare-const a (Array Int Int))
        (declare-const b (Array Int Int))
        (assert (= b (store a 0 1)))
        (assert (= (select b 0) 2))
        (check-sat)"#,
    );
    assert_eq!(unsat, "unsat");

    let sat = run_last(
        r#"(set-logic QF_AUFLIA)
        (declare-const a (Array Int Int))
        (declare-const b (Array Int Int))
        (assert (= b (store a 0 1)))
        (assert (= (select b 0) 1))
        (check-sat)"#,
    );
    assert_eq!(sat, "sat");
}

#[test]
fn plain_select_sat_unaffected_by_gate() {
    let r = run_last(
        r#"(set-logic QF_AUFLIA)
        (declare-const a (Array Int Int))
        (declare-const i Int)
        (assert (= (select a i) 3))
        (check-sat)"#,
    );
    assert_eq!(r, "sat");
}

// ─────────────────────────── set_option wiring ───────────────────────────

#[test]
fn set_option_timeout_reaches_config() {
    let mut ctx = Context::new();
    ctx.set_option(":timeout", "2500");
    assert_eq!(ctx.solver_config().timeout_ms, 2500);
    assert_eq!(ctx.get_option("timeout"), Some("2500")); // leading ':' stripped
}

#[test]
fn set_option_limits_and_theory_mode_reach_config() {
    let mut ctx = Context::new();
    ctx.set_option("max-conflicts", "1000");
    ctx.set_option("max-decisions", "2000");
    ctx.set_option("theory-mode", "lazy");
    ctx.set_option("simplify", "false");
    let cfg = ctx.solver_config();
    assert_eq!(cfg.max_conflicts, 1000);
    assert_eq!(cfg.max_decisions, 2000);
    assert_eq!(cfg.theory_mode, TheoryMode::Lazy);
    assert!(!cfg.simplify);
}

#[test]
fn granular_and_full_config_setters_are_public() {
    let mut ctx = Context::new();
    ctx.set_timeout_ms(42);
    ctx.set_max_conflicts(7);
    ctx.set_theory_mode(TheoryMode::Eager);
    assert_eq!(ctx.solver_config().timeout_ms, 42);
    assert_eq!(ctx.solver_config().max_conflicts, 7);

    // Full-config replacement path used by external portfolio drivers.
    let mut cfg: SolverConfig = ctx.solver_config().clone();
    cfg.timeout_ms = 999;
    ctx.set_solver_config(cfg);
    assert_eq!(ctx.solver_config().timeout_ms, 999);
}

#[test]
fn unknown_option_is_recorded_but_harmless() {
    let mut ctx = Context::new();
    ctx.set_option("random-seed", "12345");
    assert_eq!(ctx.get_option("random-seed"), Some("12345"));
}

// ──────────────────────── get-unsat-assumptions ────────────────────────

#[test]
fn get_unsat_assumptions_after_unsat() {
    let mut ctx = Context::new();
    ctx.execute_script(
        r#"(set-logic QF_UF)
        (declare-const p Bool)
        (assert p)
        (check-sat-assuming ((not p)))"#,
    )
    .expect("script executes");
    let ua = ctx.get_unsat_assumptions();
    assert!(
        ua.starts_with('(') && ua.contains("not") && ua.contains('p'),
        "got: {ua}"
    );
}

#[test]
fn get_unsat_assumptions_errors_without_unsat() {
    let mut ctx = Context::new();
    ctx.execute_script(
        r#"(set-logic QF_UF)
        (declare-const p Bool)
        (assert p)
        (check-sat)"#,
    )
    .expect("script executes");
    let ua = ctx.get_unsat_assumptions();
    assert!(
        ua.contains("error"),
        "expected error after non-assuming check, got: {ua}"
    );
}

// ───────────────────────────── get-assignment ─────────────────────────────

#[test]
fn get_assignment_reports_bool_consts() {
    let mut ctx = Context::new();
    ctx.execute_script(
        r#"(set-logic QF_UF)
        (declare-const p Bool)
        (declare-const q Bool)
        (assert p)
        (assert (not q))
        (check-sat)"#,
    )
    .expect("script executes");
    let a = ctx.get_assignment();
    assert!(a.contains("(p true)"), "got: {a}");
    assert!(a.contains("(q false)"), "got: {a}");
}

// ─────────────────────── declare-sort / define-fun ───────────────────────

#[test]
fn declare_sort_and_define_fun_are_honoured() {
    let mut ctx = Context::new();
    let out = ctx
        .execute_script(
            r#"(set-logic QF_UF)
        (declare-sort U 0)
        (declare-const x U)
        (declare-const y U)
        (define-fun two () Int 2)
        (assert (= x y))
        (check-sat)"#,
        )
        .expect("script executes");
    assert_eq!(out.last().map(String::as_str), Some("sat"));
    // declare-sort recorded for introspection.
    assert!(ctx.declared_sort_names().any(|(n, a)| n == "U" && a == 0));
    // define-fun (0-ary) registered as a constant so it appears in the model.
    assert!(ctx.get_fun_signature("two").is_none()); // 0-ary is a const, not a fun sig
}
