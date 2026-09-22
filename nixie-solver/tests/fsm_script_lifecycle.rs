//! Regression: FSM script-surface registration lifecycles.
//!
//! The original false-sat (2026-09-22, found by the `bench/fsm_perf`
//! verdict-agreement canary): a second `fsm.accepts` command arriving
//! after an `(assert ...)` had already triggered registration was
//! silently dropped by the idempotence guard — its result constant
//! stayed unconstrained, so `(assert (not n0))` over an accepted word
//! returned **sat**. Registration is now incremental: late acceptance
//! queries over the frozen declarations register an additional
//! propagator; mutating a registered automaton errors loudly.

use nixie_solver::Context;

const CHAIN: &str = r#"
(declare-const g_0_0_3 Bool)
(declare-const g_3_1_6 Bool)
(declare-const g_6_0_7 Bool)
(declare-const g_7_0_8 Bool)
(declare-fsm A 16 2)
(fsm.initial A 0)
(fsm.accepting A 8)
(fsm.accepting A 15)
(fsm.transition A 0 3 0 g_0_0_3)
(fsm.transition A 3 6 1 g_3_1_6)
(fsm.transition A 6 7 0 g_6_0_7)
(fsm.transition A 7 8 0 g_7_0_8)
"#;
const WORD: &str = "(0 1 0 0)";

/// The exact false-sat shape: `assert` between two `fsm.accepts` over the
/// same word with contradictory demands. Acceptance of this chain-word is
/// `g0 ∧ g3 ∧ g6 ∧ g7`; `p0 ∧ ¬n0` is unsatisfiable at any size.
#[test]
fn late_accepts_query_after_assert_is_registered() {
    let mut ctx = Context::new();
    let script = format!(
        "(set-logic ALL){CHAIN}\
         (fsm.accepts A {WORD} p0)\n(assert p0)\n\
         (fsm.accepts A {WORD} n0)\n(assert (not n0))\n(check-sat)\n"
    );
    let out = ctx.execute_script(&script).expect("script executes");
    assert_eq!(
        out.last().map(String::as_str),
        Some("unsat"),
        "second (late) fsm.accepts must constrain its atom: {out:?}"
    );
}

/// The same shape with guards pinned: the positive demand forces all
/// guards, so the late negative demand is unsat with witnesses pinned.
#[test]
fn late_accepts_query_with_pinned_guards() {
    let mut ctx = Context::new();
    let script = format!(
        "(set-logic ALL){CHAIN}\
         (fsm.accepts A {WORD} p0)\n(assert p0)\n\
         (fsm.accepts A {WORD} n0)\n(assert g_0_0_3)\n(assert g_3_1_6)\n\
         (assert g_6_0_7)\n(assert g_7_0_8)\n(assert (not n0))\n(check-sat)\n"
    );
    let out = ctx.execute_script(&script).expect("script executes");
    assert_eq!(out.last().map(String::as_str), Some("unsat"), "{out:?}");
}

/// Negative demand first also registers the later positive query.
#[test]
fn late_accepts_query_negative_first() {
    let mut ctx = Context::new();
    let script = format!(
        "(set-logic ALL){CHAIN}\
         (fsm.accepts A {WORD} n0)\n(assert (not n0))\n\
         (fsm.accepts A {WORD} p0)\n(assert p0)\n(check-sat)\n"
    );
    let out = ctx.execute_script(&script).expect("script executes");
    assert_eq!(out.last().map(String::as_str), Some("unsat"), "{out:?}");
}

/// Multiple late queries accumulate across several registration epochs.
#[test]
fn several_late_accepts_queries() {
    let mut ctx = Context::new();
    let script = format!(
        "(set-logic ALL){CHAIN}\
         (fsm.accepts A {WORD} q0)\n(assert q0)\n\
         (fsm.accepts A {WORD} q1)\n(assert q1)\n\
         (fsm.accepts A {WORD} q2)\n(assert (not q2))\n(check-sat)\n"
    );
    let out = ctx.execute_script(&script).expect("script executes");
    assert_eq!(out.last().map(String::as_str), Some("unsat"), "{out:?}");
}

/// Mutating an automaton after solving began is a loud command error,
/// never a silent drop (its product graphs are live).
#[test]
fn automaton_mutation_after_registration_errors_loudly() {
    let mut ctx = Context::new();
    let script = format!(
        "(set-logic ALL){CHAIN}\
         (fsm.accepts A {WORD} p0)\n(assert p0)\n\
         (fsm.transition A 0 5 0 g_0_0_3)\n(check-sat)\n"
    );
    let err = ctx
        .execute_script(&script)
        .expect_err("late structural declaration must error");
    assert!(
        format!("{err}").contains("frozen"),
        "unexpected error: {err}"
    );
}

/// The pre-fix ordering hazard stays green: all queries before the first
/// assert (the shape every earlier test used).
#[test]
fn all_queries_before_first_assert_still_works() {
    let mut ctx = Context::new();
    let script = format!(
        "(set-logic ALL){CHAIN}\
         (fsm.accepts A {WORD} p0)\n(fsm.accepts A {WORD} n0)\n\
         (assert p0)\n(assert (not n0))\n(check-sat)\n"
    );
    let out = ctx.execute_script(&script).expect("script executes");
    assert_eq!(out.last().map(String::as_str), Some("unsat"), "{out:?}");
}
