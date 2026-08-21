//! Regression: wall-clock-gated integer case-split refinement (false,
//! load-dependent SAT on QF_UFLIA/wisas).
//!
//! `refine_int_case_split` is the only machinery closing the non-convex
//! LIA+UF gap on the wisas shape (`s_count`/`x_count` running sums pinned
//! through `format` applications).  Until 2026-08-21 its call site gated it
//! on `check_start.elapsed() < CASE_SPLIT_REFINE_BUDGET_MS` (5 s of
//! wall-clock) with the stated goal "hard instances keep their original
//! fast answer".  That made the *verdict* a function of machine load:
//!
//! * the same release binary, identical invocations, flipped 7×`sat` /
//!   1×`unsat` on `xs_8_13.smt2`;
//! * forcing the two arms (temporary env override of the budget) gave
//!   5×`sat` at budget 0 vs 5×`unsat` at budget ∞ — the clock was the
//!   sole decider between the wrong and the right answer;
//! * z3 says `unsat`; a skipped closing round is an uncertifiable `sat`,
//!   which per AGENTS.md may never be traded for speed.
//!
//! The gate is removed (the refinement's own deterministic caps bound its
//! cost; an unaffordable search is `timeout_ms`'s business, reported as an
//! honest `unknown`).  These tests pin the verdict on the exact reproducer
//! and — because a wall-clock read anywhere in the verdict path would
//! resurface the flip — run the same check twice in-process and require
//! identical answers.

use oxiz_solver::{Context, SolverResult};

fn solve_fixture() -> SolverResult {
    let script = std::fs::read_to_string(concat!(
        env!("CARGO_MANIFEST_DIR"),
        "/tests/fixtures/wisas_xs_8_13.smt2"
    ))
    .unwrap_or_default();
    let mut ctx = Context::new();
    let outputs = ctx.execute_script(&script).unwrap_or_default();
    for tok in outputs.iter().rev() {
        match tok.trim() {
            "sat" => return SolverResult::Sat,
            "unsat" => return SolverResult::Unsat,
            "unknown" => return SolverResult::Unknown,
            _ => {}
        }
    }
    SolverResult::Unknown
}

/// The exact instance that flipped with machine load: must be `unsat`
/// (z3-certified) regardless of how long the first solve happens to take.
#[test]
fn wisas_xs_8_13_is_unsat() {
    assert_eq!(solve_fixture(), SolverResult::Unsat);
}

/// The **eager** half of the architecture (z3 `arith_eq_adapter` /
/// cvc5 `ensureLiteral` parity): a UF argument bounded by direct
/// single-variable atoms (`(>= a 0)`, `(<= a 3)`) gets its
/// `(or (= a 0) .. (= a 3))` enumeration lemma asserted BEFORE the search
/// (level-0 interval fixpoint — no simplex, no candidate model), so CDCL
/// pins the argument value from conflict #1.  Without the eager pass this
/// shape is the non-convex hole: the model assigns `a` into `[0,3]`, EUF
/// never merges `f(a)` with any pinned `f(k)`, and the answer is a wrong
/// `sat` (or depends on the reactive round noticing at the candidate).
#[test]
fn eager_enumeration_closes_bounded_uf_domain() {
    let script = r#"
        (set-logic QF_UFLIA)
        (declare-fun f (Int) Int)
        (declare-const a Int)
        (assert (>= a 0))
        (assert (<= a 3))
        (assert (= (f 0) 1))
        (assert (= (f 1) 2))
        (assert (= (f 2) 3))
        (assert (= (f 3) 4))
        (assert (= (f a) 5))
        (check-sat)
    "#;
    let mut ctx = Context::new();
    let outputs = ctx.execute_script(script).unwrap_or_default();
    let verdict = outputs
        .iter()
        .rev()
        .find_map(|t| match t.trim() {
            "sat" => Some(SolverResult::Sat),
            "unsat" => Some(SolverResult::Unsat),
            "unknown" => Some(SolverResult::Unknown),
            _ => None,
        })
        .unwrap_or(SolverResult::Unknown);
    assert_eq!(verdict, SolverResult::Unsat);
}

/// Determinism smoke: two full solves of the same script in one process
/// must agree.  A wall-clock or RNG read on the verdict path shows up here
/// as an intermittent failure under CI load — exactly the signature that
/// hid this bug through three differential runs.
#[test]
fn wisas_xs_8_13_verdict_is_stable_across_repeats() {
    let first = solve_fixture();
    let second = solve_fixture();
    assert_eq!(first, second);
    assert_eq!(first, SolverResult::Unsat);
}
