//! Symbolic real division `(/ x y)` (variable divisor) regressions.
//!
//! Real division with a symbolic divisor was the last honestly-gated class
//! of the mixed-arith differential's `unknown` gap (study 2026-09-13/14,
//! items 5–8): the defining identity `x = y·q` is nonlinear, so the linear
//! CDCL(T) path can never decide it. The nonlinear dispatcher now encodes
//! it exactly — a fresh quotient variable under the guarded defining clause
//! `y = 0 ∨ y·t − x = 0` — which makes the satisfiable classes decidable
//! while keeping every SMT-LIB corner (the zero divisor is uninterpreted)
//! faithful. These tests pin each class, including the two ways the
//! encoding could have been (and once was, mid-development) wrong:
//! the guard's polarity and the trust split between verdicts.

#![cfg(feature = "nlsat")]

use nixie_solver::{Context, SolverResult};

fn check(script: &str) -> SolverResult {
    let mut ctx = Context::new();
    let out = ctx.execute_script(script).expect("script executes");
    let last = out
        .iter()
        .rev()
        .find(|t| !t.trim().is_empty())
        .expect("a verdict");
    match last.trim() {
        "sat" => SolverResult::Sat,
        "unsat" => SolverResult::Unsat,
        "unknown" => SolverResult::Unknown,
        other => panic!("unexpected verdict line: {other}"),
    }
}

/// The headline class: operands pinned by units, quotient forced by the
/// defining identity (`5/2 = 2.5`). Decided `sat` through the NRA
/// dispatcher; before the encoding this was an honest `unknown`.
#[test]
fn real_division_with_pinned_operands_is_decidable_sat() {
    let r = check(
        "(set-logic QF_NRA)
         (declare-const x Real) (declare-const y Real)
         (assert (= x 5)) (assert (= y 2))
         (assert (= (/ x y) 2.5))
         (check-sat)",
    );
    assert_eq!(r, SolverResult::Sat);
}

/// The unsat twin: `5/2 ≠ 2`. The answer stays `unknown` — the NRA
/// dispatcher's historical Eq-distrust for `unsat` (now extended to the
/// Eq-bearing defining clauses) declines the refutation, and the linear
/// path honestly gates. It must NEVER answer `sat`: the first cut of the
/// guarded clause (`¬(y=0) ∨ y·t=x`) satisfied itself for every nonzero
/// divisor and produced exactly this wrong verdict.
#[test]
fn real_division_unsat_twin_stays_honest() {
    let r = check(
        "(set-logic QF_NRA)
         (declare-const x Real) (declare-const y Real)
         (assert (= x 5)) (assert (= y 2))
         (assert (= (/ x y) 2))
         (check-sat)",
    );
    assert_ne!(
        r,
        SolverResult::Sat,
        "5/2 = 2 is false; sat is a wrong verdict"
    );
}

/// SMT-LIB semantics: `(/ x 0)` is uninterpreted, so pinning the divisor to
/// zero and the quotient to 5 is satisfiable — the model's `t` is the
/// term's arbitrary fixed value. The encoding must emit NO defining clause
/// for a constant-zero divisor (forcing `x = 0` through the degenerate
/// clause would be wrong).
#[test]
fn division_by_pinned_zero_divisor_is_sat() {
    let r = check(
        "(set-logic QF_NRA)
         (declare-const x Real) (declare-const y Real)
         (assert (= y 0))
         (assert (= (/ x y) 5))
         (check-sat)",
    );
    assert_eq!(r, SolverResult::Sat);
}

/// Open-logic shape detection: real division engages the NL dispatcher
/// without a declared nonlinear logic, and strict inequalities over the
/// quotient are decided when the divisor is pinned.
#[test]
fn open_logic_real_division_dispatches() {
    let r = check(
        "(set-logic ALL)
         (declare-const x Real) (declare-const y Real)
         (assert (> (/ x (/ y 2)) 3))
         (assert (= y 2)) (assert (= x 5))
         (check-sat)",
    );
    assert_eq!(r, SolverResult::Sat, "5 / (2/2) = 5 > 3");
}

/// Mixed NIRA: an integer variable interacts with a real quotient. The NIA
/// backend's integer reasoning keeps its own verdicts (`i² = 2` has no
/// integer root) — regression that the real-division encoding did not
/// disturb the integer path.
#[test]
fn nia_integer_reasoning_unchanged_alongside_real_division() {
    let r = check(
        "(set-logic QF_NIRA)
         (declare-const i Int) (declare-const x Real) (declare-const y Real)
         (assert (> i 0)) (assert (< i 3))
         (assert (= (* i i) 2))
         (check-sat)",
    );
    assert_eq!(r, SolverResult::Unsat);
}

/// Open-logic routing: a bare Int NUMERAL in a Real context (`4`, `1`) is
/// not "Int-sorted arithmetic" — counting it sent pure-Real goals like this
/// one to the integer backend instead of NRA.
#[test]
fn int_literals_do_not_route_real_goals_to_the_integer_backend() {
    let r = check(
        "(set-logic ALL)
         (declare-const x Real)
         (assert (= (* x x) 2)) (assert (> x 1))
         (check-sat)",
    );
    assert_eq!(r, SolverResult::Sat, "x = sqrt(2) satisfies both");
}

/// The pre-existing Eq-distrust classes are unchanged: coupled-product
/// equality goals keep answering `sat` (models verified) and never gain an
/// `unsat` they cannot support.
#[test]
fn coupled_equality_sat_class_unchanged() {
    let sat = check(
        "(set-logic QF_NRA)
         (declare-const x Real)
         (assert (= (* x x) 4)) (assert (> x 1))
         (check-sat)",
    );
    assert_eq!(sat, SolverResult::Sat);
}

/// A division over a free dividend and free divisor whose witness needs
/// values the greedy sampler cannot enumerate stays `unknown` — the honest
/// answer, never a guess (sampler capacity, same class as coupled products
/// with free operands).
#[test]
fn free_operands_division_never_gueses() {
    let r = check(
        "(set-logic ALL)
         (declare-const x Real) (declare-const y Real)
         (assert (> (/ x y) 3))
         (check-sat)",
    );
    assert_ne!(r, SolverResult::Unsat, "x=4, y=1 satisfies the goal");
}
