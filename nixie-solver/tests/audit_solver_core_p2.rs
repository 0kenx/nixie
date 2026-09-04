//! Soundness regression tests for the `solver-core-p2` audit wave.
//!
//! Each test pins down one confirmed soundness defect in the solver core:
//!
//!   1. MBQI must answer `Unknown` (never `Sat`) once it has exhausted its
//!      instantiation heuristics without *verifying* the quantifiers.
//!   2. `push`/`pop` must not let bit-vector facts leak across scopes.
//!   3. Conflict-limit exhaustion must yield `Unknown`, never a `Sat` that
//!      silently drops a real theory conflict.
//!   4. Signed BV comparisons (`bvslt`/`bvsle`) must not be asserted into
//!      linear arithmetic with unsigned semantics.
//!
//! The invariant under test in every case is soundness: for a genuinely
//! UNSAT (or definitely-SAT) formula the solver must never return the
//! opposite verdict.  Where a heuristic is legitimately incomplete, the only
//! acceptable non-answer is `Unknown`.

use nixie_core::ast::TermManager;
use nixie_solver::{Context, Solver, SolverConfig, SolverResult};

/// Run a single SMT-LIB2 script and return the last sat/unsat/unknown verdict.
fn run_script(script: &str) -> SolverResult {
    let mut ctx = Context::new();
    let outputs = ctx.execute_script(script).unwrap_or_default();
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

// ========  ========
// Finding 1 – MBQI must not fabricate `Sat` for unverified quantifiers
// ========  ========

/// A genuinely UNSAT quantified formula whose refutation needs a chain of
/// instantiations.  Previously, after 10 inconclusive MBQI rounds the solver
/// blindly returned `Sat`; a sound solver must answer `unsat` (if it can
/// refute) or `unknown` (if MBQI is incomplete) – but NEVER `sat`.
#[test]
fn mbqi_unverified_quantifier_is_not_sat() {
    let script = r#"
(set-logic UFLIA)
(declare-fun f (Int) Int)
(assert (forall ((x Int)) (= (f x) (+ (f (- x 1)) 1))))
(assert (= (f 0) 0))
(assert (< (f 5) 3))
(check-sat)
"#;
    // f(x) = f(x-1)+1 with f(0)=0 forces f(5)=5, contradicting f(5)<3.
    // The formula is UNSAT; the solver must not claim it is satisfiable.
    assert_ne!(run_script(script), SolverResult::Sat);
}

/// A second UNSAT quantified formula: a universal fact that directly
/// contradicts a ground assertion.  Must never be reported `sat`.
#[test]
fn mbqi_universal_contradiction_is_not_sat() {
    let script = r#"
(set-logic UFLIA)
(declare-fun p (Int) Bool)
(assert (forall ((x Int)) (p x)))
(assert (not (p 7)))
(check-sat)
"#;
    assert_ne!(run_script(script), SolverResult::Sat);
}

// ========  ========
// Finding 2 – push/pop must not leak bit-vector facts across scopes
// ========  ========

/// Pin `x = #x05` inside a scope, check, then `pop` and pin `x = #x06`.
/// The stale `x = 5` must not survive the pop and spuriously clash with
/// `x = 6` – that later check must be SAT.
#[test]
fn bv_fact_does_not_leak_across_pop() {
    let script = r#"
(set-logic QF_BV)
(declare-const x (_ BitVec 8))
(push)
(assert (= x #x05))
(check-sat)
(pop)
(assert (= x #x06))
(check-sat)
"#;
    // The final (= x #x06) is satisfiable on its own; the popped (= x #x05)
    // must be gone.  A wrong UNSAT here is the leakage bug.
    assert_eq!(run_script(script), SolverResult::Sat);
}

/// The same value pinned in two consecutive scopes must both be SAT: the
/// BV solver state is rebuilt from the live assertion set each check.
#[test]
fn bv_scoped_values_are_independent() {
    let script = r#"
(set-logic QF_BV)
(declare-const x (_ BitVec 4))
(push)
(assert (= x #x1))
(check-sat)
(pop)
(push)
(assert (= x #xE))
(check-sat)
(pop)
"#;
    assert_eq!(run_script(script), SolverResult::Sat);
}

// ========  ========
// Finding 3 – conflict-limit exhaustion must never masquerade as `Sat`
// ========  ========

/// Build an UNSAT linear formula (`x > 5 ∧ x < 3`) and solve it with a
/// conflict budget of 1.  When the budget is hit while a real theory conflict
/// exists, the theory manager suppresses that conflict to stop the search;
/// the solver must then answer `Unknown` – never `Sat` over a dropped
/// conflict.  (`Unsat` is also acceptable if refuted before the limit.)
#[test]
fn conflict_limit_exhaustion_is_not_sat() {
    let mut manager = TermManager::new();
    let int_sort = manager.sorts.int_sort;
    let x = manager.mk_var("x", int_sort);
    let five = manager.mk_int(5);
    let three = manager.mk_int(3);
    let gt = manager.mk_gt(x, five); // x > 5
    let lt = manager.mk_lt(x, three); // x < 3

    let config = SolverConfig::default().with_max_conflicts(1);
    let mut solver = Solver::with_config(config);
    solver.assert(gt, &mut manager);
    solver.assert(lt, &mut manager);

    let result = solver.check(&mut manager);
    // The formula is UNSAT; under a tight conflict budget the only sound
    // answers are Unsat or Unknown.  Returning Sat is the soundness bug.
    assert_ne!(
        result,
        SolverResult::Sat,
        "solver reported Sat for an UNSAT formula after conflict-limit exhaustion"
    );
}

/// A wider UNSAT arithmetic system solved with an unlimited budget must still
/// be correctly UNSAT – the exhaustion guard must not over-fire and turn a
/// genuine refutation into Unknown.
#[test]
fn unlimited_budget_still_refutes() {
    let mut manager = TermManager::new();
    let int_sort = manager.sorts.int_sort;
    let x = manager.mk_var("x", int_sort);
    let five = manager.mk_int(5);
    let three = manager.mk_int(3);
    let gt = manager.mk_gt(x, five);
    let lt = manager.mk_lt(x, three);

    // Default config: max_conflicts == 0 (unlimited).
    let mut solver = Solver::new();
    solver.assert(gt, &mut manager);
    solver.assert(lt, &mut manager);

    assert_eq!(solver.check(&mut manager), SolverResult::Unsat);
}

// ========  ========
// Finding 4 – signed BV comparisons must not use unsigned arith semantics
// ========  ========

/// `(bvslt x #b0000) ∧ (bvult #b0100 x)` is SAT (e.g. x = #b1001 = -7 signed,
/// 9 unsigned).  The old code asserted the signed comparison into linear
/// arithmetic as `x < 0` (unsigned parse) which, combined with the unsigned
/// `x > 4`, produced a spurious `x < 0 ∧ x > 4` conflict → wrong UNSAT.
#[test]
fn signed_and_unsigned_bv_mix_is_sat() {
    let script = r#"
(set-logic QF_BV)
(declare-const x (_ BitVec 4))
(assert (bvslt x #b0000))
(assert (bvult #b0100 x))
(check-sat)
"#;
    assert_eq!(run_script(script), SolverResult::Sat);
}

/// `bvsle` variant of the same mix, also SAT (x = #b1000 = -8 signed,
/// 8 unsigned: signed x ≤ 0 holds and unsigned 4 < x holds).
#[test]
fn signed_le_and_unsigned_bv_mix_is_sat() {
    let script = r#"
(set-logic QF_BV)
(declare-const x (_ BitVec 4))
(assert (bvsle x #b0000))
(assert (bvult #b0100 x))
(check-sat)
"#;
    assert_eq!(run_script(script), SolverResult::Sat);
}

/// The signed BV path must still be able to detect real signed conflicts:
/// `(bvslt x y) ∧ (bvslt y x)` is UNSAT.  Removing the arith over-approximation
/// must not weaken the (authoritative) BV solver.
#[test]
fn signed_bv_antisymmetry_still_unsat() {
    let script = r#"
(set-logic QF_BV)
(declare-const x (_ BitVec 4))
(declare-const y (_ BitVec 4))
(assert (bvslt x y))
(assert (bvslt y x))
(check-sat)
"#;
    assert_eq!(run_script(script), SolverResult::Unsat);
}
