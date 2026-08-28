//! Soundness regression tests for the `solver-p3c` audit wave.
//!
//! Each test pins one confirmed defect in the CDCL(T) solver core.  The
//! overriding invariant is soundness: the solver must never return a definite
//! answer opposite to the truth, and where a path is genuinely incomplete the
//! only acceptable non-answer is `Unknown`.
//!
//!   1. Wall-clock timeout must be enforced across the theory / MBQI search
//!      loop (theory callbacks + between MBQI rounds) and must never fabricate
//!      `Sat` for an unsolved problem.
//!   2. Arithmetic atoms the linear solver cannot encode (div/mod, nonlinear,
//!      oversized constants) must yield `Unknown`, never a spurious verdict.
//!   4. `reset` must clear quantifier / MBQI / e-matching / nlsat state so a
//!      fresh problem is not contaminated by the previous one.
//!   5. The Tseitin encoder must not overflow the native stack on
//!      adversarially deep formulas – it answers `Unknown` instead.
//!   +  `push`/`pop` must restore theory state (a popped scope must become
//!      satisfiable again).

use oxiz_core::ast::TermManager;
use oxiz_solver::{Context, Solver, SolverConfig, SolverResult};

/// Run an SMT-LIB2 script and collect the sequence of sat/unsat/unknown tokens.
fn run_script(script: &str) -> Vec<SolverResult> {
    let mut ctx = Context::new();
    ctx.execute_script(script)
        .unwrap_or_default()
        .into_iter()
        .filter_map(|tok| match tok.trim() {
            "sat" => Some(SolverResult::Sat),
            "unsat" => Some(SolverResult::Unsat),
            "unknown" => Some(SolverResult::Unknown),
            _ => None,
        })
        .collect()
}

// ========  ========
// push / pop soundness – a popped scope must be satisfiable again
// ========  ========

#[test]
fn pushpop_bool_restores_satisfiability() {
    let r = run_script(
        r#"
(declare-const p Bool)
(assert p)
(push)
(assert (not p))
(check-sat)
(pop)
(check-sat)
"#,
    );
    assert_eq!(r, vec![SolverResult::Unsat, SolverResult::Sat]);
}

#[test]
fn pushpop_arith_restores_satisfiability() {
    let r = run_script(
        r#"
(declare-const x Int)
(assert (= x 1))
(push)
(assert (= x 2))
(check-sat)
(pop)
(check-sat)
"#,
    );
    assert_eq!(r, vec![SolverResult::Unsat, SolverResult::Sat]);
}

// ========  ========
// Finding 2 – unhandled arithmetic atoms must be Unknown, not spurious
// ========  ========

#[test]
fn mod_atom_is_not_spuriously_decided() {
    // (mod x 3) ∈ [0,3), so (> (mod x 3) 5) is unsat – but the linear solver
    // cannot encode `mod`.  It must answer Unknown, never a fabricated verdict.
    let r = run_script(r#"(declare-const x Int)(assert (> (mod x 3) 5))(check-sat)"#);
    assert_eq!(r, vec![SolverResult::Unknown]);
}

#[test]
fn nonlinear_atom_is_not_spuriously_decided() {
    // (* x y) > 5 ∧ (* x y) < 3 is unsat, but the product is nonlinear.
    // Since the NIA-over-LP relaxation engine landed (upstream v0.3.3 port),
    // this is a genuine, proof-backed Unsat: the relaxation replaces the
    // product with a monic variable `v` and `v > 5 ∧ v < 3` is LP-infeasible,
    // and an infeasible relaxation soundly refutes the original. What is
    // still excluded — and what this test was written for — is a free-Boolean
    // spurious Sat.
    let r = run_script(
        r#"(declare-const x Int)(declare-const y Int)
(assert (> (* x y) 5))(assert (< (* x y) 3))(check-sat)"#,
    );
    assert_ne!(r, vec![SolverResult::Sat]);
    assert_eq!(r, vec![SolverResult::Unsat]);
}

#[test]
fn plain_linear_arithmetic_still_decided() {
    // The honesty gate must not blunt ordinary linear reasoning.
    assert_eq!(
        run_script(r#"(declare-const x Int)(assert (> x 5))(assert (< x 3))(check-sat)"#),
        vec![SolverResult::Unsat]
    );
    assert_eq!(
        run_script(r#"(declare-const x Int)(assert (> x 5))(assert (< x 9))(check-sat)"#),
        vec![SolverResult::Sat]
    );
}

// ========  ========
// Finding 4 – reset must clear quantifier / MBQI state
// ========  ========

#[test]
fn reset_clears_quantifier_state() {
    // A quantified problem populates MBQI / e-matching / has_quantifiers.
    // After (reset) a fresh quantifier-free linear problem must solve cleanly
    // (Sat) rather than being dragged through the previous problem's stale
    // quantifier machinery.
    let r = run_script(
        r#"
(set-logic UFLIA)
(declare-fun f (Int) Int)
(assert (forall ((x Int)) (> (f x) 0)))
(check-sat)
(reset)
(declare-const a Int)
(assert (= a 1))
(assert (< a 5))
(check-sat)
"#,
    );
    // Whatever the (unknowable) quantified verdict, the post-reset check is Sat.
    assert_eq!(r.last(), Some(&SolverResult::Sat));
}

// ========  ========
// Finding 5 – deep formulas must not overflow the stack
// ========  ========

#[test]
fn deep_formula_answers_unknown_not_overflow() {
    // Build an `ite` nest far deeper than ENCODE_DEPTH_LIMIT, each level with a
    // fresh else-branch so hash-consing cannot collapse it.  The encoder must
    // truncate and answer Unknown rather than overflow the native stack.
    let mut tm = TermManager::new();
    let cfg = SolverConfig {
        simplify: false, // keep the nesting intact through to the encoder
        ..SolverConfig::default()
    };
    let mut solver = Solver::with_config(cfg);
    let b = tm.sorts.bool_sort;
    let p = tm.mk_var("p", b);
    let mut t = p;
    for i in 0..3000usize {
        let e = tm.mk_var(&format!("e{i}"), b);
        t = tm.mk_ite(p, t, e);
    }
    solver.assert(t, &mut tm);
    assert_eq!(solver.check(&mut tm), SolverResult::Unknown);
}

// ========  ========
// Finding 1 – wall-clock timeout must be enforced and never fabricate Sat
// ========  ========

#[test]
fn timeout_on_quantified_search_terminates_without_fabricating_sat() {
    // A quantified problem drives the MBQI refinement loop, where the wall-clock
    // deadline is enforced (between rounds and inside every theory callback).
    // The formula is UNSAT: f(x) = f(x-1)+1 with f(0)=0 forces f(5)=5, which
    // contradicts f(5) < 3.  With a tiny budget the solver must terminate
    // promptly and must NEVER answer Sat – Unknown (timed out) or Unsat (if
    // refuted first) are both acceptable, Sat is not.
    let mut tm = TermManager::new();
    let int = tm.sorts.int_sort;
    let cfg = SolverConfig {
        timeout_ms: 5,
        ..SolverConfig::default()
    };
    let mut solver = Solver::with_config(cfg);

    let one = tm.mk_int(1i64);
    let zero = tm.mk_int(0i64);
    let three = tm.mk_int(3i64);
    let five = tm.mk_int(5i64);

    // forall x. f(x) = f(x-1) + 1
    let x = tm.mk_var("x", int);
    let fx = tm.mk_apply("f", [x], int);
    let x_minus_1 = tm.mk_sub(x, one);
    let fx_prev = tm.mk_apply("f", [x_minus_1], int);
    let fx_prev_plus_1 = tm.mk_add([fx_prev, one]);
    let body = tm.mk_eq(fx, fx_prev_plus_1);
    let forall = tm.mk_forall([("x", int)], body);
    solver.assert(forall, &mut tm);

    // f(0) = 0
    let f0 = tm.mk_apply("f", [zero], int);
    let eq0 = tm.mk_eq(f0, zero);
    solver.assert(eq0, &mut tm);

    // f(5) < 3
    let f5 = tm.mk_apply("f", [five], int);
    let lt = tm.mk_lt(f5, three);
    solver.assert(lt, &mut tm);

    let start = std::time::Instant::now();
    let result = solver.check(&mut tm);
    let elapsed = start.elapsed();

    // Must have terminated – the whole point of the timeout.
    assert!(
        elapsed < std::time::Duration::from_secs(30),
        "timeout was not enforced: solve ran for {elapsed:?}"
    );
    // The formula is UNSAT; a timed-out solve must never fabricate Sat.
    assert_ne!(result, SolverResult::Sat);
}

#[test]
fn generous_timeout_still_solves_small_problem() {
    // A timeout large enough must not interfere with an easy solve.
    let mut tm = TermManager::new();
    let cfg = SolverConfig {
        timeout_ms: 60_000,
        ..SolverConfig::default()
    };
    let mut solver = Solver::with_config(cfg);
    let int = tm.sorts.int_sort;
    let x = tm.mk_var("x", int);
    let five = tm.mk_int(5i64);
    let nine = tm.mk_int(9i64);
    let gt = tm.mk_gt(x, five);
    let lt = tm.mk_lt(x, nine);
    solver.assert(gt, &mut tm);
    solver.assert(lt, &mut tm);
    assert_eq!(solver.check(&mut tm), SolverResult::Sat);
}

// ========  ========
// LIA depth-2 disjunction (package-note item 2) – KNOWN spurious UNSAT.
//
// x0=0 ∧ (x1=x0±1) ∧ (x2=x1±1) ∧ x2=2 is Sat (x1=1, x2=2), yet the solver
// returns Unsat.  Investigation (see the audit notes) traced this to the
// incremental theory-conflict clause-learning path in `oxiz-sat`
// (`solve_with_theory` / `analyze_theory_conflict`): the equivalent *static*
// CNF solves correctly, and no encoding / theory-routing change confined to
// the owned solver-glue files affects the outcome.  The fix therefore lives
// outside this package's owned files.  Kept as an `#[ignore]`d executable
// specification of the expected (Sat) behaviour.
// ========  ========

#[test]
#[ignore = "spurious UNSAT rooted in oxiz-sat theory conflict learning; outside owned files"]
fn lia_depth2_disjunction_is_sat() {
    let r = run_script(
        r#"
(declare-const x0 Int)
(declare-const x1 Int)
(declare-const x2 Int)
(assert (= x0 0))
(assert (or (= x1 (+ x0 1)) (= x1 (- x0 1))))
(assert (or (= x2 (+ x1 1)) (= x2 (- x1 1))))
(assert (= x2 2))
(check-sat)
"#,
    );
    assert_eq!(r, vec![SolverResult::Sat]);
}
