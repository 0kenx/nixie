//! Regression tests for audited arithmetic-solver soundness defects
//! (package: theories-arith-p2).
//!
//! Each test pins a previously-confirmed soundness bug:
//!  1. `ArithSolver::lia().check()` reporting SAT for an integer-infeasible
//!     but LP-feasible system (integrality was never enforced).
//!  2. Simplex pivot-limit exhaustion returning `Ok(())` that read as SAT.
//!  3. `LiaSolver::check()` reporting SAT for `2x = 1` because the B&B
//!     down-branch was taken after `simplex.reset()` erased all constraints.
//!  4. Invalid placeholder cuts changing satisfiability.

use num_rational::Rational64;
use num_traits::One;
use oxiz_core::ast::TermId;
use oxiz_theories::arithmetic::{ArithSolver, LiaSolver, LinExpr, Simplex};
use oxiz_theories::{SimplexConfig, Theory, TheoryCheckResult as TheoryResult};

fn r(n: i64) -> Rational64 {
    Rational64::from_integer(n)
}

/// Finding 1: y = 2x AND y = 2z + 1 is integer-infeasible (parity) but the LP
/// relaxation is feasible with x = z + 1/2.  The LIA solver must NOT answer Sat.
#[test]
fn lia_check_enforces_integrality_parity() {
    let mut solver = ArithSolver::lia();

    let x = TermId::new(1);
    let y = TermId::new(2);
    let z = TermId::new(3);
    let reason = TermId::new(100);

    // y - 2x = 0
    solver.assert_eq(&[(y, r(1)), (x, r(-2))], r(0), reason);
    // y - 2z = 1
    solver.assert_eq(&[(y, r(1)), (z, r(-2))], r(1), reason);

    let result = solver.check().expect("check must not error");
    assert!(
        matches!(result, TheoryResult::Unsat(_)),
        "y=2x AND y=2z+1 is integer-infeasible; got {result:?}"
    );
}

/// Finding 1 (model quality): when LIA is SAT, `value()` must return integral
/// assignments for Int terms — never the fractional LP optimum.
#[test]
fn lia_check_sat_returns_integral_model() {
    let mut solver = ArithSolver::lia();

    let x = TermId::new(1);
    let reason = TermId::new(100);

    // 2 <= 2x <= 4  ⇒  x in {1, 2}
    solver.assert_ge(&[(x, r(2))], r(2), reason);
    solver.assert_le(&[(x, r(2))], r(4), reason);

    let result = solver.check().expect("check must not error");
    assert!(
        matches!(result, TheoryResult::Sat),
        "expected Sat, got {result:?}"
    );

    let vx = solver.value(x).expect("x must have a value");
    assert!(vx.is_integer(), "x must be integral, got {vx}");
    assert!(vx >= r(1) && vx <= r(2), "x out of range: {vx}");
}

/// A genuinely satisfiable LIA system must still be reported SAT after B&B.
#[test]
fn lia_check_sat_simple_feasible() {
    let mut solver = ArithSolver::lia();

    let x = TermId::new(1);
    let y = TermId::new(2);
    let reason = TermId::new(100);

    // x + y = 3, x >= 0, y >= 0  — clearly SAT over integers.
    solver.assert_eq(&[(x, r(1)), (y, r(1))], r(3), reason);
    solver.assert_ge(&[(x, r(1))], r(0), reason);
    solver.assert_ge(&[(y, r(1))], r(0), reason);

    let result = solver.check().expect("check must not error");
    assert!(
        matches!(result, TheoryResult::Sat),
        "expected Sat, got {result:?}"
    );
}

/// LRA (real) mode: the same parity system IS satisfiable over the reals.
#[test]
fn lra_check_parity_is_sat() {
    let mut solver = ArithSolver::lra();

    let x = TermId::new(1);
    let y = TermId::new(2);
    let z = TermId::new(3);
    let reason = TermId::new(100);

    solver.assert_eq(&[(y, r(1)), (x, r(-2))], r(0), reason);
    solver.assert_eq(&[(y, r(1)), (z, r(-2))], r(1), reason);

    let result = solver.check().expect("check must not error");
    assert!(
        matches!(result, TheoryResult::Sat),
        "over the reals x=z+1/2 satisfies both; got {result:?}"
    );
}

/// Finding 2: with a tiny pivot budget the simplex may exhaust its budget on a
/// hard LP.  An exhausted run must be flagged via `resource_limit_reached()` and
/// its `Ok(())` must NOT be interpreted as feasibility.
#[test]
fn simplex_pivot_limit_flags_resource_limit_not_sat() {
    // A conflicting single-variable bound is always resolved trivially, so to
    // provoke the limit we build a feasibility problem and starve the pivots.
    // Effectively no room to pivot on a multi-row problem.
    let cfg = SimplexConfig {
        max_pivots: 1,
        ..SimplexConfig::default()
    };
    let mut simplex = Simplex::with_config(cfg);

    // Build several coupled constraints requiring multiple pivots to satisfy.
    let vars: Vec<_> = (0..6).map(|_| simplex.new_var()).collect();
    for &v in &vars {
        simplex.set_lower(v, r(0), 0);
        simplex.set_upper(v, r(10), 1);
    }
    // sum(v) >= 40 forces several vars up from their lower bound (many pivots).
    let mut e = LinExpr::new();
    for &v in &vars {
        e.add_term(v, Rational64::one());
    }
    e.add_constant(-r(40));
    simplex.add_ge(e, 2);

    let res = simplex.check();
    // The starved run cannot reach feasibility in one pivot, so it must stop at
    // the pivot budget and flag the resource limit rather than returning a
    // definitive answer.
    assert!(
        simplex.resource_limit_reached(),
        "one-pivot budget on a multi-row LP must hit the resource limit"
    );
    // A resource-limited run returns Ok (no conflict proven) — but that Ok is a
    // resource limit, NOT a feasibility proof; the flag is how callers tell the
    // difference and report Unknown instead of Sat.
    assert!(res.is_ok(), "resource-limited run returns Ok, not Err");
}

/// Finding 3: `2x = 1` over the integers is UNSAT.  The public `LiaSolver::check`
/// previously answered SAT because its down-branch ran after `simplex.reset()`
/// wiped every constraint.
#[test]
fn lia_solver_two_x_equals_one_is_unsat() {
    let mut solver = LiaSolver::new();
    let x = solver.new_var();

    // 2x = 1  ⇒  2x - 1 = 0
    let mut e = LinExpr::new();
    e.add_term(x, r(2));
    e.add_constant(-r(1));
    solver.add_eq(e, 0);

    let sat = solver.check().expect("check must not error");
    assert!(!sat, "2x = 1 has no integer solution; got SAT");
}

/// Finding 3 (positive control): `2x = 4` over the integers IS SAT (x = 2), and
/// both branches must remain explorable (no reset() corruption).
#[test]
fn lia_solver_two_x_equals_four_is_sat() {
    let mut solver = LiaSolver::new();
    let x = solver.new_var();

    let mut e = LinExpr::new();
    e.add_term(x, r(2));
    e.add_constant(-r(4));
    solver.add_eq(e, 0);

    let sat = solver.check().expect("check must not error");
    assert!(sat, "2x = 4 has integer solution x = 2; got UNSAT");
}

/// Finding 3/4: a system that is integer-feasible must not be reported UNSAT by
/// invalid cuts or by branch corruption.  x in [1,2], y in [1,2], x + y = 3.
#[test]
fn lia_solver_feasible_not_reported_unsat() {
    let mut solver = LiaSolver::new();
    let x = solver.new_var();
    let y = solver.new_var();

    // x >= 1, x <= 2, y >= 1, y <= 2 (as linear constraints on the solver).
    for &v in &[x, y] {
        let mut lo = LinExpr::new();
        lo.add_term(v, r(1));
        lo.add_constant(-r(1));
        solver.add_ge(lo, 0); // v - 1 >= 0

        let mut hi = LinExpr::new();
        hi.add_term(v, r(1));
        hi.add_constant(-r(2));
        solver.add_le(hi, 0); // v - 2 <= 0
    }

    // x + y = 3
    let mut e = LinExpr::new();
    e.add_term(x, r(1));
    e.add_term(y, r(1));
    e.add_constant(-r(3));
    solver.add_eq(e, 0);

    let sat = solver.check().expect("check must not error");
    assert!(
        sat,
        "x+y=3 with x,y in [1,2] is integer-feasible; got UNSAT"
    );
}
