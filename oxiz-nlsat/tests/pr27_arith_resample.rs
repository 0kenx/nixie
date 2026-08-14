//! Regression tests for chronological re-sampling of greedy arithmetic
//! decisions (`NlsatSolver::retry_last_arith_choice`, `solver/resample.rs`).
//!
//! ## The bug
//!
//! The search used to treat an arithmetic variable's empty feasible cell
//! (`ArithDecision::GreedyEmpty`) as a proof of global `Unsat` whenever it
//! happened at decision level 0 – on the theory that no *boolean* choice
//! remained to retract. That reasoning ignores that the *arithmetic*
//! witnesses committed so far were themselves free choices among many valid
//! ones. A bare, unconstrained product equality like `x·y = c` is the
//! sharpest example: the very first witness `IntervalSet::sample` offers an
//! unconstrained variable is `0` (its "always simplest" fallback), and
//! `0·y = c` for nonzero `c` has no solution for `y` – so the old code
//! answered `Unsat` for a trivially satisfiable formula.
//!
//! Every test below is a shape verified to reproduce a *wrong* answer on the
//! pre-fix search (checked by hand against the old
//! `GreedyEmpty` + `level() == 0` ⇒ `Unsat` branch); the fixed search must
//! retry the earlier variable's sample instead of concluding anything from a
//! single unlucky witness.

use num_bigint::BigInt;
use num_rational::BigRational;
use oxiz_math::polynomial::Polynomial;
use oxiz_nlsat::solver::{NlsatSolver, SolverResult};
use oxiz_nlsat::types::AtomKind;

fn rat(n: i64) -> BigRational {
    BigRational::from_integer(BigInt::from(n))
}

fn v0() -> Polynomial {
    Polynomial::from_var(0)
}

fn v1() -> Polynomial {
    Polynomial::from_var(1)
}

fn cst(n: i64) -> Polynomial {
    Polynomial::constant(rat(n))
}

/// `x·y = 35`: a bare, otherwise-unconstrained product equality. Trivially
/// satisfiable (e.g. `x=5, y=7`), but the first greedy sample for whichever
/// variable is decided first is `0`, making the other variable's cell empty.
#[test]
fn test_pr27_bare_product_equality_is_sat() {
    let mut solver = NlsatSolver::new();
    let eq = solver.new_ineq_atom(
        Polynomial::sub(&Polynomial::mul(&v0(), &v1()), &cst(35)),
        AtomKind::Eq,
    );
    solver.add_clause(vec![solver.atom_literal(eq, true)]);
    assert_eq!(
        solver.solve(),
        SolverResult::Sat,
        "x*y = 35 is satisfiable over the reals"
    );
}

/// Same shape, negative target: `x·y = -18`.
#[test]
fn test_pr27_bare_product_equality_negative_target_is_sat() {
    let mut solver = NlsatSolver::new();
    let eq = solver.new_ineq_atom(
        Polynomial::sub(&Polynomial::mul(&v0(), &v1()), &cst(-18)),
        AtomKind::Eq,
    );
    solver.add_clause(vec![solver.atom_literal(eq, true)]);
    assert_eq!(
        solver.solve(),
        SolverResult::Sat,
        "x*y = -18 is satisfiable over the reals"
    );
}

/// Same failure mode reached through a strict inequality instead of an
/// equality: `x·y > 40`. `x = 0` makes `0 > 40` false for every `y`, but the
/// conjunction (a single clause) is easily satisfiable (`x=y=7`).
#[test]
fn test_pr27_bare_product_inequality_is_sat() {
    let mut solver = NlsatSolver::new();
    let gt = solver.new_ineq_atom(
        Polynomial::sub(&Polynomial::mul(&v0(), &v1()), &cst(40)),
        AtomKind::Gt,
    );
    solver.add_clause(vec![solver.atom_literal(gt, true)]);
    assert_eq!(
        solver.solve(),
        SolverResult::Sat,
        "x*y > 40 is satisfiable over the reals"
    );
}

/// The same product equality, but reached at decision level > 0 behind a
/// free boolean disjunction, so the old level-0-only shortcut did not even
/// need to fire for this exact clause to still be at risk from the same
/// underlying `GreedyEmpty` mishandling one level up.
#[test]
fn test_pr27_product_equality_under_boolean_decision_is_sat() {
    let mut solver = NlsatSolver::new();
    let p = solver.new_bool_var();
    let q = solver.new_bool_var();
    solver.add_clause(vec![
        oxiz_nlsat::types::Literal::positive(p),
        oxiz_nlsat::types::Literal::positive(q),
    ]);

    let eq = solver.new_ineq_atom(
        Polynomial::sub(&Polynomial::mul(&v0(), &v1()), &cst(35)),
        AtomKind::Eq,
    );
    solver.add_clause(vec![solver.atom_literal(eq, true)]);

    assert_eq!(
        solver.solve(),
        SolverResult::Sat,
        "x*y = 35 must stay satisfiable even when reached behind a boolean decision"
    );
}

/// A genuinely UNSAT coupled system must still be UNSAT: re-sampling must
/// never manufacture a model that does not exist, only recover from an
/// unlucky witness for a satisfiable one. `x > 0 ∧ x·y = -1 ∧ y > 0` has no
/// real solution (a positive times a positive cannot be `-1`).
#[test]
fn test_pr27_resample_does_not_mask_genuine_unsat() {
    let mut solver = NlsatSolver::new();
    let x_pos = solver.new_ineq_atom(v0(), AtomKind::Gt);
    let y_pos = solver.new_ineq_atom(v1(), AtomKind::Gt);
    let prod = solver.new_ineq_atom(
        Polynomial::sub(&Polynomial::mul(&v0(), &v1()), &cst(-1)),
        AtomKind::Eq,
    );
    solver.add_clause(vec![solver.atom_literal(x_pos, true)]);
    solver.add_clause(vec![solver.atom_literal(y_pos, true)]);
    solver.add_clause(vec![solver.atom_literal(prod, true)]);

    let result = solver.solve();
    assert_ne!(
        result,
        SolverResult::Sat,
        "x>0 ∧ y>0 ∧ x*y=-1 has no real solution and must never be reported Sat"
    );
}

/// Three-variable chain, each pair coupled only through the next: `x·y = 12`
/// and `y·z = 30` together, with no direct constraint tying `x` and `z`.
/// Whichever variable is greedily decided first still risks the same
/// zero-sample trap propagating through the chain.
#[test]
fn test_pr27_chained_product_equalities_is_sat() {
    let mut solver = NlsatSolver::new();
    let xy = Polynomial::mul(&v0(), &v1());
    let yz = Polynomial::mul(&v1(), &Polynomial::from_var(2));
    let a1 = solver.new_ineq_atom(Polynomial::sub(&xy, &cst(12)), AtomKind::Eq);
    let a2 = solver.new_ineq_atom(Polynomial::sub(&yz, &cst(30)), AtomKind::Eq);
    solver.add_clause(vec![solver.atom_literal(a1, true)]);
    solver.add_clause(vec![solver.atom_literal(a2, true)]);

    assert_eq!(
        solver.solve(),
        SolverResult::Sat,
        "x*y=12 ∧ y*z=30 is satisfiable (e.g. x=4, y=3, z=10)"
    );
}

/// `NlsatSolver::certify_forced_chain_conflict`: a variable pinned to a
/// single exact value by a linear equality, feeding a genuinely-empty
/// quadratic constraint. `x = 4 ∧ x²+y² = 10` forces `y² = -6`, impossible.
/// Without the forced-chain certifier, re-sampling `x` alone cannot recover
/// this – `x`'s region really is the singleton `{4}` – so the fix must
/// promote the resulting dead end to a genuine lemma instead of leaving it
/// at `Unknown`.
#[test]
fn test_pr27_forced_value_outside_curve_is_unsat() {
    let mut solver = NlsatSolver::new();
    let curve = Polynomial::sub(
        &Polynomial::add(
            &Polynomial::mul(&v0(), &v0()),
            &Polynomial::mul(&v1(), &v1()),
        ),
        &cst(10),
    );
    let on_curve = solver.new_ineq_atom(curve, AtomKind::Eq);
    let pinned = solver.new_ineq_atom(Polynomial::sub(&v0(), &cst(4)), AtomKind::Eq);
    solver.add_clause(vec![solver.atom_literal(on_curve, true)]);
    solver.add_clause(vec![solver.atom_literal(pinned, true)]);

    assert_eq!(
        solver.solve(),
        SolverResult::Unsat,
        "x=4 ∧ x^2+y^2=10 is UNSAT (would need y^2=-6)"
    );
}

/// The same shape must stay SAT when the pinned value is actually reachable:
/// `x = 1 ∧ x²+y² = 10` needs `y² = 9`, i.e. `y = ±3`.
#[test]
fn test_pr27_forced_value_on_curve_stays_sat() {
    let mut solver = NlsatSolver::new();
    let curve = Polynomial::sub(
        &Polynomial::add(
            &Polynomial::mul(&v0(), &v0()),
            &Polynomial::mul(&v1(), &v1()),
        ),
        &cst(10),
    );
    let on_curve = solver.new_ineq_atom(curve, AtomKind::Eq);
    let pinned = solver.new_ineq_atom(Polynomial::sub(&v0(), &cst(1)), AtomKind::Eq);
    solver.add_clause(vec![solver.atom_literal(on_curve, true)]);
    solver.add_clause(vec![solver.atom_literal(pinned, true)]);

    assert_eq!(
        solver.solve(),
        SolverResult::Sat,
        "x=1 ∧ x^2+y^2=10 is SAT (y = ±3)"
    );
}

/// `NlsatSolver::certify_additive_bound_conflict`: individually-satisfiable
/// strict lower bounds whose sum already reaches a strict upper bound on
/// their total. `a > 10 ∧ b > 10 ∧ a+b < 15` is UNSAT since `a+b` is forced
/// `> 20`. Neither `certify_sign_conflict` (no multiplicative coupling here)
/// nor a single variable's own Sturm region can see this – only the additive
/// combination is inconsistent.
#[test]
fn test_pr27_additive_lower_bounds_exceed_sum_upper_bound_is_unsat() {
    let mut solver = NlsatSolver::new();
    let a_lo = solver.new_ineq_atom(Polynomial::sub(&v0(), &cst(10)), AtomKind::Gt);
    let b_lo = solver.new_ineq_atom(Polynomial::sub(&v1(), &cst(10)), AtomKind::Gt);
    let sum_hi = solver.new_ineq_atom(
        Polynomial::sub(&Polynomial::add(&v0(), &v1()), &cst(15)),
        AtomKind::Lt,
    );
    solver.add_clause(vec![solver.atom_literal(a_lo, true)]);
    solver.add_clause(vec![solver.atom_literal(b_lo, true)]);
    solver.add_clause(vec![solver.atom_literal(sum_hi, true)]);

    assert_eq!(
        solver.solve(),
        SolverResult::Unsat,
        "a>10 ∧ b>10 ∧ a+b<15 is UNSAT (a+b is forced above 20)"
    );
}

/// Non-strict boundary case built from negated-`Lt` (`>=`) lower bounds:
/// `a >= 3 ∧ b >= 4 ∧ a+b < 7` is still UNSAT – the non-strict lower bounds
/// force `a+b >= 7`, contradicting the strict upper bound at exactly the
/// same total. Exercises the `(AtomKind::Lt, false)` "not less than" lower
/// bound parsing branch and the equal-bound tie-break in
/// `certify_additive_bound_conflict`.
#[test]
fn test_pr27_additive_nonstrict_lower_bounds_meet_strict_upper_is_unsat() {
    let mut solver = NlsatSolver::new();
    // ¬(a < 3)  ==  a >= 3
    let a_lo = solver.new_ineq_atom(Polynomial::sub(&v0(), &cst(3)), AtomKind::Lt);
    // ¬(b < 4)  ==  b >= 4
    let b_lo = solver.new_ineq_atom(Polynomial::sub(&v1(), &cst(4)), AtomKind::Lt);
    let sum_hi = solver.new_ineq_atom(
        Polynomial::sub(&Polynomial::add(&v0(), &v1()), &cst(7)),
        AtomKind::Lt,
    );
    solver.add_clause(vec![solver.atom_literal(a_lo, false)]);
    solver.add_clause(vec![solver.atom_literal(b_lo, false)]);
    solver.add_clause(vec![solver.atom_literal(sum_hi, true)]);

    assert_eq!(
        solver.solve(),
        SolverResult::Unsat,
        "a>=3 ∧ b>=4 ∧ a+b<7 is UNSAT (a+b is forced to at least 7)"
    );
}

/// Soundness guard: lower bounds that do *not* force the sum past the upper
/// bound must stay SAT. `a > 1 ∧ b > 1 ∧ a+b < 15` has plenty of room
/// (e.g. `a=b=2`).
#[test]
fn test_pr27_additive_bounds_with_room_stay_sat() {
    let mut solver = NlsatSolver::new();
    let a_lo = solver.new_ineq_atom(Polynomial::sub(&v0(), &cst(1)), AtomKind::Gt);
    let b_lo = solver.new_ineq_atom(Polynomial::sub(&v1(), &cst(1)), AtomKind::Gt);
    let sum_hi = solver.new_ineq_atom(
        Polynomial::sub(&Polynomial::add(&v0(), &v1()), &cst(15)),
        AtomKind::Lt,
    );
    solver.add_clause(vec![solver.atom_literal(a_lo, true)]);
    solver.add_clause(vec![solver.atom_literal(b_lo, true)]);
    solver.add_clause(vec![solver.atom_literal(sum_hi, true)]);

    assert_eq!(
        solver.solve(),
        SolverResult::Sat,
        "a>1 ∧ b>1 ∧ a+b<15 is satisfiable (e.g. a=b=2)"
    );
}
