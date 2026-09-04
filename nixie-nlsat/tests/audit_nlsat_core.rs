//! Regression tests for audited soundness/termination defects in the NLSAT
//! core (solver decision, propagation and main loop).
//!
//! Each test reproduces a specific finding and asserts the corrected behaviour.
//! The overarching invariant is *soundness first*: the solver must never return
//! a definitively wrong `Sat`/`Unsat`, and it must always terminate. Where a
//! real (algebraic) answer is out of reach the honest result is `Unknown`.
//!
//! Several of these tests *do not terminate at all* on the pre-fix code: the
//! empty-feasible-region-at-level>0 loop (finding #2) spins forever, so the very
//! fact that the test returns is the regression signal. The remaining tests
//! distinguish a *wrong answer* on the pre-fix code from the correct one.

use nixie_math::polynomial::Polynomial;
use nixie_nlsat::solver::{NlsatSolver, SolverConfig, SolverResult};
use nixie_nlsat::types::{AtomKind, Literal};
use num_bigint::BigInt;
use num_rational::BigRational;

fn rat(n: i64) -> BigRational {
    BigRational::from_integer(BigInt::from(n))
}

/// `x` as a polynomial in variable 0.
fn x() -> Polynomial {
    Polynomial::from_var(0)
}

/// `y` as a polynomial in variable 1.
fn y() -> Polynomial {
    Polynomial::from_var(1)
}

fn cst(n: i64) -> Polynomial {
    Polynomial::constant(rat(n))
}

/// `x^2 - c`.
fn x2_minus(c: i64) -> Polynomial {
    let x = x();
    let x2 = Polynomial::mul(&x, &x);
    Polynomial::sub(&x2, &Polynomial::constant(rat(c)))
}

/// `x^2 + c`  (positive constant ⇒ no real root).
fn x2_plus(c: i64) -> Polynomial {
    let x = x();
    let x2 = Polynomial::mul(&x, &x);
    Polynomial::add(&x2, &Polynomial::constant(rat(c)))
}

// ======== Finding #1: irrational roots must not be silently dropped ========

/// `x^2 > 2` is SAT (e.g. x = 2). Previously the irrational roots ±√2 were
/// dropped, the feasible region collapsed to empty and the solver returned a
/// wrong UNSAT.
#[test]
fn irrational_gt_is_sat() {
    let mut solver = NlsatSolver::new();
    let atom = solver.new_ineq_atom(x2_minus(2), AtomKind::Gt);
    solver.add_clause(vec![solver.atom_literal(atom, true)]);

    let result = solver.solve();
    assert_eq!(result, SolverResult::Sat, "x^2 > 2 must be SAT");

    // The witness must genuinely satisfy the constraint.
    let model = solver.get_model().expect("SAT model");
    let v = model.arith_value(0).expect("x value").clone();
    assert!(&v * &v > rat(2), "witness x={v} must satisfy x^2 > 2");
}

/// `x^2 < 0` is genuinely UNSAT (no real value works).
#[test]
fn square_lt_zero_is_unsat() {
    let mut solver = NlsatSolver::new();
    let atom = solver.new_ineq_atom(x2_minus(0), AtomKind::Lt);
    solver.add_clause(vec![solver.atom_literal(atom, true)]);

    assert_eq!(solver.solve(), SolverResult::Unsat, "x^2 < 0 must be UNSAT");
}

/// `x^2 = 2` has only the irrational solutions ±√2. The rational-model solver
/// cannot exhibit a witness, but it must NOT return a wrong UNSAT – the honest
/// answer is `Unknown` (a full solution needs algebraic-number model support).
#[test]
fn irrational_eq_is_not_unsat() {
    let mut solver = NlsatSolver::new();
    let atom = solver.new_ineq_atom(x2_minus(2), AtomKind::Eq);
    solver.add_clause(vec![solver.atom_literal(atom, true)]);

    let result = solver.solve();
    assert_ne!(
        result,
        SolverResult::Unsat,
        "x^2 = 2 is satisfiable over the reals; must not be reported UNSAT"
    );
    assert!(
        matches!(result, SolverResult::Unknown | SolverResult::Sat),
        "x^2 = 2 should be Unknown (or Sat), got {result:?}"
    );
}

/// A higher-degree case: `x^2 - 3 > 0` (irrational roots ±√3) is SAT.
#[test]
fn irrational_gt_degree_two_variant() {
    let mut solver = NlsatSolver::new();
    let atom = solver.new_ineq_atom(x2_minus(3), AtomKind::Gt);
    solver.add_clause(vec![solver.atom_literal(atom, true)]);
    assert_eq!(solver.solve(), SolverResult::Sat, "x^2 > 3 must be SAT");
}

// ======== Finding #2: empty feasible region at level>0 must not loop forever ========

/// **Primary loop regression.** `(x^2 + 1 < 0) OR (x - 3 > 0)` is SAT (the first
/// disjunct is infeasible, so any x > 3 with the first literal false works, e.g.
/// x = 4).
///
/// On the pre-fix solver this loops *forever*: the first atom is decided at
/// level 1, `pick_arith_value` finds an empty feasible region (`x^2+1<0` is
/// unsatisfiable), and `solve()` backtracks to level 0 **without learning any
/// lemma or flipping the saved phase**, so `decide()` immediately re-picks the
/// identical decision and reproduces the empty region – indefinitely. The fixed
/// solver instead learns the valid single-variable lemma `¬(x^2+1<0)`, forces
/// that atom false, and finds x = 4.
///
/// The atoms are created so the infeasible one has the lower boolean-variable
/// index (hence is decided first): this is exactly the state that traps the old
/// greedy backtrack.
#[test]
fn empty_region_at_level_gt0_terminates_sat() {
    let mut solver = NlsatSolver::new();
    let infeasible = solver.new_ineq_atom(x2_plus(1), AtomKind::Lt); // x^2 + 1 < 0
    let gt3 = solver.new_ineq_atom(Polynomial::sub(&x(), &cst(3)), AtomKind::Gt); // x > 3
    solver.add_clause(vec![
        solver.atom_literal(infeasible, true),
        solver.atom_literal(gt3, true),
    ]);

    // On the buggy solver control never returns here.
    let result = solver.solve();
    assert_eq!(result, SolverResult::Sat, "(x^2+1<0 OR x>3) is SAT via x>3");
    let v = solver
        .get_model()
        .expect("SAT model")
        .arith_value(0)
        .expect("x value")
        .clone();
    assert!(v > rat(3), "witness x={v} must satisfy x > 3");
}

/// A companion loop regression whose answer is UNSAT: both disjuncts of
/// `(x^2 + 1 < 0) OR (x^2 + 2 < 0)` are individually infeasible, so the formula
/// is UNSAT. The pre-fix solver loops forever (empty region at level>0, no
/// lemma); the fixed solver learns `¬(x^2+1<0)` and `¬(x^2+2<0)`, empties the
/// clause and reports UNSAT.
#[test]
fn empty_region_double_infeasible_is_unsat() {
    let mut solver = NlsatSolver::new();
    let a = solver.new_ineq_atom(x2_plus(1), AtomKind::Lt); // x^2 + 1 < 0
    let b = solver.new_ineq_atom(x2_plus(2), AtomKind::Lt); // x^2 + 2 < 0
    solver.add_clause(vec![
        solver.atom_literal(a, true),
        solver.atom_literal(b, true),
    ]);

    assert_eq!(
        solver.solve(),
        SolverResult::Unsat,
        "both disjuncts infeasible ⇒ UNSAT (and must terminate)"
    );
}

/// Multivariate variant of the level>0 loop (also exercises finding #4's
/// shared-variable coupling). `(x*y > 100 OR x*y > 200)` with `0 < x < 2`,
/// `0 < y < 2` is UNSAT (the product never exceeds 4).
///
/// The pre-fix solver decides both product atoms true, samples x from its own
/// bounds while y is still unassigned (the coupling atoms are ignored for x),
/// then finds an empty region for y and backtracks *without* undoing or negating
/// the pinned product decisions – an infinite loop, since neither pinned choice
/// is ever revised. Because the emptiness couples x and y it cannot be certified
/// as a single-variable lemma, so the fixed solver honestly terminates with
/// `Unknown` rather than a wrong answer or a hang. The property that must hold
/// on the fixed solver is: it *terminates* and never answers a wrong `Sat`.
#[test]
fn multivariate_coupling_loop_terminates() {
    let mut solver = NlsatSolver::new();
    let xy = Polynomial::mul(&x(), &y());
    let hi = solver.new_ineq_atom(Polynomial::sub(&xy, &cst(100)), AtomKind::Gt); // xy > 100
    let hi2 = solver.new_ineq_atom(Polynomial::sub(&xy, &cst(200)), AtomKind::Gt); // xy > 200
    let x_pos = solver.new_ineq_atom(x(), AtomKind::Gt); // x > 0
    let x_lt2 = solver.new_ineq_atom(Polynomial::sub(&x(), &cst(2)), AtomKind::Lt); // x < 2
    let y_pos = solver.new_ineq_atom(y(), AtomKind::Gt); // y > 0
    let y_lt2 = solver.new_ineq_atom(Polynomial::sub(&y(), &cst(2)), AtomKind::Lt); // y < 2

    solver.add_clause(vec![
        solver.atom_literal(hi, true),
        solver.atom_literal(hi2, true),
    ]);
    solver.add_clause(vec![solver.atom_literal(x_pos, true)]);
    solver.add_clause(vec![solver.atom_literal(x_lt2, true)]);
    solver.add_clause(vec![solver.atom_literal(y_pos, true)]);
    solver.add_clause(vec![solver.atom_literal(y_lt2, true)]);

    // On the buggy solver control never returns here (infinite backtrack loop).
    let result = solver.solve();
    assert_ne!(
        result,
        SolverResult::Sat,
        "instance is UNSAT (xy <= 4 < 100); the fixed solver must not answer a wrong SAT"
    );
}

// ======== Finding #4: single-variable jointly-satisfiable constraints stay SAT ========

/// Three jointly-satisfiable constraints on one variable that an over-eager
/// conflict explanation could wrongly exclude: `x > 0 AND x < 2 AND x > 1`
/// (SAT, x = 3/2). Guards against a lemma that negates every shared-variable
/// atom.
#[test]
fn jointly_satisfiable_constraints_stay_sat() {
    let mut solver = NlsatSolver::new();
    let gt0 = solver.new_ineq_atom(x(), AtomKind::Gt);
    let lt2 = solver.new_ineq_atom(Polynomial::sub(&x(), &cst(2)), AtomKind::Lt);
    let gt1 = solver.new_ineq_atom(Polynomial::sub(&x(), &cst(1)), AtomKind::Gt);
    solver.add_clause(vec![solver.atom_literal(gt0, true)]);
    solver.add_clause(vec![solver.atom_literal(lt2, true)]);
    solver.add_clause(vec![solver.atom_literal(gt1, true)]);

    let result = solver.solve();
    assert_eq!(result, SolverResult::Sat, "x in (1,2) is satisfiable");
    let v = solver
        .get_model()
        .expect("model")
        .arith_value(0)
        .expect("x")
        .clone();
    assert!(v > rat(1) && v < rat(2), "witness x={v} in (1,2)");
}

// ======== Finding #3: solve() must reset state for incremental re-solve ========

/// **Stale-model regression.** First solve `x > 0`; the solver commits an
/// arithmetic witness (x = 1). Then add `x > 5` – still jointly SAT (x = 6) –
/// and re-solve.
///
/// On the pre-fix solver `solve()` never resets the trail or the arithmetic
/// model, so on the second call the freshly-asserted `x > 5` literal is
/// evaluated against the *stale* x = 1, `theory_propagate` sees a `(True,False)`
/// contradiction at level 0 and the solver returns a **wrong UNSAT**. The fixed
/// solver resets to a clean level-0 state and finds x = 6.
#[test]
fn incremental_resolve_stale_model_stays_sat() {
    let mut solver = NlsatSolver::new();
    let gt0 = solver.new_ineq_atom(x(), AtomKind::Gt); // x > 0
    solver.add_clause(vec![solver.atom_literal(gt0, true)]);
    assert_eq!(solver.solve(), SolverResult::Sat, "x > 0 is SAT");

    // Now also require x > 5 : still SAT (x = 6), but incompatible with the
    // stale witness x = 1 that the first solve committed.
    let gt5 = solver.new_ineq_atom(Polynomial::sub(&x(), &cst(5)), AtomKind::Gt); // x > 5
    solver.add_clause(vec![solver.atom_literal(gt5, true)]);

    assert_eq!(
        solver.solve(),
        SolverResult::Sat,
        "x > 0 AND x > 5 must stay SAT on re-solve (no stale-model conflict)"
    );
    let v = solver
        .get_model()
        .expect("model")
        .arith_value(0)
        .expect("x")
        .clone();
    assert!(v > rat(5), "witness x={v} must satisfy x > 5");
}

/// After a SAT solve the stale arithmetic model must be discarded so that a
/// subsequent, now-contradictory, re-solve yields UNSAT.
#[test]
fn incremental_resolve_becomes_unsat() {
    let mut solver = NlsatSolver::new();
    let gt0 = solver.new_ineq_atom(x(), AtomKind::Gt); // x > 0
    solver.add_clause(vec![solver.atom_literal(gt0, true)]);

    assert_eq!(solver.solve(), SolverResult::Sat, "x > 0 is SAT");

    // Now also require x < 0 : the conjunction is UNSAT.
    let lt0 = solver.new_ineq_atom(x(), AtomKind::Lt); // x < 0
    solver.add_clause(vec![solver.atom_literal(lt0, true)]);

    assert_eq!(
        solver.solve(),
        SolverResult::Unsat,
        "x > 0 AND x < 0 must be UNSAT on re-solve"
    );
}

// ======== Finding #5: an explicit empty clause makes the formula UNSAT ========

#[test]
fn empty_clause_is_unsat() {
    let mut solver = NlsatSolver::new();

    // A perfectly satisfiable unit constraint...
    let gt0 = solver.new_ineq_atom(x(), AtomKind::Gt);
    solver.add_clause(vec![solver.atom_literal(gt0, true)]);

    // ...plus an explicit empty (false) clause.
    solver.add_clause(Vec::<Literal>::new());

    assert_eq!(
        solver.solve(),
        SolverResult::Unsat,
        "a formula containing the empty clause is UNSAT"
    );
}

// ======== Finding #6: max_conflicts must be honoured (Unknown reachable) ========

/// Build the fully-enumerated 3-variable CNF (all 8 clauses) which is UNSAT and
/// requires several decisions/conflicts to refute. With a conflict budget of 1
/// the solver must give up with `Unknown` rather than exhausting the search.
#[test]
fn max_conflicts_yields_unknown() {
    fn build(config: SolverConfig) -> SolverResult {
        let mut solver = NlsatSolver::with_config(config);
        let a = solver.new_bool_var();
        let b = solver.new_bool_var();
        let c = solver.new_bool_var();
        for &sa in &[true, false] {
            for &sb in &[true, false] {
                for &sc in &[true, false] {
                    solver.add_clause(vec![
                        Literal::new(a, sa),
                        Literal::new(b, sb),
                        Literal::new(c, sc),
                    ]);
                }
            }
        }
        solver.solve()
    }

    // Default (large) budget: the instance is refuted as UNSAT.
    assert_eq!(
        build(SolverConfig::default()),
        SolverResult::Unsat,
        "the 8-clause CNF is UNSAT with a normal budget"
    );

    // Tiny budget: the solver must stop early with Unknown, never a wrong Sat.
    let tight = SolverConfig {
        max_conflicts: 1,
        ..SolverConfig::default()
    };
    let result = build(tight);
    assert_eq!(
        result,
        SolverResult::Unknown,
        "a conflict budget of 1 must stop the search early with Unknown"
    );
}
