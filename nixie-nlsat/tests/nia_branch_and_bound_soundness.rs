//! Regression tests for the NIA branch-and-bound soundness audit findings
//! (NIA-3, NIA-4): exact-integrality candidacy, honest incompleteness
//! reporting, and multi-round re-branching on the same variable.
//!
//! Reference: Z3's NIA solver in `nlsat/nlsat_solver.cpp`.

use nixie_math::polynomial::Polynomial;
use nixie_nlsat::nia::{NiaSolver, VarType};
use nixie_nlsat::solver::SolverResult;
use nixie_nlsat::types::AtomKind;
use num_bigint::BigInt;
use num_rational::BigRational;

fn rat(n: i64) -> BigRational {
    BigRational::from_integer(BigInt::from(n))
}

/// NIA-3 regression (exact fix_spec scenario): an integer variable bounded
/// below by a value that is *just barely* not an integer (`1 +
/// 1/10_000_000`, within the old lossy `int_tolerance` (`1e-6`) window of
/// `1`) and bounded above by `10`. Plenty of genuine integer solutions
/// exist (`x` can be any of `2..=10`).
///
/// Pre-fix, `select_branching_variable` gated candidacy on the f64 window
/// `frac > int_tolerance && frac < 1 - int_tolerance`. The lower-bound
/// witness `x = 1 + 1/10_000_000` has `frac ≈ 1e-7 < int_tolerance
/// (1e-6)`, so it was excluded as a branch candidate even though
/// `is_integer_solution`'s *exact* rational test correctly rejects it (its
/// denominator is `10_000_000`, not `1`). With no candidate, the root node
/// fell through the (then-unmarked) `else { continue; }` arm and the
/// search wrongly concluded `Unsat` once the stack emptied -- despite `x =
/// 2` (among others) being a perfectly valid integer witness.
#[test]
fn test_nia_near_integer_lower_bound_does_not_cause_false_unsat() {
    let mut solver = NiaSolver::new();
    let var_x = solver.nlsat_mut().new_arith_var();
    solver.set_var_type(var_x, VarType::Integer);

    let x = Polynomial::from_var(var_x);

    // x >= 1 + 1/10_000_000  i.e. NOT(x - (1 + 1/10_000_000) < 0)
    let just_over_one = rat(1) + BigRational::new(1.into(), 10_000_000.into());
    let lower_poly = Polynomial::sub(&x, &Polynomial::constant(just_over_one));
    let lower_atom = solver.nlsat_mut().new_ineq_atom(lower_poly, AtomKind::Lt);
    let lower_lit = solver.nlsat().atom_literal(lower_atom, false);
    solver.nlsat_mut().add_clause(vec![lower_lit]);

    // x <= 10  i.e. NOT(x - 10 > 0)
    let upper_poly = Polynomial::sub(&x, &Polynomial::constant(rat(10)));
    let upper_atom = solver.nlsat_mut().new_ineq_atom(upper_poly, AtomKind::Gt);
    let upper_lit = solver.nlsat().atom_literal(upper_atom, false);
    solver.nlsat_mut().add_clause(vec![upper_lit]);

    let result = solver.solve();
    assert_ne!(
        result,
        SolverResult::Unsat,
        "x in [1 + 1e-7, 10] has genuine integer solutions (e.g. x=2); a \
         near-but-not-at-integer lower-bound witness must not cause a \
         false Unsat"
    );
    assert_eq!(
        result,
        SolverResult::Sat,
        "the real relaxation of this problem is feasible, so the integer \
         problem must resolve to Sat, not Unknown"
    );

    if let Some(model) = solver.nlsat().get_model() {
        let x_val = model
            .arith_value(var_x)
            .expect("model must assign integer var x");
        assert_eq!(
            x_val.denom(),
            &BigInt::from(1),
            "returned model value must be an exact integer, got {x_val}"
        );
        assert!(
            *x_val >= rat(2) && *x_val <= rat(10),
            "x must lie in the feasible integer range [2, 10], got {x_val}"
        );
    } else {
        panic!("Sat result must carry a model");
    }
}

/// NIA-4 regression: a univariate integer problem structured so that
/// finding the (unique) integer alternative among several close fractional
/// disjuncts requires *more than one* round of branching on the *same*
/// (only) variable.
///
/// `x` is constrained to one of `{2.1, 2.9, 3.5, 4}` (a 4-way disjunctive
/// equality); `4` is the only integer alternative. Whichever fractional
/// disjunct the real relaxation happens to witness first, isolating `4`
/// can require branching on `x`, discovering a *still-fractional* result
/// under the new bound, and branching on `x` again -- exactly the
/// multi-level single-variable convergence that a hard "already branched"
/// filter (the pre-fix `branched_vars: HashSet<Var>`) would break, since
/// it forbade ever re-selecting `x` after its first split. Combined with
/// the NIA-3 "no candidate" incompleteness bug, that combination could
/// make this problem wrongly resolve to `Unsat` even though `x = 4` is a
/// valid integer solution.
#[test]
fn test_nia_two_rounds_of_branching_on_same_variable_finds_integer_solution() {
    let mut solver = NiaSolver::new();
    let var_x = solver.nlsat_mut().new_arith_var();
    solver.set_var_type(var_x, VarType::Integer);

    let x = Polynomial::from_var(var_x);
    let mut disjunct_lits = Vec::new();
    for value in [
        BigRational::new(21.into(), 10.into()), // 2.1
        BigRational::new(29.into(), 10.into()), // 2.9
        BigRational::new(35.into(), 10.into()), // 3.5
        rat(4),                                 // 4 (the only integer)
    ] {
        let poly = Polynomial::sub(&x, &Polynomial::constant(value));
        let atom = solver.nlsat_mut().new_ineq_atom(poly, AtomKind::Eq);
        disjunct_lits.push(solver.nlsat().atom_literal(atom, true));
    }
    solver.nlsat_mut().add_clause(disjunct_lits);

    let result = solver.solve();
    assert_eq!(
        result,
        SolverResult::Sat,
        "x in {{2.1, 2.9, 3.5, 4}} has the unique integer solution x = 4"
    );

    if let Some(model) = solver.nlsat().get_model() {
        let x_val = model
            .arith_value(var_x)
            .expect("model must assign integer var x");
        assert_eq!(*x_val, rat(4), "the only integer-satisfying model is x = 4");
    } else {
        panic!("Sat result must carry a model");
    }
}
