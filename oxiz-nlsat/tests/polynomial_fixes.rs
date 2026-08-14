//! Tests for the polynomial operation fixes:
//! - Resultant computation via Polynomial::resultant (replaces zero stub)
//! - leading_coefficient_wrt (replaces clone stub)
//! - Higher-degree root finding via rational root theorem
//! - Derivative sign estimation for monotone polynomials

use num_bigint::BigInt;
use num_rational::BigRational;
use oxiz_math::polynomial::Polynomial;
use oxiz_nlsat::evaluator::Evaluator;
use oxiz_nlsat::solver::{NlsatSolver, SolverResult};
use oxiz_nlsat::types::AtomKind;

fn rat(n: i64) -> BigRational {
    BigRational::from_integer(BigInt::from(n))
}

/// Build a univariate polynomial from integer coefficients.
/// `coeffs[k]` is the coefficient of `x^k`.
fn poly_from_coeffs(var: u32, coeffs: &[i64]) -> Polynomial {
    let mut p = Polynomial::zero();
    let x = Polynomial::from_var(var);
    for (k, &c) in coeffs.iter().enumerate() {
        if c != 0 {
            let mut term = Polynomial::constant(rat(c));
            for _ in 0..k {
                term = &term * &x;
            }
            p = &p + &term;
        }
    }
    p
}

// ======== Resultant Tests ========

/// res(x²-1, x-1, x) should be 0 because x=1 is a common root.
#[test]
fn test_resultant_common_root() {
    // x^2 - 1
    let p = poly_from_coeffs(0, &[-1, 0, 1]);
    // x - 1
    let q = poly_from_coeffs(0, &[-1, 1]);

    let res = p.resultant(&q, 0);
    assert!(
        res.is_zero(),
        "res(x²-1, x-1) should be 0 (common root at x=1), got {:?}",
        res
    );
}

/// res(x-2, x-3, x) should be non-zero (no common root).
#[test]
fn test_resultant_no_common_root() {
    // x - 2
    let p = poly_from_coeffs(0, &[-2, 1]);
    // x - 3
    let q = poly_from_coeffs(0, &[-3, 1]);

    let res = p.resultant(&q, 0);
    assert!(
        !res.is_zero(),
        "res(x-2, x-3) should be non-zero (no common root)"
    );
    // The resultant of two linear polynomials ax+b, cx+d is ad - bc.
    // (1)(-3) - (-2)(1) = -3 + 2 = -1.
    assert!(
        res.is_constant(),
        "Resultant of two linear univariate polys should be constant"
    );
}

/// res(x-2, x-2, x) = 0 (identical polynomials share all roots).
#[test]
fn test_resultant_identical_polys() {
    let p = poly_from_coeffs(0, &[-2, 1]);
    let q = poly_from_coeffs(0, &[-2, 1]);
    let res = p.resultant(&q, 0);
    assert!(
        res.is_zero(),
        "res(p, p) should be 0 for any non-trivial polynomial"
    );
}

// ======== Higher-Degree Root Tests ========

/// Degree-3 polynomial (x-1)(x-2)(x-3) = x³-6x²+11x-6 has three rational roots.
#[test]
fn test_cubic_three_rational_roots() {
    // coefficients: -6 + 11x - 6x^2 + x^3
    let poly = poly_from_coeffs(0, &[-6, 11, -6, 1]);
    let eval = Evaluator::new();
    let mut roots = eval.find_roots(&poly, 0);
    roots.sort();

    assert_eq!(roots.len(), 3, "Expected 3 roots, got {:?}", roots);
    assert_eq!(roots[0], rat(1));
    assert_eq!(roots[1], rat(2));
    assert_eq!(roots[2], rat(3));
}

/// Degree-4 polynomial (x-1)(x-2)(x-3)(x-4) has four rational roots.
#[test]
fn test_quartic_four_rational_roots() {
    // (x-1)(x-2)(x-3)(x-4) = x^4 - 10x^3 + 35x^2 - 50x + 24
    let poly = poly_from_coeffs(0, &[24, -50, 35, -10, 1]);
    let eval = Evaluator::new();
    let mut roots = eval.find_roots(&poly, 0);
    roots.sort();

    assert_eq!(roots.len(), 4, "Expected 4 roots, got {:?}", roots);
    assert_eq!(roots[0], rat(1));
    assert_eq!(roots[1], rat(2));
    assert_eq!(roots[2], rat(3));
    assert_eq!(roots[3], rat(4));
}

/// Double root: x²(x-1) = x³ - x² has roots {0, 1} (not 3 roots, since 0 is double).
/// The evaluator should return at most 2 distinct roots.
#[test]
fn test_cubic_double_root_dedup() {
    // x^3 - x^2 = x^2 * (x - 1)
    let poly = poly_from_coeffs(0, &[0, 0, -1, 1]);
    let eval = Evaluator::new();
    let mut roots = eval.find_roots(&poly, 0);
    roots.sort();

    // Deduplicated: {0, 1}
    assert!(
        roots.len() <= 2,
        "Expected at most 2 distinct roots, got {:?}",
        roots
    );
    assert!(roots.contains(&rat(0)), "Expected root at 0");
    assert!(roots.contains(&rat(1)), "Expected root at 1");
}

/// x³ - x = x(x-1)(x+1) has roots {-1, 0, 1}.
#[test]
fn test_cubic_x_cubed_minus_x_roots() {
    // x^3 - x
    let poly = poly_from_coeffs(0, &[0, -1, 0, 1]);
    let eval = Evaluator::new();
    let mut roots = eval.find_roots(&poly, 0);
    roots.sort();

    assert_eq!(roots.len(), 3, "Expected 3 roots for x³-x, got {:?}", roots);
    assert_eq!(roots[0], rat(-1));
    assert_eq!(roots[1], rat(0));
    assert_eq!(roots[2], rat(1));
}

/// Solver can satisfy x³ - x = 0 (has roots at -1, 0, 1).
#[test]
fn test_solver_cubic_sat() {
    let mut solver = NlsatSolver::new();
    let poly = poly_from_coeffs(0, &[0, -1, 0, 1]);
    let atom_id = solver.new_ineq_atom(poly.clone(), AtomKind::Eq);
    solver.add_clause(vec![solver.atom_literal(atom_id, true)]);

    let result = solver.solve();
    assert_eq!(result, SolverResult::Sat, "x³-x = 0 should be SAT");

    let model = solver.get_model().expect("SAT result should have a model");
    let x_val = model.arith_value(0).expect("x should have a value").clone();
    // Verify the model satisfies x³-x = 0
    let check = x_val.clone() * x_val.clone() * x_val.clone() - x_val.clone();
    assert_eq!(check, rat(0), "Model value {x_val} does not satisfy x³-x=0");
}

// ======== Monotonicity / Derivative Sign Tests ========

/// For x³ + x (derivative 3x² + 1 > 0 always), is_increasing should hold.
#[test]
fn test_monotone_increasing_x_cubed_plus_x() {
    use oxiz_nlsat::monotonicity::MonotonicityAnalyzer;

    // x^3 + x: always increasing (derivative 3x^2 + 1 > 0)
    let poly = poly_from_coeffs(0, &[0, 1, 0, 1]);
    let mut analyzer = MonotonicityAnalyzer::new();
    assert!(
        analyzer.is_increasing(&poly, 0),
        "x³+x should be monotone increasing"
    );
}

/// For x (derivative 1 > 0), is_increasing should hold.
#[test]
fn test_monotone_increasing_linear() {
    use oxiz_nlsat::monotonicity::MonotonicityAnalyzer;

    let poly = poly_from_coeffs(0, &[0, 1]);
    let mut analyzer = MonotonicityAnalyzer::new();
    assert!(
        analyzer.is_increasing(&poly, 0),
        "x should be monotone increasing"
    );
}

/// For -x (derivative -1 < 0), is_decreasing should hold.
#[test]
fn test_monotone_decreasing_neg_x() {
    use oxiz_nlsat::monotonicity::MonotonicityAnalyzer;

    let poly = poly_from_coeffs(0, &[0, -1]);
    let mut analyzer = MonotonicityAnalyzer::new();
    assert!(
        analyzer.is_decreasing(&poly, 0),
        "-x should be monotone decreasing"
    );
}

/// For x² (derivative 2x, changes sign at 0), monotonicity should be unknown.
#[test]
fn test_non_monotone_x_squared() {
    use oxiz_nlsat::monotonicity::MonotonicityAnalyzer;

    let poly = poly_from_coeffs(0, &[0, 0, 1]);
    let mut analyzer = MonotonicityAnalyzer::new();
    assert!(
        !analyzer.is_increasing(&poly, 0) || !analyzer.is_decreasing(&poly, 0),
        "x² is not globally monotone"
    );
}

/// For x⁴ + x² + 1 (always positive, derivative 4x³+2x = 2x(2x²+1)),
/// the polynomial itself has no real roots; derivative sign test via estimate.
#[test]
fn test_always_positive_polynomial_no_roots() {
    // x^4 + x^2 + 1 has no real roots (min value is 1)
    let poly = poly_from_coeffs(0, &[1, 0, 1, 0, 1]);
    let eval = Evaluator::new();
    let roots = eval.find_roots(&poly, 0);
    assert_eq!(roots.len(), 0, "x⁴+x²+1 should have no rational roots");
}
