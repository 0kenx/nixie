//! Regression tests for the exact multivariate resultant (todo-1128) and the
//! resultant-based real algebraic-number arithmetic (todo-1129).
//!
//! The multivariate resultant is now computed exactly as a Sylvester-matrix
//! determinant evaluated division-free (Berkowitz), rather than the former
//! wrong-valued `primitive()` approximation.

use num_bigint::BigInt;
use num_rational::BigRational;
use num_traits::Zero;
use oxiz_math::polynomial::Polynomial;
use oxiz_math::realclosure::AlgebraicNumber;

fn rat(n: i64) -> BigRational {
    BigRational::from_integer(BigInt::from(n))
}

// ======== multivariate resultant ========

/// `Res_y(y - x, y - 2) = x - 2` (eliminating y). Hand-computed: the Sylvester
/// matrix of `y - x` and `y - 2` w.r.t. y is `[[1, -x], [1, -2]]`, whose
/// determinant is `-2 + x = x - 2`.
#[test]
fn resultant_bivariate_linear_matches_hand_computed() {
    // p = y - x  (var y = 1, parameter x = 0)
    let p = Polynomial::from_coeffs_int(&[(1, &[(1, 1)]), (-1, &[(0, 1)])]);
    // q = y - 2
    let q = Polynomial::from_coeffs_int(&[(1, &[(1, 1)]), (-2, &[])]);

    let res = p.resultant(&q, 1); // eliminate y

    // Expected: x - 2
    let expected = Polynomial::from_coeffs_int(&[(1, &[(0, 1)]), (-2, &[])]);
    assert_eq!(
        res, expected,
        "Res_y(y-x, y-2) should equal x-2, got {res:?}"
    );
}

/// `Res_y(y^2 - x, y - z) = z^2 - x` (a genuinely bivariate result). The
/// Sylvester matrix w.r.t. y is
/// `[[1, 0, -x], [1, -z, 0], [0, 1, -z]]`, determinant `z^2 - x`.
#[test]
fn resultant_bivariate_quadratic_matches_hand_computed() {
    // p = y^2 - x   (y = var 1, x = var 0)
    let p = Polynomial::from_coeffs_int(&[(1, &[(1, 2)]), (-1, &[(0, 1)])]);
    // q = y - z     (z = var 2)
    let q = Polynomial::from_coeffs_int(&[(1, &[(1, 1)]), (-1, &[(2, 1)])]);

    let res = p.resultant(&q, 1); // eliminate y

    // Expected: z^2 - x
    let expected = Polynomial::from_coeffs_int(&[(1, &[(2, 2)]), (-1, &[(0, 1)])]);
    assert_eq!(
        res, expected,
        "Res_y(y^2 - x, y - z) should equal z^2 - x, got {res:?}"
    );
}

/// A shared factor forces the resultant to vanish identically, even when the
/// operands carry extra variables.
#[test]
fn resultant_bivariate_shared_factor_is_zero() {
    // p = (y - x)(y - 1) = y^2 - (x+1) y + x
    // q = (y - x)        = y - x
    // They share the factor (y - x), so Res_y(p, q) must be the zero poly.
    let p = Polynomial::from_coeffs_int(&[
        (1, &[(1, 2)]),          // y^2
        (-1, &[(0, 1), (1, 1)]), // -x*y
        (-1, &[(1, 1)]),         // -y
        (1, &[(0, 1)]),          // +x
    ]);
    let q = Polynomial::from_coeffs_int(&[(1, &[(1, 1)]), (-1, &[(0, 1)])]); // y - x

    let res = p.resultant(&q, 1);
    assert!(
        res.is_zero(),
        "shared factor (y-x) must give resultant 0, got {res:?}"
    );
}

/// Univariate behaviour is unchanged and exact: `Res(x-2, x-3) = -1`.
#[test]
fn resultant_univariate_still_exact() {
    let p = Polynomial::from_coeffs_int(&[(1, &[(0, 1)]), (-2, &[])]); // x - 2
    let q = Polynomial::from_coeffs_int(&[(1, &[(0, 1)]), (-3, &[])]); // x - 3
    let res = p.resultant(&q, 0);
    assert!(res.is_constant());
    assert_eq!(res.constant_term(), rat(-1));
}

/// `Res(x^2 - 5, x^2 - 2) = 9`, matching the Sylvester determinant test in the
/// `resultant` module – the extended-ops entry point must agree.
#[test]
fn resultant_univariate_quadratics_is_nine() {
    let p = Polynomial::univariate(0, &[rat(-5), rat(0), rat(1)]); // x^2 - 5
    let q = Polynomial::univariate(0, &[rat(-2), rat(0), rat(1)]); // x^2 - 2
    let res = p.resultant(&q, 0);
    assert!(res.is_constant());
    assert_eq!(res.constant_term(), rat(9));
}

// ======== real algebraic-number arithmetic ========

/// √2 + √2 = √8 = 2√2. The computed sum must be a genuine algebraic number
/// whose defining polynomial has 2√2 as a root (verified via gcd with x²-8),
/// and whose isolating interval brackets ≈ 2.828 – not a rational collapse.
#[test]
fn add_algebraic_sqrt2_plus_sqrt2_is_sqrt8() {
    let mut a = AlgebraicNumber::sqrt(&rat(2)).expect("sqrt(2)");
    let mut b = AlgebraicNumber::sqrt(&rat(2)).expect("sqrt(2)");

    let mut sum = a.add_algebraic(&mut b);

    // Refine to a tight interval and check it brackets 2√2 ≈ 2.8284271…
    for _ in 0..60 {
        sum.refine();
    }
    let approx = sum.approximate();
    let lo = BigRational::new(BigInt::from(2828), BigInt::from(1000)); // 2.828
    let hi = BigRational::new(BigInt::from(2829), BigInt::from(1000)); // 2.829
    assert!(
        approx > lo && approx < hi,
        "√2+√2 should be ≈ 2.8284, got {approx}"
    );

    // The defining polynomial must vanish at 2√2 – i.e. it shares the factor
    // x² - 8 (whose roots are ±2√2). gcd of the two must have positive degree.
    let x2_minus_8 = Polynomial::from_coeffs_int(&[(1, &[(0, 2)]), (-8, &[])]);
    let g = sum.polynomial().gcd_univariate(&x2_minus_8);
    assert!(
        g.degree(sum.var()) >= 1,
        "sum's minimal polynomial must share the irrational root 2√2 (root of x²-8); \
         gcd = {g:?}, poly = {:?}",
        sum.polynomial()
    );
}

/// √2 · √3 = √6. The product must be a real algebraic number whose polynomial
/// has √6 as a root (gcd with x²-6) and brackets ≈ 2.449.
#[test]
fn mul_algebraic_sqrt2_times_sqrt3_is_sqrt6() {
    let mut a = AlgebraicNumber::sqrt(&rat(2)).expect("sqrt(2)");
    let mut b = AlgebraicNumber::sqrt(&rat(3)).expect("sqrt(3)");

    let mut prod = a.mul_algebraic(&mut b);

    for _ in 0..60 {
        prod.refine();
    }
    let approx = prod.approximate();
    let lo = BigRational::new(BigInt::from(2449), BigInt::from(1000)); // 2.449
    let hi = BigRational::new(BigInt::from(2450), BigInt::from(1000)); // 2.450
    assert!(
        approx > lo && approx < hi,
        "√2·√3 should be ≈ 2.4495, got {approx}"
    );

    let x2_minus_6 = Polynomial::from_coeffs_int(&[(1, &[(0, 2)]), (-6, &[])]);
    let g = prod.polynomial().gcd_univariate(&x2_minus_6);
    assert!(
        g.degree(prod.var()) >= 1,
        "product's minimal polynomial must share the irrational root √6 (root of x²-6); \
         gcd = {g:?}, poly = {:?}",
        prod.polynomial()
    );
}

/// (1 + √2) + (1 - √2) = 2 – the rational-degeneration case. Even though both
/// operands are irrational, their sum is exactly the rational 2, and the
/// implementation must recognise this and return a rational algebraic number.
#[test]
fn add_algebraic_conjugate_pair_collapses_to_rational_two() {
    // 1 + √2
    let sqrt2 = AlgebraicNumber::sqrt(&rat(2)).expect("sqrt(2)");
    let mut one_plus = sqrt2.add_rational(&rat(1));
    // 1 - √2  = -( √2 - 1 ) = 1 + (-√2); build as 1 - √2 via negate then +1.
    let sqrt2b = AlgebraicNumber::sqrt(&rat(2)).expect("sqrt(2)");
    let mut one_minus = sqrt2b.negate().add_rational(&rat(1));

    // Neither operand is rational.
    assert!(!one_plus.is_rational(), "1+√2 must be irrational");
    assert!(!one_minus.is_rational(), "1-√2 must be irrational");

    let mut sum = one_plus.add_algebraic(&mut one_minus);

    // The exact value is 2: refine and verify the interval brackets 2 and the
    // defining polynomial vanishes at 2.
    for _ in 0..40 {
        sum.refine();
    }
    let two = rat(2);
    assert!(
        sum.polynomial()
            .eval_at(sum.var(), &two)
            .constant_term()
            .is_zero(),
        "the sum's defining polynomial must vanish at 2, poly = {:?}",
        sum.polynomial()
    );
    let (lo, hi) = sum.interval();
    assert!(
        lo <= &two && &two <= hi,
        "isolating interval [{lo}, {hi}] must bracket the exact value 2"
    );
}

/// The purely rational path is unaffected: 2 + 3 = 5, 2 · 3 = 6.
#[test]
fn algebraic_rational_operands_unchanged() {
    let mut a = AlgebraicNumber::from_rational(rat(2));
    let mut b = AlgebraicNumber::from_rational(rat(3));
    assert_eq!(a.add_algebraic(&mut b).approximate(), rat(5));

    let mut c = AlgebraicNumber::from_rational(rat(2));
    let mut d = AlgebraicNumber::from_rational(rat(3));
    assert_eq!(c.mul_algebraic(&mut d).approximate(), rat(6));
}
