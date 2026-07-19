//! Regression tests for the `sweep-core-math` minor-item triage sweep.
//!
//! Each test documents the specific defect it guards against; see the
//! corresponding source file for the full rationale.

use num_bigint::BigInt;
use num_rational::{BigRational, Rational64};
use num_traits::Zero;
use oxiz_math::delta_rational::DeltaRational;
use oxiz_math::fast_rational::FastRational;
use oxiz_math::interval::Interval;
use oxiz_math::mpfr::{ArbitraryFloat, Precision, RoundingMode};
use oxiz_math::polynomial::Polynomial;
use rustc_hash::FxHashMap;

fn rat(n: i64) -> BigRational {
    BigRational::from_integer(BigInt::from(n))
}

// ---------------------------------------------------------------------------
// oxiz-math/src/interval.rs — Interval::mul openness must not exclude an
// attainable value tied at the extremum through a different (closed) corner.
// ---------------------------------------------------------------------------

#[test]
fn interval_mul_keeps_attainable_zero_closed() {
    // self = (0, 2]  (open at 0, closed at 2)
    // other = [0, 1] (closed both ends)
    //
    // The corner (self.hi=2, other.lo=0) is closed and produces the value
    // 0, so 0 is attained by the product (e.g. x=2, y=0) even though the
    // (self.lo=0, other.lo=0) corner producing the same numeric value is
    // open. The result must therefore be closed at 0, not open.
    let self_iv = Interval::half_open_left(rat(0), rat(2));
    let other_iv = Interval::closed(rat(0), rat(1));

    let product = self_iv.mul(&other_iv);

    assert_eq!(product.lo, oxiz_math::interval::Bound::finite(rat(0)));
    assert!(
        !product.lo_open,
        "0 is attained (2 * 0 = 0) and must be a closed lower bound"
    );
    assert!(product.contains(&rat(0)));
}

// ---------------------------------------------------------------------------
// oxiz-math/src/fast_rational.rs — division by zero must panic in both
// debug and release, never silently yield 0.
// ---------------------------------------------------------------------------

#[test]
#[should_panic(expected = "division by zero")]
fn fast_rational_small_div_by_zero_panics() {
    let a = FastRational::from(5i64);
    let b = FastRational::zero();
    let _ = a / b;
}

#[test]
#[should_panic(expected = "division by zero")]
fn fast_rational_big_div_by_zero_panics() {
    // Force the `Big` representation so the non-`Small` branch of `div` is
    // exercised too.
    let a = FastRational::from(i64::MAX) * FastRational::from(i64::MAX);
    let b = FastRational::zero();
    let _ = a / b;
}

// ---------------------------------------------------------------------------
// oxiz-math/src/mpfr.rs — ArbitraryFloat::one() must equal 1, not
// 2^(precision-1); align_with must not silently truncate shifted-out bits.
// ---------------------------------------------------------------------------

#[test]
fn arbitrary_float_one_is_exactly_one() {
    for bits in [4u32, 8, 16, 53, 128] {
        let precision = Precision::new(bits);
        let one = ArbitraryFloat::one(precision);
        assert_eq!(
            one.to_f64(RoundingMode::RoundNearest),
            1.0,
            "one() at precision {bits} must evaluate to 1.0, not 2^(precision-1)"
        );
    }
}

#[test]
fn arbitrary_float_round_up_sees_truncated_bits() {
    // precision=4: representable values around 1.0 are k/8 for k in
    // [8,15], i.e. 1.0, 1.125, 1.25, ... The exact sum of 1.0 and a tiny
    // positive epsilon (far below precision) is slightly more than 1.0, so
    // RoundUp (round toward +infinity) must return something > 1.0 — never
    // exactly 1.0, which would violate "round toward +infinity" by
    // returning a value below the true sum.
    let precision = Precision::new(4);
    let one = ArbitraryFloat::one(precision);
    let epsilon = ArbitraryFloat::from_f64(0.0001, precision);

    let sum = one.add(&epsilon, RoundingMode::RoundUp);
    assert!(
        sum.to_f64(RoundingMode::RoundNearest) > 1.0,
        "RoundUp of 1.0 + tiny_epsilon must round away from zero, not silently truncate to 1.0"
    );
}

// ---------------------------------------------------------------------------
// oxiz-math/src/delta_rational.rs — scaling by a non-integer rational must
// not silently drop the infinitesimal (strict-inequality) coefficient.
// ---------------------------------------------------------------------------

#[test]
fn delta_rational_mul_by_fraction_preserves_strictness() {
    // 5 - δ  (i.e. `x < 5`), scaled by 1/2, must remain strictly below the
    // scaled rational part (2.5), not become the exact non-strict value.
    let five_minus_delta = DeltaRational::new(rat(5), -1);
    let half = BigRational::new(BigInt::from(1), BigInt::from(2));

    let scaled = five_minus_delta.mul_rational(&half);

    assert_eq!(
        scaled.rational,
        BigRational::new(BigInt::from(5), BigInt::from(2))
    );
    assert!(
        scaled.delta_coeff < 0,
        "strict-inequality direction (delta_coeff sign) must survive scaling by a fraction"
    );
}

#[test]
fn delta_rational_div_by_fraction_preserves_strictness() {
    let five_plus_delta = DeltaRational::new(rat(5), 1);
    let third = BigRational::new(BigInt::from(1), BigInt::from(3));

    let scaled = five_plus_delta
        .div_rational(&third)
        .expect("dividing by a nonzero rational must succeed");

    assert_eq!(scaled.rational, rat(15));
    assert!(
        scaled.delta_coeff > 0,
        "strict-inequality direction must survive division by a fraction"
    );
}

#[test]
fn delta_rational_mul_exact_rational_stays_exact() {
    // No infinitesimal part: scaling by a non-integer must stay exact
    // (this was never broken, but pins the "no delta to lose" fast path).
    let exact = DeltaRational::new(rat(4), 0);
    let half = BigRational::new(BigInt::from(1), BigInt::from(2));
    let scaled = exact.mul_rational(&half);
    assert_eq!(scaled.rational, rat(2));
    assert_eq!(scaled.delta_coeff, 0);
}

// ---------------------------------------------------------------------------
// oxiz-math/src/polynomial/extended_ops.rs
// ---------------------------------------------------------------------------

#[test]
fn polynomial_isolate_roots_finds_root_at_zero() {
    // p(x) = x, a single root exactly at x=0. The seed search ranges are
    // the *open* intervals (0, bound) and (-bound, 0), so a root sitting
    // exactly on their shared boundary must be found by an explicit check,
    // not by either open range.
    let p = Polynomial::from_coeffs_int(&[(1, &[(0, 1)])]);
    let roots = p.isolate_roots(0);

    assert!(
        roots.iter().any(|(lo, hi)| lo.is_zero() && hi.is_zero()),
        "root at x=0 must be isolated, got {roots:?}"
    );
}

#[test]
fn polynomial_isolate_roots_finds_zero_alongside_a_positive_root() {
    // p(x) = x^2 - 4x = x(x-4): roots at 0 and 4, neither of which lands
    // on a bisection midpoint of the other, so this isolates the "root at
    // x=0" fix without also exercising the separate (pre-existing, out of
    // scope for this fix) handling of a root landing exactly on an
    // interior bisection boundary.
    let p = Polynomial::from_coeffs_int(&[(1, &[(0, 2)]), (-4, &[(0, 1)])]);
    let roots = p.isolate_roots(0);
    assert!(
        roots.iter().any(|(lo, hi)| lo.is_zero() && hi.is_zero()),
        "root at x=0 must be isolated, got {roots:?}"
    );
    assert!(
        roots.iter().any(|(lo, hi)| *lo <= rat(4) && rat(4) <= *hi),
        "root at x=4 must still be isolated, got {roots:?}"
    );
}

#[test]
fn polynomial_try_eval_reports_missing_variable_instead_of_panicking() {
    let p = Polynomial::from_coeffs_int(&[(1, &[(0, 1)])]); // x0
    let assignment: FxHashMap<u32, BigRational> = FxHashMap::default();
    assert_eq!(p.try_eval(&assignment), None);
}

#[test]
#[should_panic]
fn polynomial_eval_still_panics_on_missing_variable_as_documented() {
    let p = Polynomial::from_coeffs_int(&[(1, &[(0, 1)])]);
    let assignment: FxHashMap<u32, BigRational> = FxHashMap::default();
    let _ = p.eval(&assignment);
}

#[test]
fn polynomial_resultant_univariate_is_exact_not_approximated() {
    // Res(f, g) = lc(f)^deg(g) * prod_{f(r)=0} g(r). For f = x-2 (root
    // r=2, monic) and g = x-3: Res = g(2) = 2-3 = -1 exactly — this must
    // come out as the *exact* small integer, not whatever a
    // primitive()-approximated value happens to be.
    let p = Polynomial::from_coeffs_int(&[(1, &[(0, 1)]), (-2, &[])]); // x - 2
    let q = Polynomial::from_coeffs_int(&[(1, &[(0, 1)]), (-3, &[])]); // x - 3

    let res = p.resultant(&q, 0);
    assert!(res.is_constant());
    let val = res.constant_term();
    assert_eq!(
        val,
        rat(-1),
        "Res(x-2, x-3) should be exactly -1, got {val}"
    );
}

#[test]
fn polynomial_resultant_shared_root_is_exactly_zero() {
    // p and q share the root x=2, so the resultant must be exactly zero.
    let p = Polynomial::from_coeffs_int(&[(1, &[(0, 2)]), (-4, &[])]); // x^2 - 4  (roots ±2)
    let q = Polynomial::from_coeffs_int(&[(1, &[(0, 1)]), (-2, &[])]); // x - 2
    let res = p.resultant(&q, 0);
    assert!(
        res.is_zero(),
        "shared root must give resultant 0, got {res:?}"
    );
}

#[test]
fn polynomial_as_dense_i64_rejects_genuinely_multivariate_polynomial() {
    // p = x0 + x2, where x2 happens to be the highest-indexed variable
    // (`max_var() == 2`). Extracting a dense i64 vector "in x2" would
    // previously silently drop the x0 term instead of returning None.
    let var = 2u32;
    let p = Polynomial::from_coeffs_int(&[(1, &[(0, 1)]), (1, &[(2, 1)])]);
    assert_eq!(
        p.as_dense_i64(var),
        None,
        "a polynomial containing a variable other than `var` must be rejected"
    );
}

#[test]
fn polynomial_as_dense_i64_accepts_true_univariate() {
    let p = Polynomial::from_coeffs_int(&[(3, &[(2, 2)]), (1, &[])]); // 3*x2^2 + 1
    assert_eq!(p.as_dense_i64(2), Some(vec![1, 0, 3]));
}

// ---------------------------------------------------------------------------
// oxiz-math/src/rewrite (via oxiz-core) is covered separately in
// oxiz-core/tests/audit_sweep_core_math.rs.
// ---------------------------------------------------------------------------

#[allow(dead_code)]
fn unused_rational64_reference(_r: Rational64) {}
