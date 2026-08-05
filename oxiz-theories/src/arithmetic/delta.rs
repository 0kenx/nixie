//! Delta-rational numbers for strict inequalities
//!
//! A delta-rational represents a value of the form `r + k*δ` where:
//! - r is a rational number (the "real" part)
//! - k is a rational number (the "delta" coefficient)
//! - δ is an infinitesimally small positive value
//!
//! This allows exact representation of strict inequalities in LRA:
//! - `x < c` becomes `x <= c - δ` (represented as (c, -1))
//! - `x > c` becomes `x >= c + δ` (represented as (c, 1))

#[allow(unused_imports)]
use crate::prelude::*;
use core::cmp::Ordering;
use core::ops::{Add, AddAssign, Mul, MulAssign, Neg, Sub, SubAssign};
use num_rational::Rational64;
use num_traits::{One, Zero};

/// A delta-rational number: represents `real + delta * δ` where δ is infinitesimal
#[derive(Debug, Clone, Copy, Default)]
pub struct DeltaRational {
    /// The real part
    pub real: Rational64,
    /// The delta coefficient (multiplied by infinitesimal δ)
    pub delta: Rational64,
}

impl DeltaRational {
    /// Create a new delta-rational from components
    #[must_use]
    pub const fn new(real: Rational64, delta: Rational64) -> Self {
        Self { real, delta }
    }

    /// Create from a rational (delta = 0)
    #[must_use]
    pub fn from_rational(r: Rational64) -> Self {
        Self {
            real: r,
            delta: Rational64::zero(),
        }
    }

    /// Create zero
    #[must_use]
    pub fn zero() -> Self {
        Self {
            real: Rational64::zero(),
            delta: Rational64::zero(),
        }
    }

    /// Create a positive infinitesimal (0 + δ)
    #[must_use]
    pub fn epsilon() -> Self {
        Self {
            real: Rational64::zero(),
            delta: Rational64::one(),
        }
    }

    /// Create a negative infinitesimal (0 - δ)
    #[must_use]
    pub fn neg_epsilon() -> Self {
        Self {
            real: Rational64::zero(),
            delta: -Rational64::one(),
        }
    }

    /// Check if this is exactly zero
    #[must_use]
    pub fn is_zero(&self) -> bool {
        self.real.is_zero() && self.delta.is_zero()
    }

    /// Check if this is positive (greater than zero)
    #[must_use]
    pub fn is_positive(&self) -> bool {
        match self.real.cmp(&Rational64::zero()) {
            Ordering::Greater => true,
            Ordering::Less => false,
            Ordering::Equal => self.delta > Rational64::zero(),
        }
    }

    /// Check if this is negative (less than zero)
    #[must_use]
    pub fn is_negative(&self) -> bool {
        match self.real.cmp(&Rational64::zero()) {
            Ordering::Less => true,
            Ordering::Greater => false,
            Ordering::Equal => self.delta < Rational64::zero(),
        }
    }

    /// Check if this is non-negative (>= 0)
    #[must_use]
    pub fn is_non_negative(&self) -> bool {
        !self.is_negative()
    }

    /// Check if this is non-positive (<= 0)
    #[must_use]
    pub fn is_non_positive(&self) -> bool {
        !self.is_positive()
    }

    /// Get the floor (largest integer <= this value)
    #[must_use]
    pub fn floor(&self) -> i64 {
        let real_floor = self.real.floor().to_integer();
        // If real is exactly an integer and delta is negative, floor is real - 1
        if self.real.fract().is_zero() && self.delta < Rational64::zero() {
            real_floor - 1
        } else {
            real_floor
        }
    }

    /// Get the ceiling (smallest integer >= this value)
    #[must_use]
    pub fn ceil(&self) -> i64 {
        let real_ceil = self.real.ceil().to_integer();
        // If real is exactly an integer and delta is positive, ceil is real + 1
        if self.real.fract().is_zero() && self.delta > Rational64::zero() {
            real_ceil + 1
        } else {
            real_ceil
        }
    }
}

impl From<Rational64> for DeltaRational {
    fn from(r: Rational64) -> Self {
        Self::from_rational(r)
    }
}

impl From<i64> for DeltaRational {
    fn from(n: i64) -> Self {
        Self::from_rational(Rational64::from_integer(n))
    }
}

impl PartialEq for DeltaRational {
    fn eq(&self, other: &Self) -> bool {
        self.real == other.real && self.delta == other.delta
    }
}

impl Eq for DeltaRational {}

impl PartialOrd for DeltaRational {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

impl Ord for DeltaRational {
    fn cmp(&self, other: &Self) -> Ordering {
        match self.real.cmp(&other.real) {
            Ordering::Equal => self.delta.cmp(&other.delta),
            other => other,
        }
    }
}

impl Neg for DeltaRational {
    type Output = Self;

    fn neg(self) -> Self::Output {
        Self {
            real: -self.real,
            delta: -self.delta,
        }
    }
}

impl Add for DeltaRational {
    type Output = Self;

    fn add(self, rhs: Self) -> Self::Output {
        Self {
            real: self.real + rhs.real,
            delta: self.delta + rhs.delta,
        }
    }
}

impl AddAssign for DeltaRational {
    fn add_assign(&mut self, rhs: Self) {
        self.real += rhs.real;
        self.delta += rhs.delta;
    }
}

impl Sub for DeltaRational {
    type Output = Self;

    fn sub(self, rhs: Self) -> Self::Output {
        Self {
            real: self.real - rhs.real,
            delta: self.delta - rhs.delta,
        }
    }
}

impl SubAssign for DeltaRational {
    fn sub_assign(&mut self, rhs: Self) {
        self.real -= rhs.real;
        self.delta -= rhs.delta;
    }
}

/// `a * b` with an integer fast-path.
///
/// QF_LIA coefficients — and, on an integer-only tableau, most simplex
/// values — have denominator 1, but `num_rational::Ratio::mul` runs its full
/// cross-GCD reduction unconditionally regardless: profiling a QF_UFLIA
/// solve showed this `Mul` as the single largest contributor to simplex time.
/// When both operands are already integers the product `a.numer() *
/// b.numer()` over denominator `1` is already in canonical (reduced,
/// positive-denominator) form, so `Ratio::new_raw` — which skips the
/// reduction `Ratio::new` performs — is exact, not an approximation.
///
/// # The overflow fallback
///
/// When both denominators are `1`, `gcd(numer, 1) == 1` always, so there is
/// *no* cross-GCD cancellation available to shrink the operands before
/// multiplying — `num_rational`'s own `Mul`/`CheckedMul` impls degenerate to
/// the same raw `numer * numer` product `checked_mul` above just tried.  So a
/// `checked_mul` failure here means the exact product genuinely does not fit
/// `i64`; falling back to plain `a * b` would re-run that same
/// non-cross-reducible multiplication through `Ratio::mul`'s unchecked `*`
/// operator, which panics under debug overflow checks (and silently wraps in
/// release) instead of failing safely.
///
/// The fallback below widens to `i128` first — `i64::MIN * i64::MIN` is
/// `2^126`, comfortably inside `i128`'s range, so this step itself can never
/// overflow. If the widened product still does not fit back into `i64`, no
/// reduction could ever have rescued it (see above), so this is a genuine
/// precision boundary of `Rational64`'s `i64` backing, not something a
/// cleverer algorithm could avoid; we saturate toward the correct sign
/// instead of panicking, trading exactness at that extreme for a defined,
/// non-crashing result. A mixed-denominator operand pair never reaches this
/// branch at all — it takes the `a * b` path below, where `Ratio::mul`'s
/// cross-GCD reduction applies normally.
fn mul_r64_fast(a: Rational64, b: Rational64) -> Rational64 {
    if *a.denom() == 1 && *b.denom() == 1 {
        let (an, bn) = (*a.numer(), *b.numer());
        if let Some(n) = an.checked_mul(bn) {
            return Rational64::new_raw(n, 1);
        }
        let wide = i128::from(an) * i128::from(bn);
        return match i64::try_from(wide) {
            Ok(n) => Rational64::new_raw(n, 1),
            Err(_) => {
                let saturated = if wide.is_positive() {
                    i64::MAX
                } else {
                    i64::MIN
                };
                Rational64::from_integer(saturated)
            }
        };
    }
    a * b
}

impl Mul<Rational64> for DeltaRational {
    type Output = Self;

    fn mul(self, rhs: Rational64) -> Self::Output {
        Self {
            real: mul_r64_fast(self.real, rhs),
            delta: mul_r64_fast(self.delta, rhs),
        }
    }
}

impl MulAssign<Rational64> for DeltaRational {
    fn mul_assign(&mut self, rhs: Rational64) {
        self.real = mul_r64_fast(self.real, rhs);
        self.delta = mul_r64_fast(self.delta, rhs);
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_delta_rational_basic() {
        let a = DeltaRational::from_rational(Rational64::from_integer(5));
        let b = DeltaRational::from_rational(Rational64::from_integer(3));

        assert!(a > b);
        assert_eq!(a - b, DeltaRational::from(2));
    }

    #[test]
    fn test_delta_rational_with_epsilon() {
        let five = DeltaRational::from(5);
        let five_minus_eps = DeltaRational::new(Rational64::from_integer(5), -Rational64::one());
        let five_plus_eps = DeltaRational::new(Rational64::from_integer(5), Rational64::one());

        assert!(five_minus_eps < five);
        assert!(five < five_plus_eps);
        assert!(five_minus_eps < five_plus_eps);
    }

    #[test]
    fn test_delta_is_positive_negative() {
        let eps = DeltaRational::epsilon();
        let neg_eps = DeltaRational::neg_epsilon();
        let zero = DeltaRational::zero();

        assert!(eps.is_positive());
        assert!(!eps.is_negative());

        assert!(neg_eps.is_negative());
        assert!(!neg_eps.is_positive());

        assert!(zero.is_zero());
        assert!(!zero.is_positive());
        assert!(!zero.is_negative());
    }

    #[test]
    fn test_delta_floor_ceil() {
        // 5 - ε should have floor 4, ceil 5
        let five_minus_eps = DeltaRational::new(Rational64::from_integer(5), -Rational64::one());
        assert_eq!(five_minus_eps.floor(), 4);
        assert_eq!(five_minus_eps.ceil(), 5);

        // 5 + ε should have floor 5, ceil 6
        let five_plus_eps = DeltaRational::new(Rational64::from_integer(5), Rational64::one());
        assert_eq!(five_plus_eps.floor(), 5);
        assert_eq!(five_plus_eps.ceil(), 6);

        // 5.5 should have floor 5, ceil 6 (delta doesn't matter)
        let five_point_five = DeltaRational::from_rational(Rational64::new(11, 2));
        assert_eq!(five_point_five.floor(), 5);
        assert_eq!(five_point_five.ceil(), 6);
    }

    #[test]
    fn test_delta_arithmetic() {
        let a = DeltaRational::new(Rational64::from_integer(3), Rational64::one());
        let b = DeltaRational::new(Rational64::from_integer(2), -Rational64::one());

        // (3 + δ) + (2 - δ) = 5
        let sum = a + b;
        assert_eq!(sum.real, Rational64::from_integer(5));
        assert_eq!(sum.delta, Rational64::zero());

        // (3 + δ) - (2 - δ) = 1 + 2δ
        let diff = a - b;
        assert_eq!(diff.real, Rational64::from_integer(1));
        assert_eq!(diff.delta, Rational64::from_integer(2));

        // (3 + δ) * 2 = 6 + 2δ
        let scaled = a * Rational64::from_integer(2);
        assert_eq!(scaled.real, Rational64::from_integer(6));
        assert_eq!(scaled.delta, Rational64::from_integer(2));
    }

    #[test]
    fn test_mul_r64_fast_matches_ratio_mul() {
        // Integer x integer takes the `new_raw` fast path; the result must
        // still equal the reference `Ratio::mul` and stay canonical
        // (denominator 1). Signs are varied across the four quadrants, and a
        // zero operand is included on the negative side so the "0 * negative
        // keeps a positive denominator" case is covered too.
        let cases = [
            (12_i64, 11_i64, 132_i64),
            (-9, 8, -72),
            (7, -6, -42),
            (-6, -7, 42),
            (0, -17, 0),
            (1, 1, 1),
        ];
        for (a, b, expected) in cases {
            let (ra, rb) = (Rational64::from_integer(a), Rational64::from_integer(b));
            let fast = mul_r64_fast(ra, rb);
            assert_eq!(fast, ra * rb, "{a} * {b} must match Ratio::mul");
            assert_eq!(fast, Rational64::from_integer(expected));
            assert_eq!(*fast.denom(), 1, "{a} * {b} must stay canonical");
        }

        // Magnitude boundary: the largest products the `checked_mul` fast path
        // still accepts. `2^31 * 2^31 = 2^62` is the round case just under
        // `i64::MAX`, and `i64::MAX * 1` is the exact edge.
        //
        // A product that genuinely overflows is deliberately NOT exercised:
        // `mul_r64_fast` hands those to `Ratio::mul`, which multiplies the
        // numerators directly (both denominators are 1, so its cross-GCD
        // cancels nothing) and therefore panics under debug overflow checks.
        // That is pre-existing `Ratio` behaviour, not something this fast path
        // introduced -- see its doc comment.
        let two_pow_31 = Rational64::from_integer(1 << 31);
        assert_eq!(
            mul_r64_fast(two_pow_31, two_pow_31),
            Rational64::from_integer(1 << 62),
            "2^31 * 2^31 must stay on the exact fast path"
        );
        let max = Rational64::from_integer(i64::MAX);
        assert_eq!(mul_r64_fast(max, Rational64::one()), max);
        assert_eq!(
            mul_r64_fast(max, -Rational64::one()),
            Rational64::from_integer(-i64::MAX)
        );

        // A fraction on either side (or both) leaves the fast path for the
        // exact `Ratio::mul`, including the cross-reduction back to canonical
        // form and sign normalisation onto the numerator.
        assert_eq!(
            mul_r64_fast(Rational64::new(3, 4), Rational64::from_integer(8)),
            Rational64::from_integer(6)
        );
        assert_eq!(
            mul_r64_fast(Rational64::from_integer(-10), Rational64::new(3, 5)),
            Rational64::from_integer(-6)
        );
        assert_eq!(
            mul_r64_fast(Rational64::new(5, 6), Rational64::new(9, 10)),
            Rational64::new(3, 4)
        );
        // Reciprocal-with-sign: the product reduces all the way to -1.
        let neg = mul_r64_fast(Rational64::new(-7, 3), Rational64::new(3, 7));
        assert_eq!(neg, -Rational64::one());
        assert_eq!(*neg.denom(), 1, "a reduced product must be canonical");
    }

    /// The boundary the earlier comment above flagged as "deliberately NOT
    /// exercised" because it used to panic: two denominator-`1` operands
    /// whose exact product overflows `i64`. Must return, not abort, even
    /// under this workspace's default dev/test profile (`overflow-checks`
    /// defaults on there since `[profile.dev]` never disables it).
    #[test]
    fn test_bonus_mul_r64_fast_overflow_no_panic() {
        let max = Rational64::from_integer(i64::MAX);
        let two = Rational64::from_integer(2);

        // Positive * positive overflow saturates to `i64::MAX`, not a panic
        // or a silently wrapped negative value.
        assert_eq!(mul_r64_fast(max, two), Rational64::from_integer(i64::MAX));

        // Positive * negative overflow saturates to `i64::MIN`.
        assert_eq!(mul_r64_fast(max, -two), Rational64::from_integer(i64::MIN));
        // And the symmetric operand order agrees.
        assert_eq!(mul_r64_fast(-two, max), Rational64::from_integer(i64::MIN));

        // `i64::MIN * i64::MIN` is the largest-magnitude product `mul_r64_fast`
        // can ever be asked for (`2^126`, still well inside `i128`) and must
        // not panic while computing the widened intermediate either.
        let min = Rational64::from_integer(i64::MIN);
        assert_eq!(mul_r64_fast(min, min), Rational64::from_integer(i64::MAX));

        // Just *below* the overflow boundary the product must still come out
        // exact, not saturated: `(MAX/2) * 2` fits `i64` (it is one short of
        // `MAX` when `MAX` is odd), so this must take the plain `checked_mul`
        // path rather than the widen-and-saturate fallback.
        let half_max = Rational64::from_integer(i64::MAX / 2);
        assert_eq!(
            mul_r64_fast(half_max, two),
            Rational64::from_integer((i64::MAX / 2) * 2)
        );
        // One step past that boundary overflows and must saturate rather
        // than panic or wrap.
        let half_max_plus_one = Rational64::from_integer(i64::MAX / 2 + 1);
        assert_eq!(
            mul_r64_fast(half_max_plus_one, two),
            Rational64::from_integer(i64::MAX)
        );
    }
}
