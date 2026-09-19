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
use num_traits::{One, ToPrimitive, Zero};

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

/// Rational multiplication with an integer fast-path.
///
/// Coefficients and many simplex values are integers (denominator 1) in
/// QF_LIA, but `num_rational`'s `Ratio::mul` still runs cross-gcd reduction
/// on every multiply – the single largest cost in the simplex profile (~25%).
/// When both operands are integers the product is `new_raw(a.n*b.n, 1)` with
/// no gcd at all; otherwise we fall back to `Ratio::mul`.  `new_raw` is valid
/// here because `(n, 1)` is already reduced with a positive denominator.
/// Overflow in the fast path falls back to the (wrapping) `Ratio::mul`, which
/// matches the previous unchecked behaviour.
fn mul_r64_fast(a: Rational64, b: Rational64) -> Rational64 {
    if *a.denom() == 1
        && *b.denom() == 1
        && let Some(n) = (*a.numer()).checked_mul(*b.numer())
    {
        return Rational64::new_raw(n, 1);
    }
    a * b
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

/// An exact, unlimited-width delta-rational (`real + delta·δ`), the wide
/// counterpart of [`DeltaRational`]: the bound store's value channel for
/// bounds whose parts leave `Rational64` width (branch bounds at `2^63`,
/// strict bounds hanging off `i64::MIN`, exact propagated bounds that do
/// not narrow).
///
/// Ordering is lexicographic on `(real, delta)` exactly as [`DeltaRational`]
/// orders, so a narrow and a wide value of the same number compare equal.
#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub struct BigDeltaRational {
    /// The real part.
    pub real: num_rational::BigRational,
    /// The infinitesimal coefficient.
    pub delta: num_rational::BigRational,
}

impl BigDeltaRational {
    /// Zero.
    #[must_use]
    pub fn zero() -> Self {
        Self {
            real: num_rational::BigRational::zero(),
            delta: num_rational::BigRational::zero(),
        }
    }

    /// Widen a narrow delta-rational exactly.
    #[must_use]
    pub fn from_narrow(d: &DeltaRational) -> Self {
        Self {
            real: num_rational::BigRational::new(
                num_bigint::BigInt::from(*d.real.numer()),
                num_bigint::BigInt::from(*d.real.denom()),
            ),
            delta: num_rational::BigRational::new(
                num_bigint::BigInt::from(*d.delta.numer()),
                num_bigint::BigInt::from(*d.delta.denom()),
            ),
        }
    }

    /// A real-only value (zero infinitesimal).
    #[must_use]
    pub fn real_only(real: num_rational::BigRational) -> Self {
        Self {
            real,
            delta: num_rational::BigRational::zero(),
        }
    }

    /// Narrow into a [`DeltaRational`]; `None` when either part does not
    /// fit.  Mirrors the workspace's `narrow_rational64` contract: the
    /// `i64::MIN` numerator is rejected (its negation does not fit, and
    /// fixed-width consumers negate bound values).
    #[must_use]
    pub fn narrow(&self) -> Option<DeltaRational> {
        let rn = self.real.numer().to_i64()?;
        let rd = self.real.denom().to_i64()?;
        let dn = self.delta.numer().to_i64()?;
        let dd = self.delta.denom().to_i64()?;
        if rn == i64::MIN || dn == i64::MIN {
            return None;
        }
        Some(DeltaRational {
            real: Rational64::new(rn, rd),
            delta: Rational64::new(dn, dd),
        })
    }

    /// Lexicographic `(real, delta)` comparison against a narrow value,
    /// without materializing this value's narrow form.
    #[must_use]
    pub fn cmp_narrow(&self, other: &DeltaRational) -> Ordering {
        let other_real = num_rational::BigRational::new(
            num_bigint::BigInt::from(*other.real.numer()),
            num_bigint::BigInt::from(*other.real.denom()),
        );
        match self.real.cmp(&other_real) {
            Ordering::Equal => {
                let other_delta = num_rational::BigRational::new(
                    num_bigint::BigInt::from(*other.delta.numer()),
                    num_bigint::BigInt::from(*other.delta.denom()),
                );
                self.delta.cmp(&other_delta)
            }
            o => o,
        }
    }
}

impl core::cmp::Ord for BigDeltaRational {
    fn cmp(&self, other: &Self) -> Ordering {
        match self.real.cmp(&other.real) {
            Ordering::Equal => self.delta.cmp(&other.delta),
            o => o,
        }
    }
}

impl core::cmp::PartialOrd for BigDeltaRational {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

impl From<DeltaRational> for BigDeltaRational {
    fn from(d: DeltaRational) -> Self {
        Self::from_narrow(&d)
    }
}

/// The value of a stored bound: the narrow fast path, or the exact wide
/// form for values that leave `Rational64` width.
///
/// This is the bound channel of the dual-width simplex (the row channel's
/// counterpart is [`crate::arithmetic::simplex::Simplex`]'s `wide_rows`):
/// every state reachable with narrow values only executes the exact same
/// comparisons it always did (the `Narrow`/`Narrow` arms are the old
/// `DeltaRational` ops), while a wide value makes every consumer either
/// compare exactly or explicitly decline — never wrap, never guess.
#[derive(Debug, Clone)]
pub enum BoundValue {
    /// The value fits `Rational64` width (the common case).
    Narrow(DeltaRational),
    /// The exact value; at least one part leaves `Rational64` width.
    Wide(std::sync::Arc<BigDeltaRational>),
}

impl BoundValue {
    /// The narrow form when one exists (an `i64::MIN` numerator is not
    /// narrow — see [`BigDeltaRational::narrow`]).
    #[must_use]
    pub fn narrow(&self) -> Option<DeltaRational> {
        match self {
            BoundValue::Narrow(d) => Some(*d),
            BoundValue::Wide(w) => w.narrow(),
        }
    }

    /// The exact form (widening a narrow value allocates).
    #[must_use]
    pub fn to_big(&self) -> BigDeltaRational {
        match self {
            BoundValue::Narrow(d) => BigDeltaRational::from_narrow(d),
            BoundValue::Wide(w) => (**w).clone(),
        }
    }

    /// Exact lexicographic comparison against a narrow value.
    #[must_use]
    pub fn cmp_narrow(&self, other: &DeltaRational) -> Ordering {
        match self {
            BoundValue::Narrow(d) => d.cmp(other),
            BoundValue::Wide(w) => w.cmp_narrow(other),
        }
    }

    /// Exact lexicographic comparison against an exact (possibly wide)
    /// point value — the wide-point-aware counterpart of
    /// [`Self::cmp_narrow`] for consumers that hold the variable's exact
    /// point from the wide point store.
    #[must_use]
    pub fn cmp_big(&self, other: &BigDeltaRational) -> Ordering {
        match self {
            BoundValue::Narrow(d) => core::cmp::Ordering::reverse(other.cmp_narrow(d)),
            BoundValue::Wide(w) => (**w).cmp(other),
        }
    }

    /// Exact lexicographic comparison between bound values.
    #[must_use]
    pub fn cmp_value(&self, other: &Self) -> Ordering {
        match (self, other) {
            (BoundValue::Narrow(a), BoundValue::Narrow(b)) => a.cmp(b),
            (BoundValue::Narrow(a), BoundValue::Wide(b)) => {
                core::cmp::Ordering::reverse(b.cmp_narrow(a))
            }
            (BoundValue::Wide(a), BoundValue::Narrow(b)) => a.cmp_narrow(b),
            (BoundValue::Wide(a), BoundValue::Wide(b)) => a.cmp(b),
        }
    }

    /// Construct from an exact value, narrowing when it fits.
    #[must_use]
    pub fn from_big(v: BigDeltaRational) -> Self {
        match v.narrow() {
            Some(d) => BoundValue::Narrow(d),
            None => BoundValue::Wide(std::sync::Arc::new(v)),
        }
    }

    /// The exact real part.
    #[must_use]
    pub fn real_big(&self) -> num_rational::BigRational {
        match self {
            BoundValue::Narrow(d) => num_rational::BigRational::new(
                num_bigint::BigInt::from(*d.real.numer()),
                num_bigint::BigInt::from(*d.real.denom()),
            ),
            BoundValue::Wide(w) => w.real.clone(),
        }
    }

    /// The exact infinitesimal coefficient.
    #[must_use]
    pub fn delta_big(&self) -> num_rational::BigRational {
        match self {
            BoundValue::Narrow(d) => num_rational::BigRational::new(
                num_bigint::BigInt::from(*d.delta.numer()),
                num_bigint::BigInt::from(*d.delta.denom()),
            ),
            BoundValue::Wide(w) => w.delta.clone(),
        }
    }
}

impl core::cmp::PartialEq for BoundValue {
    fn eq(&self, other: &Self) -> bool {
        self.cmp_value(other) == Ordering::Equal
    }
}
impl core::cmp::Eq for BoundValue {}
impl core::cmp::Ord for BoundValue {
    fn cmp(&self, other: &Self) -> Ordering {
        self.cmp_value(other)
    }
}
impl core::cmp::PartialOrd for BoundValue {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(<Self as core::cmp::Ord>::cmp(self, other))
    }
}
impl From<DeltaRational> for BoundValue {
    fn from(d: DeltaRational) -> Self {
        BoundValue::Narrow(d)
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
    fn test_mul_r64_fast() {
        // Integer × integer: fast-path must equal `Ratio::mul` and stay reduced.
        assert_eq!(
            mul_r64_fast(Rational64::from_integer(6), Rational64::from_integer(7)),
            Rational64::from_integer(42)
        );
        assert_eq!(
            mul_r64_fast(Rational64::from_integer(-4), Rational64::from_integer(5)),
            Rational64::from_integer(-20)
        );
        assert_eq!(
            mul_r64_fast(Rational64::from_integer(0), Rational64::from_integer(9)),
            Rational64::from_integer(0)
        );
        // Fraction × integer falls back to `Ratio::mul`.
        let half = Rational64::new(1, 2);
        assert_eq!(
            mul_r64_fast(half, Rational64::from_integer(6)),
            Rational64::from_integer(3)
        );
        // Fraction × fraction: full reduction.
        assert_eq!(
            mul_r64_fast(Rational64::new(2, 3), Rational64::new(3, 4)),
            Rational64::new(1, 2)
        );
        // The fast-path result must satisfy the canonical-form invariant
        // (reduced, positive denominator) so downstream `Ratio` ops stay sound.
        let p = mul_r64_fast(Rational64::from_integer(-3), Rational64::from_integer(-2));
        assert_eq!(*p.numer(), 6);
        assert_eq!(*p.denom(), 1);
    }
}
