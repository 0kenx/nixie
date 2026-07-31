//! Fast rational number type for Simplex performance.
//!
//! [`FastRational`] uses a two-tier representation:
//! - **Small**: `i64/i64` for values that fit without overflow (>95% of simplex operations)
//! - **Big**: Heap-allocated `BigRational` as a fallback when overflow occurs
//!
//! This avoids heap allocation for the common case, providing 8-12% speedup
//! on LRA benchmarks compared to always using `BigRational`.
//!
//! ## Invariants
//!
//! For `Small { num, den }`:
//! - `den > 0` (sign is always on the numerator)
//! - `gcd(|num|, den) == 1` (always in lowest terms)
//!
//! ## Consistency
//!
//! - `Eq` and `Hash` are consistent: the same rational value always compares
//!   equal and hashes the same regardless of representation.
//! - `Ord` is a total order consistent with rational ordering.

#[allow(unused_imports)]
use crate::prelude::*;
use core::cmp::Ordering;
use core::fmt;
use core::hash::{Hash, Hasher};
use core::ops::{
    Add, AddAssign, Div, DivAssign, Mul, MulAssign, Neg, Rem, RemAssign, Sub, SubAssign,
};
use num_bigint::BigInt;
use num_integer::Integer;
use num_rational::BigRational;
use num_traits::{One, Signed, Zero};

/// A rational number that uses `i64/i64` for small values and falls back to `BigRational`.
///
/// Over 95% of Simplex operations stay in the small path, avoiding heap allocation.
#[derive(Clone, Debug)]
pub enum FastRational {
    /// Small representation: `num / den` where `den > 0` and `gcd(|num|, den) == 1`.
    Small {
        /// Numerator (can be negative, zero, or positive).
        num: i64,
        /// Denominator (always positive, always coprime with `|num|`).
        den: i64,
    },
    /// Big representation: heap-allocated arbitrary-precision rational.
    Big(Box<BigRational>),
}

// ---------------------------------------------------------------------------
// GCD helper
// ---------------------------------------------------------------------------

/// Binary GCD (Stein's algorithm) for `i64` values.
///
/// Inputs are taken as absolute values internally. Returns `gcd(|a|, |b|)`.
#[inline]
fn gcd_i64(a: i64, b: i64) -> i64 {
    // Take absolute values (saturating for i64::MIN)
    let mut a = a.unsigned_abs();
    let mut b = b.unsigned_abs();
    if a == 0 {
        return b as i64;
    }
    if b == 0 {
        return a as i64;
    }
    // Use Stein's binary GCD on unsigned values
    let shift = (a | b).trailing_zeros();
    a >>= a.trailing_zeros();
    loop {
        b >>= b.trailing_zeros();
        if a > b {
            core::mem::swap(&mut a, &mut b);
        }
        b -= a;
        if b == 0 {
            break;
        }
    }
    (a << shift) as i64
}

// ---------------------------------------------------------------------------
// Construction & normalization
// ---------------------------------------------------------------------------

impl FastRational {
    /// Create a new `Small` rational, normalizing sign and reducing to lowest terms.
    ///
    /// A non-zero `den` is a caller obligation. It is checked by a
    /// `debug_assert!`, so the check is compiled out in release builds; passing
    /// `den == 0` there is not a trap and not undefined behaviour, it simply
    /// yields a malformed `Small` whose denominator stays `0` and which poisons
    /// every later operation on the value.
    ///
    /// This is about the *denominator argument* of this constructor. It says
    /// nothing about dividing *by* zero: [`Div`] for `FastRational` rejects a
    /// zero divisor with a panic in every build profile.
    ///
    /// # Panics
    ///
    /// Panics in debug builds if `den == 0`.
    #[inline]
    pub fn new_small(num: i64, den: i64) -> Self {
        debug_assert!(den != 0, "FastRational: denominator must not be zero");
        if num == 0 {
            return FastRational::Small { num: 0, den: 1 };
        }
        let (n, d) = if den < 0 {
            // Negate both to ensure den > 0
            // Handle i64::MIN carefully
            match (num.checked_neg(), den.checked_neg()) {
                (Some(nn), Some(dd)) => (nn, dd),
                _ => {
                    // Overflow on negation -- promote to Big
                    let big = BigRational::new(BigInt::from(num), BigInt::from(den));
                    return FastRational::Big(Box::new(big));
                }
            }
        } else {
            (num, den)
        };
        // NB: pass `n` directly rather than `n.saturating_abs()`. `gcd_i64`
        // already takes the absolute value via `unsigned_abs()`, which
        // (unlike `i64::saturating_abs`) is exact for `i64::MIN` (2^63 fits
        // in `u64`). Pre-computing a saturated abs here would corrupt the
        // gcd for `n == i64::MIN` and silently produce a wrong reduced
        // fraction (or, for `new_small`, an unreduced `Small` that violates
        // the lowest-terms invariant).
        let g = gcd_i64(n, d);
        if g == 0 {
            return FastRational::Small { num: 0, den: 1 };
        }
        FastRational::Small {
            num: n / g,
            den: d / g,
        }
    }

    /// Create a `FastRational` from a `BigRational`, demoting to `Small` if it fits.
    pub fn from_big(br: BigRational) -> Self {
        // Try to fit into i64/i64
        let n_opt: Option<i64> = br.numer().try_into().ok();
        let d_opt: Option<i64> = br.denom().try_into().ok();
        match (n_opt, d_opt) {
            (Some(n), Some(d)) if d != 0 => FastRational::new_small(n, d),
            _ => FastRational::Big(Box::new(br)),
        }
    }

    /// Convert to `BigRational`.
    pub fn to_big_rational(&self) -> BigRational {
        match self {
            FastRational::Small { num, den } => {
                BigRational::new(BigInt::from(*num), BigInt::from(*den))
            }
            FastRational::Big(b) => (**b).clone(),
        }
    }

    /// Convert to `f64` (lossy).
    #[inline]
    pub fn to_f64(&self) -> f64 {
        match self {
            FastRational::Small { num, den } => *num as f64 / *den as f64,
            FastRational::Big(b) => {
                use num_traits::ToPrimitive;
                b.numer().to_f64().unwrap_or(f64::NAN) / b.denom().to_f64().unwrap_or(f64::NAN)
            }
        }
    }

    /// Return the reciprocal (1/self). Returns `None` if self is zero.
    pub fn recip(&self) -> Option<Self> {
        match self {
            FastRational::Small { num, den } => {
                if *num == 0 {
                    None
                } else {
                    Some(FastRational::new_small(*den, *num))
                }
            }
            FastRational::Big(b) => {
                if b.is_zero() {
                    None
                } else {
                    Some(FastRational::from_big(b.recip()))
                }
            }
        }
    }

    /// Compute the floor (greatest integer <= self).
    pub fn floor(&self) -> BigInt {
        match self {
            FastRational::Small { num, den } => {
                if *den == 1 {
                    BigInt::from(*num)
                } else {
                    let q = num.div_floor(den);
                    BigInt::from(q)
                }
            }
            FastRational::Big(b) => crate::rational::floor(b),
        }
    }

    /// Compute the ceiling (smallest integer >= self).
    pub fn ceil(&self) -> BigInt {
        match self {
            FastRational::Small { num, den } => {
                if *den == 1 {
                    BigInt::from(*num)
                } else {
                    // Use `Integer::div_ceil`, which computes ceil(n/d) via
                    // `div_rem` (truncating division + adjustment) rather
                    // than `(n + d - 1) / d`. The naive formula overflows
                    // `i64` whenever `num + den` exceeds `i64::MAX` (e.g.
                    // `Small { num: i64::MAX, den: 2 }`); `div_rem` never
                    // adds `num` and `den` together, so it cannot overflow
                    // for any `den > 0` (guaranteed by the `Small`
                    // invariant), mirroring `div_floor` used in `floor()`.
                    let q = num.div_ceil(den);
                    BigInt::from(q)
                }
            }
            FastRational::Big(b) => crate::rational::ceil(b),
        }
    }

    /// Return the absolute value.
    pub fn abs(&self) -> Self {
        match self {
            FastRational::Small { num, den } => {
                match num.checked_abs() {
                    Some(n) => FastRational::Small { num: n, den: *den },
                    None => {
                        // num == i64::MIN
                        let big = BigRational::new(BigInt::from(*num).abs(), BigInt::from(*den));
                        FastRational::from_big(big)
                    }
                }
            }
            FastRational::Big(b) => FastRational::from_big(b.abs()),
        }
    }

    /// Return the numerator as a `BigInt`.
    pub fn numer(&self) -> BigInt {
        match self {
            FastRational::Small { num, .. } => BigInt::from(*num),
            FastRational::Big(b) => b.numer().clone(),
        }
    }

    /// Return the denominator as a `BigInt`.
    pub fn denom(&self) -> BigInt {
        match self {
            FastRational::Small { den, .. } => BigInt::from(*den),
            FastRational::Big(b) => b.denom().clone(),
        }
    }

    /// Check if this rational is an integer (denominator == 1).
    #[inline]
    pub fn is_integer(&self) -> bool {
        match self {
            FastRational::Small { den, .. } => *den == 1,
            FastRational::Big(b) => b.is_integer(),
        }
    }

    /// Create a `FastRational` from a `BigRational` reference.
    pub fn from_big_ref(br: &BigRational) -> Self {
        let n_opt: Option<i64> = br.numer().try_into().ok();
        let d_opt: Option<i64> = br.denom().try_into().ok();
        match (n_opt, d_opt) {
            (Some(n), Some(d)) if d != 0 => FastRational::new_small(n, d),
            _ => FastRational::Big(Box::new(br.clone())),
        }
    }

    /// Create a `FastRational` representing an integer from a `BigInt`.
    pub fn from_bigint(bi: &BigInt) -> Self {
        let n_opt: Option<i64> = bi.try_into().ok();
        match n_opt {
            Some(n) => FastRational::Small { num: n, den: 1 },
            None => FastRational::Big(Box::new(BigRational::from_integer(bi.clone()))),
        }
    }
}

// ---------------------------------------------------------------------------
// Small-path arithmetic (inlined for performance)
// ---------------------------------------------------------------------------

/// Add two small rationals, falling back to Big on overflow.
#[inline]
fn add_small(a_num: i64, a_den: i64, b_num: i64, b_den: i64) -> FastRational {
    // a/b + c/d = (a*d + c*b) / (b*d) -- but check overflow at each step
    if let (Some(ad), Some(cb), Some(bd)) = (
        a_num.checked_mul(b_den),
        b_num.checked_mul(a_den),
        a_den.checked_mul(b_den),
    ) && let Some(num) = ad.checked_add(cb)
    {
        return FastRational::new_small(num, bd);
    }
    // Overflow: fall back to Big
    let a = BigRational::new(BigInt::from(a_num), BigInt::from(a_den));
    let b = BigRational::new(BigInt::from(b_num), BigInt::from(b_den));
    FastRational::from_big(a + b)
}

/// Subtract two small rationals, falling back to Big on overflow.
#[inline]
fn sub_small(a_num: i64, a_den: i64, b_num: i64, b_den: i64) -> FastRational {
    // a/b - c/d = (a*d - c*b) / (b*d)
    if let (Some(ad), Some(cb), Some(bd)) = (
        a_num.checked_mul(b_den),
        b_num.checked_mul(a_den),
        a_den.checked_mul(b_den),
    ) && let Some(num) = ad.checked_sub(cb)
    {
        return FastRational::new_small(num, bd);
    }
    let a = BigRational::new(BigInt::from(a_num), BigInt::from(a_den));
    let b = BigRational::new(BigInt::from(b_num), BigInt::from(b_den));
    FastRational::from_big(a - b)
}

/// Multiply two small rationals, falling back to Big on overflow.
#[inline]
fn mul_small(a_num: i64, a_den: i64, b_num: i64, b_den: i64) -> FastRational {
    // (a/b) * (c/d) = (a*c) / (b*d)
    // Cross-reduce first to minimize overflow chance.
    // NB: pass the numerators directly (not `.saturating_abs()`) -- see the
    // comment in `new_small` for why a pre-saturated abs corrupts the gcd
    // (and hence the product) when a numerator is `i64::MIN`.
    let g1 = gcd_i64(a_num, b_den);
    let g2 = gcd_i64(b_num, a_den);
    let an = if g1 != 0 { a_num / g1 } else { a_num };
    let bd = if g1 != 0 { b_den / g1 } else { b_den };
    let bn = if g2 != 0 { b_num / g2 } else { b_num };
    let ad = if g2 != 0 { a_den / g2 } else { a_den };

    if let (Some(num), Some(den)) = (an.checked_mul(bn), ad.checked_mul(bd)) {
        return FastRational::new_small(num, den);
    }
    let a = BigRational::new(BigInt::from(a_num), BigInt::from(a_den));
    let b = BigRational::new(BigInt::from(b_num), BigInt::from(b_den));
    FastRational::from_big(a * b)
}

/// Divide two small rationals, falling back to Big on overflow.
/// Returns `None` if divisor is zero.
#[inline]
fn div_small(a_num: i64, a_den: i64, b_num: i64, b_den: i64) -> Option<FastRational> {
    if b_num == 0 {
        return None;
    }
    // (a/b) / (c/d) = (a*d) / (b*c)
    // We need new_small to normalize the sign, so just pass through directly.
    // Use checked operations to detect overflow.
    if let (Some(num), Some(den)) = (a_num.checked_mul(b_den), a_den.checked_mul(b_num)) {
        Some(FastRational::new_small(num, den))
    } else {
        let a = BigRational::new(BigInt::from(a_num), BigInt::from(a_den));
        let b = BigRational::new(BigInt::from(b_num), BigInt::from(b_den));
        Some(FastRational::from_big(a / b))
    }
}

// ---------------------------------------------------------------------------
// Trait: From conversions
// ---------------------------------------------------------------------------

impl From<i64> for FastRational {
    #[inline]
    fn from(n: i64) -> Self {
        FastRational::Small { num: n, den: 1 }
    }
}

impl From<(i64, i64)> for FastRational {
    fn from((n, d): (i64, i64)) -> Self {
        if d == 0 {
            // Return zero as a safe default for zero denominator
            FastRational::Small { num: 0, den: 1 }
        } else {
            FastRational::new_small(n, d)
        }
    }
}

impl From<BigRational> for FastRational {
    fn from(br: BigRational) -> Self {
        FastRational::from_big(br)
    }
}

impl From<BigInt> for FastRational {
    fn from(bi: BigInt) -> Self {
        FastRational::from_bigint(&bi)
    }
}

impl From<&BigRational> for FastRational {
    fn from(br: &BigRational) -> Self {
        FastRational::from_big_ref(br)
    }
}

// ---------------------------------------------------------------------------
// Trait: Zero, One
// ---------------------------------------------------------------------------

impl Zero for FastRational {
    #[inline]
    fn zero() -> Self {
        FastRational::Small { num: 0, den: 1 }
    }

    #[inline]
    fn is_zero(&self) -> bool {
        match self {
            FastRational::Small { num, .. } => *num == 0,
            FastRational::Big(b) => b.is_zero(),
        }
    }
}

impl One for FastRational {
    #[inline]
    fn one() -> Self {
        FastRational::Small { num: 1, den: 1 }
    }

    #[inline]
    fn is_one(&self) -> bool {
        match self {
            FastRational::Small { num, den } => *num == 1 && *den == 1,
            FastRational::Big(b) => b.is_one(),
        }
    }
}

// ---------------------------------------------------------------------------
// Trait: Signed
// ---------------------------------------------------------------------------

impl Signed for FastRational {
    fn abs(&self) -> Self {
        FastRational::abs(self)
    }

    fn abs_sub(&self, other: &Self) -> Self {
        let diff = self - other;
        if diff.is_positive() {
            diff
        } else {
            FastRational::zero()
        }
    }

    fn signum(&self) -> Self {
        if self.is_zero() {
            FastRational::zero()
        } else if self.is_positive() {
            FastRational::one()
        } else {
            FastRational::Small { num: -1, den: 1 }
        }
    }

    fn is_positive(&self) -> bool {
        match self {
            FastRational::Small { num, .. } => *num > 0,
            FastRational::Big(b) => b.is_positive(),
        }
    }

    fn is_negative(&self) -> bool {
        match self {
            FastRational::Small { num, .. } => *num < 0,
            FastRational::Big(b) => b.is_negative(),
        }
    }
}

impl num_traits::Num for FastRational {
    type FromStrRadixErr = String;

    fn from_str_radix(str: &str, radix: u32) -> Result<Self, Self::FromStrRadixErr> {
        // Parse as BigRational, then try to demote
        if let Some((num_str, den_str)) = str.split_once('/') {
            let num = BigInt::from_str_radix(num_str.trim(), radix)
                .map_err(|e| format!("invalid numerator: {}", e))?;
            let den = BigInt::from_str_radix(den_str.trim(), radix)
                .map_err(|e| format!("invalid denominator: {}", e))?;
            if den.is_zero() {
                return Err("denominator is zero".to_string());
            }
            Ok(FastRational::from_big(BigRational::new(num, den)))
        } else {
            let num = BigInt::from_str_radix(str.trim(), radix)
                .map_err(|e| format!("invalid integer: {}", e))?;
            Ok(FastRational::from_bigint(&num))
        }
    }
}

// ---------------------------------------------------------------------------
// Trait: Neg
// ---------------------------------------------------------------------------

impl Neg for FastRational {
    type Output = FastRational;

    #[inline]
    fn neg(self) -> Self::Output {
        match self {
            FastRational::Small { num, den } => match num.checked_neg() {
                Some(n) => FastRational::Small { num: n, den },
                None => {
                    let big = BigRational::new(-BigInt::from(num), BigInt::from(den));
                    FastRational::Big(Box::new(big))
                }
            },
            FastRational::Big(b) => FastRational::from_big(-*b),
        }
    }
}

impl Neg for &FastRational {
    type Output = FastRational;

    #[inline]
    fn neg(self) -> Self::Output {
        match self {
            FastRational::Small { num, den } => match num.checked_neg() {
                Some(n) => FastRational::Small { num: n, den: *den },
                None => {
                    let big = BigRational::new(-BigInt::from(*num), BigInt::from(*den));
                    FastRational::Big(Box::new(big))
                }
            },
            FastRational::Big(b) => FastRational::from_big(-((**b).clone())),
        }
    }
}

// ---------------------------------------------------------------------------
// Trait: Add
// ---------------------------------------------------------------------------

impl Add for FastRational {
    type Output = FastRational;

    #[inline]
    fn add(self, rhs: FastRational) -> Self::Output {
        (&self).add(&rhs)
    }
}

impl Add<&FastRational> for FastRational {
    type Output = FastRational;

    #[inline]
    fn add(self, rhs: &FastRational) -> Self::Output {
        (&self).add(rhs)
    }
}

impl Add<FastRational> for &FastRational {
    type Output = FastRational;

    #[inline]
    fn add(self, rhs: FastRational) -> Self::Output {
        self.add(&rhs)
    }
}

impl Add<&FastRational> for &FastRational {
    type Output = FastRational;

    #[inline]
    fn add(self, rhs: &FastRational) -> Self::Output {
        match (self, rhs) {
            (
                FastRational::Small { num: an, den: ad },
                FastRational::Small { num: bn, den: bd },
            ) => add_small(*an, *ad, *bn, *bd),
            (a, b) => {
                let big_a = a.to_big_rational();
                let big_b = b.to_big_rational();
                FastRational::from_big(big_a + big_b)
            }
        }
    }
}

impl AddAssign for FastRational {
    #[inline]
    fn add_assign(&mut self, rhs: FastRational) {
        *self = (&*self) + &rhs;
    }
}

impl AddAssign<&FastRational> for FastRational {
    #[inline]
    fn add_assign(&mut self, rhs: &FastRational) {
        *self = (&*self) + rhs;
    }
}

// ---------------------------------------------------------------------------
// Trait: Sub
// ---------------------------------------------------------------------------

impl Sub for FastRational {
    type Output = FastRational;

    #[inline]
    fn sub(self, rhs: FastRational) -> Self::Output {
        (&self).sub(&rhs)
    }
}

impl Sub<&FastRational> for FastRational {
    type Output = FastRational;

    #[inline]
    fn sub(self, rhs: &FastRational) -> Self::Output {
        (&self).sub(rhs)
    }
}

impl Sub<FastRational> for &FastRational {
    type Output = FastRational;

    #[inline]
    fn sub(self, rhs: FastRational) -> Self::Output {
        self.sub(&rhs)
    }
}

impl Sub<&FastRational> for &FastRational {
    type Output = FastRational;

    #[inline]
    fn sub(self, rhs: &FastRational) -> Self::Output {
        match (self, rhs) {
            (
                FastRational::Small { num: an, den: ad },
                FastRational::Small { num: bn, den: bd },
            ) => sub_small(*an, *ad, *bn, *bd),
            (a, b) => {
                let big_a = a.to_big_rational();
                let big_b = b.to_big_rational();
                FastRational::from_big(big_a - big_b)
            }
        }
    }
}

impl SubAssign for FastRational {
    #[inline]
    fn sub_assign(&mut self, rhs: FastRational) {
        *self = (&*self) - &rhs;
    }
}

impl SubAssign<&FastRational> for FastRational {
    #[inline]
    fn sub_assign(&mut self, rhs: &FastRational) {
        *self = (&*self) - rhs;
    }
}

// ---------------------------------------------------------------------------
// Trait: Mul
// ---------------------------------------------------------------------------

impl Mul for FastRational {
    type Output = FastRational;

    #[inline]
    fn mul(self, rhs: FastRational) -> Self::Output {
        (&self).mul(&rhs)
    }
}

impl Mul<&FastRational> for FastRational {
    type Output = FastRational;

    #[inline]
    fn mul(self, rhs: &FastRational) -> Self::Output {
        (&self).mul(rhs)
    }
}

impl Mul<FastRational> for &FastRational {
    type Output = FastRational;

    #[inline]
    fn mul(self, rhs: FastRational) -> Self::Output {
        self.mul(&rhs)
    }
}

impl Mul<&FastRational> for &FastRational {
    type Output = FastRational;

    #[inline]
    fn mul(self, rhs: &FastRational) -> Self::Output {
        match (self, rhs) {
            (
                FastRational::Small { num: an, den: ad },
                FastRational::Small { num: bn, den: bd },
            ) => mul_small(*an, *ad, *bn, *bd),
            (a, b) => {
                let big_a = a.to_big_rational();
                let big_b = b.to_big_rational();
                FastRational::from_big(big_a * big_b)
            }
        }
    }
}

impl MulAssign for FastRational {
    #[inline]
    fn mul_assign(&mut self, rhs: FastRational) {
        *self = (&*self) * &rhs;
    }
}

impl MulAssign<&FastRational> for FastRational {
    #[inline]
    fn mul_assign(&mut self, rhs: &FastRational) {
        *self = (&*self) * rhs;
    }
}

// ---------------------------------------------------------------------------
// Trait: Div
// ---------------------------------------------------------------------------

impl Div for FastRational {
    type Output = FastRational;

    /// Divide two `FastRational` values.
    ///
    /// # Panics
    ///
    /// Panics if the divisor is zero. Unlike the `den == 0` check in
    /// [`FastRational::new_small`], this one is unconditional: it holds in
    /// release builds too.
    #[inline]
    fn div(self, rhs: FastRational) -> Self::Output {
        (&self).div(&rhs)
    }
}

impl Div<&FastRational> for FastRational {
    type Output = FastRational;

    #[inline]
    fn div(self, rhs: &FastRational) -> Self::Output {
        (&self).div(rhs)
    }
}

impl Div<FastRational> for &FastRational {
    type Output = FastRational;

    #[inline]
    fn div(self, rhs: FastRational) -> Self::Output {
        self.div(&rhs)
    }
}

impl Div<&FastRational> for &FastRational {
    type Output = FastRational;

    #[inline]
    fn div(self, rhs: &FastRational) -> Self::Output {
        match (self, rhs) {
            (
                FastRational::Small { num: an, den: ad },
                FastRational::Small { num: bn, den: bd },
            ) => match div_small(*an, *ad, *bn, *bd) {
                Some(r) => r,
                // `debug_assert!` is compiled out in release builds, which
                // previously let this fall through to `FastRational::zero()`
                // — a silently wrong result rather than the documented
                // panic. Division by zero must fail loudly in both profiles,
                // matching `i64`'s own division-by-zero behavior.
                None => panic!("FastRational: division by zero"),
            },
            (a, b) => {
                if b.is_zero() {
                    panic!("FastRational: division by zero");
                }
                let big_a = a.to_big_rational();
                let big_b = b.to_big_rational();
                FastRational::from_big(big_a / big_b)
            }
        }
    }
}

impl DivAssign for FastRational {
    #[inline]
    fn div_assign(&mut self, rhs: FastRational) {
        *self = (&*self) / &rhs;
    }
}

impl DivAssign<&FastRational> for FastRational {
    #[inline]
    fn div_assign(&mut self, rhs: &FastRational) {
        *self = (&*self) / rhs;
    }
}

// ---------------------------------------------------------------------------
// Trait: Rem (required by Num)
// ---------------------------------------------------------------------------

impl Rem for FastRational {
    type Output = FastRational;

    /// Remainder for rationals: `a % b = a - b * floor(a/b)`.
    ///
    /// For non-zero `b`, this returns a value in `[0, |b|)`.
    #[inline]
    fn rem(self, rhs: FastRational) -> Self::Output {
        (&self).rem(&rhs)
    }
}

impl Rem<&FastRational> for &FastRational {
    type Output = FastRational;

    #[inline]
    fn rem(self, rhs: &FastRational) -> Self::Output {
        if rhs.is_zero() {
            return FastRational::zero();
        }
        let quotient = self / rhs;
        let floor_q = FastRational::from_integer(quotient.floor());
        self - &(rhs * &floor_q)
    }
}

impl RemAssign for FastRational {
    #[inline]
    fn rem_assign(&mut self, rhs: FastRational) {
        *self = (&*self).rem(&rhs);
    }
}

// ---------------------------------------------------------------------------
// Trait: PartialEq, Eq
// ---------------------------------------------------------------------------

impl PartialEq for FastRational {
    fn eq(&self, other: &Self) -> bool {
        match (self, other) {
            (
                FastRational::Small { num: an, den: ad },
                FastRational::Small { num: bn, den: bd },
            ) => {
                // Both normalized: direct comparison
                an == bn && ad == bd
            }
            (a, b) => {
                // Cross-representation comparison
                a.to_big_rational() == b.to_big_rational()
            }
        }
    }
}

impl Eq for FastRational {}

// ---------------------------------------------------------------------------
// Trait: PartialOrd, Ord
// ---------------------------------------------------------------------------

impl PartialOrd for FastRational {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

impl Ord for FastRational {
    fn cmp(&self, other: &Self) -> Ordering {
        match (self, other) {
            (
                FastRational::Small { num: an, den: ad },
                FastRational::Small { num: bn, den: bd },
            ) => {
                // Compare a_num/a_den vs b_num/b_den
                // = a_num * b_den vs b_num * a_den (both dens positive)
                // Use checked_mul to avoid overflow
                if let (Some(lhs), Some(rhs)) = (an.checked_mul(*bd), bn.checked_mul(*ad)) {
                    return lhs.cmp(&rhs);
                }
                // Overflow: fall back to BigRational comparison
                let big_a = BigRational::new(BigInt::from(*an), BigInt::from(*ad));
                let big_b = BigRational::new(BigInt::from(*bn), BigInt::from(*bd));
                big_a.cmp(&big_b)
            }
            (a, b) => {
                let big_a = a.to_big_rational();
                let big_b = b.to_big_rational();
                big_a.cmp(&big_b)
            }
        }
    }
}

// ---------------------------------------------------------------------------
// Trait: Hash (consistent with Eq)
// ---------------------------------------------------------------------------

impl Hash for FastRational {
    fn hash<H: Hasher>(&self, state: &mut H) {
        // Both Small and Big must hash the same value for equal rationals.
        // Since Small is always in lowest terms with den > 0, we can hash (num, den) directly
        // for Small. For Big, we normalize and hash the same way.
        match self {
            FastRational::Small { num, den } => {
                num.hash(state);
                den.hash(state);
            }
            FastRational::Big(b) => {
                // Normalize the BigRational and try to fit in i64
                let reduced = b.reduced();
                let n_opt: Option<i64> = reduced.numer().try_into().ok();
                let d_opt: Option<i64> = reduced.denom().try_into().ok();
                match (n_opt, d_opt) {
                    (Some(n), Some(d)) if d > 0 => {
                        n.hash(state);
                        d.hash(state);
                    }
                    (Some(n), Some(d)) if d < 0 => {
                        // Normalize sign
                        (-n).hash(state);
                        (-d).hash(state);
                    }
                    _ => {
                        // Can't fit in i64; hash the big values directly
                        // Ensure den > 0 normalization
                        let (n, d) = if reduced.denom().is_negative() {
                            (-reduced.numer(), -reduced.denom())
                        } else {
                            (reduced.numer().clone(), reduced.denom().clone())
                        };
                        n.hash(state);
                        d.hash(state);
                    }
                }
            }
        }
    }
}

// ---------------------------------------------------------------------------
// Trait: Display
// ---------------------------------------------------------------------------

impl fmt::Display for FastRational {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            FastRational::Small { num, den } => {
                if *den == 1 {
                    write!(f, "{}", num)
                } else {
                    write!(f, "{}/{}", num, den)
                }
            }
            FastRational::Big(b) => write!(f, "{}", b),
        }
    }
}

// ---------------------------------------------------------------------------
// Convenience: from_integer
// ---------------------------------------------------------------------------

impl FastRational {
    /// Create a `FastRational` from an integer.
    #[inline]
    pub fn from_integer(n: BigInt) -> Self {
        FastRational::from_bigint(&n)
    }
}

// ---------------------------------------------------------------------------
// Max / Min (used by simplex for clamping)
// ---------------------------------------------------------------------------

impl FastRational {
    /// Returns the larger of self and other.
    #[inline]
    pub fn max(self, other: Self) -> Self {
        if self >= other { self } else { other }
    }

    /// Returns the smaller of self and other.
    #[inline]
    pub fn min(self, other: Self) -> Self {
        if self <= other { self } else { other }
    }
}

// ---------------------------------------------------------------------------
// Tests
// ---------------------------------------------------------------------------

#[cfg(test)]
mod tests {
    use super::*;
    use std::collections::hash_map::DefaultHasher;

    fn small(n: i64, d: i64) -> FastRational {
        FastRational::new_small(n, d)
    }

    fn fr(n: i64) -> FastRational {
        FastRational::from(n)
    }

    fn hash_of(val: &FastRational) -> u64 {
        let mut h = DefaultHasher::new();
        val.hash(&mut h);
        h.finish()
    }

    // -- Construction and normalization --

    #[test]
    fn test_new_small_normalization() {
        // 2/4 -> 1/2
        let r = small(2, 4);
        assert_eq!(r, small(1, 2));
    }

    #[test]
    fn test_new_small_negative_den() {
        // 3/(-5) -> -3/5
        let r = small(3, -5);
        assert_eq!(r, small(-3, 5));
    }

    #[test]
    fn test_new_small_zero() {
        let r = small(0, 42);
        assert_eq!(r, FastRational::zero());
    }

    #[test]
    fn test_from_i64() {
        let r = FastRational::from(7i64);
        assert_eq!(r, small(7, 1));
    }

    #[test]
    fn test_from_tuple() {
        let r = FastRational::from((6i64, 4i64));
        assert_eq!(r, small(3, 2));
    }

    #[test]
    fn test_from_bigrational() {
        let br = BigRational::new(BigInt::from(10), BigInt::from(4));
        let r = FastRational::from(br);
        assert_eq!(r, small(5, 2));
    }

    // -- Arithmetic --

    #[test]
    fn test_add() {
        // 1/2 + 1/3 = 5/6
        let a = small(1, 2);
        let b = small(1, 3);
        assert_eq!(&a + &b, small(5, 6));
    }

    #[test]
    fn test_sub() {
        // 3/4 - 1/4 = 1/2
        let a = small(3, 4);
        let b = small(1, 4);
        assert_eq!(&a - &b, small(1, 2));
    }

    #[test]
    fn test_mul() {
        // 2/3 * 3/4 = 1/2
        let a = small(2, 3);
        let b = small(3, 4);
        assert_eq!(&a * &b, small(1, 2));
    }

    #[test]
    fn test_div() {
        // (2/3) / (4/5) = 10/12 = 5/6
        let a = small(2, 3);
        let b = small(4, 5);
        assert_eq!(&a / &b, small(5, 6));
    }

    #[test]
    fn test_neg() {
        let r = small(3, 5);
        assert_eq!(-r, small(-3, 5));
    }

    #[test]
    fn test_add_assign() {
        let mut a = small(1, 2);
        a += small(1, 3);
        assert_eq!(a, small(5, 6));
    }

    #[test]
    fn test_mul_assign() {
        let mut a = small(2, 3);
        a *= small(3, 4);
        assert_eq!(a, small(1, 2));
    }

    // -- Overflow -> Big fallback --

    #[test]
    fn test_overflow_to_big() {
        let big_val = i64::MAX;
        let a = fr(big_val);
        let b = fr(big_val);
        let result = &a + &b;
        // Should not panic, should promote to Big
        let expected = BigRational::from_integer(BigInt::from(big_val))
            + BigRational::from_integer(BigInt::from(big_val));
        assert_eq!(result.to_big_rational(), expected);
    }

    // -- Comparison --

    #[test]
    fn test_ord() {
        assert!(small(1, 3) < small(1, 2));
        assert!(small(-1, 2) < small(1, 2));
        assert!(small(0, 1) == FastRational::zero());
    }

    #[test]
    fn test_eq_cross_representation() {
        // Small(1/2) vs Big(1/2) should be equal
        let s = small(1, 2);
        let b = FastRational::Big(Box::new(BigRational::new(BigInt::from(1), BigInt::from(2))));
        assert_eq!(s, b);
    }

    // -- Hash consistency --

    #[test]
    fn test_hash_consistency() {
        let s = small(1, 2);
        let b = FastRational::Big(Box::new(BigRational::new(BigInt::from(1), BigInt::from(2))));
        assert_eq!(hash_of(&s), hash_of(&b));
    }

    // -- Signed, Zero, One --

    #[test]
    fn test_zero_one() {
        assert!(FastRational::zero().is_zero());
        assert!(FastRational::one().is_one());
        assert!(!FastRational::zero().is_one());
        assert!(!FastRational::one().is_zero());
    }

    #[test]
    fn test_signed() {
        assert!(small(3, 5).is_positive());
        assert!(small(-3, 5).is_negative());
        assert!(!FastRational::zero().is_positive());
        assert!(!FastRational::zero().is_negative());
    }

    #[test]
    fn test_abs() {
        assert_eq!(small(-3, 5).abs(), small(3, 5));
        assert_eq!(small(3, 5).abs(), small(3, 5));
    }

    // -- Misc methods --

    #[test]
    fn test_recip() {
        assert_eq!(small(3, 5).recip(), Some(small(5, 3)));
        assert_eq!(FastRational::zero().recip(), None);
    }

    #[test]
    fn test_floor_ceil() {
        // 7/3 = 2.333...
        let r = small(7, 3);
        assert_eq!(r.floor(), BigInt::from(2));
        assert_eq!(r.ceil(), BigInt::from(3));

        // -7/3 = -2.333...
        let r = small(-7, 3);
        assert_eq!(r.floor(), BigInt::from(-3));
        assert_eq!(r.ceil(), BigInt::from(-2));
    }

    #[test]
    fn test_ceil_i64_max_boundary_no_overflow() {
        // Regression test for MATH-6: the naive `(num + den - 1) / den`
        // formula overflows i64 when num is close to i64::MAX. `new_small`
        // reduces to lowest terms via gcd, so use a numerator/denominator
        // pair that stays in reduced form near i64::MAX (i64::MAX is odd,
        // so gcd(i64::MAX, 2) == 1 and the value survives reduction as
        // exactly `Small { num: i64::MAX, den: 2 }`, the case cited by the
        // finding).
        let r = FastRational::new_small(i64::MAX, 2);
        let big = r.to_big_rational();
        assert_eq!(r.ceil(), crate::rational::ceil(&big));
        assert_eq!(r.floor(), crate::rational::floor(&big));
        // Sanity: ceil == floor + 1 since i64::MAX/2 is non-integer.
        assert_eq!(r.ceil(), r.floor() + BigInt::from(1));
    }

    #[test]
    fn test_ceil_i64_min_boundary() {
        // Negative boundary: i64::MIN / 2 is exact (no rounding needed),
        // must not overflow or panic.
        let r = FastRational::new_small(i64::MIN, 2);
        assert_eq!(r.ceil(), BigInt::from(i64::MIN / 2));
        assert_eq!(r.floor(), BigInt::from(i64::MIN / 2));
    }

    #[test]
    fn test_ceil_large_positive_non_integer() {
        // Large odd numerator over a larger denominator, near the i64
        // boundary, to exercise the div_ceil path without triggering the
        // `den == 1` fast path.
        let r = FastRational::new_small(i64::MAX - 1, 4);
        let ceil = r.ceil();
        let floor = r.floor();
        // ceil - floor is 0 (exact) or 1 (fractional); verify consistency
        // via BigRational cross-check rather than duplicating arithmetic.
        let big = r.to_big_rational();
        let expected_floor = crate::rational::floor(&big);
        let expected_ceil = crate::rational::ceil(&big);
        assert_eq!(floor, expected_floor);
        assert_eq!(ceil, expected_ceil);
    }

    #[test]
    fn test_to_f64() {
        let r = small(1, 2);
        assert!((r.to_f64() - 0.5).abs() < 1e-10);
    }

    #[test]
    fn test_to_big_rational_roundtrip() {
        let r = small(7, 13);
        let big = r.to_big_rational();
        let back = FastRational::from_big(big);
        assert_eq!(r, back);
    }

    #[test]
    fn test_numer_denom() {
        let r = small(3, 7);
        assert_eq!(r.numer(), BigInt::from(3));
        assert_eq!(r.denom(), BigInt::from(7));
    }

    #[test]
    fn test_is_integer() {
        assert!(fr(5).is_integer());
        assert!(!small(5, 3).is_integer());
    }

    #[test]
    fn test_display() {
        assert_eq!(format!("{}", fr(5)), "5");
        assert_eq!(format!("{}", small(3, 7)), "3/7");
        assert_eq!(format!("{}", small(-1, 2)), "-1/2");
    }

    #[test]
    fn test_max_min() {
        let a = small(1, 3);
        let b = small(1, 2);
        assert_eq!(a.clone().max(b.clone()), b);
        assert_eq!(a.clone().min(b.clone()), a);
    }

    // -- Regression tests: i64::MIN must never be pre-corrupted by
    //    `saturating_abs` before reaching `gcd_i64` (which already handles
    //    it exactly via `unsigned_abs`). See audit finding on
    //    `mul_small`/`new_small`.

    #[test]
    fn test_new_small_i64_min_odd_denominator_stays_irreducible() {
        // gcd(2^63, 7) == 1: i64::MIN/7 is already in lowest terms and must
        // be returned unchanged, not silently reduced to an integer.
        let r = FastRational::new_small(i64::MIN, 7);
        assert_eq!(
            r,
            FastRational::Small {
                num: i64::MIN,
                den: 7
            }
        );
        // Round-trip through BigRational must agree exactly.
        let expected = BigRational::new(BigInt::from(i64::MIN), BigInt::from(7));
        assert_eq!(r.to_big_rational(), expected);
    }

    #[test]
    fn test_new_small_i64_min_even_denominator_reduces_correctly() {
        // gcd(2^63, 2) == 2: must reduce to (MIN/2)/1, preserving the
        // Small invariant `gcd(|num|, den) == 1`.
        let r = FastRational::new_small(i64::MIN, 2);
        assert_eq!(
            r,
            FastRational::Small {
                num: i64::MIN / 2,
                den: 1
            }
        );
        let expected = BigRational::new(BigInt::from(i64::MIN), BigInt::from(2));
        assert_eq!(r.to_big_rational(), expected);
    }

    #[test]
    fn test_mul_small_i64_min_by_small_fraction() {
        // Regression for the audit finding: mul_small(MIN, 1, 1, 7) used to
        // return -1317624576693539401 (an *integer*, silently wrong by a
        // factor of 1/7) because `saturating_abs(i64::MIN) == i64::MAX`
        // corrupted the cross-reduction gcd against a denominator of 7
        // (which happens to divide i64::MAX exactly).
        let a = FastRational::Small {
            num: i64::MIN,
            den: 1,
        };
        let b = FastRational::Small { num: 1, den: 7 };
        let result = &a * &b;

        let expected = BigRational::new(BigInt::from(i64::MIN), BigInt::from(7));
        assert_eq!(
            result.to_big_rational(),
            expected,
            "MIN * (1/7) must equal MIN/7 exactly, not truncate to an integer"
        );
        // The result must not be integral (MIN is not a multiple of 7).
        assert!(!result.is_integer());
    }

    #[test]
    fn test_mul_small_i64_min_eq_hash_invariant_preserved() {
        // The lowest-terms invariant must hold after multiplication
        // involving i64::MIN, so Eq/Hash stay consistent with equal values
        // produced via a different path (Big).
        let a = FastRational::Small {
            num: i64::MIN,
            den: 1,
        };
        let b = FastRational::Small { num: 1, den: 7 };
        let small_result = &a * &b;

        let big_a = BigRational::from_integer(BigInt::from(i64::MIN));
        let big_b = BigRational::new(BigInt::one(), BigInt::from(7));
        let big_result = FastRational::from_big(big_a * big_b);

        assert_eq!(small_result, big_result);
        assert_eq!(hash_of(&small_result), hash_of(&big_result));
    }

    #[test]
    fn test_from_str_radix() {
        use num_traits::Num;
        let r = FastRational::from_str_radix("3/7", 10);
        assert!(r.is_ok());
        assert_eq!(r.ok(), Some(small(3, 7)));

        let r2 = FastRational::from_str_radix("42", 10);
        assert!(r2.is_ok());
        assert_eq!(r2.ok(), Some(fr(42)));
    }
}
