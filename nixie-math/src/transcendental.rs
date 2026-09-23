//! Rigorous interval enclosures for real transcendental functions
//! (`exp`, `log`, `sin`, `cos`, `atan`, `sqrt`).
//!
//! This is the numerical foundation of the δ-satisfiability engine for the
//! transcendental theory (see `nixie-theories/src/trans/`): every value it
//! hands back is a mathematically guaranteed enclosure of the true value over
//! the queried interval, rounded outward to `f64` bounds.  The engine that
//! consumes it prunes search boxes with these intervals, so any unsoundness
//! here would be a wrong `unsat` downstream — the worst failure mode an SMT
//! solver has.  Hence the design rules:
//!
//! * **No host libm on the proof path.**  `f64::exp`/`sin`/… are not
//!   guaranteed correctly rounded, so their values are never used as bounds.
//!   (`f64::sqrt` *is* IEEE-754 correctly rounded, so `sqrt` uses it and then
//!   widens by one ulp in each direction — the true square root lies within
//!   half an ulp of the rounded one.)
//! * **Exact rational series arithmetic.**  Each enclosure range-reduces the
//!   (dyadic, hence exactly rational) `f64` argument and sums Taylor /
//!   atanh / atan series **exactly in `BigRational`**, adding an explicit
//!   rigorous tail bound.  There is no intermediate rounding to account for:
//!   the partial sum is exact, the tail bound is an exact rational known to
//!   dominate the true remainder, and only the final bracket is rounded —
//!   outward — to `f64`.
//! * **Totalized semantics, documented per function.**  SMT demands total
//!   functions.  `log(x)` for `x ≤ 0` is `−∞`; `sqrt(x)` for `x < 0` is `0`
//!   (the dReal-style totalizations, see `docs/TRANS.md`).  These choices only
//!   ever make constraints *harder* to satisfy with out-of-domain arguments
//!   and are applied consistently in evaluation and pruning.
//!
//! The public surface is the [`DI`] interval type plus the transcendental
//! interval functions; the series machinery is private.
//!
//! # Precision
//!
//! Constants (`ln 2`, `π`) are kept as rational brackets accurate to better
//! than `2^-190`; series run until the rigorous tail bound is below `2^-196`,
//! comfortably below what an `f64` bound can express.  For `sin`/`cos`, range
//! reduction is capped at `|x| ≤ 2^120` (beyond that the enclosure degrades
//! to the full range `[-1, 1]`, which is always sound).  `exp` saturates to
//! ±infinity outside `±710`.
//!
//! # Performance
//!
//! A point enclosure costs a few dozen exact-rational operations on numbers
//! of a few thousand bits (tens of microseconds).  Under `std`, every
//! `(function, f64)` point enclosure is memoized in a thread-local cache,
//! which the ICP engine hits heavily (it re-evaluates the same endpoints
//! across propagation rounds).

use core::cmp::min as imin;
use num_bigint::BigInt;
use num_integer::Integer;
use num_rational::BigRational;
use num_traits::One;
use num_traits::{Signed, ToPrimitive, Zero};

// =====================================================================
// f64 outward rounding
// =====================================================================

/// `min` for `f64` (NaN-free by contract in this module).
fn fmin(a: f64, b: f64) -> f64 {
    if a < b { a } else { b }
}

/// `max` for `f64` (NaN-free by contract in this module).
fn fmax(a: f64, b: f64) -> f64 {
    if a > b { a } else { b }
}

/// Next representable `f64` toward +∞ (`x < y` unless `x` is +∞; NaN stays
/// NaN, which callers must never feed here).
#[must_use]
pub fn f64_next_up(x: f64) -> f64 {
    if x.is_nan() {
        return x;
    }
    if x == f64::NEG_INFINITY {
        return f64::MIN;
    }
    if x == f64::INFINITY {
        return x;
    }
    let bits = x.to_bits();
    if x == 0.0 {
        return f64::from_bits(1);
    }
    if x > 0.0 {
        f64::from_bits(bits + 1)
    } else {
        f64::from_bits(bits - 1)
    }
}

/// Next representable `f64` toward −∞ (mirror of [`f64_next_up`]).
#[must_use]
pub fn f64_next_down(x: f64) -> f64 {
    if x.is_nan() {
        return x;
    }
    if x == f64::INFINITY {
        return f64::MAX;
    }
    if x == f64::NEG_INFINITY {
        return x;
    }
    let bits = x.to_bits();
    if x == 0.0 {
        return -f64::from_bits(1);
    }
    if x > 0.0 {
        f64::from_bits(bits - 1)
    } else {
        f64::from_bits(bits + 1)
    }
}

// =====================================================================
// Directed rational → f64 conversion (the single rounding point)
// =====================================================================

/// Convert the nonnegative rational `num/den` (`den > 0`) to `f64`, rounded
/// in the direction `up` selects.  Saturates to `f64::MAX` / the smallest
/// positive subnormal at the extremes.
///
/// Method (one uniform normalizing loop, no case-specific exponent algebra
/// to get wrong): write `value = q·2^-s + frac` with integer `q`, `0 ≤
/// frac < 2^-s` (the `s ≥ 0` / `s < 0` split only affects how `q` and the
/// remainder are extracted).  Shift `q` down to at most 53 bits, adjusting
/// `s` in lockstep (`q/2 · 2^-(s-1) = q·2^-s`), then scale exactly by a
/// power of two.  "Exact" records whether any information was dropped
/// (remainder, dropped low bits), which is exactly when the ceiling must
/// round one ulp up.
fn rat_nonneg_to_f64_dir(num: &BigInt, den: &BigInt, up: bool) -> f64 {
    debug_assert!(num.sign() != num_bigint::Sign::Minus && den.is_positive());
    if num.is_zero() {
        return 0.0;
    }
    // value ∈ [2^(e-1), 2^(e+1)) with e = bits(num) − bits(den).
    let e = num.bits() as i64 - den.bits() as i64;
    if e > 1025 {
        return if up { f64::INFINITY } else { f64::MAX };
    }
    if e < -1130 {
        // value < 2^-1130·2 < the smallest subnormal's half-ulp.
        return if up { f64::from_bits(1) } else { 0.0 };
    }
    // Extract q = floor(value·2^s) and the exactness of the extraction.
    let mut s = 53 - e;
    let (mut q, r) = if s >= 0 {
        let ns = num << s as u64;
        let q = &ns / den;
        let r = &ns % den;
        (q, r)
    } else {
        let ds = den << (-s) as u64;
        let q = num / &ds;
        let r = num % &ds;
        (q, r)
    };
    // Normalize q to ≤ 53 bits, tracking dropped low bits.
    let mut dropped = false;
    while q.bits() > 53 {
        dropped |= !(&q & BigInt::one()).is_zero();
        q >>= 1;
        s -= 1;
    }
    let exact = r.is_zero() && !dropped;
    let v = q
        .to_f64()
        .unwrap_or(if up { f64::INFINITY } else { f64::MAX }); // exact (≤53 bits)
    let scaled = mul_pow2(v, -s);
    if up {
        if scaled.is_infinite() {
            f64::INFINITY
        } else if scaled == 0.0 {
            f64::from_bits(1)
        } else if exact {
            scaled
        } else {
            f64_next_up(scaled)
        }
    } else if scaled.is_infinite() {
        f64::MAX
    } else {
        scaled
    }
}

/// `v · 2^k`, exact when finite (power-of-two scaling), saturating to ±∞.
fn mul_pow2(v: f64, k: i64) -> f64 {
    if v == 0.0 || !v.is_finite() || k == 0 {
        return v;
    }
    // `powi` on base 2 is exact for every representable result (repeated
    // squaring stays on the power-of-two lattice), so the only inexactness
    // is the final over/underflow the saturate guards at the call sites own.
    let mut result = v;
    let mut remaining = k;
    while remaining > 0 {
        let step = imin(remaining, 1000);
        result *= 2.0f64.powi(step as i32);
        remaining -= step;
    }
    while remaining < 0 {
        let step = imin(-remaining, 1000);
        result /= 2.0f64.powi(step as i32);
        remaining += step;
    }
    result
}

/// Directed rational → f64 (any sign; `den > 0`).
fn rat_to_f64(v: &BigRational, down: bool) -> f64 {
    let n = v.numer();
    let d = v.denom();
    if n.sign() == num_bigint::Sign::Minus {
        let mag = -n;
        if down {
            -rat_nonneg_to_f64_dir(&mag, d, true)
        } else {
            -rat_nonneg_to_f64_dir(&mag, d, false)
        }
    } else if down {
        rat_nonneg_to_f64_dir(n, d, false)
    } else {
        rat_nonneg_to_f64_dir(n, d, true)
    }
}

/// The exact rational value of a finite `f64` (dyadic).
fn f64_to_rational(x: f64) -> BigRational {
    debug_assert!(x.is_finite());
    if x == 0.0 {
        return BigRational::zero();
    }
    let bits = x.to_bits();
    let neg = bits >> 63 == 1;
    let abs_bits = bits & !(1_u64 << 63);
    let biased = ((abs_bits >> 52) & 0x7ff) as i64;
    let mantissa = if biased == 0 {
        abs_bits & ((1_u64 << 52) - 1)
    } else {
        (abs_bits & ((1_u64 << 52) - 1)) | (1_u64 << 52)
    };
    let exp = if biased == 0 {
        -1074
    } else {
        biased - 1023 - 52
    };
    let m = BigInt::from(mantissa);
    let v = if exp >= 0 {
        BigRational::from(m << exp as u64)
    } else {
        BigRational::new(m, BigInt::one() << (-exp) as u64)
    };
    if neg { -v } else { v }
}

// =====================================================================
// Rigorous constants (ln 2, π) as rational brackets
// =====================================================================

/// A rational bracket `[lo, hi]` with `lo ≤ true ≤ hi`.
#[derive(Clone, Debug)]
struct RatBracket {
    lo: BigRational,
    hi: BigRational,
}

impl RatBracket {
    fn to_f64s(&self) -> (f64, f64) {
        (rat_to_f64(&self.lo, true), rat_to_f64(&self.hi, false))
    }
}

/// Shared constants, each bracketed to better than `2^-190`.
struct TransConsts {
    /// `ln 2`
    ln2: RatBracket,
    /// `π`
    pi: RatBracket,
    /// `π/2`
    pi2: RatBracket,
}

/// `2^-190` as a rational (the convergence target).
/// `v * n` for small `n` (avoids the `Ratio * {integer}` impl gap on
/// no_std builds).
fn rmul(v: &BigRational, n: u64) -> BigRational {
    v * BigInt::from(n)
}

/// `v / n` for small `n`.
fn rdiv(v: &BigRational, n: u64) -> BigRational {
    v / BigInt::from(n)
}

fn eps190() -> BigRational {
    BigRational::new(BigInt::one(), BigInt::one() << 190)
}

impl TransConsts {
    /// * `ln 2 = 2·atanh(1/3)`: positive decreasing terms, geometric
    ///   remainder `R ≤ t^{2N+3}/((2N+3)(1−t²)) ≤ t^{2N+3}·9/(8(2N+3))`.
    /// * `π = 16·atan(1/5) − 4·atan(1/239)` (Machin), each `atan` alternating
    ///   with decreasing terms, so partial ± one omitted term brackets it.
    fn compute() -> Self {
        let third = BigRational::new(BigInt::from(1), BigInt::from(3));
        // ln2/2 = atanh(1/3) = Σ_{n≥0} t^(2n+1)/(2n+1), t = 1/3
        let mut sum = BigRational::zero();
        let mut t_pow = third.clone(); // t^(2n+1)
        let t2 = &third * &third; // 1/9
        let mut n: u64 = 0;
        loop {
            sum += &t_pow / BigInt::from(2 * n + 1);
            t_pow *= &t2;
            n += 1;
            // remainder ≤ t^(2n+1)·9/(8·(2n+1))
            let rem = &t_pow * BigInt::from(9) / (BigInt::from(8) * BigInt::from(2 * n + 1));
            if rem < eps190() || n > 400 {
                sum += rem; // hi side
                break;
            }
        }
        let ln2 = RatBracket {
            lo: rmul(&sum, 2),
            hi: rmul(&sum, 2), // sum already carries the remainder on the hi read
        };
        // Recompute cleanly: low side without remainder.
        let mut sum_lo = BigRational::zero();
        let mut t_pow = third.clone();
        let mut n: u64 = 0;
        loop {
            sum_lo += &t_pow / BigInt::from(2 * n + 1);
            t_pow *= &t2;
            n += 1;
            let rem = &t_pow * BigInt::from(9) / (BigInt::from(8) * BigInt::from(2 * n + 1));
            if rem < eps190() || n > 400 {
                break;
            }
        }
        let ln2 = RatBracket {
            lo: rmul(&sum_lo, 2),
            hi: ln2.hi,
        };

        // Machin.
        let (a5_lo, a5_hi) = atan_recip_bracket(&BigInt::from(5));
        let (a239_lo, a239_hi) = atan_recip_bracket(&BigInt::from(239));
        let pi_lo = &a5_lo * BigInt::from(16) - &a239_hi * BigInt::from(4);
        let pi_hi = &a5_hi * BigInt::from(16) - &a239_lo * BigInt::from(4);
        let pi2 = RatBracket {
            lo: rdiv(&pi_lo, 2),
            hi: rdiv(&pi_hi, 2),
        };
        Self {
            ln2,
            pi: RatBracket {
                lo: pi_lo,
                hi: pi_hi,
            },
            pi2,
        }
    }
}

/// `atan(1/q)` for integer `q ≥ 2` as a directed bracket:
/// alternating decreasing terms ⇒ partial sum ± next term brackets the limit.
fn atan_recip_bracket(q: &BigInt) -> (BigRational, BigRational) {
    let x = BigRational::new(BigInt::one(), q.clone());
    let x2 = &x * &x;
    let mut p = x.clone(); // x^(2n+1)
    let mut s = BigRational::zero();
    let mut n: u64 = 0;
    loop {
        let term = &p / BigInt::from(2 * n + 1);
        if n.is_multiple_of(2) {
            s += term;
        } else {
            s -= term;
        }
        p *= &x2;
        n += 1;
        let next = &p / BigInt::from(2 * n + 1);
        if next < eps190() || n > 400 {
            return (s.clone() - next.clone(), s + next);
        }
    }
}

#[cfg(feature = "std")]
fn consts() -> &'static TransConsts {
    static CONSTS: std::sync::OnceLock<TransConsts> = std::sync::OnceLock::new();
    CONSTS.get_or_init(TransConsts::compute)
}

#[cfg(not(feature = "std"))]
fn consts() -> &'static TransConsts {
    // No `OnceLock` without std: leak a one-time computation per process via
    // a `static` initialized on first use through `AtomicPtr`-free trick is
    // not available; recompute (deterministic, sub-millisecond).
    // Leak via Box to obtain a 'static reference.
    use alloc::boxed::Box;
    let leaked: &'static TransConsts = Box::leak(Box::new(TransConsts::compute()));
    leaked
}

// =====================================================================
// Point enclosures (rigorous, per single f64 argument)
// =====================================================================

// =====================================================================
// Interval fixed-point (IFX): every series quantity is a directed bracket
// of BigInts in units of 2^-FRAC.
//
// Why not exact rationals: the Taylor terms of atan/atanh carry their
// arguments' denominators to the n-th power, so exact-`BigRational` series
// grow to ~10^5-bit numbers and one point enclosure costs seconds (measured).
// IFX keeps every number below ~600 bits, and — because each quantity IS a
// bracket and every operation rounds toward the bound it produces — the
// enclosure property is structural: no error algebra to get wrong.
// =====================================================================

/// Fractional bits of the IFX representation.
const FRAC: u64 = 192;

fn ifx_scale() -> BigInt {
    BigInt::one() << FRAC
}

/// `num / 2^frac_bits` in lowest terms, WITHOUT the general gcd.
///
/// The `*_rational` enclosures all return dyadic fractions (denominator
/// `2^FRAC`), and `BigRational::new` runs a full binary-gcd plus two big
/// divisions per construction — two constructions per call — which
/// dominated the δ-witness profile (t19: ~35% of samples in
/// `BigUint::gcd`/`div_rem`).  With a power-of-two denominator, reduction
/// is a right-shift by the numerator's trailing zeros: the shifted
/// numerator is odd, hence coprime to the remaining `2^(frac_bits − tz)`,
/// so `new_unchecked` is exact.  Bit-for-bit identical output to
/// `BigRational::new(num, 1 << frac_bits)`.
fn rational_dyadic(num: BigInt, frac_bits: u64) -> BigRational {
    let Some(tz) = num.trailing_zeros() else {
        return BigRational::zero();
    };
    let tz = tz.min(frac_bits);
    let n = num >> tz;
    if tz == frac_bits {
        BigRational::from(n)
    } else {
        BigRational::new_raw(n, BigInt::one() << (frac_bits - tz))
    }
}

/// A directed IFX bracket `[lo, hi]` (units of `2^-FRAC`), `lo ≤ hi`.
#[derive(Clone, Debug)]
struct Ifx {
    lo: BigInt,
    hi: BigInt,
}

impl Ifx {
    fn unit() -> Self {
        Self {
            lo: ifx_scale(),
            hi: ifx_scale(),
        }
    }
    fn zero() -> Self {
        Self {
            lo: BigInt::zero(),
            hi: BigInt::zero(),
        }
    }
    /// Outward sum.
    fn add(&self, o: &Self) -> Self {
        Self {
            lo: &self.lo + &o.lo,
            hi: &self.hi + &o.hi,
        }
    }
    /// Outward difference.
    fn sub(&self, o: &Self) -> Self {
        Self {
            lo: &self.lo - &o.hi,
            hi: &self.hi - &o.lo,
        }
    }
    /// Outward negation.
    fn neg(&self) -> Self {
        Self {
            lo: -self.hi.clone(),
            hi: -self.lo.clone(),
        }
    }
    /// Outward product via the four corners.
    fn mul(&self, o: &Self) -> Self {
        let s = ifx_scale();
        let c11 = floor_div(&(&self.lo * &o.lo), &s);
        let c12 = ceil_div(&(&self.lo * &o.hi), &s);
        let c21 = ceil_div(&(&self.hi * &o.lo), &s);
        let c22 = ceil_div(&(&self.hi * &o.hi), &s);
        // min over floor-rounded corners, max over ceil-rounded corners.
        let mut lo = c11
            .clone()
            .min(c12.clone())
            .min(c21.clone())
            .min(c22.clone());
        let mut hi = c11.max(c12).max(c21).max(c22);
        // Widen by one unit each side: the corner rounding directions above
        // are mixed for negative corners; a guaranteed-outward form is to
        // floor every corner for `lo` and ceil every corner for `hi`.
        lo -= 1;
        hi += 1;
        Self { lo, hi }
    }
    /// Divide by a positive integer, outward.  Both operand and result are
    /// in units of `2^-FRAC`, so this is plain directed integer division.
    fn div_int(&self, n: u64) -> Self {
        let n = BigInt::from(n);
        Self {
            lo: floor_div(&self.lo, &n),
            hi: ceil_div(&self.hi, &n),
        }
    }
    /// Divide by a strictly positive IFX, outward.
    fn div_pos(&self, o: &Self) -> Self {
        debug_assert!(o.lo.is_positive());
        let s = ifx_scale();
        // Corners of self/o over the boxes (self may straddle 0).
        let mut cands_lo: Vec<BigInt> = Vec::new();
        let mut cands_hi: Vec<BigInt> = Vec::new();
        for a in [&self.lo, &self.hi] {
            for b in [&o.lo, &o.hi] {
                cands_lo.push(floor_div(&(a * &s), b));
                cands_hi.push(ceil_div(&(a * &s), b));
            }
        }
        let lo = cands_lo.into_iter().min().unwrap_or(BigInt::zero());
        let hi = cands_hi.into_iter().max().unwrap_or(BigInt::zero());
        Self { lo, hi }
    }
    /// `|x|` as a nonnegative point (an upper bound of the magnitude).
    fn abs_point(&self) -> BigInt {
        let a = self.lo.abs();
        let b = self.hi.abs();
        a.max(b)
    }
    /// Widen both sides by `eps` units.
    fn widen(&mut self, eps: &BigInt) {
        self.lo -= eps;
        self.hi += eps;
    }
    /// Directed conversion to an f64 bracket.
    fn to_f64s(&self) -> (f64, f64) {
        let s = ifx_scale();
        let lo = rat_nonneg_or_neg_to_f64(&self.lo, &s, false);
        let hi = rat_nonneg_or_neg_to_f64(&self.hi, &s, true);
        (lo, hi)
    }
    /// Exact conversion from a finite f64 (dyadic; subnormals below the
    /// 2^-FRAC grid clamp to 0 with a ±1-unit widening that callers'
    /// brackets already dominate — handled by clamping to the nearer of
    /// 0/±1 unit).
    fn from_f64(x: f64) -> Self {
        debug_assert!(x.is_finite());
        let r = f64_to_rational(x);
        let s = ifx_scale();
        let lo = floor_div(&(r.numer() * &s), r.denom());
        let hi = ceil_div(&(r.numer() * &s), r.denom());
        // The rational is exact; floor/ceil here only matter when the
        // denominator exceeds 2^FRAC (deep subnormals), where the two
        // candidates are 0 and ±1 unit.
        Self { lo, hi }
    }
    /// Exact conversion from a rational POINT (bracket of width ≤ 1 unit
    /// when the denominator is not a power of two ≤ 2^FRAC — the bracket
    /// semantics keep it sound).
    fn from_rat_point(v: &BigRational) -> Self {
        let s = ifx_scale();
        Self {
            lo: floor_div(&(v.numer() * &s), v.denom()),
            hi: ceil_div(&(v.numer() * &s), v.denom()),
        }
    }

    /// Directed conversion from a rational bracket.
    fn from_rat_bracket(b: &RatBracket) -> Self {
        let s = ifx_scale();
        Self {
            lo: floor_div(&(b.lo.numer() * &s), b.lo.denom()),
            hi: ceil_div(&(b.hi.numer() * &s), b.hi.denom()),
        }
    }
}

/// Floor division of possibly-negative BigInts.
fn floor_div(a: &BigInt, b: &BigInt) -> BigInt {
    a.div_floor(b)
}

/// Ceiling division of possibly-negative BigInts.
fn ceil_div(a: &BigInt, b: &BigInt) -> BigInt {
    a.div_ceil(b)
}

/// Directed rational→f64 for `n/d` with `d > 0`, any sign of `n`.
fn rat_nonneg_or_neg_to_f64(n: &BigInt, d: &BigInt, up: bool) -> f64 {
    if n.sign() == num_bigint::Sign::Minus {
        -rat_nonneg_to_f64_dir(&(-n), d, !up)
    } else {
        rat_nonneg_to_f64_dir(n, d, up)
    }
}

/// The convergence target for IFX series: stop when the tail bound drops
/// below this many units (2^-184 — far below f64 significance).
fn ifx_tail_target() -> BigInt {
    BigInt::one() << 8
}

// ---------------------------------------------------------------------
// Constants in IFX form (converted once from the exact rational brackets)
// ---------------------------------------------------------------------

struct IfxConsts {
    ln2: Ifx,
    pi: Ifx,
    pi2: Ifx,
}

#[cfg(feature = "std")]
fn ifx_consts() -> &'static IfxConsts {
    static C: std::sync::OnceLock<IfxConsts> = std::sync::OnceLock::new();
    C.get_or_init(|| IfxConsts {
        ln2: Ifx::from_rat_bracket(&consts().ln2),
        pi: Ifx::from_rat_bracket(&consts().pi),
        pi2: Ifx::from_rat_bracket(&consts().pi2),
    })
}

#[cfg(not(feature = "std"))]
fn ifx_consts() -> &'static IfxConsts {
    use alloc::boxed::Box;
    Box::leak(Box::new(IfxConsts {
        ln2: Ifx::from_rat_bracket(&consts().ln2),
        pi: Ifx::from_rat_bracket(&consts().pi),
        pi2: Ifx::from_rat_bracket(&consts().pi2),
    }))
}

// ---------------------------------------------------------------------
// Point enclosures (IFX series)
// ---------------------------------------------------------------------

/// Integer square root (floor), Newton — exact for any nonnegative input.
fn isqrt(n: &BigInt) -> BigInt {
    if n.is_zero() {
        return BigInt::zero();
    }
    let mut x = BigInt::one() << ((n.bits() / 2) + 1);
    loop {
        let y = (x.clone() + n / &x) >> 1;
        if y >= x {
            break;
        }
        x = y;
    }
    while &x * &x > n.clone() {
        x -= 1;
    }
    while (&x + 1) * (&x + 1) <= n.clone() {
        x += 1;
    }
    x
}

/// Rigorous rational bracket of `√v` for the exact rational `v ≥ 1`
/// (asin's reduction): `√(n/d) = √(n·d)/d`, integer isqrt on the scaled
/// product.
fn rat_sqrt_bracket(v: &BigRational) -> RatBracket {
    let n = v.numer();
    let d = v.denom();
    let scale_bits: u64 = 200;
    let scaled = (n * d) << (2 * scale_bits);
    let r = isqrt(&scaled);
    let lo = BigRational::new(r.clone(), d.clone() << scale_bits);
    let hi = BigRational::new(r + 1, d << scale_bits);
    RatBracket { lo, hi }
}

/// Rigorous enclosure of `e^x` for finite `x`, as an f64 bracket.
fn exp_point(x: f64) -> (f64, f64) {
    if !x.is_finite() {
        return if x > 0.0 {
            (f64::INFINITY, f64::INFINITY)
        } else {
            (0.0, 0.0)
        };
    }
    if x > 710.0 {
        return (f64::MAX, f64::INFINITY);
    }
    if x < -746.0 {
        return (0.0, f64::from_bits(1));
    }
    // k = round(x/ln2): ANY integer k works (e^x = 2^k·e^(x−k·ln2)); the
    // f64 choice only affects series length (|r| ≤ ~0.35 normally, ≤ ~1.05
    // when k rounded oddly).
    let k = (x / core::f64::consts::LN_2).round() as i64;
    let c = ifx_consts();
    let xf = Ifx::from_f64(x);
    let kln2 = Ifx {
        lo: &c.ln2.lo * k,
        hi: &c.ln2.hi * k,
    };
    let r = xf.sub(&kln2); // |r| ≲ 1.05
    let mut e = exp_ifx_series(&r);
    // × 2^k (exact shift; directed for negative k).
    if k >= 0 {
        e.lo <<= k as u64;
        e.hi <<= k as u64;
    } else {
        // value/2^sh in units is units >> sh, with directed rounding.
        let sh = (-k) as u64;
        let d = BigInt::one() << sh;
        let lo_v = ceil_div(&e.lo, &d);
        let hi_v = floor_div(&e.hi, &d);
        e.lo = lo_v;
        e.hi = hi_v;
    }
    e.to_f64s()
}

/// Taylor `e^r` for `|r| ≲ 1.1`, as an IFX bracket with rigorous tail.
fn exp_ifx_series(r: &Ifx) -> Ifx {
    let mut sum = Ifx::unit();
    let mut term = Ifx::unit();
    let mut n: u64 = 1;
    loop {
        term = term.mul(r);
        term = term.div_int(n);
        sum = sum.add(&term);
        // Tail ≤ 2·|term| once n! dominates (|r| ≤ 1.1 < n).
        let tabs = term.abs_point();
        let tail_bound = if n >= 3 {
            tabs.clone() * 2
        } else {
            tabs.clone() * 4
        };
        if tail_bound < ifx_tail_target() || n > 300 {
            let mut out = sum;
            out.widen(&tail_bound);
            return out;
        }
        n += 1;
    }
}

/// Shared trig reduction: `x = r + k·π/2` with `r` an IFX bracket
/// (`|x| ≤ 2^50` guaranteed by the callers' caps, so the f64 `k` is within
/// ±1 of the true nearest and `|r| ≤ 3π/4`).
fn trig_reduce_ifx(x: f64) -> (Ifx, i128) {
    let inv_pi2 = 2.0 / core::f64::consts::PI;
    let kf = (x * inv_pi2).round();
    let k: i128 = kf as i128;
    let c = ifx_consts();
    let xf = Ifx::from_f64(x);
    let kpi2 = Ifx {
        lo: &c.pi2.lo * k,
        hi: &c.pi2.hi * k,
    };
    (xf.sub(&kpi2), k)
}

/// Rigorous enclosure of `sin(x)` for finite `x` with `|x| ≤ 2^50`.
fn sin_point_raw(x: f64) -> (f64, f64) {
    let (r, k) = trig_reduce_ifx(x);
    let m = ((k % 4) + 4) % 4;
    match m {
        0 => sin_ifx_bracket(&r).to_f64s(),
        1 => cos_ifx_bracket(&r).to_f64s(),
        2 => sin_ifx_bracket(&r).neg().to_f64s(),
        _ => cos_ifx_bracket(&r).neg().to_f64s(),
    }
}

/// Rigorous enclosure of `cos(x)` for finite `x` with `|x| ≤ 2^50`.
fn cos_point_raw(x: f64) -> (f64, f64) {
    let (r, k) = trig_reduce_ifx(x);
    let m = ((k % 4) + 4) % 4;
    match m {
        0 => cos_ifx_bracket(&r).to_f64s(),
        1 => sin_ifx_bracket(&r).neg().to_f64s(),
        2 => cos_ifx_bracket(&r).neg().to_f64s(),
        _ => sin_ifx_bracket(&r).to_f64s(),
    }
}

/// `sin(r)` over the reduced window (|r| ≤ 3π/4): critical points at
/// `π/2 + jπ`; a window of width < π contains at most one, and when one is
/// inside, its exact value `(−1)^j` joins the hull; otherwise sin is
/// monotone and the endpoint hull is the range.
fn sin_ifx_bracket(r: &Ifx) -> Ifx {
    let c = ifx_consts();
    let width = Ifx {
        lo: r.hi.clone() - &r.lo,
        hi: r.hi.clone() - &r.lo,
    };
    if width.lo >= c.pi.lo {
        return Ifx {
            lo: -ifx_scale(),
            hi: ifx_scale(),
        };
    }
    let mut out = sin_ifx_series(r);
    // Candidate critical points inside a |r| ≤ 3π/4 window: ±π/2.
    let pi2_lo = c.pi2.lo.clone();
    let pi2_hi = c.pi2.hi.clone();
    let pi_lo = c.pi.lo.clone();
    let pi_hi = c.pi.hi.clone();
    // c = π/2 strictly inside (r.lo, r.hi)?
    if pi2_hi > r.lo && pi2_lo < r.hi {
        out.hi = out.hi.max(ifx_scale());
    }
    // c = −π/2 strictly inside?
    let neg_hi = -pi2_lo.clone();
    let neg_lo = -pi2_hi.clone();
    if neg_hi > r.lo && neg_lo < r.hi {
        out.lo = out.lo.min(-ifx_scale());
    }
    let _ = (pi_lo, pi_hi);
    out
}

/// `cos(r)` over the reduced window: critical point 0 with value 1.
fn cos_ifx_bracket(r: &Ifx) -> Ifx {
    let c = ifx_consts();
    let width = r.hi.clone() - &r.lo;
    if width >= c.pi.lo {
        return Ifx {
            lo: -ifx_scale(),
            hi: ifx_scale(),
        };
    }
    let mut out = cos_ifx_series(r);
    if r.lo.sign() == num_bigint::Sign::Minus && r.hi.sign() != num_bigint::Sign::Minus {
        // cos(0) = 1 inside the window.
        out.hi = out.hi.max(ifx_scale());
        out.lo = out.lo.min(ifx_scale()); // ≤ 1 always; keep for symmetry
    }
    out
}

/// Taylor `sin(r)` at the IFX bracket `r` (|r| ≤ 3π/4): alternating series;
/// the tail is bounded by 2× the first omitted term once the ratio
/// `r²/((n+1)(n+2))` drops below 1/2 (n ≥ 4 for |r| ≤ 2.4).
fn sin_ifx_series(r: &Ifx) -> Ifx {
    let mut sum = r.clone();
    let mut term = r.clone();
    let mut n: u64 = 1;
    loop {
        term = term.mul(r);
        term = term.mul(r);
        term = term.div_int((n + 1) * (n + 2));
        n += 2;
        if ((n - 1) / 2) % 2 == 1 {
            sum = sum.sub(&term);
        } else {
            sum = sum.add(&term);
        }
        let tabs = term.abs_point();
        // tail ≤ |next| · 2 (ratio < 1/2 by n ≥ 5 here).
        let tail = if n >= 5 {
            tabs.clone() * 2
        } else {
            tabs.clone() * 8
        };
        if tail < ifx_tail_target() || n > 200 {
            let mut out = sum;
            out.widen(&tail);
            return out;
        }
    }
}

/// Taylor `cos(r)` at the IFX bracket `r`.
fn cos_ifx_series(r: &Ifx) -> Ifx {
    let mut sum = Ifx::unit();
    let mut term = Ifx::unit();
    let mut n: u64 = 0;
    loop {
        term = term.mul(r);
        term = term.mul(r);
        term = term.div_int((n + 1) * (n + 2));
        n += 2;
        if (n / 2) % 2 == 1 {
            sum = sum.sub(&term);
        } else {
            sum = sum.add(&term);
        }
        let tabs = term.abs_point();
        let tail = if n >= 4 {
            tabs.clone() * 2
        } else {
            tabs.clone() * 8
        };
        if tail < ifx_tail_target() || n > 200 {
            let mut out = sum;
            out.widen(&tail);
            return out;
        }
    }
}

/// Rigorous enclosure of `atan(x)` for finite `x`.
fn atan_point(x: f64) -> (f64, f64) {
    if !x.is_finite() {
        let (plo, phi) = consts().pi2.to_f64s();
        return if x > 0.0 { (plo, phi) } else { (-phi, -plo) };
    }
    let neg = x < 0.0;
    let xf = Ifx::from_f64(x.abs());
    // Reduction 1: |x| > 1 ⇒ atan(x) = π/2 − atan(1/x).
    let one = Ifx::unit();
    let (used_recip, t) = if xf.lo > one.lo {
        (true, one.div_pos(&xf))
    } else {
        (false, xf)
    };
    // Reduction 2 (halving): atan(t) = 2·atan(y), y = t/(1+√(1+t²)),
    // y ∈ [0, 1/(1+√2) ≈ 0.4143].
    let one_plus = one.add(&t.mul(&t));
    let s = ifx_sqrt_pos(&one_plus);
    let denom = one.add(&s);
    let y = t.div_pos(&denom);
    let a = atan_ifx_series(&y);
    let mut v = Ifx {
        lo: &a.lo * 2 - 1,
        hi: &a.hi * 2 + 1,
    };
    if used_recip {
        let c = ifx_consts();
        v = Ifx {
            lo: &c.pi2.lo - &v.hi,
            hi: &c.pi2.hi - &v.lo,
        };
    }
    if neg { v.neg().to_f64s() } else { v.to_f64s() }
}

/// Taylor `atan(y)` for `y ∈ [0, 0.4143]` (IFX bracket): alternating with
/// ratio ≤ y² < 0.172, so the tail ≤ 2× the first omitted term.
fn atan_ifx_series(y: &Ifx) -> Ifx {
    let y2 = y.mul(y);
    let mut p = y.clone();
    let mut s = Ifx::zero();
    let mut n: u64 = 0;
    loop {
        let term = p.div_int(2 * n + 1);
        if n.is_multiple_of(2) {
            s = s.add(&term);
        } else {
            s = s.sub(&term);
        }
        p = p.mul(&y2);
        n += 1;
        let next = p.div_int(2 * n + 1);
        let tail = next.abs_point() * 2;
        if tail < ifx_tail_target() || n > 400 {
            let mut out = s;
            out.widen(&tail);
            return out;
        }
    }
}

/// Rigorous enclosure of `asin(y)` for `y ∈ [−1, 1]`:
/// `asin(y) = atan(y/√(1−y²))` (exact at ±1).
fn asin_point(y: f64) -> (f64, f64) {
    if !(-1.0..=1.0).contains(&y) {
        let c = consts();
        let hi = rat_to_f64(&c.pi2.hi, false);
        return (-hi, hi);
    }
    if y == 1.0 {
        let c = consts();
        return (rat_to_f64(&c.pi2.lo, true), rat_to_f64(&c.pi2.hi, false));
    }
    if y == -1.0 {
        let c = consts();
        return (-rat_to_f64(&c.pi2.hi, false), -rat_to_f64(&c.pi2.lo, true));
    }
    if y == 0.0 {
        return (0.0, 0.0);
    }
    // atan of the directed f64 conversions of y/√(1−y²) (atan increasing).
    let yr = f64_to_rational(y);
    let one = BigRational::one();
    let arg = &one - &yr * &yr;
    let s = rat_sqrt_bracket(&arg);
    let (q_lo, q_hi) = if y > 0.0 {
        (&yr / &s.hi, &yr / &s.lo)
    } else {
        (&yr / &s.lo, &yr / &s.hi)
    };
    (
        atan_point(rat_to_f64(&q_lo, true)).0,
        atan_point(rat_to_f64(&q_hi, false)).1,
    )
}

/// Rigorous bracket of `√v` for the IFX bracket `v ≥ 1` (atan's halving).
fn ifx_sqrt_pos(v: &Ifx) -> Ifx {
    // √(n/2^F) = isqrt(n·2^F)/2^F: scale by 2^F again for the fractional
    // half, with directed isqrt roundings on both bracket ends.
    let s = ifx_scale();
    let lo_in = &v.lo * &s;
    let hi_in = &v.hi * &s;
    let r_lo = isqrt(&lo_in);
    let r_hi = {
        let r = isqrt(&hi_in);
        if &r * &r == hi_in { r } else { r + 1 }
    };
    Ifx { lo: r_lo, hi: r_hi }
}

// ---------------------------------------------------------------------
// Exact rational enclosures: the δ-witness's publication check evaluates
// the published RATIONAL point in exact arithmetic; these hand back exact
// rational brackets from the same Ifx series that power the f64 bounds.
// ---------------------------------------------------------------------

/// |q| for a rational.
fn abs_rat(q: &BigRational) -> BigRational {
    if *q < BigRational::new(BigInt::from(0), BigInt::from(1)) {
        -q.clone()
    } else {
        q.clone()
    }
}

/// `e^x` for an exact rational `x`, as an exact rational bracket.
#[must_use]
pub fn exp_rational(x: &BigRational) -> (BigRational, BigRational) {
    let s = |v: &BigInt| rational_dyadic(v.clone(), FRAC);
    // Saturation mirrors the f64 path.
    let hi_f = x.to_f64().unwrap_or(f64::INFINITY);
    if hi_f > 710.0 {
        return (
            BigRational::from_integer(BigInt::from(1) << 1023),
            BigRational::from_integer((BigInt::from(1) << 1024) - 1u8),
        );
    }
    let lo_f = x.to_f64().unwrap_or(f64::NEG_INFINITY);
    if lo_f < -746.0 {
        return (
            BigRational::zero(),
            BigRational::new(BigInt::one(), BigInt::one() << 1074),
        );
    }
    let k = (hi_f / core::f64::consts::LN_2).round() as i64;
    let c = ifx_consts();
    let xf = Ifx::from_rat_point(x);
    let kln2 = Ifx {
        lo: &c.ln2.lo * k,
        hi: &c.ln2.hi * k,
    };
    let r = xf.sub(&kln2);
    let mut e = exp_ifx_series(&r);
    if k >= 0 {
        e.lo <<= k as u64;
        e.hi <<= k as u64;
    } else {
        let d = BigInt::one() << (-k) as u64;
        let lo_v = ceil_div(&e.lo, &d);
        let hi_v = floor_div(&e.hi, &d);
        e.lo = lo_v;
        e.hi = hi_v;
    }
    (s(&e.lo), s(&e.hi))
}

/// `atan(x)` for an exact rational `x`, as an exact rational bracket.
#[must_use]
pub fn atan_rational(x: &BigRational) -> (BigRational, BigRational) {
    let neg = x < &BigRational::zero();
    let xf_abs = Ifx::from_rat_point(&abs_rat(x));
    let one = Ifx::unit();
    let (used_recip, t) = if xf_abs.lo > one.lo {
        (true, one.div_pos(&xf_abs))
    } else {
        (false, xf_abs)
    };
    let one_plus = one.add(&t.mul(&t));
    let sq = ifx_sqrt_pos(&one_plus);
    let denom = one.add(&sq);
    let y = t.div_pos(&denom);
    let val = atan_ifx_series(&y);
    let mut v = Ifx {
        lo: &val.lo * 2 - 1,
        hi: &val.hi * 2 + 1,
    };
    if used_recip {
        let c = ifx_consts();
        v = Ifx {
            lo: &c.pi2.lo - &v.hi,
            hi: &c.pi2.hi - &v.lo,
        };
    }
    if neg {
        v = v.neg();
    }
    (rational_dyadic(v.lo, FRAC), rational_dyadic(v.hi, FRAC))
}

/// `sin(x)`/`cos(x)` for an exact rational `x` (|x| ≤ 2^50), as exact
/// rational brackets.  Larger arguments answer the full range.
#[must_use]
pub fn sin_cos_rational(x: &BigRational, want_cos: bool) -> (BigRational, BigRational) {
    let xf = x.to_f64().unwrap_or(f64::INFINITY);
    if !xf.is_finite() || xf.abs() > 2.0_f64.powi(50) {
        return (
            BigRational::from_integer(BigInt::from(-1)),
            BigRational::from_integer(BigInt::from(1)),
        );
    }
    let mut k: i128 = (xf * (2.0 / core::f64::consts::PI)).round() as i128;
    if want_cos {
        // cos(x) = sin(x + π/2): use k' = 2k+1-style shift via quadrant.
        k = (xf / core::f64::consts::PI).round() as i128;
    }
    // Quadrant dispatch for BOTH functions: sin(r + kπ/2) = S(k mod 4, r),
    // cos(r + kπ/2) = C(k mod 4, r).  (The first version forgot the sin
    // dispatch — sin(366) evaluated as sin(r) ≈ 0.0036 instead of cos(r) ≈
    // 1.0, and a false δ-witness slipped through the exact check.)
    let (r, kk) = trig_reduce_ifx(xf);
    let m = ((kk % 4) + 4) % 4;
    let (bracket, flip) = match (want_cos, m) {
        (false, 0) => (sin_ifx_bracket(&r), 1),
        (false, 1) => (cos_ifx_bracket(&r), 1),
        (false, 2) => (sin_ifx_bracket(&r), -1),
        (false, _) => (cos_ifx_bracket(&r), -1),
        (true, 0) => (cos_ifx_bracket(&r), 1),
        (true, 1) => (sin_ifx_bracket(&r), -1),
        (true, 2) => (cos_ifx_bracket(&r), -1),
        (true, _) => (sin_ifx_bracket(&r), 1),
    };
    let _ = k;
    let (lo, hi) = if flip < 0 {
        (bracket.neg().hi, bracket.neg().lo)
    } else {
        (bracket.lo, bracket.hi)
    };
    (rational_dyadic(lo, FRAC), rational_dyadic(hi, FRAC))
}

/// `log(x)` for an exact positive rational `x`, as an exact rational
/// bracket.
#[must_use]
pub fn log_rational(x: &BigRational) -> (BigRational, BigRational) {
    debug_assert!(x > &BigRational::zero());
    // Normalize x = m · 2^e with m ∈ [1, 2), exact in rationals.
    let n = x.numer();
    let d = x.denom();
    let bn = n.bits() as i64;
    let bd = d.bits() as i64;
    let e = bn - bd;
    // m = x / 2^e ∈ [1, 2): as an Ifx point.
    let m_rat = if e >= 0 {
        x / (BigInt::one() << e as u64)
    } else {
        x * (BigInt::one() << (-e) as u64)
    };
    let m = Ifx::from_rat_point(&m_rat);
    let one = Ifx::unit();
    let num = m.sub(&one);
    let den = m.add(&one);
    let t = num.div_pos(&den);
    let a = atanh_ifx_series(&t);
    let lm = Ifx {
        lo: &a.lo * 2 - 1,
        hi: &a.hi * 2 + 1,
    };
    let c = ifx_consts();
    let e_ln2 = Ifx {
        lo: &c.ln2.lo * e,
        hi: &c.ln2.hi * e,
    };
    let out = e_ln2.add(&lm);
    (rational_dyadic(out.lo, FRAC), rational_dyadic(out.hi, FRAC))
}

/// `sqrt(x)` for an exact nonnegative rational `x`, as an exact rational
/// bracket.
#[must_use]
pub fn sqrt_rational(x: &BigRational) -> (BigRational, BigRational) {
    debug_assert!(*x >= BigRational::zero());
    // √(n/d) = √(n·d)/d with integer isqrt on a scaled product.
    let n = x.numer();
    let d = x.denom();
    let scaled = (n * d) << 384;
    let r = isqrt(&scaled);
    let lo = BigRational::new(r.clone(), d.clone() << 192);
    let hi = BigRational::new(r + 1, d << 192);
    (lo, hi)
}

/// Rigorous f64 bracket for `log(x)`, `x > 0` finite:
/// `x = m·2^e` exactly; `log x = e·ln2 + 2·atanh(t)`, `t = (m−1)/(m+1)`.
fn log_point(x: f64) -> (f64, f64) {
    debug_assert!(x > 0.0 && x.is_finite());
    let bits = x.to_bits();
    let biased = ((bits >> 52) & 0x7ff) as i64;
    let mant = if biased == 0 {
        BigInt::from(bits & ((1_u64 << 52) - 1))
    } else {
        BigInt::from((bits & ((1_u64 << 52) - 1)) | (1_u64 << 52))
    };
    let exp2 = if biased == 0 {
        -1074
    } else {
        biased - 1023 - 52
    };
    let mbits = mant.bits() as i64;
    let e = exp2 + mbits - 1;
    // m = mant·2^(1−mbits) ∈ [1, 2) as IFX.
    let s = ifx_scale();
    let m = if mbits == 1 {
        Ifx::unit()
    } else {
        Ifx {
            lo: floor_div(&(&mant * &s), &(BigInt::one() << (mbits - 1))),
            hi: ceil_div(&(&mant * &s), &(BigInt::one() << (mbits - 1))),
        }
    };
    // t = (m−1)/(m+1) ∈ [0, 1/3), positive divisor.
    let one = Ifx::unit();
    let num = m.sub(&one);
    let den = m.add(&one);
    let t = num.div_pos(&den);
    let a = atanh_ifx_series(&t);
    let lm = Ifx {
        lo: &a.lo * 2 - 1,
        hi: &a.hi * 2 + 1,
    };
    let c = ifx_consts();
    let e_ln2 = Ifx {
        lo: &c.ln2.lo * e,
        hi: &c.ln2.hi * e,
    };
    e_ln2.add(&lm).to_f64s()
}

/// `atanh(t) = Σ t^(2n+1)/(2n+1)` for `t ∈ [0, 1/3)` (IFX): ratio ≤ 1/9,
/// tail ≤ 2× the first omitted term.
fn atanh_ifx_series(t: &Ifx) -> Ifx {
    let t2 = t.mul(t);
    let mut p = t.clone();
    let mut s = Ifx::zero();
    let mut n: u64 = 0;
    loop {
        s = s.add(&p.div_int(2 * n + 1));
        p = p.mul(&t2);
        n += 1;
        let next = p.div_int(2 * n + 1);
        let tail = next.abs_point() * 2;
        if tail < ifx_tail_target() || n > 400 {
            let mut out = s;
            out.widen(&tail);
            return out;
        }
    }
}

// =====================================================================
// Public interval type + operations
// =====================================================================

/// A closed interval over the extended reals, bounds as `f64` (±∞ allowed,
/// never NaN).  An *empty* interval is represented by `lo > hi`.
///
/// All operations round **outward**, so the result always contains every
/// true value of the corresponding point operation over the operand boxes —
/// the invariant the δ-ICP engine's soundness rests on.
#[derive(Clone, Copy, Debug, PartialEq)]
pub struct DI {
    /// Lower bound (toward −∞).
    pub lo: f64,
    /// Upper bound (toward +∞).
    pub hi: f64,
}

impl DI {
    /// The empty interval.
    pub const EMPTY: DI = DI {
        lo: f64::INFINITY,
        hi: f64::NEG_INFINITY,
    };
    /// The whole real line.
    pub const RN: DI = DI {
        lo: f64::NEG_INFINITY,
        hi: f64::INFINITY,
    };

    /// A point interval.
    #[must_use]
    pub fn point(v: f64) -> Self {
        Self { lo: v, hi: v }
    }

    /// Is this interval empty (`lo > hi`)?
    #[must_use]
    pub fn is_empty(&self) -> bool {
        self.lo > self.hi
    }

    /// Is this a point (`lo == hi`, finite)?
    #[must_use]
    pub fn is_point(&self) -> bool {
        self.lo == self.hi
    }

    /// Does the interval contain 0?
    #[must_use]
    pub fn contains_zero(&self) -> bool {
        self.lo <= 0.0 && self.hi >= 0.0
    }

    /// Width (`+∞` for unbounded).
    #[must_use]
    pub fn width(&self) -> f64 {
        self.hi - self.lo
    }

    /// Midpoint (0 for doubly-infinite; a finite "interesting point" for
    /// half-infinite boxes; may round for huge finite bounds — callers use it
    /// only as a split/witness point, never as a bound).
    #[must_use]
    pub fn midpoint(&self) -> f64 {
        if self.lo == f64::NEG_INFINITY && self.hi == f64::INFINITY {
            0.0
        } else if self.lo == f64::NEG_INFINITY {
            self.hi - fmax(1.0, self.hi.abs())
        } else if self.hi == f64::INFINITY {
            self.lo + fmax(1.0, self.lo.abs())
        } else {
            self.lo + (self.hi - self.lo) / 2.0
        }
    }

    /// Intersection.
    #[must_use]
    pub fn intersect(&self, other: &Self) -> Self {
        Self {
            lo: fmax(self.lo, other.lo),
            hi: fmin(self.hi, other.hi),
        }
    }

    /// Convex hull.
    #[must_use]
    pub fn hull(&self, other: &Self) -> Self {
        Self {
            lo: fmin(self.lo, other.lo),
            hi: fmax(self.hi, other.hi),
        }
    }

    /// Outward sum.
    #[must_use]
    pub fn add(&self, o: &Self) -> Self {
        Self {
            lo: f64_next_down(self.lo + o.lo),
            hi: f64_next_up(self.hi + o.hi),
        }
    }

    /// Outward negation.
    #[must_use]
    pub fn neg(&self) -> Self {
        Self {
            lo: -self.hi,
            hi: -self.lo,
        }
    }

    /// Outward difference.
    #[must_use]
    pub fn sub(&self, o: &Self) -> Self {
        self.add(&o.neg())
    }

    /// Outward product.  Four-corner method over the extended reals with the
    /// interval convention `0·±∞ = 0` — exactly the sup/inf of the pointwise
    /// product over closed intervals.
    #[must_use]
    pub fn mul(&self, o: &Self) -> Self {
        if self.is_point() && self.lo == 0.0 {
            return Self::point(0.0);
        }
        if o.is_point() && o.lo == 0.0 {
            return Self::point(0.0);
        }
        let p1 = xmul(self.lo, o.lo);
        let p2 = xmul(self.lo, o.hi);
        let p3 = xmul(self.hi, o.lo);
        let p4 = xmul(self.hi, o.hi);
        Self {
            lo: f64_next_down(fmin(fmin(p1.0, p2.0), fmin(p3.0, p4.0))),
            hi: f64_next_up(fmax(fmax(p1.1, p2.1), fmax(p3.1, p4.1))),
        }
    }

    /// Outward square `[l,h]²`: exact range (tighter than the four-corner
    /// product, which over-approximates a straddling square to
    /// `[-max², max²]`).
    #[must_use]
    pub fn square(&self) -> Self {
        let l = self.lo;
        let h = self.hi;
        if l <= 0.0 && h >= 0.0 {
            let m = fmax(l * l, h * h);
            Self {
                lo: 0.0,
                hi: f64_next_up(f64_next_up(m)),
            }
        } else if l > 0.0 {
            Self {
                lo: f64_next_down(f64_next_down(l * l)),
                hi: f64_next_up(f64_next_up(h * h)),
            }
        } else {
            Self {
                lo: f64_next_down(f64_next_down(h * h)),
                hi: f64_next_up(f64_next_up(l * l)),
            }
        }
    }

    /// Outward quotient.  If the divisor contains 0, the result is the whole
    /// line (a sound over-approximation; the ICP engine separately refuses
    /// to *verify* constraints whose divisor box touches 0).
    #[must_use]
    pub fn div(&self, o: &Self) -> Self {
        if o.contains_zero() {
            if self.is_point() && self.lo == 0.0 {
                return Self::point(0.0);
            }
            return Self::RN;
        }
        let p1 = xdiv(self.lo, o.lo);
        let p2 = xdiv(self.lo, o.hi);
        let p3 = xdiv(self.hi, o.lo);
        let p4 = xdiv(self.hi, o.hi);
        Self {
            lo: f64_next_down(fmin(fmin(p1.0, p2.0), fmin(p3.0, p4.0))),
            hi: f64_next_up(fmax(fmax(p1.1, p2.1), fmax(p3.1, p4.1))),
        }
    }

    /// Outward `exp` (monotone increasing).
    #[must_use]
    pub fn exp(&self) -> Self {
        if self.is_empty() {
            return Self::EMPTY;
        }
        let (a, _) = exp_point_cached(self.lo);
        let (_, b) = exp_point_cached(self.hi);
        Self { lo: a, hi: b }
    }

    /// Outward `log` with the totalization `log(x ≤ 0) = −∞`.
    ///
    /// * whole box ≤ 0 → the point `−∞`;
    /// * box straddles 0 → `[−∞, log(hi)]`;
    /// * box > 0 → `[log(lo), log(hi)]`.
    #[must_use]
    pub fn log(&self) -> Self {
        if self.is_empty() {
            return Self::EMPTY;
        }
        if self.hi <= 0.0 {
            return Self::point(f64::NEG_INFINITY);
        }
        let hi_enc = if self.hi == f64::INFINITY {
            f64::INFINITY
        } else {
            log_point_cached(self.hi).1
        };
        if self.lo <= 0.0 {
            return Self {
                lo: f64::NEG_INFINITY,
                hi: hi_enc,
            };
        }
        let lo_enc = log_point_cached(self.lo).0;
        Self {
            lo: lo_enc,
            hi: hi_enc,
        }
    }

    /// Outward `sin` (period- and monotonicity-aware):
    ///
    /// * width ≥ π (rigorously) → the full range `[-1, 1]` (an interval of
    ///   width ≥ π contains both a maximum and a minimum of sin);
    /// * else at most one critical point (`π/2 + kπ`) lies strictly inside;
    ///   if one does, its exact value `(−1)^k` joins the endpoint hull;
    /// * otherwise sin is monotone on the box and the endpoint enclosure
    ///   hull is the range.
    #[must_use]
    pub fn sin(&self) -> Self {
        if self.is_empty() {
            return Self::EMPTY;
        }
        let (_, pi_hi) = pi_f64_bracket();
        let width = self.hi - self.lo;
        if !width.is_finite() || width >= pi_hi {
            return Self { lo: -1.0, hi: 1.0 };
        }
        let mid = self.midpoint();
        let k = ((mid - core::f64::consts::FRAC_PI_2) / core::f64::consts::PI).round();
        let c = core::f64::consts::FRAC_PI_2 + k * core::f64::consts::PI;
        // Rigorous membership: the true critical point lies within [c−2ulp,
        // c+2ulp] (two roundings: the k·π arithmetic; membership must be
        // strict, so require the widened bracket inside the open box).
        let c_lo = f64_next_down(f64_next_down(c));
        let c_hi = f64_next_up(f64_next_up(c));
        let inside = c_lo > self.lo && c_hi < self.hi;
        let (a_lo, a_hi) = sin_point_capped(self.lo);
        let (b_lo, b_hi) = sin_point_capped(self.hi);
        if inside {
            let crit = if (k as i64) % 2 == 0 { 1.0 } else { -1.0 };
            Self {
                lo: fmin(fmin(a_lo, b_lo), crit),
                hi: fmax(fmax(a_hi, b_hi), crit),
            }
        } else {
            Self {
                lo: fmin(a_lo, b_lo),
                hi: fmax(a_hi, b_hi),
            }
        }
    }

    /// Outward `cos` (critical points at `kπ`, `cos(kπ) = (−1)^k`).
    #[must_use]
    pub fn cos(&self) -> Self {
        if self.is_empty() {
            return Self::EMPTY;
        }
        let (_, pi_hi) = pi_f64_bracket();
        let width = self.hi - self.lo;
        if !width.is_finite() || width >= pi_hi {
            return Self { lo: -1.0, hi: 1.0 };
        }
        let mid = self.midpoint();
        let k = (mid / core::f64::consts::PI).round();
        let c = k * core::f64::consts::PI;
        let c_lo = f64_next_down(f64_next_down(c));
        let c_hi = f64_next_up(f64_next_up(c));
        let inside = c_lo > self.lo && c_hi < self.hi;
        let (a_lo, a_hi) = cos_point_capped(self.lo);
        let (b_lo, b_hi) = cos_point_capped(self.hi);
        if inside {
            let crit = if (k as i64) % 2 == 0 { 1.0 } else { -1.0 };
            Self {
                lo: fmin(fmin(a_lo, b_lo), crit),
                hi: fmax(fmax(a_hi, b_hi), crit),
            }
        } else {
            Self {
                lo: fmin(a_lo, b_lo),
                hi: fmax(a_hi, b_hi),
            }
        }
    }

    /// Outward `atan` (monotone increasing, limits ±π/2).
    #[must_use]
    pub fn atan(&self) -> Self {
        if self.is_empty() {
            return Self::EMPTY;
        }
        let (a, _) = atan_point_cached(self.lo);
        let (_, b) = atan_point_cached(self.hi);
        Self { lo: a, hi: b }
    }

    /// Outward `sqrt` with the totalization `sqrt(x < 0) = 0`.
    ///
    /// Uses the IEEE-754 correctly-rounded `f64::sqrt` and widens one ulp
    /// outward on each side, covering the half-ulp rounding error.
    #[must_use]
    pub fn sqrt(&self) -> Self {
        if self.is_empty() {
            return Self::EMPTY;
        }
        if self.hi < 0.0 {
            return Self::point(0.0);
        }
        let hi = f64_next_up(self.hi.sqrt());
        let lo = if self.lo <= 0.0 {
            0.0
        } else {
            f64_next_down(self.lo.sqrt())
        };
        Self { lo, hi }
    }

    /// Outward enclosure of an exact `Rational64`.
    #[must_use]
    pub fn from_rational64(r: &num_rational::Rational64) -> Self {
        let v = BigRational::new(BigInt::from(*r.numer()), BigInt::from(*r.denom()));
        Self {
            lo: rat_to_f64(&v, true),
            hi: rat_to_f64(&v, false),
        }
    }
}

// =====================================================================
// Extended-real helpers
// =====================================================================

/// Extended-real product of two `f64`s that may be ±∞, with the interval
/// convention `0·±∞ = 0`.  Returns a bracket covering the true product.
fn xmul(a: f64, b: f64) -> (f64, f64) {
    if a == 0.0 || b == 0.0 {
        return (0.0, 0.0);
    }
    let p = a * b;
    if p.is_nan() {
        return (f64::NEG_INFINITY, f64::INFINITY);
    }
    (f64_next_down(p), f64_next_up(p))
}

/// Extended-real quotient (`b ≠ 0`, possibly ±∞).
fn xdiv(a: f64, b: f64) -> (f64, f64) {
    if a == 0.0 {
        return (0.0, 0.0);
    }
    let q = a / b;
    if q.is_nan() {
        return (f64::NEG_INFINITY, f64::INFINITY);
    }
    (f64_next_down(q), f64_next_up(q))
}

fn sin_point_capped(x: f64) -> (f64, f64) {
    // 2^50, not larger: `k = round(2x/π)` in f64 is then within ±1 of the
    // true value (see `trig_reduce`), keeping the reduced window ≤ 3π/4.
    if x.abs() > 2.0_f64.powi(50) {
        (-1.0, 1.0)
    } else {
        sin_point_cached(x)
    }
}

fn cos_point_capped(x: f64) -> (f64, f64) {
    if x.abs() > 2.0_f64.powi(50) {
        (-1.0, 1.0)
    } else {
        cos_point_cached(x)
    }
}

/// Rigorous enclosure of `asin(y)` (principal branch) for any `f64` `y`.
///
/// Outside `[−1, 1]` the answer is the full principal range `[−π/2, π/2]` —
/// sound over-approximation, never a fabricated value.
#[must_use]
pub fn asin_enclosure(y: f64) -> (f64, f64) {
    asin_point_cached(y)
}

/// Rigorous f64 bracket for π (public: the ICP engine's periodicity
/// reasoning uses it).
#[must_use]
pub fn pi_bracket() -> (f64, f64) {
    let (lo, hi) = consts().pi.to_f64s();
    (lo, hi)
}

/// Rigorous f64 bracket for π/2.
#[must_use]
pub fn pi2_bracket() -> (f64, f64) {
    let (lo, hi) = consts().pi2.to_f64s();
    (lo, hi)
}

fn pi_f64_bracket() -> (f64, f64) {
    pi_bracket()
}

// =====================================================================
// Point-enclosure memoization (std only; no_std recomputes)
// =====================================================================

#[cfg(feature = "std")]
fn cache_get_or_insert(op: u8, x: f64, f: impl FnOnce(f64) -> (f64, f64)) -> (f64, f64) {
    use std::cell::RefCell;
    use std::collections::HashMap;
    thread_local! {
        static CACHE: RefCell<HashMap<(u8, u64), (f64, f64)>> =
            RefCell::new(HashMap::new());
    }
    let key = (op, x.to_bits());
    CACHE.with(|c| {
        let mut map = c.borrow_mut();
        if let Some(v) = map.get(&key) {
            return *v;
        }
        let v = f(x);
        // Bound the cache so a long-lived solver thread cannot grow it
        // without limit.
        if map.len() > 1 << 18 {
            map.clear();
        }
        map.insert(key, v);
        v
    })
}

#[cfg(feature = "std")]
fn exp_point_cached(x: f64) -> (f64, f64) {
    cache_get_or_insert(0, x, exp_point)
}
#[cfg(feature = "std")]
fn log_point_cached(x: f64) -> (f64, f64) {
    debug_assert!(x > 0.0);
    cache_get_or_insert(1, x, log_point)
}
#[cfg(feature = "std")]
fn sin_point_cached(x: f64) -> (f64, f64) {
    cache_get_or_insert(2, x, sin_point_raw)
}
#[cfg(feature = "std")]
fn cos_point_cached(x: f64) -> (f64, f64) {
    cache_get_or_insert(3, x, cos_point_raw)
}
#[cfg(feature = "std")]
fn atan_point_cached(x: f64) -> (f64, f64) {
    cache_get_or_insert(4, x, atan_point)
}
#[cfg(feature = "std")]
fn asin_point_cached(x: f64) -> (f64, f64) {
    // asin is the most expensive point enclosure on the contraction path
    // (a ~500-bit isqrt plus two atan series per call) and the ICP's
    // sin/cos contraction calls it twice per propagation of a Sin/Cos
    // node — overwhelmingly at repeat arguments while a box converges or
    // is re-propagated after `BranchInto`.  Measured on the t19 corpus
    // goal, uncached asin dominated the whole run.
    cache_get_or_insert(5, x, asin_point)
}

#[cfg(not(feature = "std"))]
fn exp_point_cached(x: f64) -> (f64, f64) {
    exp_point(x)
}
#[cfg(not(feature = "std"))]
fn log_point_cached(x: f64) -> (f64, f64) {
    log_point(x)
}
#[cfg(not(feature = "std"))]
fn sin_point_cached(x: f64) -> (f64, f64) {
    sin_point_raw(x)
}
#[cfg(not(feature = "std"))]
fn cos_point_cached(x: f64) -> (f64, f64) {
    cos_point_raw(x)
}
#[cfg(not(feature = "std"))]
fn atan_point_cached(x: f64) -> (f64, f64) {
    atan_point(x)
}
#[cfg(not(feature = "std"))]
fn asin_point_cached(x: f64) -> (f64, f64) {
    asin_point(x)
}

#[cfg(test)]
mod tests {
    use super::*;

    /// Compare against host libm with a generous but non-trivial margin:
    /// the enclosure must contain the libm value (libm is ~1ulp accurate)
    /// and must be tight to ~1e-12 relative.
    fn check_encloses(f: fn(f64) -> (f64, f64), reference: f64, x: f64, tol: f64) {
        let (lo, hi) = f(x);
        assert!(lo <= reference + tol, "lo {lo} > ref+tol for x={x}");
        assert!(hi >= reference - tol, "hi {hi} < ref-tol for x={x}");
        assert!(
            hi - lo < fmax(tol * 4.0, 1e-13),
            "bracket too wide for x={x}"
        );
    }

    #[test]
    #[allow(clippy::approx_constant)] // e as a test input, not a definition
    fn exp_enclosures() {
        for x in [
            -20.0f64,
            -7.3,
            -2.5,
            -1.0,
            -0.5,
            -0.01,
            0.0,
            0.01,
            0.5,
            1.0,
            2.7182818284,
            5.5,
            30.0,
            100.0,
            700.0,
        ] {
            check_encloses(
                exp_point_cached,
                x.exp(),
                x,
                1e-12 * x.exp().abs().max(1e-300),
            );
        }
        // Saturation.
        assert_eq!(exp_point(800.0).1, f64::INFINITY);
        assert!(exp_point(-800.0).1 < 1e-300);
    }

    #[test]
    #[allow(clippy::approx_constant)] // e as a test input, not a definition
    fn log_enclosures() {
        for x in [
            1e-300f64,
            1e-10,
            0.001,
            0.5,
            0.9999999,
            1.0,
            1.0000001,
            2.0,
            2.718281828459045,
            10.0,
            1e10,
            1e300,
        ] {
            let r = x.ln();
            check_encloses(log_point_cached, r, x, 1e-12 * r.abs().max(1.0));
        }
    }

    #[test]
    #[allow(clippy::approx_constant)] // π as a test input, not a definition
    fn sin_cos_enclosures() {
        for x in [
            -100.0f64, -10.0, -3.14159, -1.5, -0.5, -1e-8, 0.0, 1e-8, 0.3, 1.0, 1.5, 3.14159, 4.0,
            10.0, 100.0, 1e6, 1e10,
        ] {
            check_encloses(sin_point_cached, x.sin(), x, 1e-11);
            check_encloses(cos_point_cached, x.cos(), x, 1e-11);
        }
    }

    #[test]
    fn atan_enclosures() {
        for x in [
            -1e10f64, -100.0, -3.0, -1.5, -1.0, -0.5, -1e-8, 0.0, 1e-8, 0.5, 1.0, 1.5, 3.0, 100.0,
            1e10,
        ] {
            check_encloses(atan_point_cached, x.atan(), x, 1e-11);
        }
    }

    #[test]
    fn sin_interval_monotone_and_full() {
        // sin on [0, π/2] is exactly 0..1 (endpoints).
        let s = DI { lo: 0.0, hi: 0.7 }.sin();
        assert!(s.lo <= 0.644217687237691 && s.hi >= 0.644217687237691);
        // An interval containing π/2 reaches 1.
        let s = DI { lo: 1.0, hi: 2.0 }.sin();
        assert!(s.hi >= 1.0 && s.lo <= 0.8414709848078965);
        // Wide interval → full range.
        let s = DI {
            lo: -10.0,
            hi: 10.0,
        }
        .sin();
        assert_eq!((s.lo, s.hi), (-1.0, 1.0));
    }

    #[test]
    fn sqrt_interval() {
        let s = DI { lo: 2.0, hi: 9.0 }.sqrt();
        assert!(s.lo <= 2.0_f64.sqrt() && s.hi >= 3.0);
        // Totalization: negative box → point 0.
        let s = DI { lo: -5.0, hi: -1.0 }.sqrt();
        assert_eq!((s.lo, s.hi), (0.0, 0.0));
        // Straddling: sqrt([-4, 9]) = [0, 3].
        let s = DI { lo: -4.0, hi: 9.0 }.sqrt();
        assert_eq!(s.lo, 0.0);
        assert!(s.hi >= 3.0);
    }

    #[test]
    fn log_interval_totalization() {
        let l = DI { lo: -1.0, hi: 10.0 }.log();
        assert_eq!(l.lo, f64::NEG_INFINITY);
        assert!(l.hi >= 10.0_f64.ln());
        let l = DI { lo: -5.0, hi: -1.0 }.log();
        assert_eq!((l.lo, l.hi), (f64::NEG_INFINITY, f64::NEG_INFINITY));
    }

    #[test]
    fn outward_mul_div() {
        let a = DI { lo: -2.0, hi: 3.0 };
        let b = DI { lo: 4.0, hi: 5.0 };
        let m = a.mul(&b);
        assert!(m.lo <= -10.0 && m.hi >= 15.0);
        // Divisor containing zero → whole line.
        let d = a.div(&DI { lo: -1.0, hi: 1.0 });
        assert_eq!(d, DI::RN);
        // Sound divisor: [1,2] / [2,3] ⊆ [1/3, 1].
        let q = DI::point(1.0).div(&DI { lo: 2.0, hi: 3.0 });
        assert!(q.lo <= 1.0 / 3.0 && q.hi >= 1.0 / 2.0);
    }

    #[test]
    fn asin_enclosures() {
        for y in [
            -0.9999f64, -1.0, -0.5, -0.1, -1e-9, 0.0, 1e-9, 0.1, 0.5, 0.9, 0.999999, 1.0,
        ] {
            let r = y.asin();
            let (lo, hi) = asin_enclosure(y);
            assert!(lo <= r + 1e-12, "asin({y}): lo {lo} > {r}");
            assert!(hi >= r - 1e-12, "asin({y}): hi {hi} < {r}");
            assert!(hi - lo < 1e-11, "asin({y}) bracket too wide: {lo}..{hi}");
        }
        // Out of range: full principal range, not a fabrication.
        let (lo, hi) = asin_enclosure(2.0);
        assert!(lo <= -1.57 && hi >= 1.57);
    }

    #[test]
    fn rational_dyadic_matches_the_reducing_constructor() {
        // The dyadic fast path must produce BIT-FOR-BIT the same reduced
        // fraction as the gcd-reducing `BigRational::new` — it replaced
        // that constructor on the δ-witness hot path (sin/cos/exp/log/atan
        // enclosures), where the big-integer gcd + divisions dominated
        // the runtime profile.
        let mut n: i64 = -1;
        while n <= 1 {
            let num = BigInt::from(n);
            for frac_bits in [0u64, 1, 7, 63, 64, 100, FRAC] {
                let fast = rational_dyadic(num.clone(), frac_bits);
                let slow = BigRational::new(num.clone(), BigInt::one() << frac_bits);
                assert_eq!(fast, slow, "num={n} frac={frac_bits}");
            }
            n += 1;
        }
        // Odd, even, heavily-even and zero numerators at scale.
        for num in [
            1_i64 << 40,
            (1_i64 << 40) + 1,
            -(1_i64 << 40) - 1,
            (1_i64 << 40) * 5,
            0,
        ] {
            let big = BigInt::from(num);
            for frac_bits in [1u64, 41, 42, FRAC, FRAC + 40] {
                let fast = rational_dyadic(big.clone(), frac_bits);
                let slow = BigRational::new(big.clone(), BigInt::one() << frac_bits);
                assert_eq!(fast, slow, "num={num} frac={frac_bits}");
            }
        }
    }

    #[test]
    fn pi_bracket_sane() {
        let (lo, hi) = pi_f64_bracket();
        // The rational bracket strictly contains π, but at f64 granularity it
        // may collapse onto the f64 neighbour of π, so allow equality.
        assert!(lo <= core::f64::consts::PI && hi >= core::f64::consts::PI);
        assert!(hi - lo < 1e-14);
    }
}
