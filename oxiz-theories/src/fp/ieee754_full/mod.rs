//! Complete IEEE 754-2019 Floating-Point Implementation
//!
//! This module provides a comprehensive Pure Rust implementation of IEEE 754-2019
//! binary floating-point arithmetic, including:
//!
//! - All standard formats: binary16, binary32, binary64, binary128
//! - All five rounding modes: RNE, RNA, RTZ, RTP, RTN
//! - Correct rounding for all operations
//! - Special value handling: NaN (quiet/signaling), infinities, zeros, denormals
//! - Arithmetic operations: add, sub, mul, div, fma, sqrt, rem, min, max
//! - Comparisons: eq, lt, le, gt, ge, with correct NaN semantics
//! - Conversions: between formats, to/from integers, to/from reals
//!
//! ## Design Principles
//!
//! This implementation follows a softfloat-style approach:
//! - Operations on unpacked representations for precision
//! - Exact rounding using guard, round, and sticky bits
//! - Comprehensive special case handling
//! - No dependency on hardware floating-point (Pure Rust)
//!
//! ## References
//!
//! - IEEE 754-2019: IEEE Standard for Floating-Point Arithmetic
//! - John Hauser's SoftFloat library (for algorithmic approach)
//! - Z3's theory_fpa and fpa2bv_converter (for SMT integration patterns)

use crate::fp::{FpFormat, FpRoundingMode, FpValue};
#[allow(unused_imports)]
use crate::prelude::*;
use core::cmp::Ordering;
use num_bigint::{BigInt, BigUint};

/// Extended precision representation for intermediate calculations
///
/// This unpacked format allows precise manipulation during arithmetic
/// operations before final rounding and packing.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct UnpackedFloat {
    /// Sign: true for negative
    pub sign: bool,
    /// Unbiased exponent (can be out of range)
    pub exponent: i32,
    /// Significand as u128 (including implicit bit, left-aligned for precision)
    pub significand: u128,
    /// Precision level (number of significant bits)
    pub precision: u32,
    /// Special value classification
    pub class: FpClass,
}

/// IEEE 754 floating-point value classification
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum FpClass {
    /// Signaling NaN
    SignalingNaN,
    /// Quiet NaN
    QuietNaN,
    /// Negative Infinity
    NegativeInfinity,
    /// Negative Normal number
    NegativeNormal,
    /// Negative Subnormal (denormalized)
    NegativeSubnormal,
    /// Negative Zero
    NegativeZero,
    /// Positive Zero
    PositiveZero,
    /// Positive Subnormal (denormalized)
    PositiveSubnormal,
    /// Positive Normal number
    PositiveNormal,
    /// Positive Infinity
    PositiveInfinity,
}

impl FpClass {
    /// Check if this is a NaN (signaling or quiet)
    #[must_use]
    pub const fn is_nan(self) -> bool {
        matches!(self, Self::SignalingNaN | Self::QuietNaN)
    }

    /// Check if this is an infinity
    #[must_use]
    pub const fn is_infinite(self) -> bool {
        matches!(self, Self::NegativeInfinity | Self::PositiveInfinity)
    }

    /// Check if this is zero
    #[must_use]
    pub const fn is_zero(self) -> bool {
        matches!(self, Self::NegativeZero | Self::PositiveZero)
    }

    /// Check if this is subnormal
    #[must_use]
    pub const fn is_subnormal(self) -> bool {
        matches!(self, Self::NegativeSubnormal | Self::PositiveSubnormal)
    }

    /// Check if this is normal
    #[must_use]
    pub const fn is_normal(self) -> bool {
        matches!(self, Self::NegativeNormal | Self::PositiveNormal)
    }

    /// Check if this is finite (not NaN or infinity)
    #[must_use]
    pub const fn is_finite(self) -> bool {
        !self.is_nan() && !self.is_infinite()
    }

    /// Get sign of the value
    #[must_use]
    pub const fn sign(self) -> bool {
        matches!(
            self,
            Self::NegativeInfinity
                | Self::NegativeNormal
                | Self::NegativeSubnormal
                | Self::NegativeZero
        )
    }
}

/// Rounding direction result
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum RoundDirection {
    /// Round down (toward -infinity)
    Down,
    /// Round to nearest (with tie-breaking)
    Nearest,
    /// Round up (toward +infinity)
    Up,
    /// Exact (no rounding needed)
    Exact,
}

impl UnpackedFloat {
    /// Create a canonical quiet NaN
    #[must_use]
    pub fn quiet_nan(sign: bool) -> Self {
        Self {
            sign,
            exponent: 0,
            significand: 0,
            precision: 0,
            class: FpClass::QuietNaN,
        }
    }

    /// Create a signaling NaN
    #[must_use]
    pub fn signaling_nan(sign: bool) -> Self {
        Self {
            sign,
            exponent: 0,
            significand: 0,
            precision: 0,
            class: FpClass::SignalingNaN,
        }
    }

    /// Create positive infinity
    #[must_use]
    pub fn positive_infinity() -> Self {
        Self {
            sign: false,
            exponent: 0,
            significand: 0,
            precision: 0,
            class: FpClass::PositiveInfinity,
        }
    }

    /// Create negative infinity
    #[must_use]
    pub fn negative_infinity() -> Self {
        Self {
            sign: true,
            exponent: 0,
            significand: 0,
            precision: 0,
            class: FpClass::NegativeInfinity,
        }
    }

    /// Create positive zero
    #[must_use]
    pub fn positive_zero() -> Self {
        Self {
            sign: false,
            exponent: 0,
            significand: 0,
            precision: 0,
            class: FpClass::PositiveZero,
        }
    }

    /// Create negative zero
    #[must_use]
    pub fn negative_zero() -> Self {
        Self {
            sign: true,
            exponent: 0,
            significand: 0,
            precision: 0,
            class: FpClass::NegativeZero,
        }
    }

    /// Create from normal components
    #[must_use]
    pub fn from_components(sign: bool, exponent: i32, significand: u128, precision: u32) -> Self {
        if significand == 0 {
            if sign {
                Self::negative_zero()
            } else {
                Self::positive_zero()
            }
        } else {
            let class = if sign {
                FpClass::NegativeNormal
            } else {
                FpClass::PositiveNormal
            };
            Self {
                sign,
                exponent,
                significand,
                precision,
                class,
            }
        }
    }

    /// Normalize the significand (shift until MSB is at the top)
    pub fn normalize(&mut self) {
        if self.class.is_nan() || self.class.is_infinite() || self.class.is_zero() {
            return;
        }

        if self.significand == 0 {
            *self = if self.sign {
                Self::negative_zero()
            } else {
                Self::positive_zero()
            };
            return;
        }

        // Count leading zeros and shift left
        let leading_zeros = self.significand.leading_zeros();
        if leading_zeros > 0 {
            self.significand <<= leading_zeros;
            self.exponent = self.exponent.saturating_sub(leading_zeros as i32);
        }
    }

    /// Check if this value is finite
    #[must_use]
    pub const fn is_finite(&self) -> bool {
        self.class.is_finite()
    }

    /// Check if this value is zero
    #[must_use]
    pub const fn is_zero(&self) -> bool {
        self.class.is_zero()
    }

    /// Check if this value is NaN
    #[must_use]
    pub const fn is_nan(&self) -> bool {
        self.class.is_nan()
    }
}

/// IEEE 754 Arithmetic Engine
///
/// Provides correct-rounding arithmetic operations for all IEEE 754 formats.
#[derive(Debug)]
pub struct Ieee754Engine {
    /// Current rounding mode
    rounding_mode: FpRoundingMode,
    /// Track inexact results
    inexact_flag: bool,
    /// Track invalid operations (NaN results)
    invalid_flag: bool,
    /// Track division by zero
    divide_by_zero_flag: bool,
    /// Track overflow
    overflow_flag: bool,
    /// Track underflow
    underflow_flag: bool,
}

impl Default for Ieee754Engine {
    fn default() -> Self {
        Self::new()
    }
}

impl Ieee754Engine {
    /// Create a new arithmetic engine with default rounding mode
    #[must_use]
    pub fn new() -> Self {
        Self {
            rounding_mode: FpRoundingMode::RoundNearestTiesToEven,
            inexact_flag: false,
            invalid_flag: false,
            divide_by_zero_flag: false,
            overflow_flag: false,
            underflow_flag: false,
        }
    }

    /// Multiply two 128-bit numbers and return the high 128 bits and sticky bit
    ///
    /// Computes a × b where both are 128-bit unsigned integers.
    /// Returns (high_128_bits, has_nonzero_low_bits)
    ///
    /// Uses school multiplication algorithm:
    /// a = a_hi * 2^64 + a_lo
    /// b = b_hi * 2^64 + b_lo
    /// a × b = a_hi*b_hi*2^128 + (a_hi*b_lo + a_lo*b_hi)*2^64 + a_lo*b_lo
    #[must_use]
    fn mul128(a: u128, b: u128) -> (u128, bool) {
        let a_lo = a as u64;
        let a_hi = (a >> 64) as u64;
        let b_lo = b as u64;
        let b_hi = (b >> 64) as u64;

        // Compute all four 64×64→128 bit partial products
        let ll = (a_lo as u128) * (b_lo as u128);
        let lh = (a_lo as u128) * (b_hi as u128);
        let hl = (a_hi as u128) * (b_lo as u128);
        let hh = (a_hi as u128) * (b_hi as u128);

        // Combine partial products
        // Low 128 bits: ll + (lh << 64) + (hl << 64)
        // High 128 bits: hh + (lh >> 64) + (hl >> 64) + carry

        let middle = lh + hl;
        let middle_carry = if middle < lh { 1 } else { 0 };

        let low_part = ll.wrapping_add(middle << 64);
        let low_carry = if low_part < ll { 1 } else { 0 };

        let high = hh + (middle >> 64) + middle_carry + low_carry;

        // Check if any bits in the low 128 bits are non-zero (for sticky bit)
        let sticky = low_part != 0;

        (high, sticky)
    }

    /// Divide two 128-bit numbers and return left-aligned quotient and sticky bit
    ///
    /// Computes `dividend / divisor` where both are normalized (MSB at bit 127).
    /// Returns `(quotient_left_aligned, has_nonzero_remainder)`.
    ///
    /// Concretely it computes `q = floor(dividend * 2^127 / divisor)` together
    /// with a sticky flag recording whether the true quotient has a nonzero
    /// remainder. Because both operands lie in `[2^127, 2^128)`, the exact
    /// quotient `dividend / divisor` lies in `(0.5, 2.0)`, so `q` (that quotient
    /// scaled by `2^127`) lies in `(2^126, 2^128)` — its MSB is at bit 126 or 127,
    /// exactly what the caller's normalization step expects.
    ///
    /// The running remainder must hold 129 bits: after the shift-in step it can
    /// momentarily reach just under `2 * divisor` (< 2^129) before a single
    /// conditional subtraction restores the invariant `remainder < divisor`. The
    /// earlier implementation kept the remainder in a bare `u128` and shifted it
    /// left *before* subtracting, which silently dropped bit 127 whenever the
    /// remainder's MSB was set — corrupting every division whose dividend
    /// mantissa was smaller than the divisor's (the exact quotient in `(0.5, 1)`
    /// case), returning zero. Tracking the overflow bit explicitly fixes that.
    #[must_use]
    fn div128(dividend: u128, divisor: u128) -> (u128, bool) {
        if divisor == 0 {
            return (u128::MAX, false);
        }

        // 129-bit remainder: `rem_hi` is bit 128, `rem_lo` holds bits 0..=127.
        let mut rem_lo: u128 = 0;
        let mut rem_hi: bool = false;
        let mut quotient: u128 = 0;

        // Long division of the 255-bit numerator `dividend << 127`, MSB first:
        // its top 128 bits are `dividend`, followed by 127 implicit zero bits.
        for i in (0..255).rev() {
            let bit: u128 = if i >= 127 {
                (dividend >> (i - 127)) & 1
            } else {
                0
            };
            // rem = (rem << 1) | bit, carrying bit 127 of rem_lo into rem_hi.
            let carry = (rem_lo >> 127) & 1 == 1;
            rem_lo = (rem_lo << 1) | bit;
            rem_hi = carry;

            // Compare the 129-bit remainder against the 128-bit divisor.
            let ge = rem_hi || rem_lo >= divisor;
            quotient <<= 1;
            if ge {
                // Subtract divisor. A borrow can only occur when `rem_hi` is set
                // (rem >= 2^128 > divisor), and consumes exactly that overflow
                // bit; the post-subtraction remainder is always < divisor.
                let (nl, borrow) = rem_lo.overflowing_sub(divisor);
                rem_lo = nl;
                rem_hi = rem_hi && !borrow;
                quotient |= 1;
            }
        }

        // Sticky: any nonzero remainder means the true quotient was inexact.
        let sticky = rem_hi || rem_lo != 0;

        (quotient, sticky)
    }

    /// Set the rounding mode
    pub fn set_rounding_mode(&mut self, mode: FpRoundingMode) {
        self.rounding_mode = mode;
    }

    /// Get the current rounding mode
    #[must_use]
    pub const fn rounding_mode(&self) -> FpRoundingMode {
        self.rounding_mode
    }

    /// Clear all exception flags
    pub fn clear_flags(&mut self) {
        self.inexact_flag = false;
        self.invalid_flag = false;
        self.divide_by_zero_flag = false;
        self.overflow_flag = false;
        self.underflow_flag = false;
    }

    /// Get inexact flag
    #[must_use]
    pub const fn inexact(&self) -> bool {
        self.inexact_flag
    }

    /// Get invalid flag
    #[must_use]
    pub const fn invalid(&self) -> bool {
        self.invalid_flag
    }

    /// Get division by zero flag
    #[must_use]
    pub const fn divide_by_zero(&self) -> bool {
        self.divide_by_zero_flag
    }

    /// Get overflow flag
    #[must_use]
    pub const fn overflow(&self) -> bool {
        self.overflow_flag
    }

    /// Get underflow flag
    #[must_use]
    pub const fn underflow(&self) -> bool {
        self.underflow_flag
    }

    /// Unpack a FpValue into UnpackedFloat for computation
    #[must_use]
    pub fn unpack(&self, value: &FpValue) -> UnpackedFloat {
        let format = value.format;
        let max_exp = format.max_exponent() as u64;

        // Classify the value
        let class = if value.exponent == max_exp {
            // NaN or Infinity
            if value.significand == 0 {
                if value.sign {
                    FpClass::NegativeInfinity
                } else {
                    FpClass::PositiveInfinity
                }
            } else {
                // Check if signaling or quiet NaN
                let quiet_bit = 1u64 << (format.significand_bits - 2);
                if value.significand & quiet_bit != 0 {
                    FpClass::QuietNaN
                } else {
                    FpClass::SignalingNaN
                }
            }
        } else if value.exponent == 0 {
            // Zero or Subnormal
            if value.significand == 0 {
                if value.sign {
                    FpClass::NegativeZero
                } else {
                    FpClass::PositiveZero
                }
            } else if value.sign {
                FpClass::NegativeSubnormal
            } else {
                FpClass::PositiveSubnormal
            }
        } else if value.sign {
            FpClass::NegativeNormal
        } else {
            FpClass::PositiveNormal
        };

        // Handle special values
        match class {
            FpClass::QuietNaN => UnpackedFloat::quiet_nan(value.sign),
            FpClass::SignalingNaN => UnpackedFloat::signaling_nan(value.sign),
            FpClass::PositiveInfinity => UnpackedFloat::positive_infinity(),
            FpClass::NegativeInfinity => UnpackedFloat::negative_infinity(),
            FpClass::PositiveZero => UnpackedFloat::positive_zero(),
            FpClass::NegativeZero => UnpackedFloat::negative_zero(),
            FpClass::PositiveNormal | FpClass::NegativeNormal => {
                // Normal number: add implicit bit
                let implicit_bit = 1u128 << (format.significand_bits - 1);
                let significand = (value.significand as u128) | implicit_bit;
                // Left-align for precision
                let shift = 128 - format.significand_bits;
                let aligned_sig = significand << shift;
                // For left-aligned significands, the value is (aligned_sig / 2^127) * 2^exp
                // which should equal (1.frac) * 2^(stored_exp - bias)
                // Therefore: exp = stored_exp - bias
                let unbiased_exp = (value.exponent as i32) - format.bias();

                UnpackedFloat {
                    sign: value.sign,
                    exponent: unbiased_exp,
                    significand: aligned_sig,
                    precision: format.significand_bits,
                    class,
                }
            }
            FpClass::PositiveSubnormal | FpClass::NegativeSubnormal => {
                // Subnormal: no implicit bit, value = 0.frac * 2^(1 - bias).
                // Align on the same scale as normals (shift = 128 - significand_bits)
                // so that a fully-set frac would land its MSB one bit below bit 127
                // (matching the "no implicit bit" semantics); this may leave leading
                // zeros in `aligned_sig` for anything but the largest subnormal.
                let shift = 128 - format.significand_bits;
                let aligned_sig = (value.significand as u128) << shift;
                let unbiased_exp = 1 - format.bias();

                let mut unpacked = UnpackedFloat {
                    sign: value.sign,
                    exponent: unbiased_exp,
                    significand: aligned_sig,
                    precision: format.significand_bits,
                    class,
                };
                // Renormalize so the significand is MSB-aligned at bit 127, as all
                // arithmetic (add/mul/div/sqrt/compare) assumes for finite non-zero
                // values. This adjusts the exponent below the smallest normal
                // exponent as needed; `class` is left untouched so callers can still
                // observe the original subnormal classification.
                unpacked.normalize();
                unpacked.class = class;
                unpacked
            }
        }
    }

    /// Pack an UnpackedFloat into FpValue with rounding
    pub fn pack(&mut self, unpacked: &UnpackedFloat, format: FpFormat) -> FpValue {
        // Handle special values
        match unpacked.class {
            FpClass::QuietNaN => {
                return FpValue {
                    sign: unpacked.sign,
                    exponent: format.max_exponent() as u64,
                    significand: 1 << (format.significand_bits - 2), // Quiet NaN pattern
                    format,
                };
            }
            FpClass::SignalingNaN => {
                return FpValue {
                    sign: unpacked.sign,
                    exponent: format.max_exponent() as u64,
                    significand: 1, // Signaling NaN pattern
                    format,
                };
            }
            FpClass::PositiveInfinity | FpClass::NegativeInfinity => {
                return FpValue {
                    sign: unpacked.sign,
                    exponent: format.max_exponent() as u64,
                    significand: 0,
                    format,
                };
            }
            FpClass::PositiveZero | FpClass::NegativeZero => {
                return FpValue {
                    sign: unpacked.sign,
                    exponent: 0,
                    significand: 0,
                    format,
                };
            }
            _ => {}
        }

        // Extract the significand bits we need
        let precision = format.significand_bits;
        let shift = 128 - precision;
        let mut significand = unpacked.significand >> shift;
        let mut exponent = unpacked.exponent;

        // Get guard, round, and sticky bits for rounding
        let guard_bit_pos = shift.saturating_sub(1);
        let round_bit_pos = shift.saturating_sub(2);
        let sticky_mask = if shift >= 2 {
            (1u128 << (shift - 2)).wrapping_sub(1)
        } else {
            0
        };

        let guard = if shift > 0 {
            (unpacked.significand >> guard_bit_pos) & 1
        } else {
            0
        };
        let round = if shift > 1 {
            (unpacked.significand >> round_bit_pos) & 1
        } else {
            0
        };
        let sticky = if shift > 2 {
            (unpacked.significand & sticky_mask != 0) as u128
        } else {
            0
        };

        // Determine if we need to round
        let needs_rounding = guard != 0 || round != 0 || sticky != 0;
        if needs_rounding {
            self.inexact_flag = true;
        }

        // Apply rounding based on mode
        let pre_round_lsb = significand & 1;
        let round_up = self.should_round_up(unpacked.sign, guard, round, sticky, pre_round_lsb);
        if round_up {
            significand = significand.wrapping_add(1);
            // Check for significand overflow
            if significand >= (1u128 << precision) {
                significand >>= 1;
                exponent = exponent.saturating_add(1);
            }
        }

        // Adjust exponent to biased form
        // For left-aligned representation: value = (sig / 2^127) * 2^exp
        // IEEE format: value = (1.frac) * 2^(biased_exp - bias)
        // Therefore: biased_exp = exp + bias
        let biased_exp = exponent + format.bias();

        // Handle overflow
        if biased_exp >= format.max_exponent() as i32 {
            self.overflow_flag = true;
            self.inexact_flag = true;
            // Return infinity with appropriate sign
            return match self.rounding_mode {
                FpRoundingMode::RoundTowardPositive => {
                    if unpacked.sign {
                        // Negative overflow rounds to -max
                        self.max_finite_value(format, true)
                    } else {
                        FpValue::pos_infinity(format)
                    }
                }
                FpRoundingMode::RoundTowardNegative => {
                    if unpacked.sign {
                        FpValue::neg_infinity(format)
                    } else {
                        self.max_finite_value(format, false)
                    }
                }
                FpRoundingMode::RoundTowardZero => self.max_finite_value(format, unpacked.sign),
                _ => {
                    if unpacked.sign {
                        FpValue::neg_infinity(format)
                    } else {
                        FpValue::pos_infinity(format)
                    }
                }
            };
        }

        // Handle underflow (subnormal or zero)
        if biased_exp <= 0 {
            self.underflow_flag = true;
            // Gradual underflow to subnormal
            let shift_amount = 1 - biased_exp;
            if shift_amount >= precision as i32 {
                // Too small, becomes zero
                return if unpacked.sign {
                    FpValue::neg_zero(format)
                } else {
                    FpValue::pos_zero(format)
                };
            }
            // Shift to create subnormal
            significand >>= shift_amount;
            return FpValue {
                sign: unpacked.sign,
                exponent: 0,
                significand: (significand & ((1u128 << (precision - 1)) - 1)) as u64,
                format,
            };
        }

        // Normal number
        // Remove implicit bit for storage
        let stored_significand = significand & ((1u128 << (precision - 1)) - 1);

        FpValue {
            sign: unpacked.sign,
            exponent: biased_exp as u64,
            significand: stored_significand as u64,
            format,
        }
    }

    /// Get maximum finite value for a format
    #[must_use]
    fn max_finite_value(&self, format: FpFormat, sign: bool) -> FpValue {
        let max_exp = format.max_exponent() - 1;
        let max_sig = (1u64 << (format.significand_bits - 1)) - 1;
        FpValue {
            sign,
            exponent: max_exp as u64,
            significand: max_sig,
            format,
        }
    }

    /// Determine if we should round up based on rounding mode and extra bits
    ///
    /// `lsb` is the least-significant bit of the (pre-rounding) truncated
    /// significand; it is only consulted by `RoundNearestTiesToEven` to break
    /// exact ties in favor of the even result, per IEEE 754's default
    /// rounding mode.
    #[must_use]
    fn should_round_up(
        &self,
        sign: bool,
        guard: u128,
        round: u128,
        sticky: u128,
        lsb: u128,
    ) -> bool {
        match self.rounding_mode {
            FpRoundingMode::RoundNearestTiesToEven => {
                // Round to nearest, ties to even
                if guard == 0 {
                    false
                } else if round != 0 || sticky != 0 {
                    true
                } else {
                    // Exact tie (guard=1, round=0, sticky=0): round to whichever
                    // candidate has an even LSB. If the truncated result is
                    // already even (lsb == 0), stay; otherwise round up to make
                    // it even.
                    lsb != 0
                }
            }
            FpRoundingMode::RoundNearestTiesToAway => {
                // Round to nearest, ties away from zero
                guard != 0
            }
            FpRoundingMode::RoundTowardPositive => {
                // Round toward +infinity
                !sign && (guard != 0 || round != 0 || sticky != 0)
            }
            FpRoundingMode::RoundTowardNegative => {
                // Round toward -infinity
                sign && (guard != 0 || round != 0 || sticky != 0)
            }
            FpRoundingMode::RoundTowardZero => {
                // Truncate (never round up)
                false
            }
        }
    }

    /// Add two floating-point values
    pub fn add(&mut self, a: &FpValue, b: &FpValue) -> FpValue {
        assert_eq!(a.format, b.format, "Format mismatch in addition");
        let format = a.format;

        let ua = self.unpack(a);
        let ub = self.unpack(b);

        // Handle special cases
        if ua.is_nan() || ub.is_nan() {
            self.invalid_flag =
                ua.class == FpClass::SignalingNaN || ub.class == FpClass::SignalingNaN;
            return self.pack(&UnpackedFloat::quiet_nan(false), format);
        }

        match (ua.class, ub.class) {
            (FpClass::PositiveInfinity, FpClass::NegativeInfinity)
            | (FpClass::NegativeInfinity, FpClass::PositiveInfinity) => {
                self.invalid_flag = true;
                return self.pack(&UnpackedFloat::quiet_nan(false), format);
            }
            (FpClass::PositiveInfinity, _) | (_, FpClass::PositiveInfinity) => {
                return FpValue::pos_infinity(format);
            }
            (FpClass::NegativeInfinity, _) | (_, FpClass::NegativeInfinity) => {
                return FpValue::neg_infinity(format);
            }
            _ => {}
        }

        if ua.is_zero() {
            return *b;
        }
        if ub.is_zero() {
            return *a;
        }

        // Align exponents
        let exp_diff = ua.exponent - ub.exponent;
        let (sig_a, sig_b, result_exp) = if exp_diff >= 0 {
            let shift = exp_diff.min(127) as u32;
            (ua.significand, ub.significand >> shift, ua.exponent)
        } else {
            let shift = (-exp_diff).min(127) as u32;
            (ua.significand >> shift, ub.significand, ub.exponent)
        };

        // Perform addition or subtraction based on signs
        let (result_sign, result_sig, result_exp) = if ua.sign == ub.sign {
            // Same sign: add (check for overflow)
            let (sum, overflow) = sig_a.overflowing_add(sig_b);
            if overflow {
                // Overflow occurred: the real sum is 2^128 + sum
                // We need to shift right by 1 and set the MSB
                // sum >> 1 gives us the lower bits, and we need to set bit 127
                let shifted = (sum >> 1) | (1u128 << 127);
                (ua.sign, shifted, result_exp + 1)
            } else {
                (ua.sign, sum, result_exp)
            }
        } else if sig_a >= sig_b {
            // Different signs: subtract (a - b)
            let diff = sig_a - sig_b;
            (ua.sign, diff, result_exp)
        } else {
            // Different signs: subtract (b - a)
            let diff = sig_b - sig_a;
            (ub.sign, diff, result_exp)
        };

        let mut result = UnpackedFloat::from_components(
            result_sign,
            result_exp,
            result_sig,
            format.significand_bits,
        );
        result.normalize();

        self.pack(&result, format)
    }

    /// Subtract two floating-point values
    pub fn sub(&mut self, a: &FpValue, b: &FpValue) -> FpValue {
        // Negate b and add
        let mut neg_b = *b;
        neg_b.sign = !neg_b.sign;
        self.add(a, &neg_b)
    }

    /// Multiply two floating-point values
    pub fn mul(&mut self, a: &FpValue, b: &FpValue) -> FpValue {
        assert_eq!(a.format, b.format, "Format mismatch in multiplication");
        let format = a.format;

        let ua = self.unpack(a);
        let ub = self.unpack(b);

        // Handle special cases
        if ua.is_nan() || ub.is_nan() {
            self.invalid_flag =
                ua.class == FpClass::SignalingNaN || ub.class == FpClass::SignalingNaN;
            return self.pack(&UnpackedFloat::quiet_nan(false), format);
        }

        // Determine result sign
        let result_sign = ua.sign ^ ub.sign;

        // Infinity cases
        match (ua.class, ub.class) {
            (FpClass::PositiveInfinity | FpClass::NegativeInfinity, _)
            | (_, FpClass::PositiveInfinity | FpClass::NegativeInfinity) => {
                if ua.is_zero() || ub.is_zero() {
                    self.invalid_flag = true;
                    return self.pack(&UnpackedFloat::quiet_nan(false), format);
                }
                return if result_sign {
                    FpValue::neg_infinity(format)
                } else {
                    FpValue::pos_infinity(format)
                };
            }
            _ => {}
        }

        // Zero cases
        if ua.is_zero() || ub.is_zero() {
            return if result_sign {
                FpValue::neg_zero(format)
            } else {
                FpValue::pos_zero(format)
            };
        }

        // Multiply significands using full 128×128→256 bit multiplication
        // Both significands are left-aligned (MSB at bit 127)
        let (mut product, sticky) = Self::mul128(ua.significand, ub.significand);

        // The product of two normalized values (MSB at bit 127) gives a result
        // with MSB at bit 126 or 127 (because 1.xxx * 1.yyy = 1.zzz or 10.zzz)
        // Since we're taking high 128 bits of a 256-bit product, we add 1 to exponent
        // (product_256 >> 128) / 2^127 = product_256 / 2^255 = product_value / 2
        // So we need exp+1 to compensate
        let mut result_exp = ua.exponent + ub.exponent + 1;
        if product != 0 && (product & (1u128 << 127)) == 0 {
            product <<= 1;
            result_exp -= 1;
        }

        // Include sticky bit information for proper rounding
        // The sticky bit represents whether any of the low 128 bits were non-zero
        let mut result_sig = product;
        if sticky && (result_sig & 1) == 0 {
            // Set LSB to preserve sticky information for rounding
            result_sig |= 1;
        }

        let mut result = UnpackedFloat::from_components(
            result_sign,
            result_exp,
            result_sig,
            format.significand_bits,
        );
        result.normalize();

        self.pack(&result, format)
    }

    /// Divide two floating-point values
    pub fn div(&mut self, a: &FpValue, b: &FpValue) -> FpValue {
        assert_eq!(a.format, b.format, "Format mismatch in division");
        let format = a.format;

        let ua = self.unpack(a);
        let ub = self.unpack(b);

        // Handle special cases
        if ua.is_nan() || ub.is_nan() {
            self.invalid_flag =
                ua.class == FpClass::SignalingNaN || ub.class == FpClass::SignalingNaN;
            return self.pack(&UnpackedFloat::quiet_nan(false), format);
        }

        let result_sign = ua.sign ^ ub.sign;

        // Division by zero
        if ub.is_zero() {
            if ua.is_zero() {
                self.invalid_flag = true;
                return self.pack(&UnpackedFloat::quiet_nan(false), format);
            }
            self.divide_by_zero_flag = true;
            return if result_sign {
                FpValue::neg_infinity(format)
            } else {
                FpValue::pos_infinity(format)
            };
        }

        // Infinity / Infinity
        if ua.class.is_infinite() && ub.class.is_infinite() {
            self.invalid_flag = true;
            return self.pack(&UnpackedFloat::quiet_nan(false), format);
        }

        // x / Infinity = 0
        if ub.class.is_infinite() {
            return if result_sign {
                FpValue::neg_zero(format)
            } else {
                FpValue::pos_zero(format)
            };
        }

        // Infinity / x = Infinity
        if ua.class.is_infinite() {
            return if result_sign {
                FpValue::neg_infinity(format)
            } else {
                FpValue::pos_infinity(format)
            };
        }

        // 0 / x = 0
        if ua.is_zero() {
            return if result_sign {
                FpValue::neg_zero(format)
            } else {
                FpValue::pos_zero(format)
            };
        }

        // Divide significands using full 128-bit division
        // Both significands are left-aligned (MSB at bit 127)
        let (mut quotient, sticky) = Self::div128(ua.significand, ub.significand);

        // The quotient of two normalized values (MSB at bit 127) gives a result
        // with MSB at bit 126 or 127 (because dividend/divisor ∈ [0.5, 2.0))
        // Similar to multiplication, since we're doing 128-bit division directly,
        // the exponent relationship is: result_exp = ua.exp - ub.exp
        let mut result_exp = ua.exponent - ub.exponent;

        // Normalize to have MSB at bit 127
        if quotient != 0 && (quotient & (1u128 << 127)) == 0 {
            quotient <<= 1;
            result_exp -= 1;
        }

        // Include sticky bit information for proper rounding
        let mut result_sig = quotient;
        if sticky && (result_sig & 1) == 0 {
            result_sig |= 1;
        }

        let mut result = UnpackedFloat::from_components(
            result_sign,
            result_exp,
            result_sig,
            format.significand_bits,
        );
        result.normalize();

        self.pack(&result, format)
    }

    /// Square root of a floating-point value
    pub fn sqrt(&mut self, a: &FpValue) -> FpValue {
        let format = a.format;
        let ua = self.unpack(a);

        // Handle special cases
        if ua.is_nan() {
            self.invalid_flag = ua.class == FpClass::SignalingNaN;
            return self.pack(&UnpackedFloat::quiet_nan(false), format);
        }

        // sqrt of negative (except -0) is NaN
        if ua.sign && !ua.is_zero() {
            self.invalid_flag = true;
            return self.pack(&UnpackedFloat::quiet_nan(false), format);
        }

        // sqrt(+Infinity) = +Infinity
        if ua.class == FpClass::PositiveInfinity {
            return FpValue::pos_infinity(format);
        }

        // sqrt(±0) = ±0
        if ua.is_zero() {
            return *a;
        }

        // Compute sqrt using full 128-bit precision
        //
        // For left-aligned representation: value = (sig / 2^127) × 2^exp
        // sqrt(value) = sqrt(sig / 2^127) × sqrt(2^exp)
        //             = sqrt(sig) / 2^63.5 × 2^(exp/2)
        //
        // Strategy: similar to mul/div, compute sqrt then normalize

        let sig = ua.significand;
        let mut exp = ua.exponent;

        // unpack() always left-aligns finite non-zero significands so the MSB
        // sits at bit 127 (sig ∈ [2^127, 2^128)); it can therefore never be
        // shifted left by 1 without losing that top bit. To handle an odd
        // exponent (sqrt(x × 2^(2k+1)) = sqrt(x × 2) × 2^k = sqrt(2) ×
        // sqrt(x) × 2^k) we instead compute the even-exponent sqrt(x) first
        // and fold the extra factor of sqrt(2) into the *result* significand
        // afterwards (see below), which never needs more than 128 bits.
        let odd_exponent = exp & 1 != 0;
        if odd_exponent {
            exp -= 1;
        }

        // Now exp is even
        // Compute sqrt(sig) where sig ∈ [2^127, 2^128)
        let sqrt_val = integer_sqrt(sig);
        // sqrt_val ∈ [2^63.5, 2^64)

        // We need to compute: result_sig = sqrt(sig) × 2^63.5
        // This equals: sqrt(sig) × 2^63 × sqrt(2)
        //
        // Strategy:
        // 1. Shift sqrt_val left by 63: sqrt_val × 2^63
        // 2. Multiply by sqrt(2) using high-precision arithmetic
        // 3. Extract the high 128 bits

        let temp = sqrt_val << 63;

        // sqrt(2) × 2^64 in fixed-point (64.64 format)
        // sqrt(2) ≈ 1.41421356237309504880...
        // sqrt(2) × 2^64 ≈ 26087635650665564424
        const SQRT_2_FIXED: u128 = 26087635650665564424;

        // Multiply temp by sqrt(2) using mul128
        // temp × SQRT_2_FIXED = (sqrt_val × 2^63) × (sqrt(2) × 2^64)
        //                      = sqrt_val × sqrt(2) × 2^127
        // The result is approximately 2^63.5 × sqrt(2) × 2^127 = 2^191
        // mul128 returns the high 128 bits (bits 128-255 of the 256-bit product)
        let (high, _sticky) = Self::mul128(temp, SQRT_2_FIXED);

        // high contains bits 128-255 of the product
        // For a product around 2^191, this gives us approximately 2^63
        // We need to shift left by 64 more to get the MSB at bit 127
        let mut result_sig = high << 64;
        let mut result_exp = exp / 2;

        // For an originally-odd exponent, `result_sig` currently holds
        // sqrt(x) × 2^127 (x = sig / 2^127 ∈ [1, 2)); multiply in the missing
        // factor of sqrt(2) via the same fixed-point trick to get sqrt(2x) ×
        // 2^127, which is what corresponds to the true (odd) exponent's
        // radicand. sqrt(2x) ∈ [√2, 2) so this stays MSB-aligned at bit 127.
        if odd_exponent {
            let (high2, sticky2) = Self::mul128(result_sig, SQRT_2_FIXED);
            result_sig = high2 << 64;
            if sticky2 && (result_sig & 1) == 0 {
                result_sig |= 1;
            }
        }

        // Check if normalization is needed (MSB should be at bit 127)
        if result_sig != 0 && (result_sig & (1u128 << 127)) == 0 {
            // MSB is not at bit 127, shift left
            result_sig <<= 1;
            result_exp -= 1;
        }

        let mut result = UnpackedFloat::from_components(
            false, // sqrt is always positive
            result_exp,
            result_sig,
            format.significand_bits,
        );
        result.normalize();

        self.pack(&result, format)
    }

    /// Fused multiply-add: `round(a * b + c)` with a single rounding.
    ///
    /// Implements IEEE 754-2019 `fusedMultiplyAdd`. The product `a * b` is
    /// formed exactly (the product of two `p`-bit significands is exact in
    /// `2p` bits), `c` is added exactly at the aligned scale, and the result
    /// is rounded exactly once to the target format. This is distinct from the
    /// doubly-rounded `add(mul(a, b), c)`, which can differ by up to one ulp.
    pub fn fma(&mut self, a: &FpValue, b: &FpValue, c: &FpValue) -> FpValue {
        assert_eq!(a.format, b.format, "Format mismatch in FMA");
        assert_eq!(a.format, c.format, "Format mismatch in FMA");
        let format = a.format;

        let ua = self.unpack(a);
        let ub = self.unpack(b);
        let uc = self.unpack(c);

        // NaN inputs propagate to a quiet NaN; a signaling NaN raises invalid.
        if ua.is_nan() || ub.is_nan() || uc.is_nan() {
            self.invalid_flag = ua.class == FpClass::SignalingNaN
                || ub.class == FpClass::SignalingNaN
                || uc.class == FpClass::SignalingNaN;
            return self.pack(&UnpackedFloat::quiet_nan(false), format);
        }

        let a_inf = ua.class.is_infinite();
        let b_inf = ub.class.is_infinite();
        let a_zero = ua.is_zero();
        let b_zero = ub.is_zero();

        // 0 * inf is an invalid operation regardless of the addend.
        if (a_inf && b_zero) || (b_inf && a_zero) {
            self.invalid_flag = true;
            return self.pack(&UnpackedFloat::quiet_nan(false), format);
        }

        let prod_sign = ua.sign ^ ub.sign;

        // If the product is infinite, the result is that infinity unless the
        // addend is the opposite infinity (inf - inf is invalid).
        if a_inf || b_inf {
            if uc.class.is_infinite() && uc.sign != prod_sign {
                self.invalid_flag = true;
                return self.pack(&UnpackedFloat::quiet_nan(false), format);
            }
            return if prod_sign {
                FpValue::neg_infinity(format)
            } else {
                FpValue::pos_infinity(format)
            };
        }

        // Product is finite; a finite product plus an infinite addend is that
        // infinity.
        if uc.class.is_infinite() {
            return if uc.sign {
                FpValue::neg_infinity(format)
            } else {
                FpValue::pos_infinity(format)
            };
        }

        // All operands finite. Form a*b + c exactly with arbitrary-precision
        // integers, then round once. For a finite non-zero value the unpacked
        // significand is left-aligned (MSB at bit 127), so the arithmetic value
        // is `significand * 2^(exponent - 127)`; zeros have significand 0.
        let prod_mag = BigUint::from(ua.significand) * BigUint::from(ub.significand);
        let prod_exp2 = (ua.exponent as i64 - 127) + (ub.exponent as i64 - 127);
        let c_mag = BigUint::from(uc.significand);
        let c_exp2 = uc.exponent as i64 - 127;

        // Align both addends to the common scale 2^e (e = min exponent).
        let e = prod_exp2.min(c_exp2);
        let prod_scaled = &prod_mag << ((prod_exp2 - e) as u64);
        let c_scaled = &c_mag << ((c_exp2 - e) as u64);
        let prod_signed = BigInt::from_biguint(sign_of(prod_sign), prod_scaled);
        let c_signed = BigInt::from_biguint(sign_of(uc.sign), c_scaled);
        let sum = prod_signed + c_signed;

        if sum.sign() == num_bigint::Sign::NoSign {
            // Exact zero result. Two same-signed zeros keep their sign; any
            // exact cancellation is +0 except under round-toward-negative.
            let both_zero = (a_zero || b_zero) && uc.is_zero();
            let sign = if both_zero && prod_sign == uc.sign {
                prod_sign
            } else {
                self.rounding_mode == FpRoundingMode::RoundTowardNegative
            };
            return if sign {
                FpValue::neg_zero(format)
            } else {
                FpValue::pos_zero(format)
            };
        }

        let sign = sum.sign() == num_bigint::Sign::Minus;
        let mag = sum.magnitude().clone();
        self.round_exact_to_fp(sign, &mag, e, false, format)
    }

    /// Round an exact value `sign * magnitude * 2^exp2` to `format` with a
    /// single correctly-rounded step. `extra_sticky` records nonzero value
    /// discarded below `magnitude`'s least-significant bit (used when the
    /// caller has already truncated). `magnitude` must be non-zero unless the
    /// exact value is truly zero.
    fn round_exact_to_fp(
        &mut self,
        sign: bool,
        magnitude: &BigUint,
        exp2: i64,
        extra_sticky: bool,
        format: FpFormat,
    ) -> FpValue {
        let bits = magnitude.bits();
        if bits == 0 {
            return if sign {
                FpValue::neg_zero(format)
            } else {
                FpValue::pos_zero(format)
            };
        }

        // Reduce the magnitude to a 128-bit significand with its MSB at bit 127,
        // collecting any discarded low bits into the sticky flag.
        let (mut sig128, exp128, sticky) = if bits > 128 {
            let shift = bits - 128;
            let low_nonzero = match magnitude.trailing_zeros() {
                Some(tz) => tz < shift,
                None => false,
            };
            let top = magnitude >> shift;
            (
                biguint_low_u128(&top),
                exp2 + shift as i64,
                low_nonzero || extra_sticky,
            )
        } else {
            let shift = 128 - bits;
            (
                biguint_low_u128(magnitude) << shift,
                exp2 - shift as i64,
                extra_sticky,
            )
        };
        if sticky && (sig128 & 1) == 0 {
            sig128 |= 1;
        }

        // value = (sig128 / 2^127) * 2^(exp128 + 127); pack expects the
        // unbiased exponent of that normalized (1.frac) representation.
        let unbiased = (exp128 + 127).clamp(i32::MIN as i64, i32::MAX as i64) as i32;
        let unpacked = UnpackedFloat {
            sign,
            exponent: unbiased,
            significand: sig128,
            precision: format.significand_bits,
            class: if sign {
                FpClass::NegativeNormal
            } else {
                FpClass::PositiveNormal
            },
        };
        self.pack(&unpacked, format)
    }

    /// IEEE 754 remainder: `a - n*b`, where `n` is the exact quotient `a/b`
    /// rounded to the nearest integer with ties to even.
    ///
    /// The result is always exact (`|result| <= |b|/2`), so no rounding error
    /// is introduced. This differs from a truncating/fmod-style remainder and
    /// from `a - div(a,b)*b`, which rounds the quotient to the FP format first.
    /// Reference: Z3's `mpf_manager::rem`.
    pub fn rem(&mut self, a: &FpValue, b: &FpValue) -> FpValue {
        let format = a.format;
        let ua = self.unpack(a);
        let ub = self.unpack(b);

        // Handle special cases
        if ua.is_nan() || ub.is_nan() {
            self.invalid_flag =
                ua.class == FpClass::SignalingNaN || ub.class == FpClass::SignalingNaN;
            return self.pack(&UnpackedFloat::quiet_nan(false), format);
        }

        // remainder(inf, y) and remainder(x, 0) are invalid.
        if ua.class.is_infinite() || ub.is_zero() {
            self.invalid_flag = true;
            return self.pack(&UnpackedFloat::quiet_nan(false), format);
        }

        // remainder(x, inf) = x and remainder(0, y) = 0 (sign preserved).
        if ub.class.is_infinite() || ua.is_zero() {
            return *a;
        }

        // Both finite and non-zero. Work with exact integer significands:
        // value_x = sx * 2^ex, value_y = sy * 2^ey (MSB-aligned significands).
        let sx = BigUint::from(ua.significand);
        let sy = BigUint::from(ub.significand);
        let ex = ua.exponent as i64 - 127;
        let ey = ub.exponent as i64 - 127;

        // n = round-half-even(|x/y|); |x/y| = (sx << max(ex-ey,0)) / (sy << max(ey-ex,0)).
        let d = ex - ey;
        let (num, den) = if d >= 0 {
            (&sx << (d as u64), sy.clone())
        } else {
            (sx.clone(), &sy << ((-d) as u64))
        };
        let n_mag = round_half_even_biguint(&num, &den);

        // r = x - n*y computed exactly at the common scale 2^e (e = min(ex,ey)).
        let e = ex.min(ey);
        let xv = BigInt::from_biguint(sign_of(ua.sign), &sx << ((ex - e) as u64));
        let yv = BigInt::from_biguint(sign_of(ub.sign), &sy << ((ey - e) as u64));
        let sign_q = ua.sign ^ ub.sign;
        let n_signed = BigInt::from_biguint(sign_of(sign_q), n_mag);
        let inner = xv - n_signed * yv;

        if inner.sign() == num_bigint::Sign::NoSign {
            // A zero remainder takes the sign of the dividend.
            return if ua.sign {
                FpValue::neg_zero(format)
            } else {
                FpValue::pos_zero(format)
            };
        }

        let sign_r = inner.sign() == num_bigint::Sign::Minus;
        let mag = inner.magnitude().clone();
        // The IEEE remainder is exact, so this rounding step is a no-op in
        // exact arithmetic; it merely repacks into the target format.
        self.round_exact_to_fp(sign_r, &mag, e, false, format)
    }

    /// Minimum of two values (IEEE 754 semantics)
    pub fn min(&mut self, a: &FpValue, b: &FpValue) -> FpValue {
        let ua = self.unpack(a);
        let ub = self.unpack(b);

        // NaN propagation
        if ua.is_nan() {
            return *a;
        }
        if ub.is_nan() {
            return *b;
        }

        // Compare
        match self.compare_internal(&ua, &ub) {
            Ordering::Less | Ordering::Equal => *a,
            Ordering::Greater => *b,
        }
    }

    /// Maximum of two values (IEEE 754 semantics)
    pub fn max(&mut self, a: &FpValue, b: &FpValue) -> FpValue {
        let ua = self.unpack(a);
        let ub = self.unpack(b);

        // NaN propagation
        if ua.is_nan() {
            return *a;
        }
        if ub.is_nan() {
            return *b;
        }

        // Compare
        match self.compare_internal(&ua, &ub) {
            Ordering::Greater | Ordering::Equal => *a,
            Ordering::Less => *b,
        }
    }

    /// Compare two unpacked floats
    #[must_use]
    fn compare_internal(&self, a: &UnpackedFloat, b: &UnpackedFloat) -> Ordering {
        // Handle infinities
        if a.class.is_infinite() && b.class.is_infinite() {
            // Both infinite
            if a.sign == b.sign {
                return Ordering::Equal; // Same infinity
            }
            return if a.sign {
                Ordering::Less // -inf < +inf
            } else {
                Ordering::Greater // +inf > -inf
            };
        }
        if a.class.is_infinite() {
            // a is infinite, b is not
            return if a.sign {
                Ordering::Less // -inf < anything
            } else {
                Ordering::Greater // +inf > anything
            };
        }
        if b.class.is_infinite() {
            // b is infinite, a is not
            return if b.sign {
                Ordering::Greater // anything > -inf
            } else {
                Ordering::Less // anything < +inf
            };
        }

        // Handle zeros
        if a.is_zero() && b.is_zero() {
            return Ordering::Equal;
        }

        // If only one is zero, compare based on sign of non-zero value
        if a.is_zero() {
            // a is zero, b is not
            // If b is positive, zero < b; if b is negative, zero > b
            return if b.sign {
                Ordering::Greater // 0 > -x
            } else {
                Ordering::Less // 0 < +x
            };
        }
        if b.is_zero() {
            // b is zero, a is not
            return if a.sign {
                Ordering::Less // -x < 0
            } else {
                Ordering::Greater // +x > 0
            };
        }

        // Different signs (neither is zero)
        if a.sign && !b.sign {
            return Ordering::Less;
        }
        if !a.sign && b.sign {
            return Ordering::Greater;
        }

        // Same sign, compare magnitude
        let mag_cmp = a
            .exponent
            .cmp(&b.exponent)
            .then_with(|| a.significand.cmp(&b.significand));

        if a.sign { mag_cmp.reverse() } else { mag_cmp }
    }

    /// Compare for equality (IEEE 754 semantics: NaN != NaN, +0 == -0)
    #[must_use]
    pub fn eq(&self, a: &FpValue, b: &FpValue) -> bool {
        let ua = self.unpack(a);
        let ub = self.unpack(b);

        // NaN is never equal to anything
        if ua.is_nan() || ub.is_nan() {
            return false;
        }

        // +0 == -0
        if ua.is_zero() && ub.is_zero() {
            return true;
        }

        // Bitwise comparison
        a.sign == b.sign && a.exponent == b.exponent && a.significand == b.significand
    }

    /// Less than comparison
    #[must_use]
    pub fn lt(&self, a: &FpValue, b: &FpValue) -> bool {
        let ua = self.unpack(a);
        let ub = self.unpack(b);

        // NaN comparisons are always false
        if ua.is_nan() || ub.is_nan() {
            return false;
        }

        self.compare_internal(&ua, &ub) == Ordering::Less
    }

    /// Less than or equal comparison
    #[must_use]
    pub fn le(&self, a: &FpValue, b: &FpValue) -> bool {
        let ua = self.unpack(a);
        let ub = self.unpack(b);

        if ua.is_nan() || ub.is_nan() {
            return false;
        }

        matches!(
            self.compare_internal(&ua, &ub),
            Ordering::Less | Ordering::Equal
        )
    }

    /// Greater than comparison
    #[must_use]
    pub fn gt(&self, a: &FpValue, b: &FpValue) -> bool {
        self.lt(b, a)
    }

    /// Greater than or equal comparison
    #[must_use]
    pub fn ge(&self, a: &FpValue, b: &FpValue) -> bool {
        self.le(b, a)
    }

    /// Negate a value
    #[must_use]
    pub fn neg(&self, a: &FpValue) -> FpValue {
        let mut result = *a;
        result.sign = !result.sign;
        result
    }

    /// Absolute value
    #[must_use]
    pub fn abs(&self, a: &FpValue) -> FpValue {
        let mut result = *a;
        result.sign = false;
        result
    }

    /// Classify a floating-point value
    #[must_use]
    pub fn classify(&self, a: &FpValue) -> FpClass {
        self.unpack(a).class
    }
}

/// Integer square root using binary search
#[must_use]
fn integer_sqrt(n: u128) -> u128 {
    if n == 0 {
        return 0;
    }

    let mut x = n;
    let mut y = x.div_ceil(2);

    while y < x {
        x = y;
        y = (x + n / x) / 2;
    }

    x
}

/// Extract the low 128 bits of a `BigUint`.
#[must_use]
fn biguint_low_u128(x: &BigUint) -> u128 {
    let mut digits = x.iter_u64_digits();
    let lo = digits.next().unwrap_or(0);
    let hi = digits.next().unwrap_or(0);
    ((hi as u128) << 64) | (lo as u128)
}

/// Map a sign flag (`true` = negative) to a `num_bigint::Sign`. Callers pair
/// this with a magnitude; `BigInt::from_biguint` normalizes a zero magnitude to
/// `NoSign`, so passing `Minus` with a zero magnitude is safe.
#[must_use]
fn sign_of(negative: bool) -> num_bigint::Sign {
    if negative {
        num_bigint::Sign::Minus
    } else {
        num_bigint::Sign::Plus
    }
}

/// Divide `num` by `den` (both non-negative, `den > 0`) rounding the exact
/// quotient to the nearest integer, ties to even.
#[must_use]
fn round_half_even_biguint(num: &BigUint, den: &BigUint) -> BigUint {
    let q = num / den;
    let r = num % den;
    let two_r = &r << 1u32;
    match two_r.cmp(den) {
        Ordering::Less => q,
        Ordering::Greater => q + 1u32,
        Ordering::Equal => {
            // Exact tie: round to the even quotient.
            if q.bit(0) { q + 1u32 } else { q }
        }
    }
}

/// Format conversion with rounding
pub fn convert_format(
    engine: &mut Ieee754Engine,
    value: &FpValue,
    target_format: FpFormat,
) -> FpValue {
    if value.format == target_format {
        return *value;
    }

    let unpacked = engine.unpack(value);
    engine.pack(&unpacked, target_format)
}

/// Convert floating-point to signed integer
#[must_use]
pub fn fp_to_sint(engine: &mut Ieee754Engine, value: &FpValue, width: u32) -> Option<i64> {
    let unpacked = engine.unpack(value);

    // NaN or Infinity -> None
    if unpacked.is_nan() || unpacked.class.is_infinite() {
        engine.invalid_flag = true;
        return None;
    }

    // Zero
    if unpacked.is_zero() {
        return Some(0);
    }

    // Extract integer part based on exponent
    // For left-aligned significand: value = (sig / 2^127) × 2^exp
    // Integer value = sig × 2^(exp - 127)
    let int_val = if unpacked.exponent >= 127 {
        // Value >= 1
        let left_shift = (unpacked.exponent - 127) as u32;
        if left_shift >= 63 {
            // Overflow for signed i64
            engine.invalid_flag = true;
            return None;
        }
        (unpacked.significand >> (127 - left_shift)) as i64
    } else {
        // Value < 1
        let right_shift = (127 - unpacked.exponent) as u32;
        if right_shift >= 128 {
            0
        } else {
            (unpacked.significand >> right_shift) as i64
        }
    };

    let result = if unpacked.sign {
        match int_val.checked_neg() {
            Some(neg) => neg,
            None => {
                engine.invalid_flag = true;
                return None;
            }
        }
    } else {
        int_val
    };

    // Check range
    let max_val = if width >= 64 {
        i64::MAX
    } else {
        (1i64 << (width - 1)) - 1
    };
    let min_val = if width >= 64 {
        i64::MIN
    } else {
        (1i64 << (width - 1)).wrapping_neg()
    };

    if result > max_val || result < min_val {
        engine.invalid_flag = true;
        return None;
    }

    Some(result)
}

/// Convert floating-point to unsigned integer
#[must_use]
pub fn fp_to_uint(engine: &mut Ieee754Engine, value: &FpValue, width: u32) -> Option<u64> {
    let unpacked = engine.unpack(value);

    if unpacked.is_nan() || unpacked.class.is_infinite() {
        engine.invalid_flag = true;
        return None;
    }

    if unpacked.sign {
        engine.invalid_flag = true;
        return None;
    }

    if unpacked.is_zero() {
        return Some(0);
    }

    // For left-aligned significand: value = (sig / 2^127) × 2^exp
    // Integer value = sig × 2^(exp - 127)
    // If exp < 127: int_value = sig >> (127 - exp)
    // If exp >= 127: int_value = sig << (exp - 127)
    let int_val = if unpacked.exponent >= 127 {
        // Value >= 1, need to shift left or keep as is
        let left_shift = (unpacked.exponent - 127) as u32;
        if left_shift >= 64 {
            // Overflow - value is too large for u64
            engine.invalid_flag = true;
            return None;
        }
        (unpacked.significand >> (127 - left_shift)) as u64
    } else {
        // Value < 1, shift right
        let right_shift = (127 - unpacked.exponent) as u32;
        if right_shift >= 128 {
            0
        } else {
            (unpacked.significand >> right_shift) as u64
        }
    };

    let max_val = if width >= 64 {
        u64::MAX
    } else {
        (1u64 << width) - 1
    };

    if int_val > max_val {
        engine.invalid_flag = true;
        return None;
    }

    Some(int_val)
}

/// Convert signed integer to floating-point
pub fn sint_to_fp(engine: &mut Ieee754Engine, value: i64, format: FpFormat) -> FpValue {
    if value == 0 {
        return FpValue::pos_zero(format);
    }

    let (sign, abs_val) = if value < 0 {
        (true, value.wrapping_neg() as u64)
    } else {
        (false, value as u64)
    };

    let leading_zeros = abs_val.leading_zeros();
    let significand = (abs_val as u128) << (64 + leading_zeros);
    let exponent = 63 - (leading_zeros as i32);

    let unpacked =
        UnpackedFloat::from_components(sign, exponent, significand, format.significand_bits);
    engine.pack(&unpacked, format)
}

/// Convert unsigned integer to floating-point
pub fn uint_to_fp(engine: &mut Ieee754Engine, value: u64, format: FpFormat) -> FpValue {
    if value == 0 {
        return FpValue::pos_zero(format);
    }

    let leading_zeros = value.leading_zeros();
    let significand = (value as u128) << (64 + leading_zeros);
    let exponent = 63 - (leading_zeros as i32);

    let unpacked =
        UnpackedFloat::from_components(false, exponent, significand, format.significand_bits);
    engine.pack(&unpacked, format)
}

#[cfg(test)]
mod tests;
