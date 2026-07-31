//! Constant evaluation for the SMT-LIB `FixedSizeBitVectors` operations.
//!
//! Every function here works on *unsigned* values already reduced into the
//! range `[0, 2^width)` and returns a result in the same range, so the results
//! can be handed straight to `TermManager::mk_bitvec`.  Keeping the numeric
//! core separate from the term builders makes each rule directly unit
//! testable and keeps `builder.rs` focused on term construction.
//!
//! # Reducing operands first
//!
//! That range is a **precondition**, not a check.  A `BitVecConst` is not
//! guaranteed to satisfy it — `TermManager::mk_bitvec` interns whatever value
//! it is given, so a negative or oversized literal is reachable through the
//! public API — and handing an unreduced operand to, say, [`bv_lshr`] produces
//! a result that is not a bit-vector value.  Reduce every operand through
//! [`bv_wrap_unsigned`] before folding, which is what the term builder's own
//! `bv_const_unsigned` does and what makes a negative literal mean the same
//! thing here, in the SMT-LIB printer, and in the model builder.
//!
//! # Single definition
//!
//! This module is public so that every consumer in the workspace routes
//! through *one* definition of each operator's semantics rather than keeping
//! its own copy — the term builder, the rewriter, the bit-blaster, the model
//! evaluator and the solver's early-conflict checks.  Independent copies have
//! diverged in practice: a duplicate in the array cross-theory check read a
//! shift distance out of its low 64-bit limb and so folded
//! `bvshl x (_ bv18446744073709551616 65)` to `x` where [`bv_shl`] gives zero.
//! Prefer adapting at the boundary (width agreement, "not a constant") over
//! reimplementing an operator.
//!
//! Reference: Z3's `bv_rewriter.cpp`, which folds exactly these operations.
//! The two subtleties it also encodes, and that are easy to get wrong, are:
//!
//! * **Division and remainder are total.**  SMT-LIB defines every member of
//!   the division family at a zero divisor, so folding must produce the
//!   specified value rather than skip the rewrite or panic.  See
//!   [`bv_udiv`], [`bv_urem`], [`bv_sdiv`], [`bv_srem`] and [`bv_smod`].
//! * **Shifts by at least the width are specified, not undefined.**  See
//!   [`bv_shl`], [`bv_lshr`] and [`bv_ashr`].
//!
//! `bvneg` has no entry of its own: `TermManager::mk_bv_neg` lowers it to
//! `0 - t`, so [`bv_sub`] folds it.

use num_bigint::BigInt;

#[allow(unused_imports)]
use crate::prelude::*;

/// Reduce `value` into the unsigned bit-vector range `[0, 2^width)`.
///
/// A bit-vector value is unsigned by definition, so anything outside that
/// range — a negative literal written by the user, an oversized constant, or
/// a value handed back by a theory whose relaxation carries no domain bound —
/// must wrap two's-complement style before it can be interned or printed.
/// This is the single canonical implementation of that wrap; the term
/// builder, the SMT-LIB printer and the solver's model builder all route
/// through it so they cannot drift apart.
///
/// `width == 0` is not a legal SMT-LIB bit-vector sort and has only one
/// possible value, so it maps to zero.
#[must_use]
pub fn bv_wrap_unsigned(value: &BigInt, width: u32) -> BigInt {
    if width == 0 {
        return BigInt::ZERO;
    }
    let modulus = modulus(width);
    let mut wrapped = value % &modulus;
    if wrapped < BigInt::ZERO {
        wrapped += &modulus;
    }
    wrapped
}

/// `2^width`, the modulus of `width`-bit arithmetic.
fn modulus(width: u32) -> BigInt {
    BigInt::from(1u8) << width as usize
}

/// The all-ones `width`-bit value, `2^width - 1`.
#[must_use]
pub(crate) fn all_ones(width: u32) -> BigInt {
    modulus(width) - 1
}

/// Reinterpret an unsigned `width`-bit value as a two's-complement integer.
#[must_use]
pub fn to_signed(value: &BigInt, width: u32) -> BigInt {
    if width == 0 {
        return BigInt::ZERO;
    }
    if *value >= (BigInt::from(1u8) << (width - 1) as usize) {
        value - modulus(width)
    } else {
        value.clone()
    }
}

/// Whether the sign (most significant) bit of an unsigned `width`-bit value
/// is set.
fn is_negative(value: &BigInt, width: u32) -> bool {
    width > 0 && *value >= (BigInt::from(1u8) << (width - 1) as usize)
}

/// A shift distance, interpreted as an unsigned bit-vector value.
///
/// Returns `None` when the distance is at least `width`, which every SMT-LIB
/// shift treats as a saturating case rather than as an out-of-range index.
fn shift_distance(amount: &BigInt, width: u32) -> Option<usize> {
    if *amount >= BigInt::from(width) {
        return None;
    }
    usize::try_from(amount).ok()
}

/// `bvadd` — addition modulo `2^width`.
#[must_use]
pub fn bv_add(lhs: &BigInt, rhs: &BigInt, width: u32) -> BigInt {
    bv_wrap_unsigned(&(lhs + rhs), width)
}

/// `bvsub` — subtraction modulo `2^width`.
#[must_use]
pub fn bv_sub(lhs: &BigInt, rhs: &BigInt, width: u32) -> BigInt {
    bv_wrap_unsigned(&(lhs - rhs), width)
}

/// `bvmul` — multiplication modulo `2^width`.
#[must_use]
pub fn bv_mul(lhs: &BigInt, rhs: &BigInt, width: u32) -> BigInt {
    bv_wrap_unsigned(&(lhs * rhs), width)
}

/// `bvand` — bitwise conjunction.
#[must_use]
pub fn bv_and(lhs: &BigInt, rhs: &BigInt, _width: u32) -> BigInt {
    lhs & rhs
}

/// `bvor` — bitwise disjunction.
#[must_use]
pub fn bv_or(lhs: &BigInt, rhs: &BigInt, _width: u32) -> BigInt {
    lhs | rhs
}

/// `bvxor` — bitwise exclusive disjunction.
#[must_use]
pub fn bv_xor(lhs: &BigInt, rhs: &BigInt, _width: u32) -> BigInt {
    lhs ^ rhs
}

/// `bvnot` — bitwise complement.
///
/// Computed as `all_ones - value` rather than `!value`: `BigInt`'s `Not` is
/// the infinite-precision two's-complement `-value - 1`, which is negative
/// for every non-negative input and would have to be wrapped back anyway.
#[must_use]
pub fn bv_not(value: &BigInt, width: u32) -> BigInt {
    all_ones(width) - value
}

/// `bvshl` — left shift by an unsigned distance.
///
/// A distance of `width` or more shifts every bit out, so the result is zero
/// (Reference: Z3's `bv_rewriter::mk_bv_shl`, which returns `mk_zero` for
/// `r2 >= bv_size`).
#[must_use]
pub fn bv_shl(value: &BigInt, amount: &BigInt, width: u32) -> BigInt {
    match shift_distance(amount, width) {
        None => BigInt::ZERO,
        Some(shift) => bv_wrap_unsigned(&(value << shift), width),
    }
}

/// `bvlshr` — logical (zero-filling) right shift by an unsigned distance.
///
/// A distance of `width` or more yields zero (Reference: Z3's
/// `bv_rewriter::mk_bv_lshr`).
#[must_use]
pub fn bv_lshr(value: &BigInt, amount: &BigInt, width: u32) -> BigInt {
    match shift_distance(amount, width) {
        None => BigInt::ZERO,
        Some(shift) => value >> shift,
    }
}

/// `bvashr` — arithmetic (sign-filling) right shift by an unsigned distance.
///
/// A distance of `width` or more leaves only copies of the sign bit, so the
/// result is all-ones for a negative value and zero otherwise (Reference:
/// Z3's `bv_rewriter::mk_bv_ashr`, which tests `has_sign_bit`).
#[must_use]
pub fn bv_ashr(value: &BigInt, amount: &BigInt, width: u32) -> BigInt {
    let negative = is_negative(value, width);
    let Some(shift) = shift_distance(amount, width) else {
        return if negative {
            all_ones(width)
        } else {
            BigInt::ZERO
        };
    };
    let shifted = value >> shift;
    if negative {
        // Re-introduce the `shift` sign bits the logical shift dropped.
        let keep = all_ones(width.saturating_sub(shift as u32));
        (all_ones(width) - keep) | shifted
    } else {
        shifted
    }
}

/// `bvudiv` — unsigned division.
///
/// **Division by zero is total**: SMT-LIB defines `(bvudiv s (_ bv0 m))` as
/// the all-ones vector, so folding must produce `2^width - 1` rather than
/// leave the term alone (Reference: Z3's `bv_rewriter::mk_bv_udiv_core`,
/// whose `hi_div0` branch returns `power_of_two(bv_size) - 1`).
#[must_use]
pub fn bv_udiv(lhs: &BigInt, rhs: &BigInt, width: u32) -> BigInt {
    if *rhs == BigInt::ZERO {
        all_ones(width)
    } else {
        lhs / rhs
    }
}

/// `bvurem` — unsigned remainder.
///
/// **Remainder by zero is total**: SMT-LIB defines `(bvurem s (_ bv0 m))` as
/// `s` (Reference: Z3's `bv_rewriter::mk_bv_urem_core`, whose `hi_div0`
/// branch returns `arg1`).
#[must_use]
pub fn bv_urem(lhs: &BigInt, rhs: &BigInt, _width: u32) -> BigInt {
    if *rhs == BigInt::ZERO {
        lhs.clone()
    } else {
        lhs % rhs
    }
}

/// `bvsdiv` — signed division, truncating towards zero.
///
/// **Division by zero is total**: unfolding the SMT-LIB definition of
/// `bvsdiv` at `t = 0` gives `bvudiv s 0 = all-ones = -1` for a non-negative
/// `s` and `bvneg (bvudiv (bvneg s) 0) = bvneg (-1) = 1` for a negative `s`
/// (Reference: Z3's `bv_rewriter::mk_bv_sdiv_core`, whose `hi_div0` branch
/// builds `(ite (bvslt x 0) 1 #xff..f)`).
#[must_use]
pub fn bv_sdiv(lhs: &BigInt, rhs: &BigInt, width: u32) -> BigInt {
    let signed_lhs = to_signed(lhs, width);
    let signed_rhs = to_signed(rhs, width);
    if signed_rhs == BigInt::ZERO {
        return if signed_lhs < BigInt::ZERO {
            BigInt::from(1u8)
        } else {
            all_ones(width)
        };
    }
    // `BigInt`'s division truncates towards zero, which is the rounding
    // SMT-LIB's `bvsdiv` prescribes.
    bv_wrap_unsigned(&(signed_lhs / signed_rhs), width)
}

/// `bvsrem` — signed remainder, taking the sign of the *dividend*.
///
/// **Remainder by zero is total**: unfolding the SMT-LIB definition at
/// `t = 0` gives `s` for both signs of `s` (Reference: Z3's
/// `bv_rewriter::mk_bv_srem_core`, whose `hi_div0` branch returns `arg1`).
#[must_use]
pub fn bv_srem(lhs: &BigInt, rhs: &BigInt, width: u32) -> BigInt {
    let signed_lhs = to_signed(lhs, width);
    let signed_rhs = to_signed(rhs, width);
    if signed_rhs == BigInt::ZERO {
        return lhs.clone();
    }
    // `BigInt`'s remainder follows the dividend's sign, matching `bvsrem`.
    bv_wrap_unsigned(&(signed_lhs % signed_rhs), width)
}

/// `bvsmod` — signed modulus, taking the sign of the *divisor*.
///
/// **Modulus by zero is total**: unfolding the SMT-LIB definition at `t = 0`
/// gives `s` (the `abs_t` is zero, so `u = bvurem abs_s 0 = abs_s`, and each
/// surviving branch reduces back to `s`) — matching Z3's
/// `bv_rewriter::mk_bv_smod_core`, whose `hi_div0` branch returns `arg1`.
#[must_use]
pub fn bv_smod(lhs: &BigInt, rhs: &BigInt, width: u32) -> BigInt {
    let signed_lhs = to_signed(lhs, width);
    let signed_rhs = to_signed(rhs, width);
    if signed_rhs == BigInt::ZERO {
        return lhs.clone();
    }
    let abs_lhs = if signed_lhs < BigInt::ZERO {
        -&signed_lhs
    } else {
        signed_lhs.clone()
    };
    let abs_rhs = if signed_rhs < BigInt::ZERO {
        -&signed_rhs
    } else {
        signed_rhs.clone()
    };
    let unsigned_rem = abs_lhs % abs_rhs;
    if unsigned_rem == BigInt::ZERO {
        return BigInt::ZERO;
    }
    let result = match (signed_lhs < BigInt::ZERO, signed_rhs < BigInt::ZERO) {
        (false, false) => unsigned_rem,
        (true, false) => -unsigned_rem + &signed_rhs,
        (false, true) => unsigned_rem + &signed_rhs,
        (true, true) => -unsigned_rem,
    };
    bv_wrap_unsigned(&result, width)
}

/// `concat` — `lhs` occupies the high bits, `rhs` the low `rhs_width` bits.
#[must_use]
pub fn bv_concat(lhs: &BigInt, rhs: &BigInt, rhs_width: u32) -> BigInt {
    (lhs << rhs_width as usize) | rhs
}

/// `(_ extract high low)` — the bits `high ..= low`, right-aligned.
///
/// The caller must have checked `low <= high`.
#[must_use]
pub fn bv_extract(value: &BigInt, high: u32, low: u32) -> BigInt {
    let span = high - low + 1;
    (value >> low as usize) & all_ones(span)
}

#[cfg(test)]
mod tests {
    use super::*;

    /// Widths exercised throughout: 4 and 8 are multiples of four (hex
    /// literals), 5 is not (binary literals), 16/32 cover the wider sorts.
    const WIDTHS: [u32; 5] = [4, 5, 8, 16, 32];

    fn big(value: i64) -> BigInt {
        BigInt::from(value)
    }

    #[test]
    fn test_bv_wrap_unsigned_normalizes_into_range() {
        assert_eq!(bv_wrap_unsigned(&big(-1), 8), big(255));
        assert_eq!(bv_wrap_unsigned(&big(256), 8), big(0));
        assert_eq!(bv_wrap_unsigned(&big(-1), 5), big(31));
        assert_eq!(bv_wrap_unsigned(&big(37), 5), big(5));
        assert_eq!(bv_wrap_unsigned(&big(7), 0), big(0));
        for width in WIDTHS {
            let bound = BigInt::from(1u8) << width as usize;
            for raw in [-9i64, -1, 0, 1, 7, 1000] {
                let wrapped = bv_wrap_unsigned(&big(raw), width);
                assert!(wrapped >= BigInt::ZERO && wrapped < bound);
            }
        }
    }

    #[test]
    fn test_to_signed_reinterprets_two_complement() {
        assert_eq!(to_signed(&big(255), 8), big(-1));
        assert_eq!(to_signed(&big(128), 8), big(-128));
        assert_eq!(to_signed(&big(127), 8), big(127));
        assert_eq!(to_signed(&big(16), 5), big(-16));
        assert_eq!(to_signed(&big(15), 5), big(15));
    }

    /// `BigInt`'s division must truncate towards zero and its remainder must
    /// follow the dividend's sign — `bvsdiv` / `bvsrem` fold on that.
    #[test]
    fn test_bigint_division_truncates_towards_zero() {
        assert_eq!(big(-7) / big(2), big(-3));
        assert_eq!(big(7) / big(-2), big(-3));
        assert_eq!(big(-7) % big(2), big(-1));
        assert_eq!(big(7) % big(-2), big(1));
    }

    #[test]
    fn test_arithmetic_wraps_modulo_two_to_the_width() {
        assert_eq!(bv_add(&big(14), &big(7), 4), big(5));
        assert_eq!(bv_sub(&big(3), &big(5), 4), big(14));
        assert_eq!(bv_mul(&big(6), &big(5), 5), big(30));
        assert_eq!(bv_mul(&big(200), &big(200), 8), big(64));
        // bvneg is lowered to `0 - t`, so it folds through bv_sub.
        assert_eq!(bv_sub(&BigInt::ZERO, &big(1), 8), big(255));
        assert_eq!(bv_sub(&BigInt::ZERO, &big(0), 8), big(0));
        assert_eq!(bv_not(&big(0b0011), 4), big(0b1100));
        assert_eq!(bv_not(&big(0), 5), big(31));
    }

    #[test]
    fn test_bitwise_operations() {
        assert_eq!(bv_and(&big(0b1100), &big(0b1010), 4), big(0b1000));
        assert_eq!(bv_or(&big(0b1100), &big(0b1010), 4), big(0b1110));
        assert_eq!(bv_xor(&big(0b1100), &big(0b1010), 4), big(0b0110));
    }

    /// Shifting by `0`, `1`, `width - 1`, `width` and more than `width`.
    #[test]
    fn test_shifts_at_and_beyond_the_width() {
        for width in WIDTHS {
            let ones = all_ones(width);
            let one = BigInt::from(1u8);
            // Shift by zero is the identity for all three shifts.
            assert_eq!(bv_shl(&one, &BigInt::ZERO, width), one);
            assert_eq!(bv_lshr(&ones, &BigInt::ZERO, width), ones);
            assert_eq!(bv_ashr(&ones, &BigInt::ZERO, width), ones);
            // Shift by one.
            assert_eq!(bv_shl(&one, &one, width), big(2));
            assert_eq!(bv_lshr(&big(2), &one, width), one);
            // Shift by width - 1 leaves exactly the sign bit / lowest bit.
            let almost = BigInt::from(width - 1);
            assert_eq!(
                bv_shl(&one, &almost, width),
                BigInt::from(1u8) << (width - 1) as usize
            );
            assert_eq!(bv_lshr(&ones, &almost, width), one);
            // At or beyond the width: shl/lshr vanish, ashr saturates to the
            // sign bit.
            for amount in [BigInt::from(width), BigInt::from(width + 3), ones.clone()] {
                assert_eq!(bv_shl(&ones, &amount, width), BigInt::ZERO);
                assert_eq!(bv_lshr(&ones, &amount, width), BigInt::ZERO);
                assert_eq!(bv_ashr(&ones, &amount, width), ones);
                assert_eq!(bv_ashr(&BigInt::ZERO, &amount, width), BigInt::ZERO);
            }
        }
    }

    /// `bvashr` sign-extends; `bvlshr` zero-fills.  Values cross-checked
    /// against z3 at width 4.
    #[test]
    fn test_ashr_sign_extends_where_lshr_zero_fills() {
        assert_eq!(bv_ashr(&big(0b1000), &big(1), 4), big(0b1100));
        assert_eq!(bv_lshr(&big(0b1000), &big(1), 4), big(0b0100));
        assert_eq!(bv_ashr(&big(0b1000), &big(3), 4), big(0b1111));
        assert_eq!(bv_ashr(&big(0b0100), &big(1), 4), big(0b0010));
        assert_eq!(bv_ashr(&big(0b10000), &big(2), 5), big(0b11100));
    }

    /// Every member of the division family at a zero divisor, cross-checked
    /// against z3 4.15 at width 4 (`7` is positive, `9` is `-7`).
    #[test]
    fn test_division_family_at_zero_divisor() {
        let zero = BigInt::ZERO;
        // (bvudiv s 0) = all ones.
        for width in WIDTHS {
            assert_eq!(bv_udiv(&big(7), &zero, width), all_ones(width));
            // (bvurem s 0) = s.
            assert_eq!(bv_urem(&big(7), &zero, width), big(7));
            // (bvsrem s 0) = s, (bvsmod s 0) = s, for either sign.
            let negative = bv_sub(&BigInt::ZERO, &big(7), width);
            assert_eq!(bv_srem(&big(7), &zero, width), big(7));
            assert_eq!(bv_srem(&negative, &zero, width), negative);
            assert_eq!(bv_smod(&big(7), &zero, width), big(7));
            assert_eq!(bv_smod(&negative, &zero, width), negative);
            assert_eq!(bv_smod(&zero, &zero, width), zero);
            // (bvsdiv s 0) = -1 when s >= 0, 1 when s < 0.
            assert_eq!(bv_sdiv(&big(7), &zero, width), all_ones(width));
            assert_eq!(bv_sdiv(&zero, &zero, width), all_ones(width));
            assert_eq!(bv_sdiv(&negative, &zero, width), BigInt::from(1u8));
        }
    }

    /// Signed division / remainder / modulus with a non-zero divisor, with
    /// the four sign combinations.  Values cross-checked against z3 4.15 at
    /// width 4 (`0x9 = -7`, `0x8 = -8`, `0xf = -1`).
    #[test]
    fn test_signed_division_family() {
        assert_eq!(bv_sdiv(&big(0x9), &big(0x2), 4), big(0xd)); // -7 / 2 = -3
        assert_eq!(bv_srem(&big(0x9), &big(0x2), 4), big(0xf)); // -7 rem 2 = -1
        assert_eq!(bv_smod(&big(0x9), &big(0x2), 4), big(0x1)); // -7 mod 2 = 1
        assert_eq!(bv_smod(&big(0x2), &big(0x9), 4), big(0xb)); // 2 mod -7 = -5
        assert_eq!(bv_smod(&big(0x9), &big(0x7), 4), big(0x0)); // -7 mod 7 = 0
        assert_eq!(bv_sdiv(&big(0x2), &big(0x9), 4), big(0x0)); // 2 / -7 = 0
        assert_eq!(bv_srem(&big(0x2), &big(0x9), 4), big(0x2)); // 2 rem -7 = 2
        assert_eq!(bv_sdiv(&big(0x2), &big(0x8), 4), big(0x0)); // 2 / -8 = 0
        assert_eq!(bv_smod(&big(0x9), &big(0xe), 4), big(0xf)); // -7 mod -2 = -1
        assert_eq!(bv_udiv(&big(0x9), &big(0x2), 4), big(0x4)); // 9 / 2 = 4
        assert_eq!(bv_urem(&big(0x9), &big(0x2), 4), big(0x1)); // 9 rem 2 = 1
    }

    #[test]
    fn test_concat_and_extract() {
        assert_eq!(bv_concat(&big(0xa), &big(0xb), 4), big(0xab));
        assert_eq!(bv_concat(&big(0b101), &big(0b11), 2), big(0b10111));
        assert_eq!(bv_extract(&big(0xab), 3, 0), big(0xb));
        assert_eq!(bv_extract(&big(0xab), 7, 4), big(0xa));
        assert_eq!(bv_extract(&big(0xab), 7, 0), big(0xab));
        assert_eq!(bv_extract(&big(0b10110), 4, 4), big(1));
        assert_eq!(bv_extract(&big(0b10110), 0, 0), big(0));
    }
}
