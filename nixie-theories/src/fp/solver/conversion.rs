//! Exact symbolic FP conversion: normalize, jam, round once, and pack.
//! Follows Z3 fpa2bv_converter::mk_to_fp_float and its rounder. Vectors
//! are little-endian SAT bits; no FP value is converted through native floats.
use super::*;

impl FpSolver {
    fn conversion_constant(&mut self, value: bool) -> Var {
        let v = self.sat.new_var();
        self.sat
            .add_clause([if value { Lit::pos(v) } else { Lit::neg(v) }]);
        v
    }

    fn conversion_or(&mut self, bits: &[Var], zero: Var) -> Var {
        bits.iter().fold(zero, |a, &b| self.new_or(a, b))
    }

    fn conversion_word(value: i64, width: usize, zero: Var, one: Var) -> Vec<Var> {
        (0..width)
            .map(|i| if (value >> i) & 1 != 0 { one } else { zero })
            .collect()
    }

    fn conversion_add(&mut self, a: &[Var], b: &[Var], zero: Var) -> Vec<Var> {
        let mut carry = zero;
        a.iter()
            .zip(b)
            .map(|(&x, &y)| {
                let xy = self.new_xor(x, y);
                let bit = self.new_xor(xy, carry);
                let both = self.new_and(x, y);
                let propagated = self.new_and(xy, carry);
                carry = self.new_or(both, propagated);
                bit
            })
            .collect()
    }

    fn conversion_signed_lt(&mut self, a: &[Var], b: &[Var], zero: Var) -> Var {
        let mut lt = zero;
        for (i, (&x, &y)) in a.iter().zip(b).enumerate() {
            // Flip both sign bits to order two's-complement words unsigned.
            let (x, y) = if i + 1 == a.len() {
                (self.new_not(x), self.new_not(y))
            } else {
                (x, y)
            };
            let different = self.new_xor(x, y);
            lt = self.new_mux(different, y, lt);
        }
        lt
    }

    fn conversion_mux_word(&mut self, select: Var, a: &[Var], b: &[Var]) -> Vec<Var> {
        a.iter()
            .zip(b)
            .map(|(&x, &y)| self.new_mux(select, x, y))
            .collect()
    }

    fn conversion_equate_unless(&mut self, skip: Var, a: Var, b: Var) {
        self.sat
            .add_clause([Lit::pos(skip), Lit::neg(a), Lit::pos(b)]);
        self.sat
            .add_clause([Lit::pos(skip), Lit::pos(a), Lit::neg(b)]);
    }

    pub(super) fn encode_format_conversion(&mut self, source: &FpVar, target: &FpVar) -> bool {
        let supported = |f: FpFormat| {
            (2..=30).contains(&f.exponent_bits) && (2..=256).contains(&f.significand_bits)
        };
        if !supported(source.format) || !supported(target.format) {
            return false;
        }
        let zero = self.conversion_constant(false);
        let one = self.conversion_constant(true);
        let p = target.format.significand_bits as usize;
        let source_p = source.format.significand_bits as usize;
        // Extra signed bits cover rebiasing, leading-zero normalization and
        // rounding carry, including custom formats with tiny exponents.
        let ew = source.format.exponent_bits.max(target.format.exponent_bits) as usize + 12;
        let source_bias = (1i64 << (source.format.exponent_bits - 1)) - 1;
        let target_bias = (1i64 << (target.format.exponent_bits - 1)) - 1;
        let source_normal = self.conversion_or(&source.exponent, zero);
        let mut significand = source.significand.to_vec();
        significand.push(source_normal);
        let mut prefix = vec![zero; source_p + 1];
        for i in 0..source_p {
            prefix[i + 1] = self.new_or(prefix[i], significand[i]);
        }

        // Select the highest set bit. The resulting word has p retained
        // bits, a guard bit, and a sticky bit (OR of all further discarded bits).
        let mut normalized = vec![zero; p + 2];
        let mut leading = vec![zero; ew];
        let mut higher = zero;
        for i in (0..source_p).rev() {
            let no_higher = self.new_not(higher);
            let selected = self.new_and(significand[i], no_higher);
            higher = self.new_or(higher, significand[i]);
            for (k, slot) in normalized.iter_mut().enumerate() {
                let source_bit = if k == 0 {
                    prefix[i.saturating_sub(p)]
                } else {
                    let j = i as isize - p as isize + k as isize - 1;
                    if j < 0 {
                        zero
                    } else {
                        significand.get(j as usize).copied().unwrap_or(zero)
                    }
                };
                let term = self.new_and(selected, source_bit);
                *slot = self.new_or(*slot, term);
            }
            for (k, slot) in leading.iter_mut().enumerate() {
                if i.checked_shr(k as u32).unwrap_or(0) & 1 != 0 {
                    *slot = self.new_or(*slot, selected);
                }
            }
        }
        let mut raw_exponent = source.exponent.to_vec();
        raw_exponent.resize(ew, zero);
        let exp_one = Self::conversion_word(1, ew, zero, one);
        let adjusted = self.conversion_mux_word(source_normal, &raw_exponent, &exp_one);
        let offset = Self::conversion_word(-source_bias - source_p as i64 + 1, ew, zero, one);
        let e = self.conversion_add(&adjusted, &offset, zero);
        let e = self.conversion_add(&e, &leading, zero);
        let emin = Self::conversion_word(1 - target_bias, ew, zero, one);
        let subnormal = self.conversion_signed_lt(&e, &emin, zero);

        // Underflow: right-shift by emin-E, preserving sticky at every stage.
        // Stages beyond the significand width collapse everything into sticky.
        let inverted: Vec<_> = e.iter().map(|&v| self.new_not(v)).collect();
        let neg_e = self.conversion_add(&inverted, &exp_one, zero);
        let shift = self.conversion_add(&emin, &neg_e, zero);
        let mut shifted = normalized.clone();
        for (k, &select) in shift.iter().enumerate() {
            let amount = 1usize
                .checked_shl(k as u32)
                .unwrap_or(usize::MAX)
                .min(p + 2);
            let mut moved = vec![zero; p + 2];
            moved[0] = self.conversion_or(&shifted[..amount.min(p + 1) + 1], zero);
            for (i, slot) in moved.iter_mut().enumerate().skip(1) {
                *slot = shifted.get(i + amount).copied().unwrap_or(zero);
            }
            shifted = self.conversion_mux_word(select, &moved, &shifted);
        }
        let rounded_input = self.conversion_mux_word(subnormal, &shifted, &normalized);
        let discarded = self.new_or(rounded_input[0], rounded_input[1]);
        let increment = match self.rounding_mode {
            FpRoundingMode::RoundNearestTiesToEven => {
                let odd_or_sticky = self.new_or(rounded_input[0], rounded_input[2]);
                self.new_and(rounded_input[1], odd_or_sticky)
            }
            FpRoundingMode::RoundNearestTiesToAway => rounded_input[1],
            FpRoundingMode::RoundTowardPositive => {
                let positive = self.new_not(source.sign);
                self.new_and(positive, discarded)
            }
            FpRoundingMode::RoundTowardNegative => self.new_and(source.sign, discarded),
            FpRoundingMode::RoundTowardZero => zero,
        };
        let mut rounded = Vec::with_capacity(p);
        let mut carry = increment;
        for &bit in &rounded_input[2..] {
            rounded.push(self.new_xor(bit, carry));
            carry = self.new_and(bit, carry);
        }
        let exp_carry = self.new_mux(subnormal, rounded[p - 1], carry);
        let bias = Self::conversion_word(target_bias, ew, zero, one);
        let biased = self.conversion_add(&e, &bias, zero);
        let biased = self.conversion_mux_word(subnormal, &vec![zero; ew], &biased);
        let mut bump = vec![zero; ew];
        bump[0] = exp_carry;
        let packed_exponent = self.conversion_add(&biased, &bump, zero);
        let maximum =
            Self::conversion_word((1i64 << target.format.exponent_bits) - 1, ew, zero, one);
        let below_overflow = self.conversion_signed_lt(&packed_exponent, &maximum, zero);
        let overflow = self.new_not(below_overflow);
        let overflow_to_inf = match self.rounding_mode {
            FpRoundingMode::RoundNearestTiesToEven | FpRoundingMode::RoundNearestTiesToAway => one,
            FpRoundingMode::RoundTowardPositive => self.new_not(source.sign),
            FpRoundingMode::RoundTowardNegative => source.sign,
            FpRoundingMode::RoundTowardZero => zero,
        };
        let source_nan = self.encode_is_nan(source);
        let target_nan = self.encode_is_nan(target);
        self.sat
            .add_clause([Lit::neg(source_nan), Lit::pos(target_nan)]);
        let source_inf = self.encode_is_infinite(source);
        let source_zero = self.encode_is_zero(source);
        self.conversion_equate_unless(source_nan, source.sign, target.sign);
        for (i, &bit) in target.exponent.iter().enumerate() {
            // Largest finite has exponent ...110, infinity has ...111.
            let ovf_bit = if i == 0 { overflow_to_inf } else { one };
            let bit_value = self.new_mux(overflow, ovf_bit, packed_exponent[i]);
            let bit_value = self.new_mux(source_zero, zero, bit_value);
            let bit_value = self.new_mux(source_inf, one, bit_value);
            self.conversion_equate_unless(source_nan, bit, bit_value);
        }
        let finite_overflow = self.new_not(overflow_to_inf);
        let special_zero_fraction = self.new_or(source_inf, source_zero);
        for (i, &bit) in target.significand.iter().enumerate() {
            let bit_value = self.new_mux(overflow, finite_overflow, rounded[i]);
            let bit_value = self.new_mux(special_zero_fraction, zero, bit_value);
            self.conversion_equate_unless(source_nan, bit, bit_value);
        }
        true
    }
}
