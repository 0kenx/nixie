//! Division and remainder bit-blasting for `bvudiv`, `bvurem`, `bvsdiv`,
//! and `bvsrem`.
//!
//! Split out of `solver.rs` to keep that file under the 2000-line policy.
//!
//! All four encodings realize the Euclidean relation `a = q*b + r` with
//! `0 <= r < |b|`, plus the SMT-LIB divide-by-zero conventions. Two side
//! constraints keep the relation *exact* (soundness-critical):
//!
//! 1. The product `q*b` is computed at double width and its high half is
//!    forced to zero (when `b != 0`), so `q*b` cannot wrap modulo `2^w`.
//! 2. The final sum `q*b + r` is formed with a carry-exposing adder whose
//!    carry-out is forced to zero (when `b != 0`), so `q*b + r` cannot wrap
//!    either. Without this the equation degrades to `(q*b + r) mod 2^w = a`,
//!    admitting spurious quotients (e.g. width 4, `udiv(1, 3)` accepting
//!    `q = 5, r = 2` because `15 + 2` wraps to `1`).

use super::BvSolver;
use oxiz_core::ast::TermId;
use oxiz_sat::{Lit, Var};
use smallvec::SmallVec;

impl BvSolver {
    /// Unsigned division: result = a / b (unsigned)
    /// If b = 0, result is all 1s (SMT-LIB semantics)
    pub fn bv_udiv(&mut self, result: TermId, a: TermId, b: TermId) {
        if let (Some(va), Some(vb)) = (
            self.term_to_bv.get(&a).cloned(),
            self.term_to_bv.get(&b).cloned(),
        ) {
            assert_eq!(va.width, vb.width);
            let width = va.width as usize;
            let r = self.new_bv(result, va.width).clone();

            // Check if divisor is zero
            let b_is_zero = self.sat.new_var();
            let mut all_zero_lits: SmallVec<[Var; 32]> = SmallVec::new();
            for &bit in &vb.bits {
                all_zero_lits.push(bit);
            }
            self.encode_all_zero(b_is_zero, &all_zero_lits);

            // Create quotient and remainder variables
            let mut quot_bits: SmallVec<[Var; 32]> = SmallVec::new();
            let mut rem_bits: SmallVec<[Var; 32]> = SmallVec::new();
            for _ in 0..width {
                quot_bits.push(self.sat.new_var());
                rem_bits.push(self.sat.new_var());
            }

            // Encode: full_prod = quot * b using double-width to detect overflow
            // full_prod[0..width-1] = low bits, full_prod[width..2*width-1] = high bits
            let mut full_prod_bits: SmallVec<[Var; 64]> = SmallVec::new();
            for _ in 0..(2 * width) {
                full_prod_bits.push(self.sat.new_var());
            }
            self.encode_mul_full(&full_prod_bits, &quot_bits, &vb.bits);

            // The low bits are our prod
            let prod_bits: SmallVec<[Var; 32]> = full_prod_bits[0..width].iter().copied().collect();

            // Enforce: high bits of product are zero (no overflow) when b != 0
            for i in width..(2 * width) {
                // ~b_is_zero => ~full_prod_bits[i]
                // b_is_zero | ~full_prod_bits[i]
                self.sat
                    .add_clause([Lit::pos(b_is_zero), Lit::neg(full_prod_bits[i])]);
            }

            // Encode: sum = prod + rem, capturing the carry-out.
            let mut sum_bits: SmallVec<[Var; 32]> = SmallVec::new();
            for _ in 0..width {
                sum_bits.push(self.sat.new_var());
            }
            let carry_out = self.encode_adder_carry(&sum_bits, &prod_bits, &rem_bits);

            // No wrap: q*b + r must fit in width when b != 0, else the
            // equation would only hold modulo 2^width and admit false quotients.
            self.sat
                .add_clause([Lit::pos(b_is_zero), Lit::neg(carry_out)]);

            // Enforce: a = sum (the division equation)
            for i in 0..width {
                self.encode_bit_eq(va.bits[i], sum_bits[i]);
            }

            // Enforce: rem < b (when b != 0)
            let rem_lt_b = self.sat.new_var();
            self.encode_ult_result(&rem_bits, &vb.bits, rem_lt_b);
            self.sat
                .add_clause([Lit::pos(b_is_zero), Lit::pos(rem_lt_b)]);

            // All 1s for division by zero result
            let mut all_ones: SmallVec<[Var; 32]> = SmallVec::new();
            for _ in 0..width {
                let one = self.sat.new_var();
                self.sat.add_clause([Lit::pos(one)]);
                all_ones.push(one);
            }

            // result = b_is_zero ? all_ones : quot_bits
            for i in 0..width {
                self.encode_mux(r.bits[i], b_is_zero, all_ones[i], quot_bits[i]);
            }
        }
    }

    /// Unsigned remainder: result = a % b (unsigned)
    /// If b = 0, result = a (SMT-LIB semantics)
    pub fn bv_urem(&mut self, result: TermId, a: TermId, b: TermId) {
        if let (Some(va), Some(vb)) = (
            self.term_to_bv.get(&a).cloned(),
            self.term_to_bv.get(&b).cloned(),
        ) {
            assert_eq!(va.width, vb.width);
            let width = va.width as usize;
            let r = self.new_bv(result, va.width).clone();

            // Check if divisor is zero
            let b_is_zero = self.sat.new_var();
            let mut all_zero_lits: SmallVec<[Var; 32]> = SmallVec::new();
            for &bit in &vb.bits {
                all_zero_lits.push(bit);
            }
            self.encode_all_zero(b_is_zero, &all_zero_lits);

            // Create quotient bits (unconstrained - solver will find values)
            let mut quot_bits: SmallVec<[Var; 32]> = SmallVec::new();
            for _ in 0..width {
                quot_bits.push(self.sat.new_var());
            }

            // Create remainder bits (unconstrained - solver will find values)
            let mut rem_bits: SmallVec<[Var; 32]> = SmallVec::new();
            for _ in 0..width {
                rem_bits.push(self.sat.new_var());
            }

            // Encode: full_prod = quot * b using double-width to detect overflow
            let mut full_prod_bits: SmallVec<[Var; 64]> = SmallVec::new();
            for _ in 0..(2 * width) {
                full_prod_bits.push(self.sat.new_var());
            }
            self.encode_mul_full(&full_prod_bits, &quot_bits, &vb.bits);

            // The low bits are our prod
            let prod_bits: SmallVec<[Var; 32]> = full_prod_bits[0..width].iter().copied().collect();

            // Enforce: high bits of product are zero (no overflow) when b != 0
            for i in width..(2 * width) {
                self.sat
                    .add_clause([Lit::pos(b_is_zero), Lit::neg(full_prod_bits[i])]);
            }

            // Encode: sum = prod + rem, capturing the carry-out.
            let mut sum_bits: SmallVec<[Var; 32]> = SmallVec::new();
            for _ in 0..width {
                sum_bits.push(self.sat.new_var());
            }
            let carry_out = self.encode_adder_carry(&sum_bits, &prod_bits, &rem_bits);

            // No wrap: q*b + r must fit in width when b != 0.
            self.sat
                .add_clause([Lit::pos(b_is_zero), Lit::neg(carry_out)]);

            // Enforce: a = sum (the division equation a = q*b + r)
            for i in 0..width {
                self.encode_bit_eq(va.bits[i], sum_bits[i]);
            }

            // Encode: rem < b (remainder must be less than divisor)
            let rem_lt_b = self.sat.new_var();
            self.encode_ult_result(&rem_bits, &vb.bits, rem_lt_b);
            // This constraint only applies when b != 0
            self.sat
                .add_clause([Lit::pos(b_is_zero), Lit::pos(rem_lt_b)]);

            // result = b_is_zero ? a : rem_bits
            for i in 0..width {
                self.encode_mux(r.bits[i], b_is_zero, va.bits[i], rem_bits[i]);
            }
        }
    }

    /// Signed division: result = a / b (signed, two's complement)
    /// If b = 0, result = all 1s (SMT-LIB semantics)
    pub fn bv_sdiv(&mut self, result: TermId, a: TermId, b: TermId) {
        if let (Some(va), Some(vb)) = (
            self.term_to_bv.get(&a).cloned(),
            self.term_to_bv.get(&b).cloned(),
        ) {
            assert_eq!(va.width, vb.width);
            let width = va.width as usize;
            let r = self.new_bv(result, va.width).clone();

            // Check if divisor is zero
            let b_is_zero = self.sat.new_var();
            let mut all_zero_lits: SmallVec<[Var; 32]> = SmallVec::new();
            for &bit in &vb.bits {
                all_zero_lits.push(bit);
            }
            self.encode_all_zero(b_is_zero, &all_zero_lits);

            // Get sign bits
            let sign_a = va.bits[width - 1];
            let sign_b = vb.bits[width - 1];

            // Compute absolute values using MUX
            let mut abs_a: SmallVec<[Var; 32]> = SmallVec::new();
            let mut abs_b: SmallVec<[Var; 32]> = SmallVec::new();
            for _ in 0..width {
                abs_a.push(self.sat.new_var());
                abs_b.push(self.sat.new_var());
            }

            // neg_a = -a (two's complement)
            let mut neg_a: SmallVec<[Var; 32]> = SmallVec::new();
            for _ in 0..width {
                neg_a.push(self.sat.new_var());
            }
            self.encode_two_complement(&neg_a, &va.bits);

            // abs_a = sign_a ? neg_a : a
            for i in 0..width {
                self.encode_mux(abs_a[i], sign_a, neg_a[i], va.bits[i]);
            }

            // neg_b = -b (two's complement)
            let mut neg_b: SmallVec<[Var; 32]> = SmallVec::new();
            for _ in 0..width {
                neg_b.push(self.sat.new_var());
            }
            self.encode_two_complement(&neg_b, &vb.bits);

            // abs_b = sign_b ? neg_b : b
            for i in 0..width {
                self.encode_mux(abs_b[i], sign_b, neg_b[i], vb.bits[i]);
            }

            // Create quot_abs and rem_abs for unsigned division
            let mut quot_abs: SmallVec<[Var; 32]> = SmallVec::new();
            let mut rem_abs: SmallVec<[Var; 32]> = SmallVec::new();
            for _ in 0..width {
                quot_abs.push(self.sat.new_var());
                rem_abs.push(self.sat.new_var());
            }

            // Encode division constraint: abs_a = quot_abs * abs_b + rem_abs
            // Use double-width multiplication to detect overflow
            let mut full_prod: SmallVec<[Var; 64]> = SmallVec::new();
            for _ in 0..(2 * width) {
                full_prod.push(self.sat.new_var());
            }
            self.encode_mul_full(&full_prod, &quot_abs, &abs_b);

            // The low bits are our prod
            let prod: SmallVec<[Var; 32]> = full_prod[0..width].iter().copied().collect();

            // Enforce: high bits of product are zero (no overflow) when b != 0
            for i in width..(2 * width) {
                self.sat
                    .add_clause([Lit::pos(b_is_zero), Lit::neg(full_prod[i])]);
            }

            let mut sum: SmallVec<[Var; 32]> = SmallVec::new();
            for _ in 0..width {
                sum.push(self.sat.new_var());
            }
            let carry_out = self.encode_adder_carry(&sum, &prod, &rem_abs);

            // No wrap: quot_abs*abs_b + rem_abs must fit in width when b != 0.
            self.sat
                .add_clause([Lit::pos(b_is_zero), Lit::neg(carry_out)]);

            // Enforce abs_a = sum (unconditionally - division equation always holds)
            for i in 0..width {
                self.encode_bit_eq(abs_a[i], sum[i]);
            }

            // Enforce rem_abs < abs_b (unconditionally for well-formed division)
            let rem_lt_b = self.sat.new_var();
            self.encode_ult_result(&rem_abs, &abs_b, rem_lt_b);
            // Only enforce when b != 0
            self.sat
                .add_clause([Lit::pos(b_is_zero), Lit::pos(rem_lt_b)]);

            // Result sign: sign_a XOR sign_b
            let result_sign = self.sat.new_var();
            self.encode_xor(result_sign, sign_a, sign_b);

            // neg_quot = -quot_abs
            let mut neg_quot: SmallVec<[Var; 32]> = SmallVec::new();
            for _ in 0..width {
                neg_quot.push(self.sat.new_var());
            }
            self.encode_two_complement(&neg_quot, &quot_abs);

            // signed_quot = result_sign ? neg_quot : quot_abs
            let mut signed_quot: SmallVec<[Var; 32]> = SmallVec::new();
            for _ in 0..width {
                signed_quot.push(self.sat.new_var());
            }
            for i in 0..width {
                self.encode_mux(signed_quot[i], result_sign, neg_quot[i], quot_abs[i]);
            }

            // All 1s for division by zero result
            let mut all_ones: SmallVec<[Var; 32]> = SmallVec::new();
            for _ in 0..width {
                let one = self.sat.new_var();
                self.sat.add_clause([Lit::pos(one)]); // Force to 1
                all_ones.push(one);
            }

            // result = b_is_zero ? all_ones : signed_quot
            for i in 0..width {
                self.encode_mux(r.bits[i], b_is_zero, all_ones[i], signed_quot[i]);
            }
        }
    }

    /// Signed remainder: result = a % b (signed)
    /// Sign of result matches sign of dividend a
    /// If b = 0, result = a (SMT-LIB semantics)
    pub fn bv_srem(&mut self, result: TermId, a: TermId, b: TermId) {
        if let (Some(va), Some(vb)) = (
            self.term_to_bv.get(&a).cloned(),
            self.term_to_bv.get(&b).cloned(),
        ) {
            assert_eq!(va.width, vb.width);
            let width = va.width as usize;
            let r = self.new_bv(result, va.width).clone();

            // Check if divisor is zero
            let b_is_zero = self.sat.new_var();
            let mut all_zero_lits: SmallVec<[Var; 32]> = SmallVec::new();
            for &bit in &vb.bits {
                all_zero_lits.push(bit);
            }
            self.encode_all_zero(b_is_zero, &all_zero_lits);

            // Get sign bits
            let sign_a = va.bits[width - 1];
            let sign_b = vb.bits[width - 1];

            // Compute absolute values using MUX
            let mut abs_a: SmallVec<[Var; 32]> = SmallVec::new();
            let mut abs_b: SmallVec<[Var; 32]> = SmallVec::new();
            for _ in 0..width {
                abs_a.push(self.sat.new_var());
                abs_b.push(self.sat.new_var());
            }

            // neg_a = -a (two's complement)
            let mut neg_a: SmallVec<[Var; 32]> = SmallVec::new();
            for _ in 0..width {
                neg_a.push(self.sat.new_var());
            }
            self.encode_two_complement(&neg_a, &va.bits);

            // abs_a = sign_a ? neg_a : a
            for i in 0..width {
                self.encode_mux(abs_a[i], sign_a, neg_a[i], va.bits[i]);
            }

            // neg_b = -b (two's complement)
            let mut neg_b: SmallVec<[Var; 32]> = SmallVec::new();
            for _ in 0..width {
                neg_b.push(self.sat.new_var());
            }
            self.encode_two_complement(&neg_b, &vb.bits);

            // abs_b = sign_b ? neg_b : b
            for i in 0..width {
                self.encode_mux(abs_b[i], sign_b, neg_b[i], vb.bits[i]);
            }

            // Create quot_abs and rem_abs for unsigned division
            let mut quot_abs: SmallVec<[Var; 32]> = SmallVec::new();
            let mut rem_abs: SmallVec<[Var; 32]> = SmallVec::new();
            for _ in 0..width {
                quot_abs.push(self.sat.new_var());
                rem_abs.push(self.sat.new_var());
            }

            // Encode division constraint: abs_a = quot_abs * abs_b + rem_abs
            // Use double-width multiplication to detect overflow
            let mut full_prod: SmallVec<[Var; 64]> = SmallVec::new();
            for _ in 0..(2 * width) {
                full_prod.push(self.sat.new_var());
            }
            self.encode_mul_full(&full_prod, &quot_abs, &abs_b);

            // The low bits are our prod
            let prod: SmallVec<[Var; 32]> = full_prod[0..width].iter().copied().collect();

            // Enforce: high bits of product are zero (no overflow) when b != 0
            for i in width..(2 * width) {
                self.sat
                    .add_clause([Lit::pos(b_is_zero), Lit::neg(full_prod[i])]);
            }

            let mut sum: SmallVec<[Var; 32]> = SmallVec::new();
            for _ in 0..width {
                sum.push(self.sat.new_var());
            }
            let carry_out = self.encode_adder_carry(&sum, &prod, &rem_abs);

            // No wrap: quot_abs*abs_b + rem_abs must fit in width when b != 0.
            self.sat
                .add_clause([Lit::pos(b_is_zero), Lit::neg(carry_out)]);

            // Enforce abs_a = sum (unconditionally - division equation always holds)
            for i in 0..width {
                self.encode_bit_eq(abs_a[i], sum[i]);
            }

            // Enforce rem_abs < abs_b (only when b != 0)
            let rem_lt_b = self.sat.new_var();
            self.encode_ult_result(&rem_abs, &abs_b, rem_lt_b);
            self.sat
                .add_clause([Lit::pos(b_is_zero), Lit::pos(rem_lt_b)]);

            // neg_rem = -rem_abs (for negative dividend case)
            let mut neg_rem: SmallVec<[Var; 32]> = SmallVec::new();
            for _ in 0..width {
                neg_rem.push(self.sat.new_var());
            }
            self.encode_two_complement(&neg_rem, &rem_abs);

            // signed_rem = sign_a ? neg_rem : rem_abs
            // (sign of result matches sign of dividend)
            let mut signed_rem: SmallVec<[Var; 32]> = SmallVec::new();
            for _ in 0..width {
                signed_rem.push(self.sat.new_var());
            }
            for i in 0..width {
                self.encode_mux(signed_rem[i], sign_a, neg_rem[i], rem_abs[i]);
            }

            // result = b_is_zero ? a : signed_rem
            for i in 0..width {
                self.encode_mux(r.bits[i], b_is_zero, va.bits[i], signed_rem[i]);
            }
        }
    }
}
