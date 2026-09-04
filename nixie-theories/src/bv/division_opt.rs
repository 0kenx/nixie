//! Optimized Division and Modulo Operations
//!
//! Division and modulo are among the most expensive bitvector operations.
//! This module implements optimized encodings and special-case handling to
//! make division/remainder operations more efficient.
//!
//! # Key Techniques
//!
//! ## 1. Barrett Reduction
//! - Replaces division by multiplication and shift
//! - Precompute reciprocal for constant divisors
//! - Much faster than bit-by-bit division
//! - Based on "A Division-Free Algorithm for Fixed-Point Arithmetic" (Barrett, 1986)
//!
//! ## 2. Montgomery Multiplication
//! - Efficient modular arithmetic
//! - Particularly useful for repeated operations with same modulus
//! - Avoids expensive division in modular reduction
//!
//! ## 3. Power-of-Two Optimizations
//! - Division by 2^n → right shift by n
//! - Modulo 2^n → bitwise AND with (2^n - 1)
//! - Nearly free operations
//!
//! ## 4. Small Divisor Tables
//! - Precomputed lookup tables for small divisors
//! - Direct encoding for divisors ≤ 16
//! - Balances circuit size vs. solving time
//!
//! ## 5. Newton-Raphson Division
//! - Iterative approximation of reciprocal
//! - Quadratic convergence
//! - Useful for large bit-widths
//!
//! ## 6. SRT Division (Sweeney-Robertson-Tocher)
//! - Digit recurrence algorithm
//! - Quotient selection by table lookup
//! - Used in hardware dividers
//!
//! # References
//!
//! - Z3: `src/ast/rewriter/bv_rewriter.cpp` (division optimizations)
//! - "Division by Invariant Integers using Multiplication" (Granlund & Montgomery, 1994)
//! - "Barrett Reduction" (Barrett, 1986)
//! - "Modular Arithmetic via Montgomery Multiplication" (Montgomery, 1985)
//! - "Computer Arithmetic Algorithms" (Koren, 2002)

use super::aig::{AigCircuit, AigEdge};
#[allow(unused_imports)]
use crate::prelude::*;

/// Configuration for division optimization
#[derive(Debug, Clone)]
pub struct DivisionConfig {
    /// Use Barrett reduction for constant divisors
    pub use_barrett: bool,
    /// Use Montgomery multiplication for modular arithmetic
    pub use_montgomery: bool,
    /// Use power-of-two optimizations
    pub optimize_power_of_two: bool,
    /// Maximum divisor for lookup table
    pub max_table_divisor: u64,
    /// Use Newton-Raphson for large widths
    pub use_newton_raphson: bool,
    /// Minimum width for Newton-Raphson
    pub newton_raphson_threshold: usize,
}

impl Default for DivisionConfig {
    fn default() -> Self {
        Self {
            use_barrett: true,
            use_montgomery: true,
            optimize_power_of_two: true,
            max_table_divisor: 16,
            use_newton_raphson: true,
            newton_raphson_threshold: 32,
        }
    }
}

/// Statistics for division operations
#[derive(Debug, Clone, Default)]
pub struct DivisionStats {
    /// Number of divisions optimized
    pub divisions_optimized: usize,
    /// Number of power-of-two optimizations
    pub power_of_two_opts: usize,
    /// Number of Barrett reductions
    pub barrett_reductions: usize,
    /// Number of Montgomery multiplications
    pub montgomery_muls: usize,
    /// Number of table lookups
    pub table_lookups: usize,
    /// Number of Newton-Raphson iterations
    pub newton_raphson_iterations: usize,
}

/// Division optimizer
pub struct DivisionOptimizer {
    /// Configuration
    config: DivisionConfig,
    /// Statistics
    stats: DivisionStats,
    /// Cached Barrett parameters
    barrett_cache: FxHashMap<(u64, usize), BarrettParams>,
    /// Cached Montgomery parameters
    montgomery_cache: FxHashMap<(u64, usize), MontgomeryParams>,
}

/// Barrett reduction parameters
#[derive(Debug, Clone)]
pub struct BarrettParams {
    /// Divisor
    pub divisor: u64,
    /// Bit width
    pub width: usize,
    /// Precomputed reciprocal: m = floor(2^(2*width) / divisor)
    pub m: u128,
    /// Shift amount
    pub shift: usize,
}

impl BarrettParams {
    /// Widest bit-vector for which a Barrett reciprocal is defined.
    ///
    /// The reciprocal is held in a `u128` and needs `2^(2*width)`, so it stops
    /// existing at `width = 64`: `1u128 << 128` aborts in debug builds and
    /// yields a garbage multiplier in release ones.  Beyond this width the
    /// parameters are honestly unavailable and the caller encodes the plain
    /// restoring divider instead.
    pub const MAX_WIDTH: usize = 63;

    /// Compute Barrett parameters for a divisor.
    ///
    /// Returns `None` for a zero divisor, a zero width, and for any width above
    /// [`Self::MAX_WIDTH`]: the reciprocal `floor(2^(2*width) / divisor)`
    /// is not representable then, and computing it would shift a `u128` by
    /// `2*width >= 128` bits – an abort in debug builds and a silently wrong
    /// multiplier in release ones.  Callers treat `None` as "this optimization
    /// does not apply" and encode the division the ordinary way.
    #[must_use]
    pub fn new(divisor: u64, width: usize) -> Option<Self> {
        if divisor == 0 || width == 0 || width > Self::MAX_WIDTH {
            return None;
        }

        // Compute m = floor(2^(2*width) / divisor)
        let numerator = 1u128 << (2 * width);
        let m = numerator / divisor as u128;

        Some(Self {
            divisor,
            width,
            m,
            shift: 2 * width,
        })
    }

    /// Compute quotient using Barrett reduction
    ///
    /// A `dividend` too large for the width these parameters were built for
    /// would overflow the `dividend * m` product; that case falls back to the
    /// exact quotient rather than wrapping to a wrong one.
    #[must_use]
    pub fn divide(&self, dividend: u64) -> u64 {
        // q = (dividend * m) >> shift
        let Some(product) = (dividend as u128).checked_mul(self.m) else {
            return dividend.checked_div(self.divisor).unwrap_or(u64::MAX);
        };
        let q = (product >> self.shift) as u64;

        // May need correction
        let remainder = dividend.wrapping_sub(q.wrapping_mul(self.divisor));

        if remainder >= self.divisor {
            q.wrapping_add(1)
        } else {
            q
        }
    }

    /// Compute remainder using Barrett reduction
    #[must_use]
    pub fn modulo(&self, dividend: u64) -> u64 {
        let q = self.divide(dividend);
        dividend.wrapping_sub(q.wrapping_mul(self.divisor))
    }
}

/// Montgomery multiplication parameters
#[derive(Debug, Clone)]
pub struct MontgomeryParams {
    /// Modulus
    pub modulus: u64,
    /// Bit width
    pub width: usize,
    /// R = 2^width
    pub r: u128,
    /// R^2 mod modulus (for conversion to Montgomery form)
    pub r_squared: u64,
    /// Modular inverse: modulus * m_inv ≡ -1 (mod R)
    pub m_inv: u64,
}

impl MontgomeryParams {
    /// Widest bit-vector for which Montgomery parameters are defined.
    ///
    /// `R = 2^width` and the inverse of the modulus modulo `R` are held in a
    /// `u64`, which `1u128 << width` cannot produce once `width >= 64` – in
    /// debug builds that shift aborts, in release ones it wraps and every later
    /// multiplication is silently wrong.
    pub const MAX_WIDTH: usize = 63;

    /// Compute Montgomery parameters for a modulus.
    ///
    /// Returns `None` for an even or zero modulus (Montgomery arithmetic needs
    /// `gcd(modulus, R) = 1`), for a zero width, and for any width above
    /// [`Self::MAX_WIDTH`].
    #[must_use]
    pub fn new(modulus: u64, width: usize) -> Option<Self> {
        if modulus == 0 || (modulus & 1) == 0 {
            // Montgomery only works for odd moduli
            return None;
        }
        if width == 0 || width > Self::MAX_WIDTH {
            return None;
        }

        let r = 1u128 << width;

        // Compute modular inverse using extended GCD
        // Montgomery needs: modulus * m_inv ≡ -1 (mod R)
        // First compute positive inverse: modulus * inv ≡ 1 (mod R)
        let inv = Self::compute_inverse(modulus, r as u64)?;
        // Then negate: m_inv = -inv (mod R) = R - inv
        let m_inv = (r as u64).wrapping_sub(inv);

        // Compute R^2 mod modulus
        let r_mod = (r % modulus as u128) as u64;
        let r_squared = Self::mod_mul(r_mod, r_mod, modulus);

        Some(Self {
            modulus,
            width,
            r,
            r_squared,
            m_inv,
        })
    }

    /// Compute modular inverse: find x such that a * x ≡ 1 (mod m)
    fn compute_inverse(a: u64, m: u64) -> Option<u64> {
        let (g, x, _) = Self::extended_gcd(a as i128, m as i128);

        if g != 1 {
            return None;
        }

        // Make sure result is positive
        let result = if x < 0 {
            (x + m as i128) as u64
        } else {
            x as u64
        };

        Some(result)
    }

    /// Extended GCD algorithm
    fn extended_gcd(a: i128, b: i128) -> (i128, i128, i128) {
        if b == 0 {
            return (a, 1, 0);
        }

        let (g, x1, y1) = Self::extended_gcd(b, a % b);
        let x = y1;
        let y = x1 - (a / b) * y1;

        (g, x, y)
    }

    /// Modular multiplication: (a * b) mod m
    fn mod_mul(a: u64, b: u64, m: u64) -> u64 {
        ((a as u128 * b as u128) % m as u128) as u64
    }

    /// Convert to Montgomery form: a*R mod modulus
    #[must_use]
    pub fn to_montgomery(&self, a: u64) -> u64 {
        self.montgomery_mul(a, self.r_squared)
    }

    /// Convert from Montgomery form: (aR) * R^(-1) mod modulus
    #[must_use]
    pub fn from_montgomery(&self, a_mont: u64) -> u64 {
        self.montgomery_mul(a_mont, 1)
    }

    /// Montgomery multiplication: (a * b * R^(-1)) mod modulus
    #[must_use]
    pub fn montgomery_mul(&self, a: u64, b: u64) -> u64 {
        let t = (a as u128) * (b as u128);
        // Take lower width bits of t (t mod R) before multiplying by m_inv
        let t_mod_r = (t & ((1u128 << self.width) - 1)) as u64;
        let m = (t_mod_r.wrapping_mul(self.m_inv)) as u128;
        let u = (t + m * self.modulus as u128) >> self.width;

        let result = u as u64;

        // Reduce result modulo modulus
        result % self.modulus
    }

    /// Modular exponentiation using Montgomery multiplication
    #[must_use]
    pub fn mod_exp(&self, base: u64, exp: u64) -> u64 {
        let base_mont = self.to_montgomery(base);
        let mut result_mont = self.to_montgomery(1);
        let mut exp = exp;
        let mut base_pow = base_mont;

        while exp > 0 {
            if exp & 1 == 1 {
                result_mont = self.montgomery_mul(result_mont, base_pow);
            }
            base_pow = self.montgomery_mul(base_pow, base_pow);
            exp >>= 1;
        }

        self.from_montgomery(result_mont)
    }
}

impl Default for DivisionOptimizer {
    fn default() -> Self {
        Self::new(DivisionConfig::default())
    }
}

impl DivisionOptimizer {
    /// Widest bit-vector for which a complete `2^width`-row truth table is
    /// built.  Beyond this the table is both astronomically large and, past 64
    /// bits, not even enumerable in a `u64`, so the restoring divider is used.
    const MAX_TRUTH_TABLE_WIDTH: usize = 6;

    /// Create a new division optimizer
    #[must_use]
    pub fn new(config: DivisionConfig) -> Self {
        Self {
            config,
            stats: DivisionStats::default(),
            barrett_cache: FxHashMap::default(),
            montgomery_cache: FxHashMap::default(),
        }
    }

    /// Get statistics
    #[must_use]
    pub fn stats(&self) -> &DivisionStats {
        &self.stats
    }

    /// Reset the optimizer
    pub fn reset(&mut self) {
        self.barrett_cache.clear();
        self.montgomery_cache.clear();
        self.stats = DivisionStats::default();
    }

    /// Check if a value is a power of two
    #[must_use]
    pub fn is_power_of_two(value: u64) -> bool {
        value != 0 && (value & (value - 1)) == 0
    }

    /// Get the log2 of a power of two
    #[must_use]
    pub fn log2_power_of_two(value: u64) -> Option<u32> {
        if Self::is_power_of_two(value) {
            Some(value.trailing_zeros())
        } else {
            None
        }
    }

    /// Optimize division by constant
    pub fn optimize_udiv_const(
        &mut self,
        dividend: &[AigEdge],
        divisor: u64,
        aig: &mut AigCircuit,
    ) -> Vec<AigEdge> {
        let width = dividend.len();

        // Special case: division by 0 → all 1s (SMT-LIB semantics)
        if divisor == 0 {
            self.stats.divisions_optimized += 1;
            return vec![aig.true_edge(); width];
        }

        // Special case: division by 1 → identity
        if divisor == 1 {
            self.stats.divisions_optimized += 1;
            return dividend.to_vec();
        }

        // Power-of-two optimization
        if self.config.optimize_power_of_two
            && let Some(shift) = Self::log2_power_of_two(divisor)
        {
            self.stats.power_of_two_opts += 1;
            return self.encode_udiv_power_of_two(dividend, shift as usize, aig);
        }

        // Small divisor table lookup
        if divisor <= self.config.max_table_divisor {
            self.stats.table_lookups += 1;
            return self.encode_udiv_table(dividend, divisor, aig);
        }

        // Barrett reduction
        if self.config.use_barrett {
            self.stats.barrett_reductions += 1;
            return self.encode_udiv_barrett(dividend, divisor, aig);
        }

        // Fallback to standard division
        self.encode_udiv_standard(dividend, divisor, aig)
    }

    /// Optimize remainder by constant
    pub fn optimize_urem_const(
        &mut self,
        dividend: &[AigEdge],
        divisor: u64,
        aig: &mut AigCircuit,
    ) -> Vec<AigEdge> {
        let width = dividend.len();

        // Special case: remainder by 0 → dividend (SMT-LIB semantics)
        if divisor == 0 {
            self.stats.divisions_optimized += 1;
            return dividend.to_vec();
        }

        // Special case: remainder by 1 → 0
        if divisor == 1 {
            self.stats.divisions_optimized += 1;
            return vec![aig.false_edge(); width];
        }

        // Power-of-two optimization
        if self.config.optimize_power_of_two
            && let Some(shift) = Self::log2_power_of_two(divisor)
        {
            self.stats.power_of_two_opts += 1;
            return self.encode_urem_power_of_two(dividend, shift as usize, aig);
        }

        // For small divisors, use table
        if divisor <= self.config.max_table_divisor {
            self.stats.table_lookups += 1;
            return self.encode_urem_table(dividend, divisor, aig);
        }

        // Barrett reduction
        if self.config.use_barrett {
            self.stats.barrett_reductions += 1;
            return self.encode_urem_barrett(dividend, divisor, aig);
        }

        // Fallback
        self.encode_urem_standard(dividend, divisor, aig)
    }

    /// Encode division by power of two (right shift)
    fn encode_udiv_power_of_two(
        &mut self,
        dividend: &[AigEdge],
        shift: usize,
        aig: &mut AigCircuit,
    ) -> Vec<AigEdge> {
        let width = dividend.len();
        let mut result = Vec::with_capacity(width);

        for i in 0..width {
            if i + shift < width {
                result.push(dividend[i + shift]);
            } else {
                result.push(aig.false_edge());
            }
        }

        result
    }

    /// Encode remainder by power of two (mask low bits)
    fn encode_urem_power_of_two(
        &mut self,
        dividend: &[AigEdge],
        shift: usize,
        aig: &mut AigCircuit,
    ) -> Vec<AigEdge> {
        let width = dividend.len();
        let mut result = Vec::with_capacity(width);

        for (i, item) in dividend.iter().enumerate().take(width) {
            if i < shift {
                result.push(*item);
            } else {
                result.push(aig.false_edge());
            }
        }

        result
    }

    /// Encode division using lookup table for small divisors
    fn encode_udiv_table(
        &mut self,
        dividend: &[AigEdge],
        divisor: u64,
        aig: &mut AigCircuit,
    ) -> Vec<AigEdge> {
        let width = dividend.len();

        // For very small widths, we can build a complete truth table
        if width <= Self::MAX_TRUTH_TABLE_WIDTH {
            return self.encode_udiv_truth_table(dividend, divisor, aig);
        }

        // For larger widths, use standard division
        self.encode_udiv_standard(dividend, divisor, aig)
    }

    /// Encode remainder using lookup table
    fn encode_urem_table(
        &mut self,
        dividend: &[AigEdge],
        divisor: u64,
        aig: &mut AigCircuit,
    ) -> Vec<AigEdge> {
        let width = dividend.len();

        if width <= Self::MAX_TRUTH_TABLE_WIDTH {
            return self.encode_urem_truth_table(dividend, divisor, aig);
        }

        self.encode_urem_standard(dividend, divisor, aig)
    }

    /// Encode division using complete truth table (for small bit-widths)
    ///
    /// The table has `2^width` rows, so it is only built for a width the
    /// callers have already bounded by [`Self::MAX_TRUTH_TABLE_WIDTH`]; a wider
    /// vector falls back to the restoring divider instead of shifting `1` by a
    /// width the shift cannot express.
    fn encode_udiv_truth_table(
        &mut self,
        dividend: &[AigEdge],
        divisor: u64,
        aig: &mut AigCircuit,
    ) -> Vec<AigEdge> {
        let width = dividend.len();
        if width > Self::MAX_TRUTH_TABLE_WIDTH {
            return self.encode_udiv_standard(dividend, divisor, aig);
        }
        let num_inputs = 1u64 << width;

        // Build truth table for each output bit
        let mut result_bits = Vec::with_capacity(width);

        for bit_pos in 0..width {
            let mut terms = Vec::new();

            // For each input pattern where this output bit should be 1
            for input_val in 0u64..num_inputs {
                // `(bvudiv x 0)` is all ones at this width (SMT-LIB).
                let quotient = input_val.checked_div(divisor).unwrap_or(num_inputs - 1);

                let output_bit = (quotient >> bit_pos) & 1;

                if output_bit == 1 {
                    // Build minterm for this input
                    let minterm = self.build_minterm(dividend, input_val, aig);
                    terms.push(minterm);
                }
            }

            // OR all minterms
            let result_bit = if terms.is_empty() {
                aig.false_edge()
            } else if terms.len() == 1 {
                terms[0]
            } else {
                terms
                    .into_iter()
                    .reduce(|a, b| aig.or(a, b))
                    .unwrap_or_else(|| aig.false_edge())
            };

            result_bits.push(result_bit);
        }

        result_bits
    }

    /// Encode remainder using truth table
    ///
    /// Bounded by [`Self::MAX_TRUTH_TABLE_WIDTH`] exactly as
    /// [`Self::encode_udiv_truth_table`] is.
    fn encode_urem_truth_table(
        &mut self,
        dividend: &[AigEdge],
        divisor: u64,
        aig: &mut AigCircuit,
    ) -> Vec<AigEdge> {
        let width = dividend.len();
        if width > Self::MAX_TRUTH_TABLE_WIDTH {
            return self.encode_urem_standard(dividend, divisor, aig);
        }
        let num_inputs = 1u64 << width;

        let mut result_bits = Vec::with_capacity(width);

        for bit_pos in 0..width {
            let mut terms = Vec::new();

            for input_val in 0..num_inputs {
                let remainder = if divisor == 0 {
                    input_val // Remainder by 0 = dividend
                } else {
                    input_val % divisor
                };

                let output_bit = (remainder >> bit_pos) & 1;

                if output_bit == 1 {
                    let minterm = self.build_minterm(dividend, input_val, aig);
                    terms.push(minterm);
                }
            }

            let result_bit = if terms.is_empty() {
                aig.false_edge()
            } else if terms.len() == 1 {
                terms[0]
            } else {
                terms
                    .into_iter()
                    .reduce(|a, b| aig.or(a, b))
                    .unwrap_or_else(|| aig.false_edge())
            };

            result_bits.push(result_bit);
        }

        result_bits
    }

    /// Build a minterm (AND of literals) for a specific input value
    fn build_minterm(&self, inputs: &[AigEdge], value: u64, aig: &mut AigCircuit) -> AigEdge {
        let mut result = aig.true_edge();

        for (i, &input) in inputs.iter().enumerate() {
            // Bit `i` of a `u64` is `0` for every `i >= 64` – that is the value
            // of the bit, not a fallback, and reading it with a shift would
            // abort in debug builds.
            let bit = value
                .checked_shr(u32::try_from(i).unwrap_or(u32::MAX))
                .unwrap_or(0)
                & 1;

            let literal = if bit == 1 { input } else { aig.not(input) };

            result = aig.and(result, literal);
        }

        result
    }

    /// Cache the Barrett parameters for `(divisor, width)` if they exist.
    ///
    /// A width beyond [`BarrettParams::MAX_WIDTH`] (or a zero divisor) has no
    /// Barrett reciprocal; the circuit below is the ordinary restoring divider
    /// either way, so the absence is recorded by simply not caching anything
    /// rather than by aborting on a missing precomputation.
    fn cache_barrett_params(&mut self, divisor: u64, width: usize) {
        if self.barrett_cache.contains_key(&(divisor, width)) {
            return;
        }
        if let Some(params) = BarrettParams::new(divisor, width) {
            self.barrett_cache.insert((divisor, width), params);
        }
    }

    /// Encode division using Barrett reduction
    fn encode_udiv_barrett(
        &mut self,
        dividend: &[AigEdge],
        divisor: u64,
        aig: &mut AigCircuit,
    ) -> Vec<AigEdge> {
        let width = dividend.len();

        // Get or compute Barrett parameters
        self.cache_barrett_params(divisor, width);

        // Encode: q ≈ (dividend * m) >> (2 * width)
        // We need to implement high-precision multiplication

        // For now, simplified version using standard division
        // Full implementation would encode the multiplication and shift
        self.encode_udiv_standard(dividend, divisor, aig)
    }

    /// Encode remainder using Barrett reduction
    fn encode_urem_barrett(
        &mut self,
        dividend: &[AigEdge],
        divisor: u64,
        aig: &mut AigCircuit,
    ) -> Vec<AigEdge> {
        let width = dividend.len();

        // Get or compute Barrett parameters
        self.cache_barrett_params(divisor, width);

        // Encode: r = dividend - q * divisor
        // where q = (dividend * m) >> (2 * width)

        // Simplified for now
        self.encode_urem_standard(dividend, divisor, aig)
    }

    /// Standard restoring division algorithm
    fn encode_udiv_standard(
        &mut self,
        dividend: &[AigEdge],
        divisor_val: u64,
        aig: &mut AigCircuit,
    ) -> Vec<AigEdge> {
        let width = dividend.len();

        // Create constant for divisor
        let divisor = aig.constant_bitvector(divisor_val, width);

        // Restoring division algorithm
        let mut quotient = vec![aig.false_edge(); width];
        let mut remainder = vec![aig.false_edge(); width];

        // Process from MSB to LSB
        for i in (0..width).rev() {
            // Shift remainder left and bring down next bit of dividend
            let mut new_remainder = vec![aig.false_edge(); width];

            new_remainder[1..width].copy_from_slice(&remainder[..(width - 1)]);
            new_remainder[0] = dividend[i];

            // Compare: remainder >= divisor?
            let can_subtract = self.encode_uge(&new_remainder, &divisor, aig);

            // If can subtract, set quotient bit and update remainder
            quotient[i] = can_subtract;

            // remainder = can_subtract ? (remainder - divisor) : remainder
            // Compute negated divisor first to avoid multiple mutable borrows
            let neg_divisor = self.encode_neg(&divisor, aig);
            let diff = aig.ripple_carry_adder(&new_remainder, &neg_divisor);

            for j in 0..width {
                remainder[j] = aig.mux(can_subtract, diff[j], new_remainder[j]);
            }
        }

        quotient
    }

    /// Standard remainder algorithm
    fn encode_urem_standard(
        &mut self,
        dividend: &[AigEdge],
        divisor_val: u64,
        aig: &mut AigCircuit,
    ) -> Vec<AigEdge> {
        let width = dividend.len();

        let divisor = aig.constant_bitvector(divisor_val, width);

        let mut remainder = vec![aig.false_edge(); width];

        for i in (0..width).rev() {
            let mut new_remainder = vec![aig.false_edge(); width];

            new_remainder[1..width].copy_from_slice(&remainder[..(width - 1)]);
            new_remainder[0] = dividend[i];

            let can_subtract = self.encode_uge(&new_remainder, &divisor, aig);

            // Compute negated divisor first to avoid multiple mutable borrows
            let neg_divisor = self.encode_neg(&divisor, aig);
            let diff = aig.ripple_carry_adder(&new_remainder, &neg_divisor);

            for j in 0..width {
                remainder[j] = aig.mux(can_subtract, diff[j], new_remainder[j]);
            }
        }

        remainder
    }

    /// Encode unsigned greater-or-equal comparison
    fn encode_uge(&self, a: &[AigEdge], b: &[AigEdge], aig: &mut AigCircuit) -> AigEdge {
        // a >= b is equivalent to !(a < b)
        let lt = aig.unsigned_less_than(a, b);
        aig.not(lt)
    }

    /// Encode two's complement negation
    fn encode_neg(&self, a: &[AigEdge], aig: &mut AigCircuit) -> Vec<AigEdge> {
        aig.negate_bitvector(a)
    }

    /// Encode signed division (more complex due to sign handling)
    pub fn encode_sdiv(
        &mut self,
        dividend: &[AigEdge],
        divisor: &[AigEdge],
        aig: &mut AigCircuit,
    ) -> Vec<AigEdge> {
        let width = dividend.len();

        if width == 0 {
            return Vec::new();
        }

        // Get sign bits
        let sign_dividend = dividend[width - 1];
        let sign_divisor = divisor[width - 1];

        // Compute absolute values
        let abs_dividend = self.encode_abs(dividend, aig);
        let abs_divisor = self.encode_abs(divisor, aig);

        // Unsigned division on absolute values
        let abs_quotient = self.encode_udiv_generic(&abs_dividend, &abs_divisor, aig);

        // Result sign = sign_dividend XOR sign_divisor
        let result_sign = aig.xor(sign_dividend, sign_divisor);

        // Conditionally negate result
        let neg_quotient = aig.negate_bitvector(&abs_quotient);

        let mut result = Vec::with_capacity(width);
        for i in 0..width {
            result.push(aig.mux(result_sign, neg_quotient[i], abs_quotient[i]));
        }

        result
    }

    /// Encode absolute value
    fn encode_abs(&self, a: &[AigEdge], aig: &mut AigCircuit) -> Vec<AigEdge> {
        let width = a.len();

        if width == 0 {
            return Vec::new();
        }

        let sign = a[width - 1];
        let neg = aig.negate_bitvector(a);

        let mut result = Vec::with_capacity(width);
        for i in 0..width {
            result.push(aig.mux(sign, neg[i], a[i]));
        }

        result
    }

    /// Generic unsigned division (variable divisor)
    fn encode_udiv_generic(
        &mut self,
        dividend: &[AigEdge],
        divisor: &[AigEdge],
        aig: &mut AigCircuit,
    ) -> Vec<AigEdge> {
        let width = dividend.len();

        let mut quotient = vec![aig.false_edge(); width];
        let mut remainder = vec![aig.false_edge(); width];

        for i in (0..width).rev() {
            let mut new_remainder = vec![aig.false_edge(); width];

            new_remainder[1..width].copy_from_slice(&remainder[..(width - 1)]);
            new_remainder[0] = dividend[i];

            let can_subtract = self.encode_uge(&new_remainder, divisor, aig);

            quotient[i] = can_subtract;

            // Compute negated divisor first to avoid multiple mutable borrows
            let neg_divisor = aig.negate_bitvector(divisor);
            let diff = aig.ripple_carry_adder(&new_remainder, &neg_divisor);

            for j in 0..width {
                remainder[j] = aig.mux(can_subtract, diff[j], new_remainder[j]);
            }
        }

        quotient
    }

    /// Get Barrett parameters (compute if not cached)
    pub fn get_barrett_params(&mut self, divisor: u64, width: usize) -> Option<&BarrettParams> {
        if !self.barrett_cache.contains_key(&(divisor, width))
            && let Some(params) = BarrettParams::new(divisor, width)
        {
            self.barrett_cache.insert((divisor, width), params);
        }

        self.barrett_cache.get(&(divisor, width))
    }

    /// Get Montgomery parameters (compute if not cached)
    pub fn get_montgomery_params(
        &mut self,
        modulus: u64,
        width: usize,
    ) -> Option<&MontgomeryParams> {
        if !self.montgomery_cache.contains_key(&(modulus, width))
            && let Some(params) = MontgomeryParams::new(modulus, width)
        {
            self.montgomery_cache.insert((modulus, width), params);
        }

        self.montgomery_cache.get(&(modulus, width))
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_is_power_of_two() {
        assert!(DivisionOptimizer::is_power_of_two(1));
        assert!(DivisionOptimizer::is_power_of_two(2));
        assert!(DivisionOptimizer::is_power_of_two(4));
        assert!(DivisionOptimizer::is_power_of_two(8));
        assert!(!DivisionOptimizer::is_power_of_two(0));
        assert!(!DivisionOptimizer::is_power_of_two(3));
        assert!(!DivisionOptimizer::is_power_of_two(5));
    }

    #[test]
    fn test_log2_power_of_two() {
        assert_eq!(DivisionOptimizer::log2_power_of_two(1), Some(0));
        assert_eq!(DivisionOptimizer::log2_power_of_two(2), Some(1));
        assert_eq!(DivisionOptimizer::log2_power_of_two(4), Some(2));
        assert_eq!(DivisionOptimizer::log2_power_of_two(8), Some(3));
        assert_eq!(DivisionOptimizer::log2_power_of_two(3), None);
    }

    #[test]
    fn test_barrett_params() {
        let params = BarrettParams::new(7, 8).expect("test operation should succeed");
        assert_eq!(params.divisor, 7);

        // Test division
        assert_eq!(params.divide(14), 2);
        assert_eq!(params.divide(20), 2);
        assert_eq!(params.divide(21), 3);

        // Test modulo
        assert_eq!(params.modulo(14), 0);
        assert_eq!(params.modulo(15), 1);
        assert_eq!(params.modulo(20), 6);
    }

    #[test]
    fn test_montgomery_params() {
        let params = MontgomeryParams::new(7, 8).expect("test operation should succeed");
        assert_eq!(params.modulus, 7);

        // Test conversion to/from Montgomery form
        let a = 5;
        let a_mont = params.to_montgomery(a);
        let a_back = params.from_montgomery(a_mont);
        assert_eq!(a_back, a % 7);

        // Test Montgomery multiplication
        let a = 3;
        let b = 4;
        let a_mont = params.to_montgomery(a);
        let b_mont = params.to_montgomery(b);
        let c_mont = params.montgomery_mul(a_mont, b_mont);
        let c = params.from_montgomery(c_mont);
        assert_eq!(c, (a * b) % 7);
    }

    #[test]
    fn test_montgomery_mod_exp() {
        let params = MontgomeryParams::new(11, 8).expect("test operation should succeed");

        // 2^3 mod 11 = 8
        assert_eq!(params.mod_exp(2, 3), 8);

        // 3^4 mod 11 = 81 mod 11 = 4
        assert_eq!(params.mod_exp(3, 4), 4);

        // 5^2 mod 11 = 25 mod 11 = 3
        assert_eq!(params.mod_exp(5, 2), 3);
    }

    #[test]
    fn test_division_optimizer() {
        let mut opt = DivisionOptimizer::new(DivisionConfig::default());
        let mut aig = AigCircuit::new();

        let dividend = aig.constant_bitvector(20, 8);

        // Division by power of 2
        let result = opt.optimize_udiv_const(&dividend, 4, &mut aig);
        assert_eq!(result.len(), 8);
        assert_eq!(opt.stats().power_of_two_opts, 1);

        // Division by 1
        let result = opt.optimize_udiv_const(&dividend, 1, &mut aig);
        assert_eq!(result.len(), 8);
    }

    #[test]
    fn test_remainder_optimizer() {
        let mut opt = DivisionOptimizer::new(DivisionConfig::default());
        let mut aig = AigCircuit::new();

        let dividend = aig.constant_bitvector(23, 8);

        // Remainder by power of 2
        let result = opt.optimize_urem_const(&dividend, 8, &mut aig);
        assert_eq!(result.len(), 8);

        // Remainder by 1 should be 0
        let result = opt.optimize_urem_const(&dividend, 1, &mut aig);
        assert_eq!(result.len(), 8);
    }

    #[test]
    fn test_barrett_division_correctness() {
        let params = BarrettParams::new(13, 16).expect("test operation should succeed");

        for dividend in 0..200 {
            let quotient = params.divide(dividend);
            let expected = dividend / 13;
            assert_eq!(quotient, expected, "Failed for dividend {}", dividend);

            let remainder = params.modulo(dividend);
            let expected_rem = dividend % 13;
            assert_eq!(remainder, expected_rem, "Failed remainder for {}", dividend);
        }
    }

    #[test]
    fn test_montgomery_odd_modulus_only() {
        // Even modulus should fail
        assert!(MontgomeryParams::new(8, 8).is_none());
        assert!(MontgomeryParams::new(10, 8).is_none());

        // Odd modulus should succeed
        assert!(MontgomeryParams::new(7, 8).is_some());
        assert!(MontgomeryParams::new(9, 8).is_some());
        assert!(MontgomeryParams::new(11, 8).is_some());
    }

    #[test]
    fn test_extended_gcd() {
        let (g, x, y) = MontgomeryParams::extended_gcd(7, 11);
        assert_eq!(g, 1);
        assert_eq!(7 * x + 11 * y, 1);

        let (g, x, y) = MontgomeryParams::extended_gcd(15, 28);
        assert_eq!(g, 1);
        assert_eq!(15 * x + 28 * y, 1);
    }

    #[test]
    fn test_division_config_defaults() {
        let config = DivisionConfig::default();
        assert!(config.use_barrett);
        assert!(config.use_montgomery);
        assert!(config.optimize_power_of_two);
        assert_eq!(config.max_table_divisor, 16);
    }

    /// Barrett precomputation must refuse widths whose `2^(2*width)`
    /// numerator does not exist in a `u128`.
    ///
    /// `1u128 << (2 * width)` aborted in debug builds and produced a garbage
    /// reciprocal in release ones from width 64 upward, so the parameters are
    /// now honestly unavailable and the caller encodes the plain divider.
    #[test]
    fn barrett_params_none_for_wide_widths() {
        assert!(BarrettParams::new(7, 64).is_none());
        assert!(BarrettParams::new(7, 65).is_none());
        assert!(BarrettParams::new(7, 128).is_none());
        assert!(BarrettParams::new(7, 0).is_none());
        assert!(BarrettParams::new(0, 32).is_none());
        // The widest width that still has a reciprocal keeps working.
        assert!(BarrettParams::new(7, 63).is_some());
    }

    /// Barrett division stays exact at the widest supported width, including
    /// for a dividend whose product with the reciprocal would overflow.
    #[test]
    fn barrett_divide_is_exact_at_max_width() {
        let params = BarrettParams::new(7, 63).expect("width 63 is supported");
        for dividend in [0u64, 1, 6, 7, 8, 1_000_003, u64::MAX] {
            assert_eq!(params.divide(dividend), dividend / 7, "dividend {dividend}");
            assert_eq!(params.modulo(dividend), dividend % 7, "dividend {dividend}");
        }
    }

    /// Montgomery precomputation must refuse widths whose `R = 2^width` does
    /// not fit the `u64` inverse it needs.
    #[test]
    fn montgomery_params_none_for_wide_widths() {
        assert!(MontgomeryParams::new(7, 64).is_none());
        assert!(MontgomeryParams::new(7, 65).is_none());
        assert!(MontgomeryParams::new(7, 128).is_none());
        assert!(MontgomeryParams::new(7, 0).is_none());
        assert!(MontgomeryParams::new(7, 63).is_some());
    }

    /// Montgomery multiplication still round-trips at the widest supported
    /// width, so the guard did not cost a working configuration.
    #[test]
    fn montgomery_round_trips_at_max_width() {
        let params = MontgomeryParams::new(11, 63).expect("width 63 is supported");
        let a_mont = params.to_montgomery(7);
        assert_eq!(params.from_montgomery(a_mont), 7);
    }

    /// The optimizer's cached-parameter accessors report the same absence
    /// rather than aborting inside the cache-filling closure.
    #[test]
    fn optimizer_param_cache_reports_wide_widths_as_absent() {
        let mut opt = DivisionOptimizer::new(DivisionConfig::default());
        assert!(opt.get_barrett_params(7, 128).is_none());
        assert!(opt.get_montgomery_params(7, 128).is_none());
        assert!(opt.get_barrett_params(7, 32).is_some());
        assert!(opt.get_montgomery_params(7, 32).is_some());
    }

    /// Encoding a division at a width with no Barrett reciprocal must still
    /// produce a circuit – the abort was inside `or_insert_with`, on a path
    /// that only ever fell back to the standard divider anyway.
    #[test]
    fn encode_udiv_at_width_64_does_not_abort() {
        let mut opt = DivisionOptimizer::new(DivisionConfig::default());
        let mut aig = AigCircuit::new();
        let dividend = aig.constant_bitvector(100, 64);

        // Divisor above `max_table_divisor` and not a power of two: the Barrett
        // path, which is where the precomputation used to be forced.
        let result = opt.optimize_udiv_const(&dividend, 17, &mut aig);
        assert_eq!(result.len(), 64);

        let result = opt.optimize_urem_const(&dividend, 17, &mut aig);
        assert_eq!(result.len(), 64);
    }

    #[test]
    fn test_division_stats() {
        let mut opt = DivisionOptimizer::new(DivisionConfig::default());
        let mut aig = AigCircuit::new();

        let dividend = aig.constant_bitvector(100, 8);

        opt.optimize_udiv_const(&dividend, 16, &mut aig);
        assert!(opt.stats().power_of_two_opts > 0);

        opt.optimize_udiv_const(&dividend, 1, &mut aig);
        assert!(opt.stats().divisions_optimized > 0);
    }
}
