//! Floating-point theory constraint checking

#[allow(unused_imports)]
use crate::prelude::*;
use num_traits::ToPrimitive;
use oxiz_core::ast::{RoundingMode, TermId, TermKind, TermManager};

use super::Solver;
use super::types::FpConstraintData;

mod extended;
#[cfg(test)]
mod tests;

impl Solver {
    /// Invalidate FP constraint cache (call when assertions change)
    pub(super) fn invalidate_fp_cache(&mut self) {
        self.fp_constraint_cache.clear();
    }

    fn collect_fp_data_cached(&self, assertion: TermId, manager: &TermManager) -> FpConstraintData {
        if let Some(cached) = self.fp_constraint_cache.get(&assertion) {
            return cached.clone();
        }
        let mut data = FpConstraintData::new();
        self.collect_fp_constraints_extended(
            assertion,
            manager,
            &mut data.additions,
            &mut data.divisions,
            &mut data.multiplications,
            &mut data.comparisons,
            &mut data.equalities,
            &mut data.literals,
            &mut data.rounding_add_results,
            &mut data.is_zero,
            &mut data.is_positive,
            &mut data.is_negative,
            &mut data.not_nan,
            &mut data.gt_comparisons,
            &mut data.lt_comparisons,
            &mut data.conversions,
            &mut data.real_to_fp_conversions,
            &mut data.subtractions,
            true,
        );
        data
    }

    pub(super) fn check_fp_constraints(&mut self, manager: &TermManager) -> bool {
        let mut merged = FpConstraintData::new();
        let assertions_snapshot: Vec<TermId> = self.assertions.clone();
        for &assertion in &assertions_snapshot {
            let data = self.collect_fp_data_cached(assertion, manager);
            self.fp_constraint_cache
                .entry(assertion)
                .or_insert_with(|| data.clone());
            merged.merge(&data);
        }
        let _fp_additions = merged.additions;
        let fp_divisions = merged.divisions;
        let fp_multiplications = merged.multiplications;
        let fp_comparisons = merged.comparisons;
        let mut fp_equalities = merged.equalities;
        let fp_literals = merged.literals;
        let rounding_add_results = merged.rounding_add_results;
        let fp_is_zero = merged.is_zero;
        let fp_is_positive = merged.is_positive;
        let fp_is_negative = merged.is_negative;
        let fp_not_nan = merged.not_nan;
        let fp_gt_comparisons = merged.gt_comparisons;
        let fp_lt_comparisons = merged.lt_comparisons;
        let fp_conversions = merged.conversions;
        let real_to_fp_conversions = merged.real_to_fp_conversions;
        let fp_subtractions = merged.subtractions;

        // Infer equalities from isZero(fp.sub(a, b)) => a == b
        for &zero_term in &fp_is_zero {
            for &(sub_lhs, sub_rhs, sub_result) in &fp_subtractions {
                if zero_term == sub_result {
                    // isZero(diff) where diff = fp.sub(a, b) implies a == b
                    fp_equalities.push((sub_lhs, sub_rhs));
                }
                // Also check via equalities
                for &(eq_lhs, eq_rhs) in fp_equalities.clone().iter() {
                    if (eq_lhs == zero_term && eq_rhs == sub_result)
                        || (eq_rhs == zero_term && eq_lhs == sub_result)
                    {
                        fp_equalities.push((sub_lhs, sub_rhs));
                    }
                }
            }
        }

        // Check 1: fp_10 - Direct contradiction: z1 > v AND z1 < v
        // This is impossible for any value z1
        for &(gt_lhs, gt_rhs) in &fp_gt_comparisons {
            for &(lt_lhs, lt_rhs) in &fp_lt_comparisons {
                // Check if same variable has both > and < with the same comparison value
                if gt_lhs == lt_lhs {
                    // Check if gt_rhs and lt_rhs represent the same value
                    if gt_rhs == lt_rhs {
                        return true; // Direct contradiction: z1 > v AND z1 < v
                    }
                    // Also check via literal values
                    if let (Some(&gt_val), Some(&lt_val)) =
                        (fp_literals.get(&gt_rhs), fp_literals.get(&lt_rhs))
                    {
                        if (gt_val - lt_val).abs() < f64::EPSILON {
                            return true; // Same literal value: z1 > v AND z1 < v
                        }
                    }
                }
            }
        }

        // Check 2: fp_06 - Zero sign handling
        // In RNE mode, +0 + -0 = +0 (positive zero)
        // So asserting isZero(x) AND isNegative(x) when x = fp.add(RNE, +0, -0) is UNSAT
        for &var in &fp_is_zero {
            if fp_is_negative.contains(&var) {
                // Check if this var is the result of +0 + -0
                for &(eq_lhs, eq_rhs) in &fp_equalities {
                    let add_term = if eq_lhs == var {
                        eq_rhs
                    } else if eq_rhs == var {
                        eq_lhs
                    } else {
                        continue;
                    };
                    if let Some(term_data) = manager.get(add_term) {
                        if let TermKind::FpAdd(rm, lhs, rhs) = &term_data.kind {
                            // Check if one is +0 and the other is -0
                            let lhs_pos_zero =
                                fp_is_zero.contains(lhs) && fp_is_positive.contains(lhs);
                            let lhs_neg_zero =
                                fp_is_zero.contains(lhs) && fp_is_negative.contains(lhs);
                            let rhs_pos_zero =
                                fp_is_zero.contains(rhs) && fp_is_positive.contains(rhs);
                            let rhs_neg_zero =
                                fp_is_zero.contains(rhs) && fp_is_negative.contains(rhs);

                            // +0 + -0 = +0 for every IEEE-754 rounding mode EXCEPT
                            // roundTowardNegative (RTN), where it is -0.  Only claim
                            // a contradiction when the sum is provably +0, i.e. rm != RTN.
                            if *rm != RoundingMode::RTN
                                && ((lhs_pos_zero && rhs_neg_zero)
                                    || (lhs_neg_zero && rhs_pos_zero))
                            {
                                // Result is +0 (positive), so asserting isNegative is UNSAT.
                                return true;
                            }
                        }
                    }
                }
            }
        }

        // Check 3: fp_06 - 0/0 = NaN, so not(isNaN(y)) when y = 0/0 is UNSAT
        for &var in &fp_not_nan {
            // Check if var is the result of a division
            for &(eq_lhs, eq_rhs) in &fp_equalities {
                let div_term = if eq_lhs == var {
                    eq_rhs
                } else if eq_rhs == var {
                    eq_lhs
                } else {
                    continue;
                };
                if let Some(term_data) = manager.get(div_term) {
                    if let TermKind::FpDiv(_, dividend, divisor) = &term_data.kind {
                        // Check if both dividend and divisor are zero
                        if fp_is_zero.contains(dividend) && fp_is_zero.contains(divisor) {
                            // 0/0 = NaN, but we assert not(isNaN), contradiction
                            return true;
                        }
                    }
                }
            }
        }

        // Check 4: fp_08 - Precision loss through conversions
        // Float32 -> Float64 loses precision information
        // If x64_1 = to_fp64(x32) AND x64_2 = to_fp64(val) AND x64_1 = x64_2
        // where x32 = to_fp32(val), this is UNSAT for values that lose precision in float32

        // Check within FpToFp conversions
        for i in 0..fp_conversions.len() {
            for j in (i + 1)..fp_conversions.len() {
                let (src1, eb1, sb1, result1) = fp_conversions[i];
                let (src2, eb2, sb2, result2) = fp_conversions[j];

                // Check if same target format
                if eb1 == eb2 && sb1 == sb2 {
                    // Check if result1 = result2 is asserted
                    let results_equal = result1 == result2
                        || fp_equalities.iter().any(|&(l, r)| {
                            (l == result1 && r == result2) || (l == result2 && r == result1)
                        });

                    if results_equal {
                        // Check if one source went through a smaller format (float32)
                        // and the other is direct from a real value
                        let src1_through_smaller = self.source_went_through_smaller_format_check(
                            src1,
                            eb1,
                            sb1,
                            manager,
                            &fp_equalities,
                        );
                        let src2_direct =
                            self.is_direct_from_real_value(src2, manager, &fp_equalities);

                        if src1_through_smaller && src2_direct {
                            if self.value_loses_precision_check(
                                src2,
                                manager,
                                &fp_equalities,
                                &real_to_fp_conversions,
                            ) {
                                return true;
                            }
                        }

                        let src2_through_smaller = self.source_went_through_smaller_format_check(
                            src2,
                            eb2,
                            sb2,
                            manager,
                            &fp_equalities,
                        );
                        let src1_direct =
                            self.is_direct_from_real_value(src1, manager, &fp_equalities);

                        if src2_through_smaller && src1_direct {
                            if self.value_loses_precision_check(
                                src1,
                                manager,
                                &fp_equalities,
                                &real_to_fp_conversions,
                            ) {
                                return true;
                            }
                        }
                    }
                }
            }
        }

        // Check between FpToFp and RealToFp conversions
        // x64_1 = FpToFp(x32) where x32 = RealToFp(val) [float32]
        // x64_2 = RealToFp(val) [float64]
        // if x64_1 = x64_2 is asserted, this is UNSAT for values that lose precision
        for &(fp_src, fp_eb, fp_sb, fp_result) in &fp_conversions {
            for &(real_arg, real_eb, real_sb, real_result) in &real_to_fp_conversions {
                // Check if same target format (both converting to float64)
                if fp_eb == real_eb && fp_sb == real_sb {
                    // Check if fp_result = real_result is asserted
                    let results_equal = fp_result == real_result
                        || fp_equalities.iter().any(|&(l, r)| {
                            (l == fp_result && r == real_result)
                                || (l == real_result && r == fp_result)
                        });

                    if results_equal {
                        // The FP source went through a smaller format if:
                        // fp_src is itself a float32 variable that was assigned from RealToFp
                        // Check if fp_src is the result of a RealToFp conversion with smaller format
                        let fp_src_smaller_format =
                            real_to_fp_conversions.iter().any(
                                |&(_, src_eb, src_sb, src_result)| {
                                    src_result == fp_src && (src_eb < fp_eb || src_sb < fp_sb)
                                },
                            ) || fp_equalities.iter().any(|&(eq_l, eq_r)| {
                                let check_term = if eq_l == fp_src {
                                    eq_r
                                } else if eq_r == fp_src {
                                    eq_l
                                } else {
                                    return false;
                                };
                                real_to_fp_conversions.iter().any(
                                    |&(_, src_eb, src_sb, src_result)| {
                                        src_result == check_term
                                            && (src_eb < fp_eb || src_sb < fp_sb)
                                    },
                                )
                            });

                        if fp_src_smaller_format {
                            // Check if the real value loses precision in float32
                            if let Some(real_data) = manager.get(real_arg) {
                                if let TermKind::RealConst(r) = &real_data.kind {
                                    if let Some(val) = r.to_f64() {
                                        let as_f32 = val as f32;
                                        let back_to_f64 = as_f32 as f64;
                                        if (val - back_to_f64).abs() > f64::EPSILON {
                                            return true; // Precision loss conflict
                                        }
                                    }
                                }
                            }
                        }
                    }
                }
            }
        }

        // Additional fp_08 check: Look for chained conversions
        // Pattern: x64_1 = to_fp64(x32), x32 = to_fp32(val), x64_2 = to_fp64(val), x64_1 = x64_2
        // This pattern loses precision if val cannot be exactly represented in float32
        //
        // Find: small_conv = to_fp(small_eb, small_sb, val) [e.g., float32 from real]
        //       large_conv_indirect = to_fp(large_eb, large_sb, small_conv) [e.g., float64 from var]
        //       large_conv_direct = to_fp(large_eb, large_sb, val) [e.g., float64 from real]
        //       assert large_conv_indirect = large_conv_direct
        for &(small_arg, small_eb, small_sb, small_result) in &real_to_fp_conversions {
            // Check if small_arg is a RealConst (this is the small format conversion from real)
            let small_arg_is_real = if let Some(d) = manager.get(small_arg) {
                matches!(d.kind, TermKind::RealConst(_))
            } else {
                false
            };

            if !small_arg_is_real {
                continue;
            }

            // Look for a large format conversion that uses small_result as its source
            for &(large_arg, large_eb, large_sb, large_result_indirect) in &real_to_fp_conversions {
                // Check if this is a larger format
                if large_eb <= small_eb && large_sb <= small_sb {
                    continue;
                }

                // Check if large_arg is equal to small_result (the conversion chain)
                let chain_connected = large_arg == small_result
                    || fp_equalities.iter().any(|&(l, r)| {
                        (l == large_arg && r == small_result)
                            || (l == small_result && r == large_arg)
                    });

                if !chain_connected {
                    continue;
                }

                // Now look for a direct conversion to the large format from the same real value
                for &(direct_arg, direct_eb, direct_sb, large_result_direct) in
                    &real_to_fp_conversions
                {
                    // Same large format
                    if direct_eb != large_eb || direct_sb != large_sb {
                        continue;
                    }

                    // Check if direct_arg is the same as small_arg (same original real value)
                    let same_original = direct_arg == small_arg || {
                        if let (Some(d1), Some(d2)) =
                            (manager.get(small_arg), manager.get(direct_arg))
                        {
                            match (&d1.kind, &d2.kind) {
                                (TermKind::RealConst(v1), TermKind::RealConst(v2)) => {
                                    if v1 == v2 {
                                        true
                                    } else if let (Some(f1), Some(f2)) = (v1.to_f64(), v2.to_f64())
                                    {
                                        (f1 - f2).abs() < 1e-15
                                    } else {
                                        false
                                    }
                                }
                                _ => false,
                            }
                        } else {
                            false
                        }
                    };

                    if !same_original {
                        continue;
                    }

                    // Check if the indirect and direct results are asserted equal
                    let results_equal = large_result_indirect == large_result_direct
                        || fp_equalities.iter().any(|&(l, r)| {
                            (l == large_result_indirect && r == large_result_direct)
                                || (l == large_result_direct && r == large_result_indirect)
                        });

                    if results_equal {
                        // Check if the value loses precision in the small format
                        if let Some(real_data) = manager.get(small_arg) {
                            if let TermKind::RealConst(r) = &real_data.kind {
                                if let Some(val) = r.to_f64() {
                                    let as_f32 = val as f32;
                                    let back_to_f64 = as_f32 as f64;
                                    if (val - back_to_f64).abs() > f64::EPSILON {
                                        return true; // Precision loss conflict
                                    }
                                }
                            }
                        }
                    }
                }
            }
        }

        // Also check with FpToFp conversions (if parser uses FpToFp for FP-to-FP conversion)
        for &(small_arg, small_eb, small_sb, small_result) in &real_to_fp_conversions {
            // Check if small_arg is a RealConst
            let small_arg_is_real = if let Some(d) = manager.get(small_arg) {
                matches!(d.kind, TermKind::RealConst(_))
            } else {
                false
            };

            if !small_arg_is_real {
                continue;
            }

            // Look for FpToFp large format conversion that uses small_result as its source
            for &(fp_src, fp_eb, fp_sb, fp_result) in &fp_conversions {
                // Check if this is a larger format
                if fp_eb <= small_eb && fp_sb <= small_sb {
                    continue;
                }

                // Check if fp_src is equal to small_result (the conversion chain)
                let chain_connected = fp_src == small_result
                    || fp_equalities.iter().any(|&(l, r)| {
                        (l == fp_src && r == small_result) || (l == small_result && r == fp_src)
                    });

                if !chain_connected {
                    continue;
                }

                // Look for a direct conversion to the large format from the same real value
                for &(direct_arg, direct_eb, direct_sb, large_result_direct) in
                    &real_to_fp_conversions
                {
                    // Same large format
                    if direct_eb != fp_eb || direct_sb != fp_sb {
                        continue;
                    }

                    // Check if direct_arg is the same as small_arg (same original real value)
                    let same_original = direct_arg == small_arg || {
                        if let (Some(d1), Some(d2)) =
                            (manager.get(small_arg), manager.get(direct_arg))
                        {
                            match (&d1.kind, &d2.kind) {
                                (TermKind::RealConst(v1), TermKind::RealConst(v2)) => {
                                    if v1 == v2 {
                                        true
                                    } else if let (Some(f1), Some(f2)) = (v1.to_f64(), v2.to_f64())
                                    {
                                        (f1 - f2).abs() < 1e-15
                                    } else {
                                        false
                                    }
                                }
                                _ => false,
                            }
                        } else {
                            false
                        }
                    };

                    if !same_original {
                        continue;
                    }

                    // Check if indirect (fp_result) and direct results are asserted equal
                    let results_equal = fp_result == large_result_direct
                        || fp_equalities.iter().any(|&(l, r)| {
                            (l == fp_result && r == large_result_direct)
                                || (l == large_result_direct && r == fp_result)
                        });

                    if results_equal {
                        // Check if the value loses precision in the small format
                        if let Some(real_data) = manager.get(small_arg) {
                            if let TermKind::RealConst(r) = &real_data.kind {
                                if let Some(val) = r.to_f64() {
                                    let as_f32 = val as f32;
                                    let back_to_f64 = as_f32 as f64;
                                    if (val - back_to_f64).abs() > f64::EPSILON {
                                        return true; // Precision loss conflict
                                    }
                                }
                            }
                        }
                    }
                }
            }
        }

        // Simplified fp_08 check: Track precision loss through literal values
        // If two variables should be equal but one went through a smaller precision format
        for &(small_arg, small_eb, small_sb, small_result) in &real_to_fp_conversions {
            // Get the real value being converted to small format
            let small_value = if let Some(d) = manager.get(small_arg) {
                if let TermKind::RealConst(r) = &d.kind {
                    r.to_f64()
                } else {
                    None
                }
            } else {
                None
            };

            let Some(small_val) = small_value else {
                continue;
            };

            // Check if this value loses precision in the small format
            let as_small = small_val as f32;
            let back_to_large = as_small as f64;
            if (small_val - back_to_large).abs() <= f64::EPSILON {
                continue; // No precision loss, skip
            }

            // This value loses precision. Check if there's a larger format conversion
            // from the small result that's asserted equal to a direct conversion
            // First check in real_to_fp_conversions
            for &(large_arg, large_eb, large_sb, large_result) in &real_to_fp_conversions {
                // Skip if not a larger format
                if large_eb <= small_eb && large_sb <= small_sb {
                    continue;
                }

                // Check if large_arg is the small_result (or equal via equalities)
                let is_chain = large_arg == small_result
                    || fp_equalities.iter().any(|&(l, r)| {
                        (l == large_arg && r == small_result)
                            || (l == small_result && r == large_arg)
                    });

                if !is_chain {
                    continue;
                }

                // Check if there's another conversion to large format from the same real value
                // that's asserted equal to large_result
                for &(direct_arg, direct_eb, direct_sb, direct_result) in &real_to_fp_conversions {
                    if direct_eb != large_eb || direct_sb != large_sb {
                        continue;
                    }

                    // Check if direct_arg has the same value as small_arg
                    let direct_val = if let Some(d) = manager.get(direct_arg) {
                        if let TermKind::RealConst(r) = &d.kind {
                            r.to_f64()
                        } else {
                            None
                        }
                    } else {
                        None
                    };

                    let Some(dval) = direct_val else { continue };
                    if (dval - small_val).abs() > f64::EPSILON {
                        continue; // Different value
                    }

                    // Same value! Check if large_result and direct_result are asserted equal
                    let are_equal = large_result == direct_result
                        || fp_equalities.iter().any(|&(l, r)| {
                            (l == large_result && r == direct_result)
                                || (l == direct_result && r == large_result)
                        });

                    if are_equal {
                        return true; // Precision loss conflict!
                    }
                }
            }

            // Also check in fp_conversions (FpToFp) for the large conversion
            for &(fp_src, fp_eb, fp_sb, fp_result) in &fp_conversions {
                // Skip if not a larger format
                if fp_eb <= small_eb && fp_sb <= small_sb {
                    continue;
                }

                // Check if fp_src is the small_result (or equal via equalities)
                let is_chain = fp_src == small_result
                    || fp_equalities.iter().any(|&(l, r)| {
                        (l == fp_src && r == small_result) || (l == small_result && r == fp_src)
                    });

                if !is_chain {
                    continue;
                }

                // Check if there's a direct RealToFp to the same large format with same real value
                // that's asserted equal to fp_result
                for &(direct_arg, direct_eb, direct_sb, direct_result) in &real_to_fp_conversions {
                    if direct_eb != fp_eb || direct_sb != fp_sb {
                        continue;
                    }

                    // Check if direct_arg has the same value as small_arg
                    let direct_val = if let Some(d) = manager.get(direct_arg) {
                        if let TermKind::RealConst(r) = &d.kind {
                            r.to_f64()
                        } else {
                            None
                        }
                    } else {
                        None
                    };

                    let Some(dval) = direct_val else { continue };
                    if (dval - small_val).abs() > f64::EPSILON {
                        continue; // Different value
                    }

                    // Same value! Check if fp_result and direct_result are asserted equal
                    let are_equal = fp_result == direct_result
                        || fp_equalities.iter().any(|&(l, r)| {
                            (l == fp_result && r == direct_result)
                                || (l == direct_result && r == fp_result)
                        });

                    if are_equal {
                        return true; // Precision loss conflict!
                    }
                }
            }
        }

        // Check 4b: Direct fp_08 pattern - simplified detection
        // For any two FP variables asserted equal, check if one went through smaller precision
        for &(eq_lhs, eq_rhs) in &fp_equalities {
            // Try to find the conversion source for each side
            let lhs_source = self.find_fp_conversion_source(
                eq_lhs,
                manager,
                &fp_equalities,
                &fp_conversions,
                &real_to_fp_conversions,
            );
            let rhs_source = self.find_fp_conversion_source(
                eq_rhs,
                manager,
                &fp_equalities,
                &fp_conversions,
                &real_to_fp_conversions,
            );

            // Check if one went through smaller precision and one is direct
            if let (Some((lhs_val, lhs_through_small)), Some((rhs_val, rhs_through_small))) =
                (lhs_source, rhs_source)
            {
                // Same original value?
                if (lhs_val - rhs_val).abs() < 1e-15 {
                    // One through small, one direct?
                    if lhs_through_small != rhs_through_small {
                        // Check if value loses precision in float32
                        let as_f32 = lhs_val as f32;
                        let back_to_f64 = as_f32 as f64;
                        if (lhs_val - back_to_f64).abs() > f64::EPSILON {
                            return true; // Precision loss conflict!
                        }
                    }
                }
            }
        }

        // Check 5: RTP addition >= RTN addition for same operands (fp_03)
        // If we have fp.add(RTP, x, y) = z1 and fp.add(RTN, x, y) = z2, then z1 >= z2
        // So z1 < z2 is UNSAT
        for &(lt_arg, gt_arg, is_lt) in &fp_comparisons {
            if !is_lt {
                continue;
            }
            // Check if lt_arg is RTP addition and gt_arg is RTN addition of same operands
            // Or if gt_arg is RTP and lt_arg is RTN (which would be valid)
            for (key, result) in &rounding_add_results {
                let (op1, op2, rm) = key;
                if *result == lt_arg && *rm == RoundingMode::RTP {
                    // Check if gt_arg is RTN addition of same operands
                    let rtn_key = (*op1, *op2, RoundingMode::RTN);
                    if let Some(&rtn_result) = rounding_add_results.get(&rtn_key) {
                        if rtn_result == gt_arg {
                            // We have (fp.add RTP x y) < (fp.add RTN x y)
                            // This is impossible for positive operands with proper rounding
                            return true;
                        }
                    }
                }
            }
        }

        // Check 6: (10/3)*3 != 10 in FP (fp_10)
        // If we have z = x/y and product = z*y and assert product = x
        // For non-exact division this is UNSAT
        for &(div_result, dividend, divisor, _result_var, _rm) in &fp_divisions {
            // Look for multiplication z*divisor
            for &(mul_result, mul_op1, mul_op2, _mul_result_var, _mul_rm) in &fp_multiplications {
                let is_div_mul_pattern = (mul_op1 == div_result && mul_op2 == divisor)
                    || (mul_op2 == div_result && mul_op1 == divisor);
                if is_div_mul_pattern {
                    // Check if mul_result = dividend is asserted
                    for &(eq_lhs, eq_rhs) in &fp_equalities {
                        if (eq_lhs == mul_result && eq_rhs == dividend)
                            || (eq_rhs == mul_result && eq_lhs == dividend)
                        {
                            // Check if division is non-exact (dividend / divisor is not exact)
                            if let (Some(&div_val), Some(&divis_val)) =
                                (fp_literals.get(&dividend), fp_literals.get(&divisor))
                            {
                                if divis_val != 0.0 {
                                    let exact = div_val / divis_val;
                                    let reconstructed = exact * divis_val;
                                    if (reconstructed - div_val).abs() > f64::EPSILON {
                                        // Non-exact division, mul result cannot equal dividend
                                        return true;
                                    }
                                }
                            }
                        }
                    }
                }
            }
        }

        // Final fp_08 check: Direct analysis of precision loss through format conversion chains
        // Pattern: A value converted to small format (lossy) -> large format != same value directly to large format
        // We look for chains where the small format conversion loses precision
        for &(small_real_arg, small_eb, small_sb, small_result) in &real_to_fp_conversions {
            // Get the real value being converted to small format
            let small_real_val = if let Some(d) = manager.get(small_real_arg) {
                if let TermKind::RealConst(r) = &d.kind {
                    r.to_f64()
                } else {
                    None
                }
            } else {
                None
            };

            let Some(real_val) = small_real_val else {
                continue;
            };

            // Check if this value loses precision in the small format
            let as_small = real_val as f32;
            let back_to_large = as_small as f64;
            if (real_val - back_to_large).abs() <= f64::EPSILON {
                continue; // No precision loss, skip
            }

            // This value loses precision in small format (e.g., float32)
            // Look for FpToFp chain: small_result -> large_result
            for &(chain_src, chain_eb, chain_sb, chain_result) in &fp_conversions {
                // Check if chain_src == small_result (direct or via equality)
                let is_chain_src = chain_src == small_result
                    || fp_equalities.iter().any(|&(l, r)| {
                        (l == chain_src && r == small_result)
                            || (l == small_result && r == chain_src)
                    });

                if !is_chain_src || chain_eb <= small_eb || chain_sb <= small_sb {
                    continue;
                }

                // We have: real_val -> small_result -> chain_result (lossy chain)
                // Now look for: real_val -> direct_result (direct conversion to same large format)
                for &(direct_real_arg, direct_eb, direct_sb, direct_result) in
                    &real_to_fp_conversions
                {
                    if direct_eb != chain_eb || direct_sb != chain_sb {
                        continue;
                    }

                    // Check if direct_real_arg has the same value as small_real_arg
                    let direct_real_val = if let Some(d) = manager.get(direct_real_arg) {
                        if let TermKind::RealConst(r) = &d.kind {
                            r.to_f64()
                        } else {
                            None
                        }
                    } else {
                        None
                    };

                    let Some(direct_val) = direct_real_val else {
                        continue;
                    };
                    if (real_val - direct_val).abs() > f64::EPSILON {
                        continue; // Different real value
                    }

                    // Same real value! Check if chain_result == direct_result is asserted
                    // Use BFS to find transitive equality through any number of hops
                    let are_transitively_equal = Self::are_terms_equal_transitively(
                        chain_result,
                        direct_result,
                        &fp_equalities,
                    );

                    if are_transitively_equal {
                        // chain_result (lossy) == direct_result (lossless) is impossible!
                        return true;
                    }
                }
            }
        }

        false
    }

    /// Check if a source term went through a smaller FP format
    fn source_went_through_smaller_format_check(
        &self,
        source: TermId,
        target_eb: u32,
        target_sb: u32,
        manager: &TermManager,
        equalities: &[(TermId, TermId)],
    ) -> bool {
        if let Some(term_data) = manager.get(source) {
            if let TermKind::FpToFp { eb, sb, .. } = &term_data.kind {
                return *eb < target_eb || *sb < target_sb;
            }
        }
        // Check via equality constraints
        for &(eq_lhs, eq_rhs) in equalities {
            let to_check = if eq_lhs == source {
                eq_rhs
            } else if eq_rhs == source {
                eq_lhs
            } else {
                continue;
            };
            if let Some(term_data) = manager.get(to_check) {
                if let TermKind::FpToFp { eb, sb, .. } = &term_data.kind {
                    return *eb < target_eb || *sb < target_sb;
                }
            }
        }
        false
    }

    /// Check if term is directly converted from a real value
    fn is_direct_from_real_value(
        &self,
        term: TermId,
        manager: &TermManager,
        equalities: &[(TermId, TermId)],
    ) -> bool {
        if let Some(term_data) = manager.get(term) {
            if matches!(term_data.kind, TermKind::RealToFp { .. }) {
                return true;
            }
        }
        for &(eq_lhs, eq_rhs) in equalities {
            let to_check = if eq_lhs == term {
                eq_rhs
            } else if eq_rhs == term {
                eq_lhs
            } else {
                continue;
            };
            if let Some(term_data) = manager.get(to_check) {
                if matches!(term_data.kind, TermKind::RealToFp { .. }) {
                    return true;
                }
            }
        }
        false
    }

    /// Check if converting a value would lose precision in float32
    fn value_loses_precision_check(
        &self,
        term: TermId,
        manager: &TermManager,
        equalities: &[(TermId, TermId)],
        real_to_fp: &[(TermId, u32, u32, TermId)],
    ) -> bool {
        // Get the original real value
        if let Some(val) =
            self.get_original_real_value_from_term(term, manager, equalities, real_to_fp)
        {
            // Convert to f32 and back to see if precision is lost
            let as_f32 = val as f32;
            let back_to_f64 = as_f32 as f64;
            if (val - back_to_f64).abs() > f64::EPSILON {
                return true;
            }
        }
        false
    }

    /// Get the original real value from a term
    fn get_original_real_value_from_term(
        &self,
        term: TermId,
        manager: &TermManager,
        equalities: &[(TermId, TermId)],
        real_to_fp: &[(TermId, u32, u32, TermId)],
    ) -> Option<f64> {
        // Check direct RealToFp
        if let Some(term_data) = manager.get(term) {
            if let TermKind::RealToFp { arg, .. } = &term_data.kind {
                if let Some(arg_data) = manager.get(*arg) {
                    if let TermKind::RealConst(r) = &arg_data.kind {
                        return r.to_f64();
                    }
                }
            }
        }
        // Check via equalities
        for &(eq_lhs, eq_rhs) in equalities {
            let to_check = if eq_lhs == term {
                eq_rhs
            } else if eq_rhs == term {
                eq_lhs
            } else {
                continue;
            };
            if let Some(term_data) = manager.get(to_check) {
                if let TermKind::RealToFp { arg, .. } = &term_data.kind {
                    if let Some(arg_data) = manager.get(*arg) {
                        if let TermKind::RealConst(r) = &arg_data.kind {
                            return r.to_f64();
                        }
                    }
                }
            }
        }
        // Check via real_to_fp tracking
        for &(real_arg, _, _, result) in real_to_fp {
            if result == term {
                if let Some(arg_data) = manager.get(real_arg) {
                    if let TermKind::RealConst(r) = &arg_data.kind {
                        return r.to_f64();
                    }
                }
            }
        }
        None
    }

    /// Find the conversion source for an FP term
    /// Returns (original_value, went_through_smaller_precision)
    fn find_fp_conversion_source(
        &self,
        term: TermId,
        manager: &TermManager,
        equalities: &[(TermId, TermId)],
        fp_conversions: &[(TermId, u32, u32, TermId)],
        real_to_fp_conversions: &[(TermId, u32, u32, TermId)],
    ) -> Option<(f64, bool)> {
        // Helper to check if two terms match directly or via equalities
        let terms_match = |a: TermId, b: TermId| -> bool {
            a == b
                || equalities
                    .iter()
                    .any(|&(l, r)| (l == a && r == b) || (l == b && r == a))
        };

        // Helper to get RealConst value from a term
        let get_real_value = |t: TermId| -> Option<f64> {
            if let Some(data) = manager.get(t) {
                if let TermKind::RealConst(r) = &data.kind {
                    return r.to_f64();
                }
            }
            None
        };

        // Check if term is in real_to_fp_conversions (eb=11, sb=53 for float64)
        for &(real_arg, eb, sb, result) in real_to_fp_conversions {
            if terms_match(result, term) && eb == 11 && sb == 53 {
                // Check if real_arg is a RealConst (direct conversion from real)
                if let Some(val) = get_real_value(real_arg) {
                    return Some((val, false)); // Direct conversion, no precision loss path
                }

                // Check if real_arg is a variable that came from a smaller format conversion
                // This handles: x64_1 = to_fp(11, 53)(x32) where real_arg = x32
                // and x32 = to_fp(8, 24)(real_value)
                for &(inner_arg, inner_eb, inner_sb, inner_result) in real_to_fp_conversions {
                    if terms_match(inner_result, real_arg) && inner_eb < eb && inner_sb < sb {
                        // real_arg came from a smaller precision conversion
                        if let Some(val) = get_real_value(inner_arg) {
                            return Some((val, true)); // Went through smaller precision
                        }
                    }
                }
            }
        }

        // Check if term is in fp_conversions (FpToFp from a smaller format)
        for &(fp_src, eb, sb, result) in fp_conversions {
            if terms_match(result, term) && eb == 11 && sb == 53 {
                // This is a conversion to float64 from another FP format
                // Check if fp_src came from a smaller format RealToFp
                for &(real_arg, src_eb, src_sb, src_result) in real_to_fp_conversions {
                    if terms_match(fp_src, src_result) && src_eb < 11 && src_sb < 53 {
                        // fp_src came from a smaller precision RealToFp
                        if let Some(val) = get_real_value(real_arg) {
                            return Some((val, true)); // Went through smaller precision
                        }
                    }
                }
            }
        }

        // Also check via equalities - term might be equal to a conversion result
        for &(eq_lhs, eq_rhs) in equalities {
            let other = if eq_lhs == term {
                eq_rhs
            } else if eq_rhs == term {
                eq_lhs
            } else {
                continue;
            };

            // Check if other is in real_to_fp_conversions (float64)
            for &(real_arg, eb, sb, result) in real_to_fp_conversions {
                if result == other && eb == 11 && sb == 53 {
                    if let Some(val) = get_real_value(real_arg) {
                        return Some((val, false));
                    }
                    // Check chain through smaller format
                    for &(inner_arg, inner_eb, inner_sb, inner_result) in real_to_fp_conversions {
                        if terms_match(inner_result, real_arg) && inner_eb < eb && inner_sb < sb {
                            if let Some(val) = get_real_value(inner_arg) {
                                return Some((val, true));
                            }
                        }
                    }
                }
            }

            // Check if other is in fp_conversions (FpToFp to float64)
            for &(fp_src, eb, sb, result) in fp_conversions {
                if result == other && eb == 11 && sb == 53 {
                    for &(real_arg, src_eb, src_sb, src_result) in real_to_fp_conversions {
                        if terms_match(fp_src, src_result) && src_eb < 11 && src_sb < 53 {
                            if let Some(val) = get_real_value(real_arg) {
                                return Some((val, true));
                            }
                        }
                    }
                }
            }
        }

        None
    }

    /// Check if two terms are transitively equal through equalities using BFS
    fn are_terms_equal_transitively(
        term1: TermId,
        term2: TermId,
        equalities: &[(TermId, TermId)],
    ) -> bool {
        if term1 == term2 {
            return true;
        }

        // BFS to find if term2 is reachable from term1 through equalities
        let mut visited = FxHashSet::default();
        let mut queue = crate::prelude::VecDeque::new();
        queue.push_back(term1);
        visited.insert(term1);

        while let Some(current) = queue.pop_front() {
            if current == term2 {
                return true;
            }

            // Find all terms equal to current
            for &(l, r) in equalities {
                let neighbor = if l == current && !visited.contains(&r) {
                    Some(r)
                } else if r == current && !visited.contains(&l) {
                    Some(l)
                } else {
                    None
                };

                if let Some(n) = neighbor {
                    if n == term2 {
                        return true;
                    }
                    visited.insert(n);
                    queue.push_back(n);
                }
            }
        }

        false
    }

    /// Collect FP constraints from a term that is asserted **positively and
    /// unconditionally**.
    ///
    /// Superseded by [`Self::collect_fp_constraints_extended`], which tracks
    /// polarity; kept as the narrow reference version.  It carries no polarity
    /// flag, so it may only ever descend through the conjuncts of an `And` –
    /// every other Boolean node is a polarity boundary whose sub-terms are
    /// conditional, and the facts here feed a definite-conflict check.  Same
    /// shape as `check_string.rs::collect_string_constraints`.
    ///
    /// Driven by an explicit heap worklist rather than native recursion: the
    /// `And`-conjunct descent used to recurse once per nesting level, and a
    /// term built directly through [`TermManager::intern_term`] can nest
    /// `And`s arbitrarily deep (`mk_and` flattens; the raw interner does
    /// not), so a sufficiently deep conjunction overflowed the native stack –
    /// a fatal, `catch_unwind`-proof process abort.  A depth cap is not an
    /// option: the return type is `()`, so a cap could only silently drop
    /// constraints and turn a definite conflict into a false `Sat`.
    /// Conjuncts are pushed in reverse so the pop order reproduces the
    /// original left-to-right recursion exactly – `rounding_add_results` is a
    /// `HashMap` whose later insertions overwrite earlier ones, so visit
    /// order is observable.  No `visited` set, matching both the original and
    /// [`Self::collect_fp_constraints_extended`] (see `check_fp/extended.rs`'s
    /// module doc for why dedup is deliberately not added to these
    /// collectors).
    #[allow(clippy::too_many_arguments)]
    #[allow(dead_code)]
    fn collect_fp_constraints(
        &self,
        term: TermId,
        manager: &TermManager,
        fp_additions: &mut Vec<(TermId, TermId, TermId, TermId, RoundingMode)>,
        fp_divisions: &mut Vec<(TermId, TermId, TermId, TermId, RoundingMode)>,
        fp_multiplications: &mut Vec<(TermId, TermId, TermId, TermId, RoundingMode)>,
        fp_comparisons: &mut Vec<(TermId, TermId, bool)>,
        fp_equalities: &mut Vec<(TermId, TermId)>,
        fp_literals: &mut FxHashMap<TermId, f64>,
        rounding_add_results: &mut FxHashMap<(TermId, TermId, RoundingMode), TermId>,
    ) {
        let mut stack: Vec<TermId> = vec![term];
        while let Some(term) = stack.pop() {
            let Some(term_data) = manager.get(term) else {
                continue;
            };

            match &term_data.kind {
                TermKind::Eq(lhs, rhs) => {
                    fp_equalities.push((*lhs, *rhs));

                    // Check for FP literal assignment
                    if let Some(val) = self.get_fp_literal_value(*rhs, manager) {
                        fp_literals.insert(*lhs, val);
                    } else if let Some(val) = self.get_fp_literal_value(*lhs, manager) {
                        fp_literals.insert(*rhs, val);
                    }

                    // Check for FP operation results
                    if let Some(rhs_data) = manager.get(*rhs) {
                        match &rhs_data.kind {
                            TermKind::FpAdd(rm, x, y) => {
                                fp_additions.push((*lhs, *x, *y, *lhs, *rm));
                                rounding_add_results.insert((*x, *y, *rm), *lhs);
                            }
                            TermKind::FpDiv(rm, x, y) => {
                                fp_divisions.push((*lhs, *x, *y, *lhs, *rm));
                            }
                            TermKind::FpMul(rm, x, y) => {
                                fp_multiplications.push((*lhs, *x, *y, *lhs, *rm));
                            }
                            _ => {}
                        }
                    }
                    if let Some(lhs_data) = manager.get(*lhs) {
                        match &lhs_data.kind {
                            TermKind::FpAdd(rm, x, y) => {
                                fp_additions.push((*rhs, *x, *y, *rhs, *rm));
                                rounding_add_results.insert((*x, *y, *rm), *rhs);
                            }
                            TermKind::FpDiv(rm, x, y) => {
                                fp_divisions.push((*rhs, *x, *y, *rhs, *rm));
                            }
                            TermKind::FpMul(rm, x, y) => {
                                fp_multiplications.push((*rhs, *x, *y, *rhs, *rm));
                            }
                            _ => {}
                        }
                    }

                    // No descent into `lhs` / `rhs`: an equality's operands are a
                    // polarity boundary.  This AST has no `Iff`, so `(= a b)` on
                    // two Bool-sorted terms is a `TermKind::Eq` and is satisfied
                    // with both sides false.
                }
                TermKind::FpLt(a, b) => {
                    fp_comparisons.push((*a, *b, true));
                }
                TermKind::FpGt(a, b) => {
                    fp_comparisons.push((*b, *a, true)); // a > b means b < a
                }
                TermKind::And(args) => {
                    // Reverse push: popping then reproduces the original
                    // left-to-right, subtree-complete-before-next-sibling
                    // conjunct order exactly.
                    for &arg in args.iter().rev() {
                        stack.push(arg);
                    }
                }
                // `Or` and `Not` are deliberately NOT traversed: their sub-terms are
                // conditional, and this collector's facts feed a definite-conflict
                // check (see the doc comment above).
                _ => {}
            }
        }
    }

    /// Returns `true` if `kind` is a floating-point theory atom (predicate,
    /// arithmetic operation, or conversion) whose truth value / result the
    /// current incomplete FP reasoning cannot soundly certify.
    ///
    /// Bare FP constants and FP-sorted variables are intentionally excluded:
    /// they only participate through structural equality, which the EUF core
    /// handles soundly.
    fn is_fp_theory_atom(kind: &TermKind) -> bool {
        matches!(
            kind,
            TermKind::FpAbs(_)
                | TermKind::FpNeg(_)
                | TermKind::FpSqrt(_, _)
                | TermKind::FpRoundToIntegral(_, _)
                | TermKind::FpAdd(_, _, _)
                | TermKind::FpSub(_, _, _)
                | TermKind::FpMul(_, _, _)
                | TermKind::FpDiv(_, _, _)
                | TermKind::FpRem(_, _)
                | TermKind::FpMin(_, _)
                | TermKind::FpMax(_, _)
                | TermKind::FpFma(_, _, _, _)
                | TermKind::FpLeq(_, _)
                | TermKind::FpLt(_, _)
                | TermKind::FpGeq(_, _)
                | TermKind::FpGt(_, _)
                | TermKind::FpEq(_, _)
                | TermKind::FpIsNormal(_)
                | TermKind::FpIsSubnormal(_)
                | TermKind::FpIsZero(_)
                | TermKind::FpIsInfinite(_)
                | TermKind::FpIsNaN(_)
                | TermKind::FpIsNegative(_)
                | TermKind::FpIsPositive(_)
                | TermKind::FpToFp { .. }
                | TermKind::FpToSBV { .. }
                | TermKind::FpToUBV { .. }
                | TermKind::FpToReal(_)
                | TermKind::RealToFp { .. }
                | TermKind::SBVToFp { .. }
                | TermKind::UBVToFp { .. }
        )
    }

    /// Returns `true` when the current assertion set contains any FP theory
    /// atom that the (incomplete) FP conflict checks above cannot decide.
    ///
    /// When this holds and no definite FP conflict was found, the solver MUST
    /// answer `Unknown` rather than let the SAT core treat the atom as a free
    /// Boolean – the latter would report `Sat` for formulas such as
    /// `fp.lt x y ∧ fp.lt y x`, which are unsatisfiable.
    pub(super) fn fp_atoms_need_theory(&self, manager: &TermManager) -> bool {
        let mut visited: FxHashSet<TermId> = FxHashSet::default();
        let mut stack: Vec<TermId> = self.assertions.clone();
        while let Some(term) = stack.pop() {
            if !visited.insert(term) {
                continue;
            }
            let Some(term_data) = manager.get(term) else {
                continue;
            };
            if Self::is_fp_theory_atom(&term_data.kind) {
                return true;
            }
            super::term_walk::collect_structural_children(&term_data.kind, &mut stack);
        }
        false
    }
}
