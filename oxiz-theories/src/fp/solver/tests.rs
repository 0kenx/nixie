//! Auto-generated test module (consolidated from inline `#[cfg(test)] mod` blocks)

#[allow(unused_imports)]
use crate::prelude::*;
use crate::theory::TheoryResult;
use oxiz_core::ast::TermId;
use oxiz_sat::Lit;

use super::*;

#[cfg(test)]
mod tests_2 {
    use super::*;

    #[test]
    fn test_fp_format_constants() {
        assert_eq!(FpFormat::FLOAT32.width(), 32);
        assert_eq!(FpFormat::FLOAT32.bias(), 127);
        assert_eq!(FpFormat::FLOAT32.max_exponent(), 255);

        assert_eq!(FpFormat::FLOAT64.width(), 64);
        assert_eq!(FpFormat::FLOAT64.bias(), 1023);
        assert_eq!(FpFormat::FLOAT64.max_exponent(), 2047);
    }

    #[test]
    fn test_fp_value_from_f32() {
        let val = FpValue::from_f32(1.0);
        assert!(!val.sign);
        assert_eq!(val.exponent, 127); // bias
        assert_eq!(val.significand, 0); // 1.0 has no fractional part

        let val = FpValue::from_f32(-2.0);
        assert!(val.sign);
        assert_eq!(val.exponent, 128); // 127 + 1
    }

    #[test]
    fn test_fp_value_special_values() {
        let zero = FpValue::pos_zero(FpFormat::FLOAT32);
        assert!(zero.is_zero());
        assert!(!zero.is_nan());
        assert!(!zero.is_infinite());

        let inf = FpValue::pos_infinity(FpFormat::FLOAT32);
        assert!(inf.is_infinite());
        assert!(!inf.is_nan());
        assert!(!inf.is_zero());

        let nan = FpValue::nan(FpFormat::FLOAT32);
        assert!(nan.is_nan());
        assert!(!nan.is_infinite());
        assert!(!nan.is_zero());
    }

    #[test]
    fn test_fp_solver_const() {
        let mut solver = FpSolver::new();

        let a = TermId::new(1);
        let value = FpValue::from_f32(42.0);

        solver.assert_const(a, &value);

        let result = solver.check().expect("test operation should succeed");
        assert!(matches!(result, TheoryResult::Sat));

        let retrieved = solver.get_value(a).expect("test operation should succeed");
        assert_eq!(retrieved.to_f32(), Some(42.0));
    }

    #[test]
    fn test_fp_solver_eq() {
        let mut solver = FpSolver::new();

        let a = TermId::new(1);
        let b = TermId::new(2);

        solver.new_fp(a, FpFormat::FLOAT32);
        solver.new_fp(b, FpFormat::FLOAT32);

        // a = 1.5
        solver.assert_const(a, &FpValue::from_f32(1.5));

        // a = b
        solver.assert_fp_eq(a, b);

        let result = solver.check().expect("test operation should succeed");
        assert!(matches!(result, TheoryResult::Sat));

        // b should also be 1.5
        let b_val = solver.get_value(b).expect("test operation should succeed");
        assert_eq!(b_val.to_f32(), Some(1.5));
    }

    #[test]
    fn test_fp_solver_neg() {
        let mut solver = FpSolver::new();

        let a = TermId::new(1);
        let b = TermId::new(2);

        solver.new_fp(a, FpFormat::FLOAT32);
        solver.new_fp(b, FpFormat::FLOAT32);

        // a = 2.75
        solver.assert_const(a, &FpValue::from_f32(2.75));

        // b = -a
        solver.assert_fp_neg(b, a);

        let result = solver.check().expect("test operation should succeed");
        assert!(matches!(result, TheoryResult::Sat));

        let b_val = solver.get_value(b).expect("test operation should succeed");
        assert_eq!(b_val.to_f32(), Some(-2.75));
    }

    #[test]
    fn test_fp_solver_abs() {
        let mut solver = FpSolver::new();

        let a = TermId::new(1);
        let b = TermId::new(2);

        solver.new_fp(a, FpFormat::FLOAT32);
        solver.new_fp(b, FpFormat::FLOAT32);

        // a = -5.0
        solver.assert_const(a, &FpValue::from_f32(-5.0));

        // b = |a|
        solver.assert_fp_abs(b, a);

        let result = solver.check().expect("test operation should succeed");
        assert!(matches!(result, TheoryResult::Sat));

        let b_val = solver.get_value(b).expect("test operation should succeed");
        assert_eq!(b_val.to_f32(), Some(5.0));
    }

    #[test]
    fn test_fp_rounding_modes() {
        let mut solver = FpSolver::new();
        assert_eq!(
            solver.rounding_mode(),
            FpRoundingMode::RoundNearestTiesToEven
        );

        solver.set_rounding_mode(FpRoundingMode::RoundTowardZero);
        assert_eq!(solver.rounding_mode(), FpRoundingMode::RoundTowardZero);
    }

    #[test]
    fn test_fp_is_nan_constraint() {
        let mut solver = FpSolver::new();

        let a = TermId::new(1);
        solver.new_fp(a, FpFormat::FLOAT32);
        solver.assert_is_nan(a);

        let result = solver.check().expect("test operation should succeed");
        assert!(matches!(result, TheoryResult::Sat));

        let val = solver.get_value(a).expect("test operation should succeed");
        assert!(val.is_nan());
    }

    #[test]
    fn test_fp_is_infinite_constraint() {
        let mut solver = FpSolver::new();

        let a = TermId::new(1);
        solver.new_fp(a, FpFormat::FLOAT32);
        solver.assert_is_infinite(a);

        let result = solver.check().expect("test operation should succeed");
        assert!(matches!(result, TheoryResult::Sat));

        let val = solver.get_value(a).expect("test operation should succeed");
        assert!(val.is_infinite());
    }

    #[test]
    fn test_fp_is_zero_constraint() {
        let mut solver = FpSolver::new();

        let a = TermId::new(1);
        solver.new_fp(a, FpFormat::FLOAT32);
        solver.assert_is_zero(a);

        let result = solver.check().expect("test operation should succeed");
        assert!(matches!(result, TheoryResult::Sat));

        let val = solver.get_value(a).expect("test operation should succeed");
        assert!(val.is_zero());
    }

    #[test]
    fn test_fp_comparison_lt() {
        let mut solver = FpSolver::new();

        let a = TermId::new(1);
        let b = TermId::new(2);

        solver.new_fp(a, FpFormat::FLOAT32);
        solver.new_fp(b, FpFormat::FLOAT32);

        // a = -1.0 (negative)
        solver.assert_const(a, &FpValue::from_f32(-1.0));
        // b = 1.0 (positive)
        solver.assert_const(b, &FpValue::from_f32(1.0));

        // a < b
        let lt_result = solver.assert_fp_lt(a, b);
        solver.sat.add_clause([Lit::pos(lt_result)]);

        let result = solver.check().expect("test operation should succeed");
        assert!(matches!(result, TheoryResult::Sat));
    }

    /// Audit regression (theories-fp): `assert_fp_lt` must encode the real
    /// IEEE-754 total order, not "sign(a) negative AND sign(b) positive".
    /// 1.0 < 2.0 must be satisfiable when asserted true.
    #[test]
    fn audit_fp_lt_positive_magnitudes() {
        let mut solver = FpSolver::new();

        let a = TermId::new(1);
        let b = TermId::new(2);

        solver.new_fp(a, FpFormat::FLOAT32);
        solver.new_fp(b, FpFormat::FLOAT32);

        solver.assert_const(a, &FpValue::from_f32(1.0));
        solver.assert_const(b, &FpValue::from_f32(2.0));

        let lt_result = solver.assert_fp_lt(a, b);
        solver.sat.add_clause([Lit::pos(lt_result)]);

        let result = solver.check().expect("test operation should succeed");
        assert!(
            matches!(result, TheoryResult::Sat),
            "1.0 < 2.0 must be SAT under the real total order"
        );
    }

    /// Audit regression (theories-fp): NOT(0.5 < 0.25) must be satisfiable
    /// (i.e. asserting `0.5 < 0.25` as true must be UNSAT), which the old
    /// sign-only encoding could not detect since both operands are positive.
    #[test]
    fn audit_fp_lt_rejects_wrong_direction() {
        let mut solver = FpSolver::new();

        let a = TermId::new(1);
        let b = TermId::new(2);

        solver.new_fp(a, FpFormat::FLOAT32);
        solver.new_fp(b, FpFormat::FLOAT32);

        solver.assert_const(a, &FpValue::from_f32(0.5));
        solver.assert_const(b, &FpValue::from_f32(0.25));

        // Assert (falsely) that 0.5 < 0.25 -- must be UNSAT.
        let lt_result = solver.assert_fp_lt(a, b);
        solver.sat.add_clause([Lit::pos(lt_result)]);

        let result = solver.check().expect("test operation should succeed");
        assert!(
            matches!(result, TheoryResult::Unsat(_)),
            "0.5 < 0.25 must be UNSAT under the real total order"
        );
    }

    /// Audit regression (theories-fp): `assert_fp_le` must actually encode
    /// an ordering constraint. `5.0 <= 1.0` must be UNSAT (the old encoding
    /// silently dropped the ordering and allowed it as SAT).
    #[test]
    fn audit_fp_le_rejects_wrong_direction() {
        let mut solver = FpSolver::new();

        let a = TermId::new(1);
        let b = TermId::new(2);

        solver.new_fp(a, FpFormat::FLOAT32);
        solver.new_fp(b, FpFormat::FLOAT32);

        solver.assert_const(a, &FpValue::from_f32(5.0));
        solver.assert_const(b, &FpValue::from_f32(1.0));

        let le_result = solver.assert_fp_le(a, b);
        solver.sat.add_clause([Lit::pos(le_result)]);

        let result = solver.check().expect("test operation should succeed");
        assert!(
            matches!(result, TheoryResult::Unsat(_)),
            "5.0 <= 1.0 must be UNSAT"
        );
    }

    /// Audit regression (theories-fp): `<=` must be reflexive: `a <= a`.
    #[test]
    fn audit_fp_le_reflexive() {
        let mut solver = FpSolver::new();

        let a = TermId::new(1);
        let b = TermId::new(2);

        solver.new_fp(a, FpFormat::FLOAT32);
        solver.new_fp(b, FpFormat::FLOAT32);

        solver.assert_const(a, &FpValue::from_f32(3.5));
        solver.assert_const(b, &FpValue::from_f32(3.5));

        let le_result = solver.assert_fp_le(a, b);
        solver.sat.add_clause([Lit::pos(le_result)]);

        let result = solver.check().expect("test operation should succeed");
        assert!(matches!(result, TheoryResult::Sat), "a <= a must be SAT");
    }

    /// Audit regression (theories-fp): NaN comparisons are always false per
    /// SMT-LIB `fp.lt`/`fp.leq` semantics, in both `<` and `<=`, regardless
    /// of operand order.
    #[test]
    fn audit_fp_comparisons_false_on_nan() {
        let mut solver = FpSolver::new();

        let a = TermId::new(1);
        let b = TermId::new(2);

        solver.new_fp(a, FpFormat::FLOAT32);
        solver.new_fp(b, FpFormat::FLOAT32);

        solver.assert_const(a, &FpValue::nan(FpFormat::FLOAT32));
        solver.assert_const(b, &FpValue::from_f32(1.0));

        let lt_result = solver.assert_fp_lt(a, b);
        solver.sat.add_clause([Lit::pos(lt_result)]);
        let result = solver.check().expect("test operation should succeed");
        assert!(
            matches!(result, TheoryResult::Unsat(_)),
            "NaN < 1.0 must be UNSAT (fp.lt is false on NaN)"
        );

        let mut solver = FpSolver::new();
        solver.new_fp(a, FpFormat::FLOAT32);
        solver.new_fp(b, FpFormat::FLOAT32);
        solver.assert_const(a, &FpValue::from_f32(1.0));
        solver.assert_const(b, &FpValue::nan(FpFormat::FLOAT32));

        let le_result = solver.assert_fp_le(a, b);
        solver.sat.add_clause([Lit::pos(le_result)]);
        let result = solver.check().expect("test operation should succeed");
        assert!(
            matches!(result, TheoryResult::Unsat(_)),
            "1.0 <= NaN must be UNSAT (fp.leq is false on NaN)"
        );
    }

    /// Audit regression (theories-fp): -0.0 and +0.0 must compare equal
    /// under `<` (neither is strictly less than the other) and both
    /// directions of `<=` must hold.
    #[test]
    fn audit_fp_lt_signed_zero_equal() {
        let mut solver = FpSolver::new();

        let a = TermId::new(1);
        let b = TermId::new(2);

        solver.new_fp(a, FpFormat::FLOAT32);
        solver.new_fp(b, FpFormat::FLOAT32);

        solver.assert_const(a, &FpValue::neg_zero(FpFormat::FLOAT32));
        solver.assert_const(b, &FpValue::pos_zero(FpFormat::FLOAT32));

        // -0.0 < +0.0 must be UNSAT (they are equal, not ordered).
        let lt_result = solver.assert_fp_lt(a, b);
        solver.sat.add_clause([Lit::pos(lt_result)]);
        let result = solver.check().expect("test operation should succeed");
        assert!(
            matches!(result, TheoryResult::Unsat(_)),
            "-0.0 < +0.0 must be UNSAT"
        );

        // +0.0 < -0.0 must also be UNSAT.
        let mut solver = FpSolver::new();
        solver.new_fp(a, FpFormat::FLOAT32);
        solver.new_fp(b, FpFormat::FLOAT32);
        solver.assert_const(a, &FpValue::pos_zero(FpFormat::FLOAT32));
        solver.assert_const(b, &FpValue::neg_zero(FpFormat::FLOAT32));
        let lt_result = solver.assert_fp_lt(a, b);
        solver.sat.add_clause([Lit::pos(lt_result)]);
        let result = solver.check().expect("test operation should succeed");
        assert!(
            matches!(result, TheoryResult::Unsat(_)),
            "+0.0 < -0.0 must be UNSAT"
        );

        // -0.0 <= +0.0 and +0.0 <= -0.0 must both be SAT.
        let mut solver = FpSolver::new();
        solver.new_fp(a, FpFormat::FLOAT32);
        solver.new_fp(b, FpFormat::FLOAT32);
        solver.assert_const(a, &FpValue::neg_zero(FpFormat::FLOAT32));
        solver.assert_const(b, &FpValue::pos_zero(FpFormat::FLOAT32));
        let le_result = solver.assert_fp_le(a, b);
        solver.sat.add_clause([Lit::pos(le_result)]);
        let result = solver.check().expect("test operation should succeed");
        assert!(
            matches!(result, TheoryResult::Sat),
            "-0.0 <= +0.0 must be SAT"
        );
    }

    #[test]
    fn test_fp_conversion_same_format() {
        let mut solver = FpSolver::new();

        let a = TermId::new(1);
        let b = TermId::new(2);

        solver.new_fp(a, FpFormat::FLOAT32);
        solver.assert_const(a, &FpValue::from_f32(2.75));

        // Convert a to b (same format)
        solver.assert_fp_to_fp(b, a, FpFormat::FLOAT32);

        let result = solver.check().expect("test operation should succeed");
        assert!(matches!(result, TheoryResult::Sat));

        let b_val = solver.get_value(b).expect("test operation should succeed");
        assert_eq!(b_val.to_f32(), Some(2.75));
    }

    #[test]
    fn test_fp_conversion_preserves_nan() {
        let mut solver = FpSolver::new();

        let a = TermId::new(1);
        let b = TermId::new(2);

        solver.new_fp(a, FpFormat::FLOAT32);
        solver.assert_const(a, &FpValue::nan(FpFormat::FLOAT32));

        // Convert to FLOAT64
        solver.assert_fp_to_fp(b, a, FpFormat::FLOAT64);

        let result = solver.check().expect("test operation should succeed");
        assert!(matches!(result, TheoryResult::Sat));

        let b_val = solver.get_value(b).expect("test operation should succeed");
        assert!(b_val.is_nan());
    }

    #[test]
    fn test_fp_conversion_preserves_infinity() {
        let mut solver = FpSolver::new();

        let a = TermId::new(1);
        let b = TermId::new(2);

        solver.new_fp(a, FpFormat::FLOAT32);
        solver.assert_const(a, &FpValue::pos_infinity(FpFormat::FLOAT32));

        // Convert to FLOAT64
        solver.assert_fp_to_fp(b, a, FpFormat::FLOAT64);

        let result = solver.check().expect("test operation should succeed");
        assert!(matches!(result, TheoryResult::Sat));

        let b_val = solver.get_value(b).expect("test operation should succeed");
        assert!(b_val.is_infinite());
        assert!(b_val.is_positive());
    }

    // Audit regression (theories-fp): `assert_fp_eq` conflated `fp.eq` and
    // structural `=`, forcing BOTH operands to be non-NaN and forcing sign
    // bits equal. Per SMT-LIB semantics, `=` treats NaN as a single
    // abstract value (NaN = NaN holds), so this must now be SAT.
    #[test]
    fn audit_assert_fp_eq_allows_nan_eq_nan() {
        let mut solver = FpSolver::new();
        let a = TermId::new(1);
        let b = TermId::new(2);

        solver.new_fp(a, FpFormat::FLOAT32);
        solver.new_fp(b, FpFormat::FLOAT32);
        solver.assert_const(a, &FpValue::nan(FpFormat::FLOAT32));
        solver.assert_const(b, &FpValue::nan(FpFormat::FLOAT32));

        solver.assert_fp_eq(a, b);

        let result = solver.check().expect("test operation should succeed");
        assert!(
            matches!(result, TheoryResult::Sat),
            "NaN = NaN must be SAT under structural `=` (single abstract NaN value)"
        );
    }

    // Audit regression (theories-fp): structural `=` must still distinguish
    // `+0` and `-0` (they have distinct bit patterns and are different
    // SMT-LIB FloatingPoint values under `=`), unlike `fp.eq`.
    #[test]
    fn audit_assert_fp_eq_distinguishes_signed_zero() {
        let mut solver = FpSolver::new();
        let a = TermId::new(1);
        let b = TermId::new(2);

        solver.new_fp(a, FpFormat::FLOAT32);
        solver.new_fp(b, FpFormat::FLOAT32);
        solver.assert_const(a, &FpValue::pos_zero(FpFormat::FLOAT32));
        solver.assert_const(b, &FpValue::neg_zero(FpFormat::FLOAT32));

        solver.assert_fp_eq(a, b);

        let result = solver.check().expect("test operation should succeed");
        assert!(
            matches!(result, TheoryResult::Unsat(_)),
            "+0 = -0 must be UNSAT under structural `=` (distinct bit patterns)"
        );
    }

    // Audit regression (theories-fp): `fp.eq` (IEEE-754 equality) must treat
    // `+0` and `-0` as equal, unlike structural `=`.
    #[test]
    fn audit_fp_ieee_eq_treats_signed_zero_equal() {
        let mut solver = FpSolver::new();
        let a = TermId::new(1);
        let b = TermId::new(2);

        solver.new_fp(a, FpFormat::FLOAT32);
        solver.new_fp(b, FpFormat::FLOAT32);
        solver.assert_const(a, &FpValue::pos_zero(FpFormat::FLOAT32));
        solver.assert_const(b, &FpValue::neg_zero(FpFormat::FLOAT32));

        let holds = solver.assert_fp_ieee_eq(a, b);
        solver.sat.add_clause([Lit::pos(holds)]);

        let result = solver.check().expect("test operation should succeed");
        assert!(
            matches!(result, TheoryResult::Sat),
            "fp.eq(+0, -0) must be true (SAT when asserted)"
        );
    }

    // Audit regression (theories-fp): `fp.eq` must be false for NaN against
    // itself (unlike structural `=`), per SMT-LIB semantics.
    #[test]
    fn audit_fp_ieee_eq_false_on_nan_vs_nan() {
        let mut solver = FpSolver::new();
        let a = TermId::new(1);
        let b = TermId::new(2);

        solver.new_fp(a, FpFormat::FLOAT32);
        solver.new_fp(b, FpFormat::FLOAT32);
        solver.assert_const(a, &FpValue::nan(FpFormat::FLOAT32));
        solver.assert_const(b, &FpValue::nan(FpFormat::FLOAT32));

        let holds = solver.assert_fp_ieee_eq(a, b);
        // Force fp.eq(a, b) to be true; this must be UNSAT since NaN is
        // never fp.eq-equal to anything, including itself.
        solver.sat.add_clause([Lit::pos(holds)]);

        let result = solver.check().expect("test operation should succeed");
        assert!(
            matches!(result, TheoryResult::Unsat(_)),
            "fp.eq(NaN, NaN) must be false, so asserting it true must be UNSAT"
        );
    }

    // Audit regression (theories-fp): `FpSolver::check()` previously ran
    // `solve()` without the BvSolver-style incremental-probe cleanup
    // (trail rollback + learned-clause forgetting). A satisfied model or a
    // clause learned during one probe could poison the next incremental
    // probe on the same instance, spuriously turning a satisfiable
    // continuation into `Unsat`.
    #[test]
    fn audit_fp_check_is_incremental_safe_across_probes() {
        let mut solver = FpSolver::new();
        let a = TermId::new(1);
        let b = TermId::new(2);

        solver.new_fp(a, FpFormat::FLOAT32);
        solver.new_fp(b, FpFormat::FLOAT32);
        solver.assert_const(a, &FpValue::from_f32(1.5));

        // First probe: satisfiable (b unconstrained).
        let result1 = solver.check().expect("first probe should succeed");
        assert!(
            matches!(result1, TheoryResult::Sat),
            "probe 1 should be SAT"
        );

        // Second probe on the SAME instance, after adding a fresh
        // constraint: must not be spuriously UNSAT due to residue from
        // probe 1.
        solver.assert_const(b, &FpValue::from_f32(2.5));
        let result2 = solver.check().expect("second probe should succeed");
        assert!(
            matches!(result2, TheoryResult::Sat),
            "probe 2 should still be SAT; got {result2:?} (probe 1 residue leaked?)"
        );

        let b_val = solver.get_value(b).expect("b should have a value");
        assert_eq!(b_val.to_f32(), Some(2.5));
    }

    // Audit regression (theories-fp): on UNSAT, `check()` previously
    // returned an empty conflict (`TheoryResult::Unsat(Vec::new())`),
    // fabricating a conflict explanation that cites nothing. It must now
    // return the actual asserted terms responsible.
    #[test]
    fn audit_fp_check_unsat_returns_nonempty_conflict() {
        let mut solver = FpSolver::new();
        let a = TermId::new(1);

        solver.new_fp(a, FpFormat::FLOAT32);
        solver.assert_const(a, &FpValue::from_f32(1.0));
        solver.assert_const(a, &FpValue::from_f32(2.0));

        let result = solver.check().expect("test operation should succeed");
        match result {
            TheoryResult::Unsat(conflict) => {
                assert!(
                    !conflict.is_empty(),
                    "UNSAT conflict explanation must not be fabricated as empty"
                );
            }
            other => panic!("expected Unsat, got {other:?}"),
        }
    }

    // ------------------------------------------------------------------
    // Honesty (theories-fp): the FP<->int/real conversion methods do not
    // yet bit-blast their semantics. They must NOT let `check()` report a
    // bogus `Sat` on a model that ignores the conversion -- an unsupported
    // conversion assertion forces `Unknown`. `Unsat` (sound regardless of
    // the free conversion bits) is still reported.
    // ------------------------------------------------------------------

    #[test]
    fn audit_unsupported_conversion_reports_unknown_not_sat() {
        // sbv_to_fp is unconstrained; a plain FP problem that would be Sat
        // must degrade to Unknown once such a conversion is asserted.
        let mut solver = FpSolver::new();
        let src = TermId::new(1);
        let dst = TermId::new(2);
        solver.new_fp(dst, FpFormat::FLOAT32);
        solver.assert_sbv_to_fp(dst, src, 32, FpFormat::FLOAT32);

        let result = solver.check().expect("check must not error");
        assert!(
            matches!(result, TheoryResult::Unknown),
            "unsupported conversion must yield Unknown, not a bogus Sat; got {result:?}"
        );
    }

    #[test]
    fn audit_fp_to_ubv_reports_unknown() {
        let mut solver = FpSolver::new();
        let src = TermId::new(1);
        let dst = TermId::new(2);
        solver.new_fp(src, FpFormat::FLOAT32);
        solver.assert_const(src, &FpValue::from_f32(3.5));
        solver.assert_fp_to_ubv(dst, src, 32);

        let result = solver.check().expect("check must not error");
        assert!(
            matches!(result, TheoryResult::Unknown),
            "fp.to_ubv is unsupported: expected Unknown, got {result:?}"
        );
    }

    #[test]
    fn audit_unsupported_conversion_still_reports_unsat() {
        // A definite conflict elsewhere must still be reported as Unsat even
        // when an unsupported conversion is present -- Unsat is sound because
        // it holds regardless of the free conversion bits.
        let mut solver = FpSolver::new();
        let a = TermId::new(1);
        let src = TermId::new(2);
        let dst = TermId::new(3);
        solver.new_fp(a, FpFormat::FLOAT32);
        solver.assert_const(a, &FpValue::from_f32(1.0));
        solver.assert_const(a, &FpValue::from_f32(2.0));
        solver.assert_real_to_fp(dst, src, FpFormat::FLOAT32);

        let result = solver.check().expect("check must not error");
        assert!(
            matches!(result, TheoryResult::Unsat(_)),
            "a definite conflict must remain Unsat despite an unsupported conversion; got {result:?}"
        );
    }

    #[test]
    fn audit_unsupported_conversion_flag_is_scoped_by_pop() {
        // The unsupported-conversion flag must be undone by pop() so a
        // conversion asserted only inside a popped scope does not keep
        // forcing Unknown afterwards.
        let mut solver = FpSolver::new();
        let a = TermId::new(1);
        let src = TermId::new(2);
        let dst = TermId::new(3);
        solver.new_fp(a, FpFormat::FLOAT32);
        solver.assert_const(a, &FpValue::from_f32(1.0));

        solver.push();
        solver.assert_ubv_to_fp(dst, src, 32, FpFormat::FLOAT32);
        let inside = solver.check().expect("check must not error");
        assert!(
            matches!(inside, TheoryResult::Unknown),
            "conversion inside scope must force Unknown; got {inside:?}"
        );
        solver.pop();

        let after = solver.check().expect("check must not error");
        assert!(
            matches!(after, TheoryResult::Sat),
            "after popping the conversion scope, the plain problem is Sat again; got {after:?}"
        );
    }
}
