//! Unit tests for the IEEE 754 engine.
#![allow(clippy::float_cmp)]

use super::*;

#[test]
fn test_unpack_pack_f32() {
    let engine = Ieee754Engine::new();
    let val = FpValue::from_f32(1.0);
    let unpacked = engine.unpack(&val);
    assert_eq!(unpacked.class, FpClass::PositiveNormal);
    assert!(!unpacked.sign);

    let mut pack_engine = Ieee754Engine::new();
    let packed = pack_engine.pack(&unpacked, FpFormat::FLOAT32);
    assert_eq!(packed.to_f32(), Some(1.0));
}

#[test]
fn test_addition_basic() {
    let mut engine = Ieee754Engine::new();
    let a = FpValue::from_f32(1.0);
    let b = FpValue::from_f32(2.0);
    let result = engine.add(&a, &b);
    assert_eq!(result.to_f32(), Some(3.0));
}

#[test]
fn test_subtraction_basic() {
    let mut engine = Ieee754Engine::new();
    let a = FpValue::from_f32(5.0);
    let b = FpValue::from_f32(2.0);
    let result = engine.sub(&a, &b);
    assert_eq!(result.to_f32(), Some(3.0));
}

#[test]
fn test_multiplication_basic() {
    let mut engine = Ieee754Engine::new();
    let a = FpValue::from_f32(2.0);
    let b = FpValue::from_f32(3.0);
    let result = engine.mul(&a, &b);
    assert_eq!(result.to_f32(), Some(6.0));
}

#[test]
fn test_division_basic() {
    let mut engine = Ieee754Engine::new();
    let a = FpValue::from_f32(6.0);
    let b = FpValue::from_f32(2.0);
    let result = engine.div(&a, &b);
    assert_eq!(result.to_f32(), Some(3.0));
}

#[test]
fn test_sqrt_basic() {
    let mut engine = Ieee754Engine::new();
    let a = FpValue::from_f32(4.0);
    let result = engine.sqrt(&a);
    let res_f32 = result.to_f32();
    assert!(res_f32.is_some());
    let val = res_f32.unwrap_or(0.0);
    println!("sqrt(4.0) = {}, expected 2.0", val);
    assert!((val - 2.0).abs() < 0.1); // Approximate check
}

#[test]
fn test_special_values_nan() {
    let engine = Ieee754Engine::new();
    let nan = FpValue::nan(FpFormat::FLOAT32);
    let unpacked = engine.unpack(&nan);
    assert!(unpacked.is_nan());
}

#[test]
fn test_special_values_infinity() {
    let engine = Ieee754Engine::new();
    let inf = FpValue::pos_infinity(FpFormat::FLOAT32);
    let unpacked = engine.unpack(&inf);
    assert_eq!(unpacked.class, FpClass::PositiveInfinity);
}

#[test]
fn test_special_values_zero() {
    let engine = Ieee754Engine::new();
    let zero = FpValue::pos_zero(FpFormat::FLOAT32);
    let unpacked = engine.unpack(&zero);
    assert!(unpacked.is_zero());
}

#[test]
fn test_inf_plus_inf() {
    let mut engine = Ieee754Engine::new();
    let inf1 = FpValue::pos_infinity(FpFormat::FLOAT32);
    let inf2 = FpValue::pos_infinity(FpFormat::FLOAT32);
    let result = engine.add(&inf1, &inf2);
    assert!(result.is_infinite());
}

#[test]
fn test_inf_minus_inf() {
    let mut engine = Ieee754Engine::new();
    let inf1 = FpValue::pos_infinity(FpFormat::FLOAT32);
    let inf2 = FpValue::neg_infinity(FpFormat::FLOAT32);
    let result = engine.add(&inf1, &inf2);
    assert!(result.is_nan());
    assert!(engine.invalid());
}

#[test]
fn test_zero_times_inf() {
    let mut engine = Ieee754Engine::new();
    let zero = FpValue::pos_zero(FpFormat::FLOAT32);
    let inf = FpValue::pos_infinity(FpFormat::FLOAT32);
    let result = engine.mul(&zero, &inf);
    assert!(result.is_nan());
    assert!(engine.invalid());
}

#[test]
fn test_division_by_zero() {
    let mut engine = Ieee754Engine::new();
    let one = FpValue::from_f32(1.0);
    let zero = FpValue::pos_zero(FpFormat::FLOAT32);
    let result = engine.div(&one, &zero);
    assert!(result.is_infinite());
    assert!(engine.divide_by_zero());
}

#[test]
fn test_sqrt_negative() {
    let mut engine = Ieee754Engine::new();
    let neg = FpValue::from_f32(-1.0);
    let result = engine.sqrt(&neg);
    assert!(result.is_nan());
    assert!(engine.invalid());
}

#[test]
fn test_comparison_eq() {
    let engine = Ieee754Engine::new();
    let a = FpValue::from_f32(1.0);
    let b = FpValue::from_f32(1.0);
    assert!(engine.eq(&a, &b));
}

#[test]
fn test_comparison_lt() {
    let engine = Ieee754Engine::new();
    let a = FpValue::from_f32(1.0);
    let b = FpValue::from_f32(2.0);
    assert!(engine.lt(&a, &b));
    assert!(!engine.lt(&b, &a));
}

#[test]
fn test_comparison_nan() {
    let engine = Ieee754Engine::new();
    let nan = FpValue::nan(FpFormat::FLOAT32);
    let one = FpValue::from_f32(1.0);
    assert!(!engine.eq(&nan, &nan));
    assert!(!engine.lt(&nan, &one));
    assert!(!engine.lt(&one, &nan));
}

#[test]
fn test_negation() {
    let engine = Ieee754Engine::new();
    let a = FpValue::from_f32(1.0);
    let neg_a = engine.neg(&a);
    assert_eq!(neg_a.to_f32(), Some(-1.0));
}

#[test]
fn test_absolute_value() {
    let engine = Ieee754Engine::new();
    let a = FpValue::from_f32(-2.5);
    let abs_a = engine.abs(&a);
    assert_eq!(abs_a.to_f32(), Some(2.5));
}

#[test]
fn test_min_max() {
    let mut engine = Ieee754Engine::new();
    let a = FpValue::from_f32(1.0);
    let b = FpValue::from_f32(2.0);

    let min_val = engine.min(&a, &b);
    assert_eq!(min_val.to_f32(), Some(1.0));

    let max_val = engine.max(&a, &b);
    assert_eq!(max_val.to_f32(), Some(2.0));
}

#[test]
fn test_classification() {
    let engine = Ieee754Engine::new();

    let normal = FpValue::from_f32(1.0);
    assert_eq!(engine.classify(&normal), FpClass::PositiveNormal);

    let zero = FpValue::pos_zero(FpFormat::FLOAT32);
    assert_eq!(engine.classify(&zero), FpClass::PositiveZero);

    let inf = FpValue::pos_infinity(FpFormat::FLOAT32);
    assert_eq!(engine.classify(&inf), FpClass::PositiveInfinity);

    let nan = FpValue::nan(FpFormat::FLOAT32);
    assert!(engine.classify(&nan).is_nan());
}

#[test]
fn test_rounding_modes() {
    let mut engine = Ieee754Engine::new();

    // Test different rounding modes
    engine.set_rounding_mode(FpRoundingMode::RoundTowardZero);
    assert_eq!(engine.rounding_mode(), FpRoundingMode::RoundTowardZero);

    engine.set_rounding_mode(FpRoundingMode::RoundTowardPositive);
    assert_eq!(engine.rounding_mode(), FpRoundingMode::RoundTowardPositive);
}

#[test]
fn test_format_conversion_f32_to_f64() {
    let mut engine = Ieee754Engine::new();
    let f32_val = FpValue::from_f32(1.5);
    let f64_val = convert_format(&mut engine, &f32_val, FpFormat::FLOAT64);

    assert_eq!(f64_val.format, FpFormat::FLOAT64);
    // Value should be preserved
    let unpacked = engine.unpack(&f64_val);
    assert_eq!(unpacked.class, FpClass::PositiveNormal);
}

#[test]
fn test_sint_conversion() {
    let mut engine = Ieee754Engine::new();
    let fp_val = FpValue::from_f32(42.0);
    let int_val = fp_to_sint(&mut engine, &fp_val, 64);
    assert_eq!(int_val, Some(42));
}

#[test]
fn test_uint_conversion() {
    let mut engine = Ieee754Engine::new();
    let fp_val = FpValue::from_f32(42.0);
    let uint_val = fp_to_uint(&mut engine, &fp_val, 64);
    assert_eq!(uint_val, Some(42));
}

#[test]
fn test_sint_to_fp() {
    let mut engine = Ieee754Engine::new();
    let fp_val = sint_to_fp(&mut engine, 42, FpFormat::FLOAT32);
    let result = fp_val.to_f32();
    assert!(result.is_some());
}

#[test]
fn test_uint_to_fp() {
    let mut engine = Ieee754Engine::new();
    let fp_val = uint_to_fp(&mut engine, 42, FpFormat::FLOAT32);
    let result = fp_val.to_f32();
    assert!(result.is_some());
}

#[test]
fn test_binary16_format() {
    let format = FpFormat::FLOAT16;
    assert_eq!(format.width(), 16);
    assert_eq!(format.exponent_bits, 5);
    assert_eq!(format.significand_bits, 11);
}

#[test]
fn test_binary128_format() {
    let format = FpFormat::FLOAT128;
    assert_eq!(format.width(), 128);
    assert_eq!(format.exponent_bits, 15);
    assert_eq!(format.significand_bits, 113);
}

#[test]
fn test_exception_flags() {
    let mut engine = Ieee754Engine::new();

    // Test division by zero flag
    let one = FpValue::from_f32(1.0);
    let zero = FpValue::pos_zero(FpFormat::FLOAT32);
    engine.div(&one, &zero);
    assert!(engine.divide_by_zero());

    engine.clear_flags();
    assert!(!engine.divide_by_zero());

    // Test invalid flag
    let nan1 = FpValue::nan(FpFormat::FLOAT32);
    let nan2 = FpValue::nan(FpFormat::FLOAT32);
    engine.add(&nan1, &nan2);
    // Invalid flag should not be set for quiet NaN operations in some cases

    engine.clear_flags();

    // Test 0 * infinity
    let inf = FpValue::pos_infinity(FpFormat::FLOAT32);
    engine.mul(&zero, &inf);
    assert!(engine.invalid());
}

#[test]
fn test_denormal_numbers() {
    let engine = Ieee754Engine::new();

    // Create a subnormal number (exponent = 0, significand != 0)
    let subnormal = FpValue {
        sign: false,
        exponent: 0,
        significand: 1,
        format: FpFormat::FLOAT32,
    };

    let unpacked = engine.unpack(&subnormal);
    assert_eq!(unpacked.class, FpClass::PositiveSubnormal);
}

#[test]
fn test_signed_zero_semantics() {
    let engine = Ieee754Engine::new();
    let pos_zero = FpValue::pos_zero(FpFormat::FLOAT32);
    let neg_zero = FpValue::neg_zero(FpFormat::FLOAT32);

    // +0 == -0 in IEEE 754
    assert!(engine.eq(&pos_zero, &neg_zero));
}

#[test]
fn test_fma_operation() {
    let mut engine = Ieee754Engine::new();
    let a = FpValue::from_f32(2.0);
    let b = FpValue::from_f32(3.0);
    let c = FpValue::from_f32(4.0);

    let result = engine.fma(&a, &b, &c);
    // 2 * 3 + 4 = 10
    assert_eq!(result.to_f32(), Some(10.0));
}

// ---------------------------------------------------------------------------
// IEEE 754 remainder (round-to-nearest-integer quotient) regression tests.
// ---------------------------------------------------------------------------

#[test]
fn test_rem_5_3_is_negative_one() {
    // remainder(5,3): n = round(5/3) = 2, r = 5 - 2*3 = -1 (not fmod's +2).
    let mut engine = Ieee754Engine::new();
    let a = FpValue::from_f32(5.0);
    let b = FpValue::from_f32(3.0);
    assert_eq!(engine.rem(&a, &b).to_f32(), Some(-1.0));
}

#[test]
fn test_rem_matches_hand_computed_vectors_f32() {
    // Each case: (x, y, IEEE remainder). n = round-half-even(x/y).
    let cases = [
        (5.0f32, 3.0f32, -1.0f32), // 5/3->2
        (7.0, 3.0, 1.0),           // 7/3->2, 7-6=1
        (6.0, 3.0, 0.0),           // exact multiple
        (1.0, 3.0, 1.0),           // 1/3->0
        (2.0, 3.0, -1.0),          // 2/3->1, 2-3=-1
        (4.0, 3.0, 1.0),           // 4/3->1
        (-5.0, 3.0, 1.0),          // -5/3->-2, -5+6=1
        (5.0, -3.0, -1.0),         // sign of y does not affect r sign here
        (1.5, 1.0, -0.5),          // tie 1.5->2 (even), 1.5-2=-0.5
        (2.5, 1.0, 0.5),           // tie 2.5->2 (even), 2.5-2=0.5
        (0.5, 1.0, 0.5),           // 0.5/1->0
        (10.0, 4.0, 2.0),          // tie 10/4=2.5->2 (even), 10-8=2
    ];
    for (x, y, expected) in cases {
        let mut engine = Ieee754Engine::new();
        let r = engine.rem(&FpValue::from_f32(x), &FpValue::from_f32(y));
        assert_eq!(r.to_f32(), Some(expected), "rem({x}, {y})");
    }
}

#[test]
fn test_rem_zero_result_takes_dividend_sign() {
    let mut engine = Ieee754Engine::new();
    // remainder(-6, 3) = -0.0 (exact multiple, sign of dividend).
    let r = engine.rem(&FpValue::from_f32(-6.0), &FpValue::from_f32(3.0));
    assert!(r.is_zero());
    assert!(r.sign, "zero remainder of a negative dividend must be -0");
}

#[test]
fn test_rem_special_cases() {
    let mut engine = Ieee754Engine::new();
    let three = FpValue::from_f32(3.0);
    // remainder(x, inf) = x
    let r = engine.rem(&three, &FpValue::pos_infinity(FpFormat::FLOAT32));
    assert_eq!(r.to_f32(), Some(3.0));
    // remainder(inf, y) = NaN
    assert!(
        engine
            .rem(&FpValue::pos_infinity(FpFormat::FLOAT32), &three)
            .is_nan()
    );
    // remainder(x, 0) = NaN
    assert!(
        engine
            .rem(&three, &FpValue::pos_zero(FpFormat::FLOAT32))
            .is_nan()
    );
    // remainder(0, y) = 0
    assert!(
        engine
            .rem(&FpValue::pos_zero(FpFormat::FLOAT32), &three)
            .is_zero()
    );
}

#[test]
fn test_rem_f64_vectors() {
    let cases = [
        (5.0f64, 3.0f64, -1.0f64),
        (13.0, 4.0, 1.0),  // 13/4=3.25->3, 13-12=1
        (11.0, 4.0, -1.0), // 11/4=2.75->3, 11-12=-1
        (1.0e10, 3.0, 1.0),
    ];
    for (x, y, expected) in cases {
        let mut engine = Ieee754Engine::new();
        let r = engine.rem(&FpValue::from_f64(x), &FpValue::from_f64(y));
        assert_eq!(r.to_f64(), Some(expected), "rem({x}, {y})");
    }
}

// ---------------------------------------------------------------------------
// Single-rounded fused multiply-add regression tests. f32/f64 `mul_add` is the
// hardware/std single-rounded reference for the matching format.
// ---------------------------------------------------------------------------

#[test]
fn test_fma_matches_std_mul_add_f32() {
    // Values where the exact product needs more than 24 bits, so a doubly
    // rounded (mul then add) result would differ from the fused result.
    let samples: [(f32, f32, f32); 6] = [
        (1.0 + f32::EPSILON, 1.0 + f32::EPSILON, -1.0),
        (1.0000001, 3.0, 0.0000002),
        (123456.79, 9876.543, -1.0),
        (0.1, 0.1, -0.01),
        (3.3333333, 3.0, -10.0),
        (f32::MAX, 2.0, -f32::MAX),
    ];
    for (a, b, c) in samples {
        let mut engine = Ieee754Engine::new();
        let got = engine.fma(
            &FpValue::from_f32(a),
            &FpValue::from_f32(b),
            &FpValue::from_f32(c),
        );
        let want = a.mul_add(b, c);
        assert_eq!(got.to_f32(), Some(want), "fma({a}, {b}, {c})");
    }
}

#[test]
fn test_fma_matches_std_mul_add_f64() {
    let samples: [(f64, f64, f64); 5] = [
        (1.0 + f64::EPSILON, 1.0 + f64::EPSILON, -1.0),
        (1.000_000_000_000_1, 3.0, 0.0),
        (123456.789, 9876.543, -1.0),
        (0.1, 0.1, -0.01),
        (1.0e300, 1.0e300, -1.0e300),
    ];
    for (a, b, c) in samples {
        let mut engine = Ieee754Engine::new();
        let got = engine.fma(
            &FpValue::from_f64(a),
            &FpValue::from_f64(b),
            &FpValue::from_f64(c),
        );
        let want = a.mul_add(b, c);
        assert_eq!(got.to_f64(), Some(want), "fma({a}, {b}, {c})");
    }
}

#[test]
fn test_fma_single_rounding_differs_from_double_rounding() {
    // a = 2^23 + 1 (exactly representable in f32). a*a = 2^46 + 2^24 + 1, which
    // rounds to 2^46 + 2^24 in f32 (the trailing 1 is well below half an ulp).
    // With c = -(2^46 + 2^24): the fused result is the exact 1.0, while the
    // doubly rounded mul(a,a)+c discards the low bit and yields 0.0.
    let mut engine = Ieee754Engine::new();
    let a_f32 = 8_388_609.0f32; // 2^23 + 1
    let c_f32 = -(a_f32 * a_f32); // -(2^46 + 2^24), exactly representable
    let a = FpValue::from_f32(a_f32);
    let c = FpValue::from_f32(c_f32);

    let fused = engine.fma(&a, &a, &c);
    let prod = engine.mul(&a, &a);
    let doubled = engine.add(&prod, &c);

    let want = a_f32.mul_add(a_f32, c_f32);
    assert_eq!(want, 1.0, "std mul_add reference should be exactly 1.0");
    assert_eq!(
        fused.to_f32(),
        Some(1.0),
        "fused fma must recover the low bit"
    );
    assert_eq!(
        doubled.to_f32(),
        Some(0.0),
        "double rounding loses the low bit"
    );
    assert_ne!(fused.to_f32(), doubled.to_f32());
}

#[test]
fn test_fma_special_cases() {
    let mut engine = Ieee754Engine::new();
    let fmt = FpFormat::FLOAT32;
    // 0 * inf + finite = NaN (invalid)
    assert!(
        engine
            .fma(
                &FpValue::pos_zero(fmt),
                &FpValue::pos_infinity(fmt),
                &FpValue::from_f32(1.0)
            )
            .is_nan()
    );
    // inf * 1 + (-inf) = NaN
    assert!(
        engine
            .fma(
                &FpValue::pos_infinity(fmt),
                &FpValue::from_f32(1.0),
                &FpValue::neg_infinity(fmt)
            )
            .is_nan()
    );
    // 2 * 3 + inf = inf
    let r = engine.fma(
        &FpValue::from_f32(2.0),
        &FpValue::from_f32(3.0),
        &FpValue::pos_infinity(fmt),
    );
    assert!(r.is_infinite() && !r.sign);
    // fma(0, 5, 4) = 4
    assert_eq!(
        engine
            .fma(
                &FpValue::pos_zero(fmt),
                &FpValue::from_f32(5.0),
                &FpValue::from_f32(4.0)
            )
            .to_f32(),
        Some(4.0)
    );
}

/// Regression: `div128` previously kept the running remainder in a bare `u128`
/// and shifted it left before subtracting, silently dropping bit 127 whenever
/// the remainder's MSB was set. Every division whose dividend mantissa was
/// smaller than the divisor's (true quotient in `(0.5, 1)`) — e.g. `10/3`,
/// `1/3`, `9/3` — therefore returned `0.0`. The 129-bit remainder fix makes the
/// quotient bit-exact against the host `f64` divider for the RNE mode.
#[test]
fn test_division_quotient_below_one_is_exact() {
    let mut engine = Ieee754Engine::new();
    let cases = [
        (10.0_f64, 3.0_f64),
        (1.0, 3.0),
        (9.0, 3.0),
        (2.0, 3.0),
        (1.0, 7.0),
        (22.0, 7.0),
        (5.0, 9.0),
        (1.0, 10.0),
        (100.0, 3.0),
    ];
    for (x, y) in cases {
        let a = FpValue::from_f64(x);
        let b = FpValue::from_f64(y);
        engine.set_rounding_mode(FpRoundingMode::RoundNearestTiesToEven);
        let q = engine.div(&a, &b).to_f64();
        assert_eq!(q, Some(x / y), "div({x}, {y}) mismatched the host divider");
    }
}

/// Regression: directed rounding on division must bracket the round-to-nearest
/// result — `RTP` never below and `RTN` never above the exact quotient — so
/// `fp.div RTP` and `fp.div RTN` of `10/3` straddle `3.3333…`.
#[test]
fn test_division_directed_rounding_brackets_rne() {
    let mut engine = Ieee754Engine::new();
    let a = FpValue::from_f64(10.0);
    let b = FpValue::from_f64(3.0);

    engine.set_rounding_mode(FpRoundingMode::RoundTowardPositive);
    let rtp = engine.div(&a, &b);
    engine.set_rounding_mode(FpRoundingMode::RoundTowardNegative);
    let rtn = engine.div(&a, &b);

    let rtp_f = rtp.to_f64().unwrap_or(f64::NAN);
    let rtn_f = rtn.to_f64().unwrap_or(f64::NAN);
    let exact = 10.0_f64 / 3.0_f64;

    assert!(
        rtp_f >= exact,
        "RTP {rtp_f} rounded below the RNE quotient {exact}"
    );
    assert!(
        rtn_f <= exact,
        "RTN {rtn_f} rounded above the RNE quotient {exact}"
    );
    assert!(rtp_f >= rtn_f, "RTP must be >= RTN for positive operands");
    assert!(rtp_f > 3.333 && rtn_f < 3.334);
}
