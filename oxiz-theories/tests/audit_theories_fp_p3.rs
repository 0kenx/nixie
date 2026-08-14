//! Regression tests for audited IEEE-754 arithmetic soundness defects
//! (package: theories-fp-p3), pinned against known bit patterns.
//!
//! Findings fixed in `oxiz-theories/src/fp/ieee754_full.rs`:
//!  1. `RoundNearestTiesToEven` rounded every exact tie *up* instead of to
//!     the candidate with an even least-significant bit.
//!  2. Subnormal unpacking used a shift one bit too large, doubling every
//!     subnormal value used in arithmetic/comparisons.
//!  3. `sqrt()` silently halved the true result for every odd-exponent
//!     input because the (dead) odd-exponent doubling step still
//!     decremented the exponent.

use oxiz_theories::fp::ieee754_full::{FpClass, Ieee754Engine, UnpackedFloat};
use oxiz_theories::fp::{FpFormat, FpRoundingMode, FpValue};

// ========  ========
// Finding 1: RNE must round exact ties to even, not always up.
// ========  ========

/// Directly pins `pack()`'s rounding decision on a hand-constructed exact
/// tie (guard = 1, round = 0, sticky = 0): the pre-round LSB decides the
/// outcome, not "always round up".
#[test]
fn pack_round_nearest_ties_to_even_uses_lsb_not_always_up() {
    let format = FpFormat::FLOAT32;
    let mut engine = Ieee754Engine::new();
    assert_eq!(
        engine.rounding_mode(),
        FpRoundingMode::RoundNearestTiesToEven
    );

    // significand bits are aligned so that MSB = bit 127; pack() extracts
    // the top `significand_bits` (24) bits, with guard/round/sticky bits
    // immediately below. shift = 128 - 24 = 104, so the guard bit is bit 103.

    // Case A: exact tie, pre-round LSB (bit 104) = 0 (already even) -> stay.
    let even_tie = UnpackedFloat {
        sign: false,
        exponent: 0,
        significand: (1u128 << 127) | (1u128 << 103),
        precision: format.significand_bits,
        class: FpClass::PositiveNormal,
    };
    let packed_even = engine.pack(&even_tie, format);
    assert_eq!(packed_even.exponent, 127);
    assert_eq!(
        packed_even.significand, 0,
        "tie with an even pre-round LSB must round DOWN to stay even"
    );
    assert_eq!(packed_even.to_f32(), Some(1.0f32));

    // Case B: exact tie, pre-round LSB (bit 104) = 1 (odd) -> round up to even.
    let odd_tie = UnpackedFloat {
        sign: false,
        exponent: 0,
        significand: (1u128 << 127) | (1u128 << 104) | (1u128 << 103),
        precision: format.significand_bits,
        class: FpClass::PositiveNormal,
    };
    let packed_odd = engine.pack(&odd_tie, format);
    assert_eq!(packed_odd.exponent, 127);
    assert_eq!(
        packed_odd.significand, 2,
        "tie with an odd pre-round LSB must round UP to become even"
    );
}

/// End-to-end check through the real `add()` pipeline (unpack -> align ->
/// add -> normalize -> pack) using a deliberately low-precision custom
/// format so exact halfway sums are easy to construct: 1.0 + 2^-4 = 1.0625
/// sits exactly halfway between 1.000 (even) and 1.125 (odd) at 3 fraction
/// bits, so RNE must round DOWN to 1.0 (2.5 -> 2 pattern); 1.125 + 2^-4 =
/// 1.1875 sits exactly halfway between 1.125 (odd) and 1.25 (even), so RNE
/// must round UP to 1.25 (3.5 -> 4 pattern).
#[test]
fn add_round_nearest_ties_to_even_end_to_end() {
    let format = FpFormat::new(5, 4); // 5 exponent bits, 3 stored fraction bits
    let bias = format.bias();
    let mut engine = Ieee754Engine::new();

    // a = 1.0 (mantissa 000, even), b = 2^-4 = 0.0625 (exact halfway step).
    let a_even = FpValue {
        sign: false,
        exponent: bias as u64,
        significand: 0b000,
        format,
    };
    let b = FpValue {
        sign: false,
        exponent: (-4 + bias) as u64,
        significand: 0,
        format,
    };
    let sum_even = engine.add(&a_even, &b);
    assert_eq!(
        sum_even.significand, 0b000,
        "1.0 + 2^-4 is an exact tie with even LSB; must round down to 1.0"
    );
    assert_eq!(sum_even.exponent, bias as u64);

    // a = 1.125 (mantissa 001, odd) + 2^-4 -> exact tie, must round UP to 1.25.
    let a_odd = FpValue {
        sign: false,
        exponent: bias as u64,
        significand: 0b001,
        format,
    };
    let sum_odd = engine.add(&a_odd, &b);
    assert_eq!(
        sum_odd.significand, 0b010,
        "1.125 + 2^-4 is an exact tie with odd LSB; must round up to 1.25"
    );
    assert_eq!(sum_odd.exponent, bias as u64);
}

// ========  ========
// Finding 2: subnormal unpack must not double the value.
// ========  ========

/// The smallest positive subnormal f32 (0x0000_0001, value 2^-149) must
/// unpack, round-trip, and arithmetic-combine as its true value, not double
/// it.
#[test]
fn subnormal_unpack_f32_min_subnormal_is_not_doubled() {
    let engine_ro = Ieee754Engine::new();
    let min_sub = FpValue {
        sign: false,
        exponent: 0,
        significand: 1,
        format: FpFormat::FLOAT32,
    };
    assert_eq!(f32::from_bits(1), min_sub.to_f32().unwrap_or(0.0));

    let unpacked = engine_ro.unpack(&min_sub);
    assert_eq!(unpacked.class, FpClass::PositiveSubnormal);

    // Reconstruct the numeric value implied by the (now-normalized)
    // unpacked significand/exponent and compare against the true value
    // 2^-149, not 2 * 2^-149.
    let reconstructed =
        (unpacked.significand as f64) / (1u128 << 127) as f64 * 2f64.powi(unpacked.exponent);
    let true_value = 2f64.powi(-149);
    let doubled_value = 2.0 * true_value;
    assert!(
        (reconstructed - true_value).abs() < true_value * 1e-9,
        "min subnormal f32 unpacked to {reconstructed}, expected {true_value} (doubled bug would give {doubled_value})"
    );

    // Round trip through pack() must reproduce the exact original bits.
    let mut engine = Ieee754Engine::new();
    let repacked = engine.pack(&unpacked, FpFormat::FLOAT32);
    assert_eq!(repacked.exponent, 0);
    assert_eq!(repacked.significand, 1);
    assert_eq!(repacked.to_f32(), Some(2f32.powi(-149)));
}

/// The largest positive subnormal f32 (0x007F_FFFF) must also round-trip
/// exactly (this pins the general shift, not just a single-bit edge case).
#[test]
fn subnormal_unpack_f32_max_subnormal_round_trips() {
    let engine_ro = Ieee754Engine::new();
    let max_sub = FpValue {
        sign: false,
        exponent: 0,
        significand: 0x007F_FFFF,
        format: FpFormat::FLOAT32,
    };
    let unpacked = engine_ro.unpack(&max_sub);
    assert_eq!(unpacked.class, FpClass::PositiveSubnormal);

    let mut engine = Ieee754Engine::new();
    let repacked = engine.pack(&unpacked, FpFormat::FLOAT32);
    assert_eq!(repacked.exponent, 0);
    assert_eq!(repacked.significand, 0x007F_FFFF);
}

/// Doubling the smallest subnormal via addition must land on the *second*
/// smallest subnormal (significand = 2), not the *third* (significand = 4,
/// which is what the doubling bug produced since every subnormal operand
/// was silently worth 2x).
#[test]
fn subnormal_add_min_plus_min_equals_second_subnormal() {
    let mut engine = Ieee754Engine::new();
    let min_sub = FpValue {
        sign: false,
        exponent: 0,
        significand: 1,
        format: FpFormat::FLOAT32,
    };
    let result = engine.add(&min_sub, &min_sub);
    assert_eq!(result.exponent, 0);
    assert_eq!(
        result.significand, 2,
        "min_subnormal + min_subnormal must equal significand=2, not the doubled-bug value"
    );
    assert_eq!(result.to_f32(), Some(2f32.powi(-148)));
}

/// Subnormal magnitude ordering must be correct: with the doubling bug,
/// `compare_internal`'s (exponent, significand) lexicographic comparison
/// could reorder subnormals relative to the smallest normal.
#[test]
fn subnormal_ordering_smallest_normal_is_larger_than_any_subnormal() {
    let engine = Ieee754Engine::new();
    let max_sub = FpValue {
        sign: false,
        exponent: 0,
        significand: 0x007F_FFFF, // largest f32 subnormal
        format: FpFormat::FLOAT32,
    };
    let smallest_normal = FpValue {
        sign: false,
        exponent: 1,
        significand: 0,
        format: FpFormat::FLOAT32,
    };
    assert!(engine.lt(&max_sub, &smallest_normal));
    assert!(engine.gt(&smallest_normal, &max_sub));

    // And within the subnormal range itself: min < 2*min < max.
    let min_sub = FpValue {
        sign: false,
        exponent: 0,
        significand: 1,
        format: FpFormat::FLOAT32,
    };
    let two_min_sub = FpValue {
        sign: false,
        exponent: 0,
        significand: 2,
        format: FpFormat::FLOAT32,
    };
    assert!(engine.lt(&min_sub, &two_min_sub));
    assert!(engine.lt(&two_min_sub, &max_sub));
}

/// Same shift-doubling defect, checked against f64's min/max subnormal.
#[test]
fn subnormal_unpack_f64_min_and_max_subnormal_round_trip() {
    let mut engine = Ieee754Engine::new();

    let min_sub = FpValue {
        sign: false,
        exponent: 0,
        significand: 1,
        format: FpFormat::FLOAT64,
    };
    let unpacked_min = engine.unpack(&min_sub);
    let repacked_min = engine.pack(&unpacked_min, FpFormat::FLOAT64);
    assert_eq!(repacked_min.significand, 1);
    assert_eq!(repacked_min.to_f64(), Some(f64::from_bits(1)));

    let max_sub = FpValue {
        sign: false,
        exponent: 0,
        significand: 0x000F_FFFF_FFFF_FFFF,
        format: FpFormat::FLOAT64,
    };
    let unpacked_max = engine.unpack(&max_sub);
    let repacked_max = engine.pack(&unpacked_max, FpFormat::FLOAT64);
    assert_eq!(repacked_max.significand, 0x000F_FFFF_FFFF_FFFF);
    assert_eq!(
        repacked_max.to_f64(),
        Some(f64::from_bits(0x000F_FFFF_FFFF_FFFF))
    );
}

// ========  ========
// Finding 3: sqrt() must not halve odd-exponent inputs.
// ========  ========

/// sqrt(2.0) must be ~1.4142135..., not 1.0 (which is what the dead
/// doubling / unconditional `exp -= 1` bug produced: sqrt(1.0) = 1.0).
#[test]
fn sqrt_of_two_matches_std_sqrt() {
    let mut engine = Ieee754Engine::new();
    let a = FpValue::from_f64(2.0);
    let result = engine.sqrt(&a);
    let got = result.to_f64().unwrap_or(0.0);
    let expected = 2.0f64.sqrt();
    assert!(
        (got - expected).abs() < expected * 1e-12,
        "sqrt(2.0) = {got}, expected ~{expected} (bug would give ~1.0)"
    );
    // Explicitly rule out the halved (bug) result.
    assert!((got - 1.0).abs() > 0.3);
}

/// sqrt(0.5) must be ~0.70710678..., not 0.5^... (halved-again bug value).
#[test]
fn sqrt_of_half_matches_std_sqrt() {
    let mut engine = Ieee754Engine::new();
    let a = FpValue::from_f64(0.5);
    let result = engine.sqrt(&a);
    let got = result.to_f64().unwrap_or(0.0);
    let expected = 0.5f64.sqrt();
    assert!(
        (got - expected).abs() < expected * 1e-12,
        "sqrt(0.5) = {got}, expected ~{expected}"
    );
}

/// sqrt across a spread of odd- and even-exponent inputs (including
/// subnormals) must agree with `f64::sqrt` (which is correctly rounded)
/// to within a tight relative tolerance; the old bug was off by an exact
/// factor of sqrt(2) for every odd-exponent input.
#[test]
fn sqrt_odd_and_even_exponents_match_std_sqrt_f64() {
    let mut engine = Ieee754Engine::new();
    let cases: &[f64] = &[
        2.0,
        8.0,
        32.0,
        0.5,
        0.125,
        3.0,
        7.0,
        200.0,
        1e-300,
        1e300,
        4.0,               // even exponent, sanity check unaffected
        16.0,              // even exponent
        f64::from_bits(3), // small subnormal (odd internal exponent path)
    ];
    for &x in cases {
        let a = FpValue::from_f64(x);
        let result = engine.sqrt(&a);
        let got = result.to_f64().unwrap_or(0.0);
        let expected = x.sqrt();
        let rel_err = ((got - expected).abs()) / expected;
        assert!(
            rel_err < 1e-9,
            "sqrt({x}) = {got}, expected {expected} (relative error {rel_err})"
        );
    }
}

/// sqrt(4.0) = 2.0 exactly (even exponent, unaffected by the odd-exponent
/// bug); pins that the fix did not regress the previously-passing case.
#[test]
fn sqrt_of_four_is_exactly_two() {
    let mut engine = Ieee754Engine::new();
    let a = FpValue::from_f64(4.0);
    let result = engine.sqrt(&a);
    assert_eq!(result.to_f64(), Some(2.0));
}
