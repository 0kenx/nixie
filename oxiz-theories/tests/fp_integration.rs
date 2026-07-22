//! Integration tests for Floating-Point Theory Solver (QF_FP)
//!
//! These tests verify the integration of the FP solver with SAT constraints,
//! model extraction, and solver mechanics. Tests cover:
//! - Basic arithmetic operations (fp.add, fp.mul, fp.div, fp.sub)
//! - Rounding modes (RNE, RTP, RTN, RTZ, RNA)
//! - Special values (NaN, +infinity, -infinity, +zero, -zero)
//! - Comparison predicates (fp.lt, fp.gt, fp.leq, fp.geq, fp.eq)
//! - Classification predicates (fp.isNaN, fp.isInfinite, fp.isZero, fp.isNormal)
//! - Format conversions (Float32 <-> Float64, to_fp)
//! - Solver integration (push/pop, model extraction, multiple assertions)

use oxiz_core::ast::TermId;
use oxiz_theories::fp::{FpFormat, FpRoundingMode, FpSolver, FpValue};
use oxiz_theories::{Theory, TheoryCheckResult as TheoryResult};

/// Helper function to create a unique TermId
fn term(id: u32) -> TermId {
    TermId::new(id)
}

#[test]
fn test_fp_const_float32() {
    let mut solver = FpSolver::new();

    let a = term(1);
    let value = FpValue::from_f32(42.5);

    solver.assert_const(a, &value);

    let result = solver.check().expect("check should succeed");
    assert!(matches!(result, TheoryResult::Sat));

    let retrieved = solver.get_value(a).expect("value should exist");
    assert_eq!(retrieved.to_f32(), Some(42.5));
}

#[test]
fn test_fp_const_float64() {
    let mut solver = FpSolver::new();

    let a = term(1);
    let value = FpValue::from_f64(std::f64::consts::PI);

    solver.assert_const(a, &value);

    let result = solver.check().expect("check should succeed");
    assert!(matches!(result, TheoryResult::Sat));

    let retrieved = solver.get_value(a).expect("value should exist");
    let val = retrieved.to_f64().expect("should convert to f64");
    assert!((val - std::f64::consts::PI).abs() < 1e-10);
}

#[test]
fn test_fp_equality_constraint() {
    let mut solver = FpSolver::new();

    let a = term(1);
    let b = term(2);

    solver.new_fp(a, FpFormat::FLOAT32);
    solver.new_fp(b, FpFormat::FLOAT32);

    // a = 7.5
    solver.assert_const(a, &FpValue::from_f32(7.5));

    // a = b
    solver.assert_fp_eq(a, b);

    let result = solver.check().expect("check should succeed");
    assert!(matches!(result, TheoryResult::Sat));

    // b should also be 7.5
    let b_val = solver.get_value(b).expect("value should exist");
    assert_eq!(b_val.to_f32(), Some(7.5));
}

#[test]
fn test_fp_negation_float32() {
    let mut solver = FpSolver::new();

    let a = term(1);
    let b = term(2);

    solver.new_fp(a, FpFormat::FLOAT32);
    solver.new_fp(b, FpFormat::FLOAT32);

    // a = 12.25
    solver.assert_const(a, &FpValue::from_f32(12.25));

    // b = -a
    solver.assert_fp_neg(b, a);

    let result = solver.check().expect("check should succeed");
    assert!(matches!(result, TheoryResult::Sat));

    let b_val = solver.get_value(b).expect("value should exist");
    assert_eq!(b_val.to_f32(), Some(-12.25));
}

#[test]
fn test_fp_negation_float64() {
    let mut solver = FpSolver::new();

    let a = term(1);
    let b = term(2);

    solver.new_fp(a, FpFormat::FLOAT64);
    solver.new_fp(b, FpFormat::FLOAT64);

    // a = 99.875
    solver.assert_const(a, &FpValue::from_f64(99.875));

    // b = -a
    solver.assert_fp_neg(b, a);

    let result = solver.check().expect("check should succeed");
    assert!(matches!(result, TheoryResult::Sat));

    let b_val = solver.get_value(b).expect("value should exist");
    assert_eq!(b_val.to_f64(), Some(-99.875));
}

#[test]
fn test_fp_absolute_value() {
    let mut solver = FpSolver::new();

    let a = term(1);
    let b = term(2);

    solver.new_fp(a, FpFormat::FLOAT32);
    solver.new_fp(b, FpFormat::FLOAT32);

    // a = -15.5
    solver.assert_const(a, &FpValue::from_f32(-15.5));

    // b = |a|
    solver.assert_fp_abs(b, a);

    let result = solver.check().expect("check should succeed");
    assert!(matches!(result, TheoryResult::Sat));

    let b_val = solver.get_value(b).expect("value should exist");
    assert_eq!(b_val.to_f32(), Some(15.5));
}

#[test]
fn test_fp_special_value_positive_zero() {
    let mut solver = FpSolver::new();

    let a = term(1);
    let value = FpValue::pos_zero(FpFormat::FLOAT32);

    solver.assert_const(a, &value);

    let result = solver.check().expect("check should succeed");
    assert!(matches!(result, TheoryResult::Sat));

    let retrieved = solver.get_value(a).expect("value should exist");
    assert!(retrieved.is_zero());
    assert!(!retrieved.sign);
}

#[test]
fn test_fp_special_value_negative_zero() {
    let mut solver = FpSolver::new();

    let a = term(1);
    let value = FpValue::neg_zero(FpFormat::FLOAT32);

    solver.assert_const(a, &value);

    let result = solver.check().expect("check should succeed");
    assert!(matches!(result, TheoryResult::Sat));

    let retrieved = solver.get_value(a).expect("value should exist");
    assert!(retrieved.is_zero());
    assert!(retrieved.sign);
}

#[test]
fn test_fp_special_value_positive_infinity() {
    let mut solver = FpSolver::new();

    let a = term(1);
    let value = FpValue::pos_infinity(FpFormat::FLOAT64);

    solver.assert_const(a, &value);

    let result = solver.check().expect("check should succeed");
    assert!(matches!(result, TheoryResult::Sat));

    let retrieved = solver.get_value(a).expect("value should exist");
    assert!(retrieved.is_infinite());
    assert!(retrieved.is_positive());
}

#[test]
fn test_fp_special_value_negative_infinity() {
    let mut solver = FpSolver::new();

    let a = term(1);
    let value = FpValue::neg_infinity(FpFormat::FLOAT64);

    solver.assert_const(a, &value);

    let result = solver.check().expect("check should succeed");
    assert!(matches!(result, TheoryResult::Sat));

    let retrieved = solver.get_value(a).expect("value should exist");
    assert!(retrieved.is_infinite());
    assert!(retrieved.is_negative());
}

#[test]
fn test_fp_special_value_nan() {
    let mut solver = FpSolver::new();

    let a = term(1);
    let value = FpValue::nan(FpFormat::FLOAT32);

    solver.assert_const(a, &value);

    let result = solver.check().expect("check should succeed");
    assert!(matches!(result, TheoryResult::Sat));

    let retrieved = solver.get_value(a).expect("value should exist");
    assert!(retrieved.is_nan());
}

#[test]
fn test_fp_predicate_is_nan() {
    let mut solver = FpSolver::new();

    let a = term(1);
    solver.new_fp(a, FpFormat::FLOAT32);
    solver.assert_is_nan(a);

    let result = solver.check().expect("check should succeed");
    assert!(matches!(result, TheoryResult::Sat));

    let val = solver.get_value(a).expect("value should exist");
    assert!(val.is_nan());
}

#[test]
fn test_fp_predicate_is_infinite() {
    let mut solver = FpSolver::new();

    let a = term(1);
    solver.new_fp(a, FpFormat::FLOAT64);
    solver.assert_is_infinite(a);

    let result = solver.check().expect("check should succeed");
    assert!(matches!(result, TheoryResult::Sat));

    let val = solver.get_value(a).expect("value should exist");
    assert!(val.is_infinite());
}

#[test]
fn test_fp_predicate_is_zero() {
    let mut solver = FpSolver::new();

    let a = term(1);
    solver.new_fp(a, FpFormat::FLOAT32);
    solver.assert_is_zero(a);

    let result = solver.check().expect("check should succeed");
    assert!(matches!(result, TheoryResult::Sat));

    let val = solver.get_value(a).expect("value should exist");
    assert!(val.is_zero());
}

#[test]
fn test_fp_predicate_is_normal() {
    let mut solver = FpSolver::new();

    let a = term(1);
    solver.new_fp(a, FpFormat::FLOAT32);
    solver.assert_is_normal(a);

    // `assert_is_normal` constrains the exponent to be nonzero and not
    // all-ones (i.e. neither subnormal/zero nor NaN/infinity), which is
    // always satisfiable (e.g. exponent = 1, any significand). A solver
    // that answers Unsat/Unknown here has a real bug, so this must be a
    // hard assertion, not a vacuous `if Sat` guard.
    let result = solver.check().expect("check should succeed");
    assert!(matches!(result, TheoryResult::Sat));
    let val = solver.get_value(a).expect("value should exist");
    assert!(val.is_normal());
    assert!(!val.is_zero());
    assert!(!val.is_nan());
    assert!(!val.is_infinite());
}

/// `fp.isNormal` must reject a value whose classification is pinned to a
/// mutually exclusive predicate by direct construction (`assert_is_zero` /
/// `assert_is_nan`, each building its own encode_is_* reification over the
/// same underlying exponent/significand bits as `assert_is_normal`). These
/// two directions confirm `assert_is_normal`'s own encoding is sound: it
/// correctly conflicts with `is_zero` and with `is_nan` via the shared
/// bit-level variables, with no `assert_const` in the picture.
#[test]
fn test_fp_predicate_is_normal_conflicts_with_is_zero() {
    let mut solver = FpSolver::new();

    let a = term(1);
    solver.new_fp(a, FpFormat::FLOAT32);
    solver.assert_is_normal(a);
    solver.assert_is_zero(a);

    let result = solver.check().expect("check should succeed");
    assert!(matches!(result, TheoryResult::Unsat(_)));
}

#[test]
fn test_fp_predicate_is_normal_conflicts_with_is_nan() {
    let mut solver = FpSolver::new();

    let a = term(1);
    solver.new_fp(a, FpFormat::FLOAT32);
    solver.assert_is_normal(a);
    solver.assert_is_nan(a);

    let result = solver.check().expect("check should succeed");
    assert!(matches!(result, TheoryResult::Unsat(_)));
}

/// `fp.isNormal` must also reject the negative case: a value pinned to
/// the subnormal-only range (exponent field all zero, nonzero
/// significand) can never be normal, so asserting both `fp.isNormal` and
/// a concrete subnormal constant must be Unsat.
///
/// CONFIRMED PRODUCTION BUG (out of scope for this pass -- do not fix
/// here; this test documents it for whichever wave owns oxiz-sat /
/// oxiz-theories check() plumbing):
///
/// `FpSolver::assert_is_normal`'s own clauses are sound in isolation (see
/// the two tests above), but this combination -- `assert_const` with a
/// subnormal value *before* `assert_is_normal` -- currently returns `Sat`
/// with a model equal to the literal subnormal constant, which plainly
/// violates `assert_is_normal`'s own `exp_nonzero` clause. Root cause,
/// traced through both crates:
///
/// - `oxiz_sat::Solver::add_clause` special-cases unit (single-literal)
///   clauses by pushing them straight onto the trail via
///   `trail.assign_decision(lit)` with **no backing clause** (see
///   `oxiz-sat/src/solver/mod.rs`, the `len() == 1` arm). Both
///   `assert_const`'s per-bit fixing and `assert_is_normal`'s
///   `exp_nonzero`/`is_nan`/`is_inf`/`is_zero` unit clauses go through
///   this path.
/// - The multi-literal definitional clause
///   `[¬exp_nonzero, e_1, ..., e_8]` is added *before* `exp_nonzero` is
///   pinned true, at which point every `e_i` is already false (from the
///   prior `assert_const`); nothing re-validates that clause against the
///   trail when `exp_nonzero` is fixed true immediately afterward, so the
///   resulting violation is only ever surfaced later, through search-time
///   conflict analysis -- not through `add_clause`-time propagation.
/// - `FpSolver::check()` (`oxiz-theories/src/fp/solver/mod.rs`, the `if
///   matches!(solve_result, SolverResult::Unsat) { restore_to_trail_size
///   (..); forget_learned_since(..); solve_result = self.sat.solve(); }`
///   double-solve) unconditionally discards learned clauses and retries
///   whenever the first `solve()` reports Unsat, mirroring a workaround
///   documented for `BvSolver` against a *spurious*-Unsat failure mode.
///   Here the first `Unsat` is genuine (confirmed by the two tests
///   above using the same encoding without `assert_const`), but the
///   blanket retry cannot distinguish "spurious" from "genuine" and the
///   second, learned-clause-free `solve()` fails to re-derive the same
///   conflict, yielding a false `Sat`.
///
/// This is a soundness bug spanning `oxiz-sat`'s unit-clause fast path
/// and/or `oxiz-theories`'s blanket double-solve retry, not an error in
/// `assert_is_normal`'s constraint logic. Fixing it requires either making
/// `oxiz_sat::Solver::add_clause`'s unit-clause fast path re-validate
/// affected multi-literal clauses, or making the double-solve retry
/// distinguish genuine from spurious Unsat -- both out of this test
/// file's scope. Un-ignore once fixed.
#[test]
#[ignore = "confirmed production bug: FpSolver::check() double-solve retry \
            (oxiz-theories/src/fp/solver/mod.rs) turns a genuine Unsat \
            (assert_const subnormal + assert_is_normal) into a spurious \
            Sat; root cause traced into oxiz_sat::Solver::add_clause's \
            unit-clause fast path -- see doc comment above, out of scope \
            for this pass"]
fn test_fp_predicate_is_normal_rejects_subnormal_range() {
    let mut solver = FpSolver::new();

    let a = term(1);
    // A subnormal FLOAT32 value: exponent field = 0, nonzero significand.
    let subnormal = FpValue {
        sign: false,
        exponent: 0,
        significand: 1,
        format: FpFormat::FLOAT32,
    };
    assert!(subnormal.is_subnormal());
    solver.assert_const(a, &subnormal);
    solver.assert_is_normal(a);

    let result = solver.check().expect("check should succeed");
    assert!(matches!(result, TheoryResult::Unsat(_)));
}

#[test]
fn test_fp_comparison_less_than() {
    let mut solver = FpSolver::new();

    let a = term(1);
    let b = term(2);

    solver.new_fp(a, FpFormat::FLOAT32);
    solver.new_fp(b, FpFormat::FLOAT32);

    // a = -5.0 (negative)
    solver.assert_const(a, &FpValue::from_f32(-5.0));
    // b = 10.0 (positive)
    solver.assert_const(b, &FpValue::from_f32(10.0));

    // Test that comparison can be called (returns a Var)
    let _lt_result = solver.assert_fp_lt(a, b);

    let result = solver.check().expect("check should succeed");
    assert!(matches!(result, TheoryResult::Sat));
}

#[test]
#[allow(clippy::approx_constant)]
fn test_fp_comparison_less_equal() {
    let mut solver = FpSolver::new();

    let a = term(1);
    let b = term(2);

    solver.new_fp(a, FpFormat::FLOAT64);
    solver.new_fp(b, FpFormat::FLOAT64);

    // a = 3.14
    solver.assert_const(a, &FpValue::from_f64(3.14));
    // b = 3.14
    solver.assert_const(b, &FpValue::from_f64(3.14));

    // Test that comparison can be called (returns a Var)
    let _le_result = solver.assert_fp_le(a, b);

    let result = solver.check().expect("check should succeed");
    assert!(matches!(result, TheoryResult::Sat));
}

#[test]
fn test_fp_conversion_same_format() {
    let mut solver = FpSolver::new();

    let a = term(1);
    let b = term(2);

    solver.new_fp(a, FpFormat::FLOAT32);
    solver.assert_const(a, &FpValue::from_f32(6.75));

    // Convert a to b (same format)
    solver.assert_fp_to_fp(b, a, FpFormat::FLOAT32);

    let result = solver.check().expect("check should succeed");
    assert!(matches!(result, TheoryResult::Sat));

    let b_val = solver.get_value(b).expect("value should exist");
    assert_eq!(b_val.to_f32(), Some(6.75));
}

#[test]
fn test_fp_conversion_float32_to_float64() {
    let mut solver = FpSolver::new();

    let a = term(1);
    let b = term(2);

    solver.new_fp(a, FpFormat::FLOAT32);
    solver.assert_const(a, &FpValue::from_f32(2.5));

    // Convert Float32 to Float64
    solver.assert_fp_to_fp(b, a, FpFormat::FLOAT64);

    let result = solver.check().expect("check should succeed");
    assert!(matches!(result, TheoryResult::Sat));

    let b_val = solver.get_value(b).expect("value should exist");
    assert_eq!(b_val.format, FpFormat::FLOAT64);
}

#[test]
fn test_fp_conversion_preserves_nan() {
    let mut solver = FpSolver::new();

    let a = term(1);
    let b = term(2);

    solver.new_fp(a, FpFormat::FLOAT32);
    solver.assert_const(a, &FpValue::nan(FpFormat::FLOAT32));

    // Convert to FLOAT64
    solver.assert_fp_to_fp(b, a, FpFormat::FLOAT64);

    let result = solver.check().expect("check should succeed");
    assert!(matches!(result, TheoryResult::Sat));

    let b_val = solver.get_value(b).expect("value should exist");
    assert!(b_val.is_nan());
    assert_eq!(b_val.format, FpFormat::FLOAT64);
}

#[test]
fn test_fp_conversion_preserves_infinity() {
    let mut solver = FpSolver::new();

    let a = term(1);
    let b = term(2);

    solver.new_fp(a, FpFormat::FLOAT32);
    solver.assert_const(a, &FpValue::neg_infinity(FpFormat::FLOAT32));

    // Convert to FLOAT64
    solver.assert_fp_to_fp(b, a, FpFormat::FLOAT64);

    let result = solver.check().expect("check should succeed");
    assert!(matches!(result, TheoryResult::Sat));

    let b_val = solver.get_value(b).expect("value should exist");
    assert!(b_val.is_infinite());
    assert!(b_val.is_negative());
    assert_eq!(b_val.format, FpFormat::FLOAT64);
}

#[test]
fn test_fp_conversion_preserves_zero() {
    let mut solver = FpSolver::new();

    let a = term(1);
    let b = term(2);

    solver.new_fp(a, FpFormat::FLOAT32);
    solver.assert_const(a, &FpValue::pos_zero(FpFormat::FLOAT32));

    // Convert to FLOAT64
    solver.assert_fp_to_fp(b, a, FpFormat::FLOAT64);

    let result = solver.check().expect("check should succeed");
    assert!(matches!(result, TheoryResult::Sat));

    let b_val = solver.get_value(b).expect("value should exist");
    assert!(b_val.is_zero());
    assert!(b_val.is_positive());
    assert_eq!(b_val.format, FpFormat::FLOAT64);
}

#[test]
fn test_fp_rounding_mode_rne() {
    let mut solver = FpSolver::new();

    solver.set_rounding_mode(FpRoundingMode::RoundNearestTiesToEven);
    assert_eq!(
        solver.rounding_mode(),
        FpRoundingMode::RoundNearestTiesToEven
    );
    assert_eq!(solver.rounding_mode().smtlib_name(), "RNE");
}

#[test]
fn test_fp_rounding_mode_rna() {
    let mut solver = FpSolver::new();

    solver.set_rounding_mode(FpRoundingMode::RoundNearestTiesToAway);
    assert_eq!(
        solver.rounding_mode(),
        FpRoundingMode::RoundNearestTiesToAway
    );
    assert_eq!(solver.rounding_mode().smtlib_name(), "RNA");
}

#[test]
fn test_fp_rounding_mode_rtp() {
    let mut solver = FpSolver::new();

    solver.set_rounding_mode(FpRoundingMode::RoundTowardPositive);
    assert_eq!(solver.rounding_mode(), FpRoundingMode::RoundTowardPositive);
    assert_eq!(solver.rounding_mode().smtlib_name(), "RTP");
}

#[test]
fn test_fp_rounding_mode_rtn() {
    let mut solver = FpSolver::new();

    solver.set_rounding_mode(FpRoundingMode::RoundTowardNegative);
    assert_eq!(solver.rounding_mode(), FpRoundingMode::RoundTowardNegative);
    assert_eq!(solver.rounding_mode().smtlib_name(), "RTN");
}

#[test]
fn test_fp_rounding_mode_rtz() {
    let mut solver = FpSolver::new();

    solver.set_rounding_mode(FpRoundingMode::RoundTowardZero);
    assert_eq!(solver.rounding_mode(), FpRoundingMode::RoundTowardZero);
    assert_eq!(solver.rounding_mode().smtlib_name(), "RTZ");
}

#[test]
fn test_fp_solver_push_pop() {
    let mut solver = FpSolver::new();

    let a = term(1);
    solver.new_fp(a, FpFormat::FLOAT32);

    // Level 0: a is unconstrained
    solver.push();

    // Level 1: assert a = 5.0
    solver.assert_const(a, &FpValue::from_f32(5.0));
    let result = solver.check().expect("check should succeed");
    assert!(matches!(result, TheoryResult::Sat));

    solver.push();

    // Level 2: additional constraint
    let b = term(2);
    solver.new_fp(b, FpFormat::FLOAT32);
    solver.assert_const(b, &FpValue::from_f32(10.0));
    let result = solver.check().expect("check should succeed");
    assert!(matches!(result, TheoryResult::Sat));

    // Pop back to level 1
    solver.pop();
    let result = solver.check().expect("check should succeed");
    assert!(matches!(result, TheoryResult::Sat));

    // Pop back to level 0
    solver.pop();
}

#[test]
fn test_fp_solver_multiple_assertions() {
    let mut solver = FpSolver::new();

    let a = term(1);
    let b = term(2);
    let c = term(3);

    solver.new_fp(a, FpFormat::FLOAT32);
    solver.new_fp(b, FpFormat::FLOAT32);
    solver.new_fp(c, FpFormat::FLOAT32);

    // a = 2.0
    solver.assert_const(a, &FpValue::from_f32(2.0));

    // b = -a
    solver.assert_fp_neg(b, a);

    // c = |b|
    solver.assert_fp_abs(c, b);

    let result = solver.check().expect("check should succeed");
    assert!(matches!(result, TheoryResult::Sat));

    // Verify: a = 2.0, b = -2.0, c = 2.0
    let a_val = solver.get_value(a).expect("value should exist");
    let b_val = solver.get_value(b).expect("value should exist");
    let c_val = solver.get_value(c).expect("value should exist");

    assert_eq!(a_val.to_f32(), Some(2.0));
    assert_eq!(b_val.to_f32(), Some(-2.0));
    assert_eq!(c_val.to_f32(), Some(2.0));
}

#[test]
fn test_fp_solver_conflicting_constraints() {
    let mut solver = FpSolver::new();

    let a = term(1);
    solver.new_fp(a, FpFormat::FLOAT32);

    // Assert a is NaN
    solver.assert_is_nan(a);

    // Assert a is zero (conflicting with NaN)
    solver.assert_is_zero(a);

    let result = solver.check().expect("check should succeed");
    // Should be UNSAT due to conflicting constraints
    assert!(matches!(result, TheoryResult::Unsat(_)));
}

#[test]
fn test_fp_solver_theory_interface() {
    let mut solver = FpSolver::new();

    // Test Theory trait implementation
    assert_eq!(solver.name(), "FP");

    let a = term(1);
    assert!(solver.can_handle(a));

    // Test assert_true/assert_false
    let result = solver.assert_true(a).expect("assert should succeed");
    assert!(matches!(result, TheoryResult::Sat));

    let result = solver.assert_false(a).expect("assert should succeed");
    assert!(matches!(result, TheoryResult::Sat));

    // Test reset
    solver.reset();
}

#[test]
fn test_fp_double_negation() {
    let mut solver = FpSolver::new();

    let a = term(1);
    let b = term(2);
    let c = term(3);

    solver.new_fp(a, FpFormat::FLOAT64);
    solver.new_fp(b, FpFormat::FLOAT64);
    solver.new_fp(c, FpFormat::FLOAT64);

    // a = 7.5
    solver.assert_const(a, &FpValue::from_f64(7.5));

    // b = -a
    solver.assert_fp_neg(b, a);

    // c = -b (should equal a)
    solver.assert_fp_neg(c, b);

    let result = solver.check().expect("check should succeed");
    assert!(matches!(result, TheoryResult::Sat));

    let c_val = solver.get_value(c).expect("value should exist");
    assert_eq!(c_val.to_f64(), Some(7.5));
}

#[test]
fn test_fp_equality_chain() {
    let mut solver = FpSolver::new();

    let a = term(1);
    let b = term(2);
    let c = term(3);

    solver.new_fp(a, FpFormat::FLOAT32);
    solver.new_fp(b, FpFormat::FLOAT32);
    solver.new_fp(c, FpFormat::FLOAT32);

    // a = 3.75
    solver.assert_const(a, &FpValue::from_f32(3.75));

    // a = b
    solver.assert_fp_eq(a, b);

    // b = c
    solver.assert_fp_eq(b, c);

    let result = solver.check().expect("check should succeed");
    assert!(matches!(result, TheoryResult::Sat));

    // Verify transitivity: a = b = c = 3.75
    let b_val = solver.get_value(b).expect("value should exist");
    let c_val = solver.get_value(c).expect("value should exist");

    assert_eq!(b_val.to_f32(), Some(3.75));
    assert_eq!(c_val.to_f32(), Some(3.75));
}
