//! Regression tests for the concrete floating-point model finder.
//!
//! These pin the `QF_FP` benchmarks that previously answered `Unknown` because
//! the CDCL(T) core has no complete FP theory: every FP atom fell through to the
//! honesty gate. `Solver::try_fp_model_sat` now constructs and *verifies* a
//! concrete IEEE-754 model for the concrete-evaluation fragment, so these
//! satisfiable formulas are reported `Sat` — while the soundness tests at the
//! bottom confirm that unsatisfiable concrete formulas are never reported `Sat`.
//!
//! The shapes below mirror `bench/z3_parity/benchmarks/qf_fp/fp_0*.smt2`.

use num_rational::Rational64;
use oxiz_core::ast::{RoundingMode, TermManager};
use oxiz_solver::{Solver, SolverResult};

const F32_EB: u32 = 8;
const F32_SB: u32 = 24;
const F64_EB: u32 = 11;
const F64_SB: u32 = 53;

/// Build a `Real` constant term from an exact rational `num/den`.
fn real(m: &mut TermManager, num: i64, den: i64) -> oxiz_core::ast::TermId {
    m.mk_real(Rational64::new(num, den))
}

/// fp_01: RNE addition plus RTZ multiplication of Float32 constants, checked
/// against loose bounds. Satisfiable.
#[test]
fn rne_add_and_rtz_mul_float32_is_sat() {
    let mut solver = Solver::new();
    let mut m = TermManager::new();
    let f32 = m.sorts.float_sort(F32_EB, F32_SB);

    let x = m.mk_var("x", f32);
    let y = m.mk_var("y", f32);
    let z = m.mk_var("z", f32);
    let w = m.mk_var("w", f32);

    // x = 1.5, y = 2.3
    let c15 = real(&mut m, 3, 2);
    let c15_fp = m.mk_real_to_fp(RoundingMode::RNE, c15, F32_EB, F32_SB);
    let e = m.mk_eq(x, c15_fp);
    solver.assert(e, &mut m);
    let c23 = real(&mut m, 23, 10);
    let c23_fp = m.mk_real_to_fp(RoundingMode::RNE, c23, F32_EB, F32_SB);
    let e = m.mk_eq(y, c23_fp);
    solver.assert(e, &mut m);

    // z = x + y (RNE), 3.7 < z < 3.9
    let add = m.mk_fp_add(RoundingMode::RNE, x, y);
    let e = m.mk_eq(z, add);
    solver.assert(e, &mut m);
    let c37 = real(&mut m, 37, 10);
    let c37_fp = m.mk_real_to_fp(RoundingMode::RNE, c37, F32_EB, F32_SB);
    let gt = m.mk_fp_gt(z, c37_fp);
    solver.assert(gt, &mut m);
    let c39 = real(&mut m, 39, 10);
    let c39_fp = m.mk_real_to_fp(RoundingMode::RNE, c39, F32_EB, F32_SB);
    let lt = m.mk_fp_lt(z, c39_fp);
    solver.assert(lt, &mut m);

    // w = x * y (RTZ), w > +0
    let mul = m.mk_fp_mul(RoundingMode::RTZ, x, y);
    let e = m.mk_eq(w, mul);
    solver.assert(e, &mut m);
    let zero = real(&mut m, 0, 1);
    let zero_fp = m.mk_real_to_fp(RoundingMode::RTZ, zero, F32_EB, F32_SB);
    let gt = m.mk_fp_gt(w, zero_fp);
    solver.assert(gt, &mut m);

    assert_eq!(solver.check(&mut m), SolverResult::Sat);
}

/// fp_02: directed-rounding division. `RTP` and `RTN` of `10/3` bracket the
/// exact quotient, so the ordering and bound constraints are satisfiable. This
/// exercises the `div128` remainder fix.
#[test]
fn div_rtp_rtn_float64_is_sat() {
    let mut solver = Solver::new();
    let mut m = TermManager::new();
    let f64s = m.sorts.float_sort(F64_EB, F64_SB);

    let a = m.mk_var("a", f64s);
    let b = m.mk_var("b", f64s);
    let c_rtp = m.mk_var("c_rtp", f64s);
    let c_rtn = m.mk_var("c_rtn", f64s);

    let c10 = real(&mut m, 10, 1);
    let c10_fp = m.mk_real_to_fp(RoundingMode::RNE, c10, F64_EB, F64_SB);
    let e = m.mk_eq(a, c10_fp);
    solver.assert(e, &mut m);
    let c3 = real(&mut m, 3, 1);
    let c3_fp = m.mk_real_to_fp(RoundingMode::RNE, c3, F64_EB, F64_SB);
    let e = m.mk_eq(b, c3_fp);
    solver.assert(e, &mut m);

    let div_p = m.mk_fp_div(RoundingMode::RTP, a, b);
    let e = m.mk_eq(c_rtp, div_p);
    solver.assert(e, &mut m);
    let div_n = m.mk_fp_div(RoundingMode::RTN, a, b);
    let e = m.mk_eq(c_rtn, div_n);
    solver.assert(e, &mut m);

    let geq = m.mk_fp_geq(c_rtp, c_rtn);
    solver.assert(geq, &mut m);

    let c333 = real(&mut m, 3333, 1000);
    let c333_fp = m.mk_real_to_fp(RoundingMode::RNE, c333, F64_EB, F64_SB);
    let gt = m.mk_fp_gt(c_rtp, c333_fp);
    solver.assert(gt, &mut m);
    let c334 = real(&mut m, 3334, 1000);
    let c334_fp = m.mk_real_to_fp(RoundingMode::RNE, c334, F64_EB, F64_SB);
    let lt = m.mk_fp_lt(c_rtn, c334_fp);
    solver.assert(lt, &mut m);

    assert_eq!(solver.check(&mut m), SolverResult::Sat);
}

/// fp_04: a free variable constrained only by `fp.isNaN` gets a NaN witness,
/// and NaN propagates through `fp.add`. Satisfiable.
#[test]
fn nan_witness_and_propagation_is_sat() {
    let mut solver = Solver::new();
    let mut m = TermManager::new();
    let f32 = m.sorts.float_sort(F32_EB, F32_SB);

    let x = m.mk_var("x", f32);
    let y = m.mk_var("y", f32);
    let z = m.mk_var("z", f32);

    let is_nan_x = m.mk_fp_is_nan(x);
    solver.assert(is_nan_x, &mut m);

    let c5 = real(&mut m, 5, 1);
    let c5_fp = m.mk_real_to_fp(RoundingMode::RNE, c5, F32_EB, F32_SB);
    let e = m.mk_eq(y, c5_fp);
    solver.assert(e, &mut m);
    let not_nan_y = m.mk_fp_is_nan(y);
    let not_nan_y = m.mk_not(not_nan_y);
    solver.assert(not_nan_y, &mut m);

    let add = m.mk_fp_add(RoundingMode::RNE, x, y);
    let e = m.mk_eq(z, add);
    solver.assert(e, &mut m);
    let is_nan_z = m.mk_fp_is_nan(z);
    solver.assert(is_nan_z, &mut m);

    let is_pos_y = m.mk_fp_is_positive(y);
    solver.assert(is_pos_y, &mut m);

    assert_eq!(solver.check(&mut m), SolverResult::Sat);
}

/// fp_05: free variables constrained by `fp.isInfinite`/`fp.isPositive` get the
/// `+oo` witness, which absorbs finite addition/multiplication. Satisfiable.
#[test]
fn infinity_witness_and_arithmetic_is_sat() {
    let mut solver = Solver::new();
    let mut m = TermManager::new();
    let f64s = m.sorts.float_sort(F64_EB, F64_SB);

    let inf_pos = m.mk_var("inf_pos", f64s);
    let x = m.mk_var("x", f64s);
    let y = m.mk_var("y", f64s);

    let is_inf = m.mk_fp_is_infinite(inf_pos);
    solver.assert(is_inf, &mut m);
    let is_pos = m.mk_fp_is_positive(inf_pos);
    solver.assert(is_pos, &mut m);

    let c42 = real(&mut m, 42, 1);
    let c42_fp = m.mk_real_to_fp(RoundingMode::RNE, c42, F64_EB, F64_SB);
    let e = m.mk_eq(x, c42_fp);
    solver.assert(e, &mut m);

    let add = m.mk_fp_add(RoundingMode::RNE, inf_pos, x);
    let e = m.mk_eq(y, add);
    solver.assert(e, &mut m);
    let y_inf = m.mk_fp_is_infinite(y);
    solver.assert(y_inf, &mut m);
    let y_pos = m.mk_fp_is_positive(y);
    solver.assert(y_pos, &mut m);

    let gt = m.mk_fp_gt(inf_pos, x);
    solver.assert(gt, &mut m);

    assert_eq!(solver.check(&mut m), SolverResult::Sat);
}

/// fp_07: widening a Float32 datum to Float64 preserves sign and value, so the
/// ordering and bound constraints on the widened term hold. Satisfiable.
#[test]
fn float32_to_float64_widening_is_sat() {
    let mut solver = Solver::new();
    let mut m = TermManager::new();
    let f32 = m.sorts.float_sort(F32_EB, F32_SB);
    let f64s = m.sorts.float_sort(F64_EB, F64_SB);

    let x32 = m.mk_var("x32", f32);
    let x64 = m.mk_var("x64", f64s);

    let c = real(&mut m, 314159, 100000);
    let c_fp = m.mk_real_to_fp(RoundingMode::RNE, c, F32_EB, F32_SB);
    let e = m.mk_eq(x32, c_fp);
    solver.assert(e, &mut m);

    let widen = m.mk_fp_to_fp(RoundingMode::RNE, x32, F64_EB, F64_SB);
    let e = m.mk_eq(x64, widen);
    solver.assert(e, &mut m);

    let is_pos = m.mk_fp_is_positive(x64);
    solver.assert(is_pos, &mut m);

    let lo = real(&mut m, 314, 100);
    let lo_fp = m.mk_real_to_fp(RoundingMode::RNE, lo, F64_EB, F64_SB);
    let gt = m.mk_fp_gt(x64, lo_fp);
    solver.assert(gt, &mut m);
    let hi = real(&mut m, 315, 100);
    let hi_fp = m.mk_real_to_fp(RoundingMode::RNE, hi, F64_EB, F64_SB);
    let lt = m.mk_fp_lt(x64, hi_fp);
    solver.assert(lt, &mut m);

    assert_eq!(solver.check(&mut m), SolverResult::Sat);
}

/// fp_09: exact integer arithmetic over Float64 — `5 + 7 = 12` and `5 * 3 = 15`
/// with round-to-nearest — is satisfiable and equals the expected constants.
#[test]
fn exact_integer_add_mul_float64_is_sat() {
    let mut solver = Solver::new();
    let mut m = TermManager::new();
    let f64s = m.sorts.float_sort(F64_EB, F64_SB);

    let a = m.mk_var("a", f64s);
    let b = m.mk_var("b", f64s);
    let c = m.mk_var("c", f64s);
    let sum = m.mk_var("sum", f64s);
    let product = m.mk_var("product", f64s);

    for (var, val) in [(a, 5i64), (b, 7), (c, 3)] {
        let k = real(&mut m, val, 1);
        let k_fp = m.mk_real_to_fp(RoundingMode::RNE, k, F64_EB, F64_SB);
        let e = m.mk_eq(var, k_fp);
        solver.assert(e, &mut m);
    }

    let add = m.mk_fp_add(RoundingMode::RNE, a, b);
    let e = m.mk_eq(sum, add);
    solver.assert(e, &mut m);
    let mul = m.mk_fp_mul(RoundingMode::RNE, a, c);
    let e = m.mk_eq(product, mul);
    solver.assert(e, &mut m);

    let c12 = real(&mut m, 12, 1);
    let c12_fp = m.mk_real_to_fp(RoundingMode::RNE, c12, F64_EB, F64_SB);
    let e = m.mk_eq(sum, c12_fp);
    solver.assert(e, &mut m);
    let c15 = real(&mut m, 15, 1);
    let c15_fp = m.mk_real_to_fp(RoundingMode::RNE, c15, F64_EB, F64_SB);
    let e = m.mk_eq(product, c15_fp);
    solver.assert(e, &mut m);

    assert_eq!(solver.check(&mut m), SolverResult::Sat);
}

// ──────────────────────────────────────────────────────────────────
// Soundness: the model finder must never report `Sat` for a concrete
// formula that is actually unsatisfiable. The honest fallback is `Unknown`
// (never a wrong `Sat`, and never a wrong `Unsat`).
// ──────────────────────────────────────────────────────────────────

/// `10 / 3` is not equal to `3`, so `(fp.eq (fp.div RNE 10 3) 3)` is
/// unsatisfiable. The constructed model fails verification, so the solver must
/// not answer `Sat`.
#[test]
fn div_result_not_equal_wrong_constant_is_not_sat() {
    let mut solver = Solver::new();
    let mut m = TermManager::new();
    let f64s = m.sorts.float_sort(F64_EB, F64_SB);

    let a = m.mk_var("a", f64s);
    let b = m.mk_var("b", f64s);
    let q = m.mk_var("q", f64s);

    let c10 = real(&mut m, 10, 1);
    let c10_fp = m.mk_real_to_fp(RoundingMode::RNE, c10, F64_EB, F64_SB);
    let e = m.mk_eq(a, c10_fp);
    solver.assert(e, &mut m);
    let c3 = real(&mut m, 3, 1);
    let c3_fp = m.mk_real_to_fp(RoundingMode::RNE, c3, F64_EB, F64_SB);
    let e = m.mk_eq(b, c3_fp);
    solver.assert(e, &mut m);

    let div = m.mk_fp_div(RoundingMode::RNE, a, b);
    let e = m.mk_eq(q, div);
    solver.assert(e, &mut m);

    // q == 3.0 is false (q ≈ 3.3333…).
    let three = real(&mut m, 3, 1);
    let three_fp = m.mk_real_to_fp(RoundingMode::RNE, three, F64_EB, F64_SB);
    let bad = m.mk_fp_eq(q, three_fp);
    solver.assert(bad, &mut m);

    assert_ne!(
        solver.check(&mut m),
        SolverResult::Sat,
        "10/3 == 3 must not be reported satisfiable"
    );
}

/// A concrete non-NaN value asserted `fp.isNaN` is unsatisfiable; the finder
/// must decline `Sat`.
#[test]
fn concrete_value_asserted_nan_is_not_sat() {
    let mut solver = Solver::new();
    let mut m = TermManager::new();
    let f32 = m.sorts.float_sort(F32_EB, F32_SB);

    let x = m.mk_var("x", f32);
    let c = real(&mut m, 3, 2); // 1.5
    let c_fp = m.mk_real_to_fp(RoundingMode::RNE, c, F32_EB, F32_SB);
    let e = m.mk_eq(x, c_fp);
    solver.assert(e, &mut m);

    let is_nan = m.mk_fp_is_nan(x);
    solver.assert(is_nan, &mut m);

    assert_ne!(
        solver.check(&mut m),
        SolverResult::Sat,
        "isNaN(1.5) must not be reported satisfiable"
    );
}

/// Two contradictory strict bounds on the same term (`z > 3.9` and `z < 3.7`)
/// are unsatisfiable; the finder must decline `Sat`.
#[test]
fn contradictory_bounds_is_not_sat() {
    let mut solver = Solver::new();
    let mut m = TermManager::new();
    let f32 = m.sorts.float_sort(F32_EB, F32_SB);

    let x = m.mk_var("x", f32);
    let y = m.mk_var("y", f32);
    let z = m.mk_var("z", f32);

    let c15 = real(&mut m, 3, 2);
    let c15_fp = m.mk_real_to_fp(RoundingMode::RNE, c15, F32_EB, F32_SB);
    let e = m.mk_eq(x, c15_fp);
    solver.assert(e, &mut m);
    let c23 = real(&mut m, 23, 10);
    let c23_fp = m.mk_real_to_fp(RoundingMode::RNE, c23, F32_EB, F32_SB);
    let e = m.mk_eq(y, c23_fp);
    solver.assert(e, &mut m);
    let add = m.mk_fp_add(RoundingMode::RNE, x, y);
    let e = m.mk_eq(z, add);
    solver.assert(e, &mut m);

    let hi = real(&mut m, 39, 10);
    let hi_fp = m.mk_real_to_fp(RoundingMode::RNE, hi, F32_EB, F32_SB);
    let gt = m.mk_fp_gt(z, hi_fp); // z > 3.9  (false, z ≈ 3.8)
    solver.assert(gt, &mut m);

    assert_ne!(solver.check(&mut m), SolverResult::Sat);
}
