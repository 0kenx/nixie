//! Regression tests for the `p2:opt-arith` audit wave
//! (`oxiz-solver/src/optimization.rs`).
//!
//! Each test pins down one confirmed gap in `Optimizer::optimize`:
//!
//!   1. (opt-5) An integer maximize under a *strict* upper bound must find
//!      the correct integer optimum (`x < 10` maximizes to `9`, not `10`).
//!      This is the class of bound the historical arithmetic-incompleteness
//!      bug broke, and it had no direct regression test.
//!   2. (opt-6) An UNSAT problem whose refutation genuinely requires
//!      arithmetic (LIA) theory reasoning -- not just propositional
//!      reasoning over a shared atom -- must be reported `Unsat`. The only
//!      prior UNSAT test (`x = y AND x != y`) is a pure propositional
//!      contradiction that needs no theory combination at all.
//!   3. (opt-3) A finite integer/real optimum whose magnitude is at or
//!      beyond the old fixed `2^40` unbounded-probe cap must still be found
//!      exactly, not misreported `Unbounded`.

use num_bigint::BigInt;
use oxiz_core::ast::{TermKind, TermManager};
use oxiz_solver::{OptimizationResult, Optimizer};

/// Extract a concrete `BigInt` from an `Optimal` integer result, panicking
/// with a descriptive message on any other outcome.
fn expect_int_optimal(result: OptimizationResult, tm: &TermManager) -> BigInt {
    match result {
        OptimizationResult::Optimal { value, .. } => match tm.get(value).map(|t| t.kind.clone()) {
            Some(TermKind::IntConst(n)) => n,
            other => panic!("expected an integer optimum, got term kind {other:?}"),
        },
        other => panic!("expected Optimal, got {other:?}"),
    }
}

// ─────────────────────────────────────────────────────────────────────────
// opt-5 — integer maximize under a strict upper bound
// ─────────────────────────────────────────────────────────────────────────

/// `x < 10` (strict), maximize `x` -> the integer optimum is `9`, not `10`.
/// The only pre-existing maximize regression used a non-strict `x <= 10`
/// bound (optimum `10`), which cannot distinguish a solver that mishandles
/// strict integer bounds from one that handles them correctly.
#[test]
fn test_integer_maximize_strict_upper_bound_gives_nine() {
    let mut opt = Optimizer::new();
    let mut tm = TermManager::new();
    opt.set_logic("QF_LIA");

    let x = tm.mk_var("x", tm.sorts.int_sort);
    let zero = tm.mk_int(BigInt::from(0));
    let ten = tm.mk_int(BigInt::from(10));

    opt.assert(tm.mk_ge(x, zero));
    opt.assert(tm.mk_lt(x, ten)); // strict: x < 10

    opt.maximize(x);

    let result = opt.optimize(&mut tm);
    let value = expect_int_optimal(result, &tm);
    assert_eq!(
        value,
        BigInt::from(9),
        "x < 10 should maximize to 9, not 10"
    );
}

/// Symmetric case: `x > 0` (strict), minimize `x` -> the integer optimum is
/// `1`, not `0`.
#[test]
fn test_integer_minimize_strict_lower_bound_gives_one() {
    let mut opt = Optimizer::new();
    let mut tm = TermManager::new();
    opt.set_logic("QF_LIA");

    let x = tm.mk_var("x", tm.sorts.int_sort);
    let zero = tm.mk_int(BigInt::from(0));
    let ten = tm.mk_int(BigInt::from(10));

    opt.assert(tm.mk_gt(x, zero)); // strict: x > 0
    opt.assert(tm.mk_le(x, ten));

    opt.minimize(x);

    let result = opt.optimize(&mut tm);
    let value = expect_int_optimal(result, &tm);
    assert_eq!(value, BigInt::from(1), "x > 0 should minimize to 1, not 0");
}

// ─────────────────────────────────────────────────────────────────────────
// opt-6 — UNSAT that genuinely requires arithmetic (LIA) theory reasoning
// ─────────────────────────────────────────────────────────────────────────

/// `x >= 5 AND x <= 3` is UNSAT purely by LIA bound reasoning: there is no
/// shared propositional atom to refute (unlike `x = y AND x != y`), so this
/// exercises the arithmetic theory solver's own conflict detection.
#[test]
fn test_arithmetic_bound_contradiction_is_unsat() {
    let mut opt = Optimizer::new();
    let mut tm = TermManager::new();
    opt.set_logic("QF_LIA");

    let x = tm.mk_var("x", tm.sorts.int_sort);
    let five = tm.mk_int(BigInt::from(5));
    let three = tm.mk_int(BigInt::from(3));

    opt.assert(tm.mk_ge(x, five));
    opt.assert(tm.mk_le(x, three));

    opt.minimize(x);

    match opt.optimize(&mut tm) {
        OptimizationResult::Unsat => {}
        other => panic!("expected Unsat for `x >= 5 AND x <= 3`, got {other:?}"),
    }
}

/// `x < y AND y < x` is UNSAT by LIA transitivity/antisymmetry reasoning
/// over two distinct variables -- again no shared atom for a purely
/// propositional refutation to key off.
#[test]
fn test_arithmetic_ordering_contradiction_is_unsat() {
    let mut opt = Optimizer::new();
    let mut tm = TermManager::new();
    opt.set_logic("QF_LIA");

    let x = tm.mk_var("x", tm.sorts.int_sort);
    let y = tm.mk_var("y", tm.sorts.int_sort);

    opt.assert(tm.mk_lt(x, y));
    opt.assert(tm.mk_lt(y, x));

    opt.minimize(x);

    match opt.optimize(&mut tm) {
        OptimizationResult::Unsat => {}
        other => panic!("expected Unsat for `x < y AND y < x`, got {other:?}"),
    }
}

// ─────────────────────────────────────────────────────────────────────────
// opt-3 — a large-magnitude *finite* optimum must not be misreported
// Unbounded
// ─────────────────────────────────────────────────────────────────────────

/// `x` pinned to a narrow window around `2^45` (well beyond the old fixed
/// `2^40` single-probe cap): minimizing must find the exact finite optimum,
/// not report `Unbounded`.
#[test]
fn test_integer_minimize_large_magnitude_optimum_not_unbounded() {
    let mut opt = Optimizer::new();
    let mut tm = TermManager::new();
    opt.set_logic("QF_LIA");

    let x = tm.mk_var("x", tm.sorts.int_sort);
    let base = BigInt::from(1u64) << 45u32; // 2^45, >> the old 2^40 cap
    let lo = tm.mk_int(base.clone());
    let hi = tm.mk_int(&base + BigInt::from(100));

    opt.assert(tm.mk_ge(x, lo));
    opt.assert(tm.mk_le(x, hi));
    opt.minimize(x);

    let result = opt.optimize(&mut tm);
    let value = expect_int_optimal(result, &tm);
    assert_eq!(
        value, base,
        "finite optimum at 2^45 must be found exactly, not reported Unbounded"
    );
}

/// Mirror in the maximize direction, with the window entirely below `2^45`.
#[test]
fn test_integer_maximize_large_magnitude_optimum_not_unbounded() {
    let mut opt = Optimizer::new();
    let mut tm = TermManager::new();
    opt.set_logic("QF_LIA");

    let x = tm.mk_var("x", tm.sorts.int_sort);
    let base = BigInt::from(1u64) << 45u32;
    let lo = tm.mk_int(&base - BigInt::from(100));
    let hi = tm.mk_int(base.clone());

    opt.assert(tm.mk_ge(x, lo));
    opt.assert(tm.mk_le(x, hi));
    opt.maximize(x);

    let result = opt.optimize(&mut tm);
    let value = expect_int_optimal(result, &tm);
    assert_eq!(
        value, base,
        "finite optimum at 2^45 must be found exactly, not reported Unbounded"
    );
}

/// A genuinely unbounded integer objective must still be reported
/// `Unbounded` after the exponential-probe fix -- the fix widens what counts
/// as a *finite* optimum, it must not turn a truly unbounded problem into a
/// non-terminating or fabricated result.
#[test]
fn test_integer_still_reports_unbounded_when_genuinely_unbounded() {
    let mut opt = Optimizer::new();
    let mut tm = TermManager::new();
    opt.set_logic("QF_LIA");

    let x = tm.mk_var("x", tm.sorts.int_sort);
    // Only an upper bound: unbounded below (mirrors the internal
    // `test_unbounded_minimize_reports_unbounded` regression, which
    // establishes that a *fully* unconstrained variable can leave the
    // objective symbolic in the model rather than exercising the
    // exponential probe at all -- a one-sided bound is what actually drives
    // Phase 2's doubling loop out to the safety cap).
    let hundred = tm.mk_int(BigInt::from(100));
    opt.assert(tm.mk_le(x, hundred));
    opt.minimize(x);

    match opt.optimize(&mut tm) {
        OptimizationResult::Unbounded => {}
        other => panic!("expected Unbounded for a one-sided-bounded minimize, got {other:?}"),
    }
}

/// Same large-magnitude check for a real (rational) objective: the
/// exponential unbounded-probe fix in `optimize_real` must likewise find a
/// finite optimum beyond the old `2^40` cap instead of reporting
/// `Unbounded`.
#[test]
fn test_real_minimize_large_magnitude_optimum_not_unbounded() {
    let mut opt = Optimizer::new();
    let mut tm = TermManager::new();
    opt.set_logic("QF_LRA");

    let x = tm.mk_var("x", tm.sorts.real_sort);
    let base = 1i64 << 41; // 2^41, beyond the old 2^40 cap
    let lo = tm.mk_real(num_rational::Rational64::from_integer(base));
    let hi = tm.mk_real(num_rational::Rational64::from_integer(base + 100));

    opt.assert(tm.mk_ge(x, lo));
    opt.assert(tm.mk_le(x, hi));
    opt.minimize(x);

    match opt.optimize(&mut tm) {
        OptimizationResult::Optimal { value, .. } => match tm.get(value).map(|t| t.kind.clone()) {
            Some(TermKind::RealConst(v)) => {
                assert_eq!(
                    v,
                    num_rational::Rational64::from_integer(base),
                    "finite real optimum at 2^41 must be found exactly, not Unbounded"
                );
            }
            other => panic!("expected a real optimum, got term kind {other:?}"),
        },
        other => panic!("expected Optimal, got {other:?}"),
    }
}

// ─────────────────────────────────────────────────────────────────────────
// opt-4 — no-objective optimize() must not fabricate a numeric value
// ─────────────────────────────────────────────────────────────────────────

/// With no objectives registered, `optimize` degrades to a plain
/// satisfiability check. It must still report `Optimal` with a model on a
/// satisfiable problem (existing behavior, preserved for compatibility), but
/// the sentinel `value` must not be a numeric constant -- a numeric sentinel
/// (the previous `IntConst(0)`) is indistinguishable from a genuine
/// objective optimum of `0`.
#[test]
fn test_no_objectives_optimal_value_is_not_a_fabricated_number() {
    let mut opt = Optimizer::new();
    let mut tm = TermManager::new();
    opt.set_logic("QF_LIA");

    let x = tm.mk_var("x", tm.sorts.int_sort);
    let zero = tm.mk_int(BigInt::from(0));
    opt.assert(tm.mk_ge(x, zero));

    match opt.optimize(&mut tm) {
        OptimizationResult::Optimal { value, .. } => match tm.get(value).map(|t| t.kind.clone()) {
            Some(TermKind::IntConst(_)) | Some(TermKind::RealConst(_)) => {
                panic!("no-objective Optimal must not carry a fabricated numeric value")
            }
            _ => {}
        },
        other => panic!("expected Optimal for a satisfiable no-objective problem, got {other:?}"),
    }
}
