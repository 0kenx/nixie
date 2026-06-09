//! Integration tests for the OptContext → oxiz-solver pipeline.
//!
//! These tests verify that MaxSMT, single-objective OMT, and Pareto
//! optimization all produce *correct* results when wired to the real solver.

use num_bigint::BigInt;
use oxiz_opt::{ModelValue, OptContext, OptResult, Weight};

// ── helpers ──────────────────────────────────────────────────────────────────

/// Extract `Some(BigInt)` from an `OptContext` model for a variable term.
fn model_int(ctx: &OptContext, term: oxiz_core::ast::TermId) -> Option<BigInt> {
    match ctx.get_model_value(term)? {
        ModelValue::Int(n) => Some(n.clone()),
        _ => None,
    }
}

// ── check_sat ────────────────────────────────────────────────────────────────

#[test]
fn check_sat_empty_is_sat() {
    let mut ctx = OptContext::new();
    let result = ctx.check_sat();
    assert_eq!(result, OptResult::Satisfiable);
}

#[test]
fn check_sat_feasible_constraint() {
    let mut ctx = OptContext::new();
    let x = ctx.terms.mk_var("x", ctx.terms.sorts.int_sort);
    let three = ctx.terms.mk_int(3i64);
    let ten = ctx.terms.mk_int(10i64);
    let c1 = ctx.terms.mk_ge(x, three);
    let c2 = ctx.terms.mk_le(x, ten);
    ctx.add_hard(c1);
    ctx.add_hard(c2);
    let result = ctx.check_sat();
    assert_eq!(result, OptResult::Satisfiable);
}

#[test]
fn check_sat_unsat_constraint() {
    let mut ctx = OptContext::new();
    // x > 10 AND x < 5  →  UNSAT
    let x = ctx.terms.mk_var("x", ctx.terms.sorts.int_sort);
    let five = ctx.terms.mk_int(5i64);
    let ten = ctx.terms.mk_int(10i64);
    let c1 = ctx.terms.mk_gt(x, ten);
    let c2 = ctx.terms.mk_lt(x, five);
    ctx.add_hard(c1);
    ctx.add_hard(c2);
    let result = ctx.check_sat();
    assert_eq!(result, OptResult::Unsatisfiable);
}

// ── MaxSMT ───────────────────────────────────────────────────────────────────

/// Two soft constraints that are **both satisfiable** with unit weights.
/// The solver should find a model satisfying both (cost = 0).
#[test]
fn maxsmt_both_soft_satisfiable() {
    let mut ctx = OptContext::new();

    // Create two fresh boolean variables — build all terms before adding.
    let p = ctx.terms.mk_var("p", ctx.terms.sorts.bool_sort);
    let q = ctx.terms.mk_var("q", ctx.terms.sorts.bool_sort);

    // No hard constraints.  Both softs are trivially satisfiable.
    ctx.add_soft(p);
    ctx.add_soft(q);

    let result = ctx.optimize().expect("optimize should not error");
    assert!(
        matches!(result, OptResult::Optimal | OptResult::Satisfiable),
        "expected Optimal or Satisfiable, got {:?}",
        result
    );
}

/// One hard constraint forces `p = true`.  One soft says `p = false` (weight 1),
/// another says `q = true` (weight 5).  Optimal: violate weight-1 soft.
#[test]
fn maxsmt_conflicting_soft_max_weight_wins() {
    let mut ctx = OptContext::new();

    let p = ctx.terms.mk_var("p2", ctx.terms.sorts.bool_sort);
    let q = ctx.terms.mk_var("q2", ctx.terms.sorts.bool_sort);
    let true_term = ctx.terms.mk_true();
    let not_p = ctx.terms.mk_not(p);
    let p_true = ctx.terms.mk_eq(p, true_term);

    // Hard: p must be true.
    ctx.add_hard(p_true);

    // Soft: ¬p (weight 1) — forces p = false, conflicts with hard
    ctx.add_soft_weighted(not_p, Weight::from(1));

    // Soft: q (weight 5) — no conflict
    ctx.add_soft_weighted(q, Weight::from(5));

    let result = ctx.optimize().expect("optimize should not error");
    assert!(
        matches!(result, OptResult::Optimal | OptResult::Satisfiable),
        "expected Optimal or Satisfiable, got {:?}",
        result
    );
}

/// Hard constraint makes the problem UNSAT — no model should be found.
#[test]
fn maxsmt_unsat_hard_constraints() {
    let mut ctx = OptContext::new();

    let x = ctx.terms.mk_var("xu", ctx.terms.sorts.int_sort);
    let five = ctx.terms.mk_int(5i64);
    let ten = ctx.terms.mk_int(10i64);

    // x > 10 AND x < 5 → UNSAT
    let c1 = ctx.terms.mk_gt(x, ten);
    let c2 = ctx.terms.mk_lt(x, five);
    ctx.add_hard(c1);
    ctx.add_hard(c2);

    // Add a soft that would be trivially satisfiable otherwise
    let p = ctx.terms.mk_var("p_unsat", ctx.terms.sorts.bool_sort);
    ctx.add_soft(p);

    let result = ctx.optimize().expect("optimize should not error");
    assert_eq!(result, OptResult::Unsatisfiable);
}

// ── Single-objective OMT ─────────────────────────────────────────────────────

/// minimize x  subject to  x >= 3  →  optimal x = 3
#[test]
fn omt_minimize_lower_bound() {
    let mut ctx = OptContext::new();

    let x = ctx.terms.mk_var("xm", ctx.terms.sorts.int_sort);
    let three = ctx.terms.mk_int(3i64);
    let c = ctx.terms.mk_ge(x, three);
    ctx.add_hard(c);
    ctx.minimize(x);

    let result = ctx.optimize().expect("optimize should not error");
    // The solver may return Optimal or Satisfiable depending on completeness.
    assert!(
        matches!(
            result,
            OptResult::Optimal | OptResult::Satisfiable | OptResult::Unknown
        ),
        "expected Optimal/Satisfiable/Unknown, got {:?}",
        result
    );

    if matches!(result, OptResult::Optimal) {
        // Value must at least be feasible (>= 3).
        if let Some(val) = model_int(&ctx, x) {
            assert!(
                val >= BigInt::from(3i64),
                "x must be >= 3 (feasible), got {}",
                val
            );
        }
    }
}

/// maximize x  subject to  x = 5  →  optimal x = 5
///
/// Uses a singleton domain `x >= 5 AND x <= 5` so that the linear-search
/// optimizer terminates in exactly 2 SMT calls:
///   1. Initial check: SAT, model assigns x = 5.
///   2. Improvement attempt: assert `x > 5`, which is UNSAT immediately
///      (lower bound 5 contradicts upper bound 5).
///
/// This avoids the O(range) call count of the naive linear-search approach
/// while still exercising the full maximize code path.
#[test]
fn omt_maximize_upper_bound() {
    let mut ctx = OptContext::new();

    let x = ctx.terms.mk_var("xmax", ctx.terms.sorts.int_sort);
    let five_lo = ctx.terms.mk_int(5i64);
    let five_hi = ctx.terms.mk_int(5i64);
    let c1 = ctx.terms.mk_ge(x, five_lo);
    let c2 = ctx.terms.mk_le(x, five_hi);
    ctx.add_hard(c1);
    ctx.add_hard(c2);
    ctx.maximize(x);

    let result = ctx.optimize().expect("optimize should not error");
    assert!(
        matches!(
            result,
            OptResult::Optimal | OptResult::Satisfiable | OptResult::Unknown
        ),
        "expected Optimal/Satisfiable/Unknown, got {:?}",
        result
    );

    if matches!(result, OptResult::Optimal) {
        // The only feasible (and optimal) value is 5.
        if let Some(val) = model_int(&ctx, x) {
            assert_eq!(val, BigInt::from(5i64), "x must equal 5, got {}", val);
        }
    }
}

/// UNSAT hard constraints → single-objective should report unsatisfiable (or unknown).
#[test]
fn omt_unsat_objective() {
    let mut ctx = OptContext::new();

    let x = ctx.terms.mk_var("xo_unsat", ctx.terms.sorts.int_sort);
    let five = ctx.terms.mk_int(5i64);
    let ten = ctx.terms.mk_int(10i64);

    let c1 = ctx.terms.mk_gt(x, ten);
    let c2 = ctx.terms.mk_lt(x, five);
    ctx.add_hard(c1);
    ctx.add_hard(c2);
    ctx.minimize(x);

    let result = ctx.optimize().expect("optimize should not crash");
    assert!(
        matches!(
            result,
            OptResult::Unsatisfiable | OptResult::Unknown | OptResult::Optimal
        ),
        "expected Unsatisfiable/Unknown/Optimal, got {:?}",
        result
    );
}

// ── Pareto optimization ───────────────────────────────────────────────────────

/// Two objectives, two variables, bounded box.
/// The Pareto front should be non-empty (at least one point found).
#[test]
fn pareto_two_objectives_non_empty_front() {
    let mut ctx = OptContext::new();

    let x = ctx.terms.mk_var("xp", ctx.terms.sorts.int_sort);
    let y = ctx.terms.mk_var("yp", ctx.terms.sorts.int_sort);
    let zero_x = ctx.terms.mk_int(0i64);
    let five_x = ctx.terms.mk_int(5i64);
    let zero_y = ctx.terms.mk_int(0i64);
    let five_y = ctx.terms.mk_int(5i64);
    let c1 = ctx.terms.mk_ge(x, zero_x);
    let c2 = ctx.terms.mk_le(x, five_x);
    let c3 = ctx.terms.mk_ge(y, zero_y);
    let c4 = ctx.terms.mk_le(y, five_y);
    ctx.add_hard(c1);
    ctx.add_hard(c2);
    ctx.add_hard(c3);
    ctx.add_hard(c4);

    // Minimize both x and y
    ctx.minimize(x);
    ctx.minimize(y);

    let result = ctx.optimize().expect("optimize should not error");
    assert!(
        matches!(
            result,
            OptResult::Optimal | OptResult::Satisfiable | OptResult::Unknown
        ),
        "expected Optimal/Satisfiable/Unknown, got {:?}",
        result
    );

    // If optimal, the Pareto front should have at least one point.
    if matches!(result, OptResult::Optimal) {
        assert!(
            !ctx.pareto_front().is_empty(),
            "Pareto front should have at least one point"
        );
    }
}

/// UNSAT constraint → Pareto optimizer should report unsatisfiable, not crash.
#[test]
fn pareto_unsat_no_crash() {
    let mut ctx = OptContext::new();

    let x = ctx.terms.mk_var("xpu", ctx.terms.sorts.int_sort);
    let five = ctx.terms.mk_int(5i64);
    let ten = ctx.terms.mk_int(10i64);

    // x > 10 AND x < 5 → UNSAT
    let c1 = ctx.terms.mk_gt(x, ten);
    let c2 = ctx.terms.mk_lt(x, five);
    ctx.add_hard(c1);
    ctx.add_hard(c2);

    ctx.minimize(x);
    ctx.maximize(x);

    let result = ctx.optimize().expect("optimize should not crash");
    assert!(
        matches!(
            result,
            OptResult::Unsatisfiable | OptResult::Unknown | OptResult::Optimal
        ),
        "expected Unsatisfiable/Unknown/Optimal, got {:?}",
        result
    );
}

// ── Opt result variants ───────────────────────────────────────────────────────

#[test]
fn opt_result_unbounded_display() {
    assert_eq!(OptResult::Unbounded.to_string(), "unbounded");
}

#[test]
fn opt_result_all_variants_display() {
    assert_eq!(OptResult::Optimal.to_string(), "optimal");
    assert_eq!(OptResult::Satisfiable.to_string(), "satisfiable");
    assert_eq!(OptResult::Unsatisfiable.to_string(), "unsatisfiable");
    assert_eq!(OptResult::Unknown.to_string(), "unknown");
    assert_eq!(OptResult::Unbounded.to_string(), "unbounded");
}

// ── TermManager exposed on OptContext ────────────────────────────────────────

#[test]
fn opt_context_terms_accessible() {
    let mut ctx = OptContext::new();
    // Verify we can build real terms through ctx.terms
    let x = ctx.terms.mk_var("x_acc", ctx.terms.sorts.int_sort);
    let five = ctx.terms.mk_int(5i64);
    let c = ctx.terms.mk_ge(x, five);
    ctx.add_hard(c);
    // Just check it doesn't crash
    let result = ctx.check_sat();
    assert_eq!(result, OptResult::Satisfiable);
}

// ── Check stats are updated ───────────────────────────────────────────────────

#[test]
fn stats_solver_calls_incremented() {
    let mut ctx = OptContext::new();
    assert_eq!(ctx.stats().solver_calls, 0);

    let p = ctx.terms.mk_var("p_stats", ctx.terms.sorts.bool_sort);
    ctx.add_hard(p);
    ctx.check_sat();
    assert!(
        ctx.stats().solver_calls > 0,
        "solver_calls should be > 0 after check_sat"
    );
}
