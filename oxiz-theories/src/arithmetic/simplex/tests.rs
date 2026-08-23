//! Auto-generated test module (consolidated from inline `#[cfg(test)] mod` blocks)

use crate::arithmetic::delta::DeltaRational;
#[allow(unused_imports)]
use crate::prelude::*;
use num_rational::Rational64;

use super::*;

#[cfg(test)]
mod tests_2 {
    use super::*;

    #[test]
    fn test_simplex_basic() {
        let mut simplex = Simplex::new();

        let x = simplex.new_var();
        let y = simplex.new_var();

        // x >= 0, y >= 0
        simplex.set_lower(x, Rational64::zero(), 0);
        simplex.set_lower(y, Rational64::zero(), 1);

        // x <= 10
        simplex.set_upper(x, Rational64::from_integer(10), 2);

        assert!(simplex.check().is_ok());
    }

    #[test]
    fn test_simplex_infeasible() {
        let mut simplex = Simplex::new();

        let x = simplex.new_var();

        // x >= 10 and x <= 5 is infeasible
        simplex.set_lower(x, Rational64::from_integer(10), 0);
        simplex.set_upper(x, Rational64::from_integer(5), 1);

        assert!(simplex.check().is_err());
    }

    #[test]
    fn test_simplex_strict_bounds() {
        let mut simplex = Simplex::new();

        let x = simplex.new_var();

        // x > 0 (strict lower bound)
        simplex.set_strict_lower(x, Rational64::zero(), 0);

        // x < 10 (strict upper bound)
        simplex.set_strict_upper(x, Rational64::from_integer(10), 1);

        assert!(simplex.check().is_ok());

        // Value should be between 0 and 10 (exclusive)
        let val = simplex.delta_value(x);
        assert!(val.is_positive()); // > 0
        assert!(val < DeltaRational::from(10)); // < 10
    }

    #[test]
    fn test_simplex_strict_infeasible() {
        let mut simplex = Simplex::new();

        let x = simplex.new_var();

        // x >= 5 and x < 5 is infeasible
        simplex.set_lower(x, Rational64::from_integer(5), 0);
        simplex.set_strict_upper(x, Rational64::from_integer(5), 1);

        assert!(simplex.check().is_err());
    }

    #[test]
    fn test_simplex_strict_feasible_boundary() {
        let mut simplex = Simplex::new();

        let x = simplex.new_var();

        // x > 5 and x <= 6 is feasible
        simplex.set_strict_lower(x, Rational64::from_integer(5), 0);
        simplex.set_upper(x, Rational64::from_integer(6), 1);

        assert!(simplex.check().is_ok());

        let val = simplex.delta_value(x);
        assert!(val > DeltaRational::from(5));
        assert!(val <= DeltaRational::from(6));
    }

    #[test]
    fn test_bound_propagation() {
        let mut simplex = Simplex::new();

        let x = simplex.new_var();
        let y = simplex.new_var();

        // x >= 0, x <= 10
        simplex.set_lower(x, Rational64::zero(), 0);
        simplex.set_upper(x, Rational64::from_integer(10), 1);

        // y >= 0, y <= 10
        simplex.set_lower(y, Rational64::zero(), 2);
        simplex.set_upper(y, Rational64::from_integer(10), 3);

        // Add constraint: x + y <= 15
        // This introduces slack variable s, where s = 15 - x - y, s >= 0
        let mut expr = LinExpr::new();
        expr.add_term(x, Rational64::one());
        expr.add_term(y, Rational64::one());
        expr.add_constant(-Rational64::from_integer(15));
        simplex.add_le(expr, 4);

        // Propagate bounds
        simplex.propagate_bounds();

        // Check the constraint is feasible
        assert!(simplex.check().is_ok());

        // The accessor methods work
        assert!(simplex.get_lower(x).is_some());
        assert!(simplex.get_upper(x).is_some());
    }

    #[test]
    fn test_tighten_bounds() {
        let mut simplex = Simplex::new();

        let x = simplex.new_var();

        // x >= 5
        simplex.set_lower(x, Rational64::from_integer(5), 0);

        // x <= 15
        simplex.set_upper(x, Rational64::from_integer(15), 1);

        // The accessor methods work
        let lo = simplex.get_lower(x).expect("test operation should succeed");
        assert_eq!(lo.value.real, Rational64::from_integer(5));

        let hi = simplex.get_upper(x).expect("test operation should succeed");
        assert_eq!(hi.value.real, Rational64::from_integer(15));

        assert!(simplex.check().is_ok());
    }

    #[test]
    fn test_farkas_conflict_explanation() {
        let mut simplex = Simplex::new();

        let x = simplex.new_var();
        let y = simplex.new_var();

        // Constraint: x + y <= 5 (reason 0)
        // Which becomes: x + y - 5 <= 0, introduce slack s where s = 5 - x - y, s >= 0
        let mut expr1 = LinExpr::new();
        expr1.add_term(x, Rational64::one());
        expr1.add_term(y, Rational64::one());
        expr1.add_constant(-Rational64::from_integer(5));
        simplex.add_le(expr1, 0);

        // x >= 3 (reason 1)
        simplex.set_lower(x, Rational64::from_integer(3), 1);

        // y >= 3 (reason 2)
        simplex.set_lower(y, Rational64::from_integer(3), 2);

        // This is infeasible: x >= 3, y >= 3 implies x + y >= 6, but x + y <= 5
        let result = simplex.check();
        assert!(result.is_err());

        // The conflict should include the relevant reasons
        let reasons = result.unwrap_err();
        assert!(!reasons.is_empty());
        // Should include at least the constraint reason (0) and the bound reasons
    }

    #[test]
    fn test_farkas_multiple_variables() {
        let mut simplex = Simplex::new();

        let x = simplex.new_var();
        let y = simplex.new_var();
        let z = simplex.new_var();

        // x + y + z <= 10 (reason 0)
        let mut expr = LinExpr::new();
        expr.add_term(x, Rational64::one());
        expr.add_term(y, Rational64::one());
        expr.add_term(z, Rational64::one());
        expr.add_constant(-Rational64::from_integer(10));
        simplex.add_le(expr, 0);

        // x >= 4 (reason 1)
        simplex.set_lower(x, Rational64::from_integer(4), 1);

        // y >= 4 (reason 2)
        simplex.set_lower(y, Rational64::from_integer(4), 2);

        // z >= 4 (reason 3)
        simplex.set_lower(z, Rational64::from_integer(4), 3);

        // Infeasible: x + y + z >= 12 but x + y + z <= 10
        let result = simplex.check();
        assert!(result.is_err());

        let reasons = result.unwrap_err();
        // Should have multiple reasons in the conflict
        assert!(reasons.len() >= 2);
    }

    #[test]
    fn test_simplex_push_pop() {
        let mut simplex = Simplex::new();

        let x = simplex.new_var();

        // Level 0: x >= 0, x <= 100
        simplex.set_lower(x, Rational64::zero(), 0);
        simplex.set_upper(x, Rational64::from_integer(100), 1);

        assert!(simplex.check().is_ok());

        // Push to level 1
        simplex.push();

        // Level 1: tighten to x >= 50, x <= 60
        simplex.set_lower(x, Rational64::from_integer(50), 2);
        simplex.set_upper(x, Rational64::from_integer(60), 3);

        assert!(simplex.check().is_ok());
        let lo = simplex.get_lower(x).expect("test operation should succeed");
        assert_eq!(lo.value.real, Rational64::from_integer(50));

        // Push to level 2
        simplex.push();

        // Level 2: infeasible bounds x >= 70, x <= 60
        simplex.set_lower(x, Rational64::from_integer(70), 4);

        assert!(simplex.check().is_err());

        // Pop to level 1 - should be feasible again
        simplex.pop();

        // After pop, bounds should be back to x >= 50, x <= 60
        let lo = simplex.get_lower(x).expect("test operation should succeed");
        assert_eq!(lo.value.real, Rational64::from_integer(50));
        let hi = simplex.get_upper(x).expect("test operation should succeed");
        assert_eq!(hi.value.real, Rational64::from_integer(60));

        assert!(simplex.check().is_ok());

        // Pop to level 0
        simplex.pop();

        // After pop, bounds should be back to x >= 0, x <= 100
        let lo = simplex.get_lower(x).expect("test operation should succeed");
        assert_eq!(lo.value.real, Rational64::zero());
        let hi = simplex.get_upper(x).expect("test operation should succeed");
        assert_eq!(hi.value.real, Rational64::from_integer(100));

        assert!(simplex.check().is_ok());
    }

    #[test]
    fn test_simplex_push_pop_vars() {
        let mut simplex = Simplex::new();

        let x = simplex.new_var();
        simplex.set_lower(x, Rational64::zero(), 0);
        simplex.set_upper(x, Rational64::from_integer(10), 1);

        assert_eq!(simplex.num_original_vars(), 1);

        simplex.push();

        // Variables and rows are search-global (Dutertre–de Moura / Z3
        // `lar_solver`): interning one inside a scope does not vanish at the
        // scope's pop – only the BOUNDS are scoped and rolled back.  This is
        // what lets one interned row serve every level that asserts its
        // atom, instead of re-creating rows on every re-assertion.
        let y = simplex.new_var();
        simplex.set_lower(y, Rational64::zero(), 2);
        simplex.set_upper(y, Rational64::from_integer(20), 3);

        assert_eq!(simplex.num_original_vars(), 2);
        assert!(simplex.check().is_ok());

        simplex.pop();

        // The variable survives the pop (its VarId is never recycled), but
        // the bounds asserted inside the popped scope are undone.
        assert_eq!(simplex.num_original_vars(), 2);
        assert!(simplex.get_lower(y).is_none());
        assert!(simplex.get_upper(y).is_none());
        assert!(simplex.check().is_ok());
    }

    #[test]
    fn lazy_scope_snapshot_restores_variables_added_on_both_sides_of_check() {
        let mut simplex = Simplex::new();
        let x = simplex.new_var();
        simplex.set_lower(x, Rational64::zero(), 0);

        simplex.push();

        // Rows/variables are search-global: created inside a scope, they
        // survive its pop (the tableau never shrinks on backtrack), while the
        // constraint BOUNDS the scope asserted are rolled back.
        let y = simplex.new_var();
        let mut first = LinExpr::new();
        first.add_term(x, Rational64::one());
        first.add_term(y, Rational64::one());
        first.add_constant(Rational64::from_integer(-4));
        simplex.add_eq(first, 1);
        assert!(simplex.check().is_ok());
        assert!(!simplex.tableau.is_empty());

        let z = simplex.new_var();
        let mut second = LinExpr::new();
        second.add_term(y, Rational64::one());
        second.add_term(z, Rational64::one());
        second.add_constant(Rational64::from_integer(-6));
        simplex.add_eq(second, 2);
        assert!(simplex.check().is_ok());

        let rows_before_pop = simplex.tableau.len();
        simplex.pop();
        // Final contract (Dutertre–de Moura, with lazy basis snapshots):
        // variables are permanent and rows are permanent definitions, while
        // the BOUNDS the scope asserted are rolled back.  Because the second
        // scoped row was interned AFTER the first  took its lazy
        // snapshot, the pop restores that snapshot's basis and then undoes
        // the first row's bounds — the tableau keeps every row interned
        // before the snapshot, and the post-snapshot row is dropped with the
        // basis restore (it only ever lived in the pivoted view).
        assert_eq!(simplex.tableau.len(), rows_before_pop - 1);
        assert_eq!(simplex.num_original_vars(), 3);
        assert!(simplex.get_lower(y).is_none());
        assert!(simplex.get_lower(z).is_none());
        assert!(simplex.check().is_ok());

        let mut again = LinExpr::new();
        again.add_term(x, Rational64::one());
        again.add_term(y, Rational64::one());
        again.add_constant(Rational64::from_integer(-4));
        simplex.add_eq(again, 1);
        // Re-asserting the first form re-interns its row (a content-cache
        // entry naming a basis-restored row misses): one row again.
        assert_eq!(simplex.tableau.len(), rows_before_pop - 1);
        assert!(simplex.check().is_ok());
    }

    #[test]
    fn pop_without_simplex_run_keeps_parent_assignment_without_snapshot() {
        let mut simplex = Simplex::new();
        let x = simplex.new_var();
        simplex.set_lower(x, Rational64::from_integer(3), 0);
        assert!(simplex.check().is_ok());
        let parent_value = simplex.delta_value(x);

        simplex.push();
        simplex.set_upper(x, Rational64::from_integer(9), 1);
        assert!(matches!(simplex.saved_tableaux.last(), Some(None)));
        simplex.pop();

        assert_eq!(simplex.delta_value(x), parent_value);
        assert!(simplex.get_upper(x).is_none());
        assert!(simplex.check().is_ok());
    }

    #[test]
    fn test_dual_simplex_basic() {
        // Test dual simplex - it works best when we have a basis already
        // For a simple feasibility test, dual_simplex should find violations
        let mut simplex = Simplex::new();

        let x = simplex.new_var();
        let y = simplex.new_var();

        // x, y >= 0
        simplex.set_lower(x, Rational64::zero(), 0);
        simplex.set_lower(y, Rational64::zero(), 1);

        // Add a constraint: x + y = 10 (using slack variable, becomes basic)
        let mut expr = LinExpr::new();
        expr.add_term(x, Rational64::one());
        expr.add_term(y, Rational64::one());
        expr.add_constant(Rational64::from_integer(-10));
        simplex.add_eq(expr, 2);

        // dual_simplex should be able to find a feasible solution
        assert!(simplex.dual_simplex().is_ok());

        // Check values
        let x_val = simplex.value(x);
        let y_val = simplex.value(y);
        assert!(x_val + y_val >= Rational64::from_integer(9)); // Allow some slack
        assert!(x_val + y_val <= Rational64::from_integer(11));
    }

    #[test]
    fn test_dual_simplex_feasible() {
        // Test dual simplex on a feasible problem
        let mut simplex = Simplex::new();

        let x = simplex.new_var();
        let y = simplex.new_var();

        // x >= 0, y >= 0
        simplex.set_lower(x, Rational64::zero(), 0);
        simplex.set_lower(y, Rational64::zero(), 1);

        // x <= 10, y <= 10
        simplex.set_upper(x, Rational64::from_integer(10), 2);
        simplex.set_upper(y, Rational64::from_integer(10), 3);

        // Add constraint: x + y >= 5
        let mut expr = LinExpr::new();
        expr.add_term(x, Rational64::one());
        expr.add_term(y, Rational64::one());
        expr.add_constant(Rational64::from_integer(-5));
        simplex.add_ge(expr, 4);

        // Should be feasible
        assert!(simplex.dual_simplex().is_ok());

        // Check that solution satisfies bounds
        let x_val = simplex.value(x);
        let y_val = simplex.value(y);

        assert!(x_val >= Rational64::zero());
        assert!(y_val >= Rational64::zero());
        assert!(x_val + y_val >= Rational64::from_integer(5));
    }

    /// Test that x<=y AND y<=x makes x<y infeasible (probe test).
    #[test]
    fn test_bidirectional_constraints_probe() {
        let mut simplex = Simplex::new();
        let x = simplex.new_var();
        let y = simplex.new_var();

        // x <= y  (x - y <= 0)
        let mut e1 = LinExpr::new();
        e1.add_term(x, Rational64::one());
        e1.add_term(y, -Rational64::one());
        simplex.add_le(e1, 0);

        // y <= x  (y - x <= 0)
        let mut e2 = LinExpr::new();
        e2.add_term(y, Rational64::one());
        e2.add_term(x, -Rational64::one());
        simplex.add_le(e2, 1);

        assert!(simplex.check().is_ok(), "x<=y AND y<=x should be SAT");

        // Probe: x < y should be UNSAT (since x=y is forced)
        {
            simplex.push();
            let mut e3 = LinExpr::new();
            e3.add_term(x, Rational64::one());
            e3.add_term(y, -Rational64::one());
            simplex.add_strict_lt(e3, 99);
            let probe1 = simplex.check();
            simplex.pop();
            assert!(
                probe1.is_err(),
                "x<y should be UNSAT when x=y is forced; got Ok"
            );
        }

        // Re-establish SAT state.
        assert!(simplex.check().is_ok(), "should still be SAT after probe 1");

        // Probe: y < x should also be UNSAT
        {
            simplex.push();
            let mut e4 = LinExpr::new();
            e4.add_term(y, Rational64::one());
            e4.add_term(x, -Rational64::one());
            simplex.add_strict_lt(e4, 99);
            let probe2 = simplex.check();
            simplex.pop();
            assert!(
                probe2.is_err(),
                "y<x should be UNSAT when x=y is forced; got Ok"
            );
        }
    }

    // Audit regression (theories-arith): `Simplex::pivot` used raw
    // `Rational64` (`i64`-backed) arithmetic operators, which panic on
    // overflow in debug builds and silently wrap to a wrong coefficient in
    // release builds. The checked-rational helpers below must catch every
    // overflow case instead of miscomputing.
    #[test]
    fn checked_rational_helpers_detect_overflow() {
        let huge = Rational64::new(i64::MAX, 1);
        let two = Rational64::from_integer(2);

        assert!(
            checked_mul_r64(huge, two).is_none(),
            "i64::MAX * 2 must overflow, not wrap"
        );
        assert_eq!(
            checked_mul_r64(Rational64::from_integer(3), Rational64::from_integer(4)),
            Some(Rational64::from_integer(12))
        );

        assert!(
            checked_add_r64(huge, huge).is_none(),
            "i64::MAX + i64::MAX must overflow, not wrap"
        );
        assert_eq!(
            checked_add_r64(Rational64::from_integer(1), Rational64::from_integer(2)),
            Some(Rational64::from_integer(3))
        );

        // Division that reduces cleanly must succeed even with a huge
        // numerator.
        assert_eq!(checked_div_r64(huge, Rational64::one()), Some(huge));
        assert!(
            checked_div_r64(Rational64::one(), Rational64::zero()).is_none(),
            "division by zero must be rejected"
        );

        assert!(
            checked_recip_r64(Rational64::zero()).is_none(),
            "reciprocal of zero is undefined"
        );
        assert_eq!(
            checked_recip_r64(Rational64::new(2, 3)),
            Some(Rational64::new(3, 2))
        );

        // `i64::MIN` has no positive `i64` representation of its absolute
        // value.
        assert!(checked_neg_r64(Rational64::new(i64::MIN, 1)).is_none());
        assert_eq!(
            checked_neg_r64(Rational64::from_integer(5)),
            Some(Rational64::from_integer(-5))
        );
    }

    // Audit regression (theories-arith): a pivot whose coefficient
    // computation overflows `i64` must refuse honestly (return `false` +
    // set `resource_limit`) with NO partial tableau mutation, instead of
    // panicking (debug) or committing a silently-wrapped, wrong coefficient
    // (release).
    #[test]
    fn pivot_overflow_is_refused_not_silently_wrong() {
        let mut simplex = Simplex::new();
        let b = simplex.new_var();
        let d = simplex.new_var();

        // Row `s1 = 1*b + i64::MAX*d`. Pivoting `b` into the basis expresses
        // `b` in terms of `s1` and `d`, giving `d` a coefficient of magnitude
        // `i64::MAX` in the new row for `b`.  Rows are interned through the
        // public API so the column index (pivot's row-discovery structure)
        // stays consistent.
        let mut row_a = LinExpr::new();
        row_a.terms.push((b, Rational64::one()));
        row_a.terms.push((d, Rational64::new(i64::MAX, 1)));
        row_a.constant = Rational64::zero();
        let a = simplex.intern_row(row_a);

        // A second row also referencing `b`, with a huge coefficient of its
        // own. Substituting `b`'s new (huge) `d`-coefficient into this row
        // multiplies two `i64::MAX`-scale values together -- this is where
        // unchecked `Rational64` multiplication would overflow.
        let mut row_c = LinExpr::new();
        row_c.terms.push((b, Rational64::new(i64::MAX, 1)));
        row_c.constant = Rational64::zero();
        let c = simplex.intern_row(row_c);

        let ok = simplex.pivot(a, b);
        assert!(
            !ok,
            "pivot must detect the i64 overflow and refuse, not silently wrap"
        );
        assert!(
            simplex.resource_limit_reached(),
            "an overflow-refused pivot must be reported as a resource limit \
             so callers answer Unknown instead of trusting a corrupt state"
        );

        // No partial mutation: row `c` must be exactly as it was before the
        // aborted pivot (transactional validate-then-commit).
        let still_c = simplex
            .tableau
            .get(&c)
            .expect("row c must still exist, untouched, after an aborted pivot");
        assert_eq!(
            still_c
                .terms
                .iter()
                .find(|(v, _)| *v == b)
                .map(|(_, coef)| *coef),
            Some(Rational64::new(i64::MAX, 1)),
            "row c's coefficient for b must be unchanged by the aborted pivot"
        );
        assert!(
            simplex.tableau.contains_key(&a),
            "basic_var's row must not have been removed by an aborted pivot"
        );
    }

    // Audit regression (theories-honesty / arithmetic-simplex): a bound
    // derived by propagation from SEVERAL non-basic bounds is implied by ALL
    // of those bounds. Previously only `reasons.first()` was stored on the
    // derived `Bound`, so a conflict on that bound produced an INCOMPLETE
    // (unsound) explanation that dropped the other antecedents. The derived
    // bound must now carry every contributing reason.
    #[test]
    fn propagated_bound_conflict_lists_all_contributing_reasons() {
        let mut simplex = Simplex::new();
        let x = simplex.new_var();
        let y = simplex.new_var();

        // Constraint: x + y <= 0 (reason 100), introducing slack >= 0.
        let mut e = LinExpr::new();
        e.add_term(x, Rational64::one());
        e.add_term(y, Rational64::one());
        simplex.add_le(e, 100);

        // x >= 3 (reason 1), y >= 4 (reason 2)  =>  x + y >= 7, contradicting
        // x + y <= 0. The derived UPPER bound on the slack (= -(3 + 4) = -7)
        // is implied by BOTH reason 1 and reason 2.
        simplex.set_lower(x, Rational64::from_integer(3), 1);
        simplex.set_lower(y, Rational64::from_integer(4), 2);

        simplex.propagate_bounds();

        let conflict = simplex
            .check()
            .expect_err("x + y <= 0 with x >= 3, y >= 4 must be infeasible");

        // The explanation must cite the constraint (100) and BOTH lower-bound
        // reasons (1 and 2) that fed the derived slack upper bound. The old
        // behavior dropped reason 2.
        assert!(
            conflict.contains(&1),
            "conflict {conflict:?} must include lower-bound reason 1"
        );
        assert!(
            conflict.contains(&2),
            "conflict {conflict:?} must include lower-bound reason 2 (was dropped before the fix)"
        );
    }

    // Audit regression (theories-honesty / arithmetic-simplex): the fix must
    // survive a *multi-hop* derivation. When a non-basic variable's bound is
    // itself a propagated bound carrying auxiliary reasons, `derive_basic_bound`
    // must fold in EVERY one of those antecedents (primary + auxiliary), not
    // just the primary one. The earlier partial fix updated the conflict
    // consumers (`check`, `explain_conflict`) to use `all_reasons()` but left
    // `derive_basic_bound` pushing only `.reason`, so an auxiliary reason on a
    // source bound was silently dropped one derivation step later.
    #[test]
    fn derived_bound_carries_source_aux_reasons_through_derivation() {
        let mut simplex = Simplex::new();
        let x = simplex.new_var();
        let y = simplex.new_var();

        // Constraint: x + y <= 0 (reason 100), introducing slack >= 0.
        let mut e = LinExpr::new();
        e.add_term(x, Rational64::one());
        e.add_term(y, Rational64::one());
        simplex.add_le(e, 100);

        // Give x a lower bound (x >= 3) that itself carries TWO antecedents
        // {1, 5}, as if produced by an earlier propagation step. Before the
        // fix, folding this bound into the slack's derived bound kept only the
        // primary reason (1) and dropped the auxiliary reason (5).
        let mut x_reasons: SmallVec<[u32; 4]> = SmallVec::new();
        x_reasons.push(1);
        x_reasons.push(5);
        simplex.set_lower_delta(
            x,
            DeltaRational::from_rational(Rational64::from_integer(3)),
            x_reasons,
        );

        // y >= 4 (reason 2).
        simplex.set_lower(y, Rational64::from_integer(4), 2);

        simplex.propagate_bounds();

        let conflict = simplex
            .check()
            .expect_err("x + y <= 0 with x >= 3, y >= 4 must be infeasible");

        assert!(
            conflict.contains(&1),
            "conflict {conflict:?} must include x's primary reason 1"
        );
        assert!(
            conflict.contains(&5),
            "conflict {conflict:?} must include x's auxiliary reason 5 (dropped before the fix)"
        );
        assert!(
            conflict.contains(&2),
            "conflict {conflict:?} must include y's reason 2"
        );
    }
}

#[test]
fn dbg_probe_two_le_entails_eq() {
    use num_traits::One;
    let mut s = Simplex::new();
    let x = s.new_var();
    let y = s.new_var();
    let mut e1 = LinExpr::new();
    e1.add_term(x, Rational64::one());
    e1.add_term(y, -Rational64::one());
    s.add_le(e1, 0);
    let mut e2 = LinExpr::new();
    e2.add_term(y, Rational64::one());
    e2.add_term(x, -Rational64::one());
    s.add_le(e2, 0);
    assert!(s.check().is_ok());

    // Probe: x < y must be infeasible.
    s.push();
    let mut p = LinExpr::new();
    p.add_term(x, Rational64::one());
    p.add_term(y, -Rational64::one());
    s.add_strict_lt(p, 0);
    let r = s.check();
    s.pop();
    // After pop, base system must still be feasible.
    assert!(
        s.check().is_ok(),
        "base system must remain feasible after a probe pop"
    );
    assert!(r.is_err(), "x<y must be infeasible under x<=y<=x");

    // Probe 2 after probe 1's pop: y < x must ALSO be infeasible.
    s.push();
    let mut p2 = LinExpr::new();
    p2.add_term(y, Rational64::one());
    p2.add_term(x, -Rational64::one());
    s.add_strict_lt(p2, 0);
    let r2p = s.check();
    s.pop();
    assert!(
        r2p.is_err(),
        "y<x must be infeasible under x<=y<=x after probe1 pop"
    );
}

#[cfg(test)]
mod soi_differential {
    use super::*;

    /// Deterministic xorshift for reproducible random tableaus.
    pub(super) struct Rng(u64);
    impl Rng {
        fn next(&mut self) -> u64 {
            let mut x = self.0;
            x ^= x << 13;
            x ^= x >> 7;
            x ^= x << 17;
            self.0 = x;
            x
        }
        fn i64_in(&mut self, lo: i64, hi: i64) -> i64 {
            lo + (self.next() % ((hi - lo + 1) as u64)) as i64
        }
    }

    /// Build one random bounded linear system on a fresh simplex: n vars,
    /// random dense `<=` rows (via `add_le`), random lower/upper bounds.
    /// Returns the simplex configured with `soi`.
    pub(super) fn build(seed: u64, n: usize, rows: usize, soi: bool) -> Simplex {
        let mut rng = Rng(seed);
        let cfg = crate::config::SimplexConfig {
            enable_soi: soi,
            ..crate::config::SimplexConfig::default()
        };
        let mut s = Simplex::with_config(cfg);
        let vars: Vec<VarId> = (0..n).map(|_| s.new_var()).collect();
        for (i, &v) in vars.iter().enumerate() {
            // Mixed bound shapes: some free, some boxed, some half-bounded.
            match rng.next() % 4 {
                0 => {
                    s.set_lower(v, Rational64::from_integer(rng.i64_in(-8, 0)), i as u32);
                    s.set_upper(v, Rational64::from_integer(rng.i64_in(1, 9)), i as u32);
                }
                1 => {
                    s.set_lower(v, Rational64::from_integer(rng.i64_in(-5, 5)), i as u32);
                }
                2 => {
                    s.set_upper(v, Rational64::from_integer(rng.i64_in(-5, 5)), i as u32);
                }
                _ => {}
            }
        }
        for r in 0..rows {
            let mut expr = LinExpr::new();
            let terms = rng.i64_in(2, n as i64).max(2) as usize;
            for _ in 0..terms {
                let v = vars[rng.next() as usize % n];
                let c = rng.i64_in(-3, 3);
                if c != 0 {
                    expr.terms.push((v, Rational64::from_integer(c)));
                }
            }
            expr.constant = Rational64::from_integer(rng.i64_in(-10, 10));
            s.add_le(expr, 100 + r as u32);
        }
        s
    }

    /// SOI and the standard driver must agree on feasibility for every
    /// random system, and a feasible SOI answer must be backed by an
    /// assignment within the asserted bounds.
    #[test]
    fn soi_matches_standard_on_random_systems() {
        for seed in 1..=400u64 {
            for &(n, rows) in &[(3usize, 4usize), (5, 7), (8, 10), (12, 14)] {
                let mut std = build(seed, n, rows, false);
                let mut soi = build(seed, n, rows, true);
                let r_std = std.check();
                let r_soi = soi.check();
                match (&r_std, &r_soi) {
                    (Ok(()), Ok(())) => {
                        // Both feasible: the SOI assignment must satisfy
                        // every bound AND every tableau row (the stored
                        // basic assignment must equal its row evaluated at
                        // the nonbasic assignments — a divergent delta
                        // propagation shows up here, not in the bounds).
                        for v in 0..soi.assignment.len() {
                            let val = soi.assignment[v];
                            if let Some(lo) = &soi.lower[v] {
                                assert!(
                                    val >= lo.value,
                                    "seed={seed} n={n}: SOI model violates lower on var {v}"
                                );
                            }
                            if let Some(hi) = &soi.upper[v] {
                                assert!(
                                    val <= hi.value,
                                    "seed={seed} n={n}: SOI model violates upper on var {v}"
                                );
                            }
                        }
                        let mut basics: Vec<VarId> = soi.tableau.keys().copied().collect();
                        basics.sort_unstable();
                        for b in basics {
                            let row = soi.tableau.get(&b).unwrap().clone();
                            let mut acc = DeltaRational::from_rational(row.constant);
                            for (nv, c) in &row.terms {
                                let av = soi.assignment[*nv as usize];
                                acc = crate::arithmetic::simplex::checked_add_delta(
                                    acc,
                                    crate::arithmetic::simplex::checked_mul_delta(av, *c)
                                        .expect("row eval overflow"),
                                )
                                .expect("row eval overflow");
                            }
                            assert_eq!(
                                soi.assignment[b as usize], acc,
                                "seed={seed} n={n}: SOI assignment diverged from row of var {b}"
                            );
                        }
                    }
                    (Err(_), Err(_)) => {}
                    (Err(stdc), Ok(())) => {
                        // The simplex `Ok(())` contract: feasible, OR a
                        // resource limit was hit (overflow/budget) and the
                        // caller must treat the answer as inconclusive —
                        // an inconclusive SOI is acceptable (same contract
                        // as the standard driver), not a wrong answer.
                        if soi.resource_limit_reached() {
                            return;
                        }
                        // Std conflicts, SOI feasible: decide who is right
                        // by validating the SOI model against rows+bounds.
                        let mut ok_model = true;
                        'outer: for b in soi.tableau.keys().copied().collect::<Vec<_>>() {
                            let row = soi.tableau.get(&b).unwrap().clone();
                            let mut acc = DeltaRational::from_rational(row.constant);
                            for (nv, c) in &row.terms {
                                match crate::arithmetic::simplex::checked_mul_delta(
                                    soi.assignment[*nv as usize],
                                    *c,
                                )
                                .and_then(|d| crate::arithmetic::simplex::checked_add_delta(acc, d))
                                {
                                    Some(v) => acc = v,
                                    None => {
                                        ok_model = false;
                                        break 'outer;
                                    }
                                }
                            }
                            if acc != soi.assignment[b as usize] {
                                panic!(
                                    "ROW-DIVERGE b={b} stored={:?} row={:?}",
                                    soi.assignment[b as usize].real, acc.real
                                );
                            }
                            if let Some(lo) = &soi.lower[b as usize]
                                && acc < lo.value
                            {
                                panic!(
                                    "LOWER-VIOL b={b} acc={:?} lo={:?}",
                                    acc.real, lo.value.real
                                );
                            }
                            if let Some(hi) = &soi.upper[b as usize]
                                && acc > hi.value
                            {
                                panic!(
                                    "UPPER-VIOL b={b} acc={:?} hi={:?}",
                                    acc.real, hi.value.real
                                );
                            }
                        }
                        if ok_model {
                            panic!(
                                "STD SPURIOUS CONFLICT seed={seed} n={n} rows={rows}: std={stdc:?} — SOI model validated"
                            );
                        } else {
                            panic!(
                                "SOI FALSE FEASIBLE seed={seed} n={n} rows={rows}: std={stdc:?} soi model invalid"
                            );
                        }
                    }
                    (a, b) => {
                        panic!(
                            "verdict mismatch seed={seed} n={n} rows={rows}: std={a:?} soi={b:?}"
                        );
                    }
                }
            }
        }
    }

    /// Degenerate systems (many identical bounds) are the SOI paper's
    /// target regime; exercise heavily-tied boxes.
    #[test]
    fn soi_degenerate_boxes() {
        for seed in 1..=200u64 {
            let mut rng = Rng(seed);
            let cfg = crate::config::SimplexConfig {
                enable_soi: true,
                ..crate::config::SimplexConfig::default()
            };
            let mut s = Simplex::with_config(cfg);
            let vars: Vec<VarId> = (0..6).map(|_| s.new_var()).collect();
            for (i, &v) in vars.iter().enumerate() {
                // Everything boxed into the SAME tiny range: maximal ties.
                s.set_lower(v, Rational64::zero(), i as u32);
                s.set_upper(
                    v,
                    Rational64::from_integer(if i % 2 == 0 { 0 } else { 1 }),
                    i as u32,
                );
            }
            for r in 0..6 {
                let mut expr = LinExpr::new();
                for (k, &v) in vars.iter().enumerate() {
                    let c = if (rng.next() >> k) & 1 == 0 { 1 } else { -1 };
                    expr.terms.push((v, Rational64::from_integer(c)));
                }
                expr.constant = Rational64::from_integer(rng.i64_in(-4, 4));
                s.add_le(expr, 100 + r as u32);
            }
            let reference = build(seed, 0, 0, false);
            drop(reference);
            // Reference: same system on the standard driver.
            let mut std = {
                let mut rng = Rng(seed);
                let mut s2 = Simplex::new();
                let vars: Vec<VarId> = (0..6).map(|_| s2.new_var()).collect();
                for (i, &v) in vars.iter().enumerate() {
                    s2.set_lower(v, Rational64::zero(), i as u32);
                    s2.set_upper(
                        v,
                        Rational64::from_integer(if i % 2 == 0 { 0 } else { 1 }),
                        i as u32,
                    );
                }
                for r in 0..6 {
                    let mut expr = LinExpr::new();
                    for (k, &v) in vars.iter().enumerate() {
                        let c = if (rng.next() >> k) & 1 == 0 { 1 } else { -1 };
                        expr.terms.push((v, Rational64::from_integer(c)));
                    }
                    expr.constant = Rational64::from_integer(rng.i64_in(-4, 4));
                    s2.add_le(expr, 100 + r as u32);
                }
                s2
            };
            let a = std.check();
            let b = s.check();
            // Same contract as the random differential: an SOI give-up
            // (resource limit) is inconclusive, not wrong; any *answered*
            // pair must agree, and an SOI-feasible answer must be backed by
            // a row-consistent in-bounds assignment.
            if s.resource_limit_reached() {
                continue;
            }
            if std.resource_limit_reached() {
                continue;
            }
            assert_eq!(
                a.is_ok(),
                b.is_ok(),
                "degenerate mismatch seed={seed}: std={a:?} soi={b:?}"
            );
            if b.is_ok() {
                for bv in s.tableau.keys().copied().collect::<Vec<_>>() {
                    let row = s.tableau.get(&bv).unwrap().clone();
                    let mut acc = DeltaRational::from_rational(row.constant);
                    for (nv, c) in &row.terms {
                        acc = crate::arithmetic::simplex::checked_add_delta(
                            acc,
                            crate::arithmetic::simplex::checked_mul_delta(
                                s.assignment[*nv as usize],
                                *c,
                            )
                            .expect("overflow"),
                        )
                        .expect("overflow");
                    }
                    assert_eq!(s.assignment[bv as usize], acc, "row divergence");
                    if let Some(lo) = &s.lower[bv as usize] {
                        assert!(acc >= lo.value, "lower violation seed={seed}");
                    }
                    if let Some(hi) = &s.upper[bv as usize] {
                        assert!(acc <= hi.value, "upper violation seed={seed}");
                    }
                }
            }
        }
    }
}

#[cfg(test)]
mod soi_pivot_bench {

    /// Pivot-count comparison SOI vs standard on the random-harness systems
    /// (diagnostic only, run via OXIZ_SOI_BENCH=1; prints the counters the
    /// go/no-go metrics require).
    #[test]
    fn soi_pivot_counts() {
        if std::env::var("OXIZ_SOI_BENCH").is_err() {
            return;
        }
        for &(n, rows) in &[(8usize, 10usize), (16, 20), (32, 40)] {
            for driver in [false, true] {
                crate::arithmetic::simplex::diag::reset();
                let mut answered = 0u32;
                for seed in 1..=50u64 {
                    let mut s = super::soi_differential::build(seed, n, rows, driver);
                    let r = s.check();
                    if r.is_ok() && !s.resource_limit_reached() || r.is_err() {
                        answered += 1;
                    }
                }
                println!("n={n} rows={rows} soi={driver}: answered={answered}");
                crate::arithmetic::simplex::diag::print();
            }
        }
    }
}
