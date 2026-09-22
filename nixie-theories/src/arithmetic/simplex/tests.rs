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
        assert_eq!(
            lo.value.narrow().expect("narrow").real,
            Rational64::from_integer(5)
        );

        let hi = simplex.get_upper(x).expect("test operation should succeed");
        assert_eq!(
            hi.value.narrow().expect("narrow").real,
            Rational64::from_integer(15)
        );

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
        assert_eq!(
            lo.value.narrow().expect("narrow").real,
            Rational64::from_integer(50)
        );

        // Push to level 2
        simplex.push();

        // Level 2: infeasible bounds x >= 70, x <= 60
        simplex.set_lower(x, Rational64::from_integer(70), 4);

        assert!(simplex.check().is_err());

        // Pop to level 1 - should be feasible again
        simplex.pop();

        // After pop, bounds should be back to x >= 50, x <= 60
        let lo = simplex.get_lower(x).expect("test operation should succeed");
        assert_eq!(
            lo.value.narrow().expect("narrow").real,
            Rational64::from_integer(50)
        );
        let hi = simplex.get_upper(x).expect("test operation should succeed");
        assert_eq!(
            hi.value.narrow().expect("narrow").real,
            Rational64::from_integer(60)
        );

        assert!(simplex.check().is_ok());

        // Pop to level 0
        simplex.pop();

        // After pop, bounds should be back to x >= 0, x <= 100
        let lo = simplex.get_lower(x).expect("test operation should succeed");
        assert_eq!(lo.value.narrow().expect("narrow").real, Rational64::zero());
        let hi = simplex.get_upper(x).expect("test operation should succeed");
        assert_eq!(
            hi.value.narrow().expect("narrow").real,
            Rational64::from_integer(100)
        );

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
        // Final contract (Dutertre–de Moura, bounds-only backtracking):
        // variables are permanent and rows are permanent definitions, while
        // the BOUNDS the scope asserted are rolled back.  The tableau never
        // shrinks on backtrack — a row without bounds constrains nothing and
        // its content-cache entry stays valid.  (This used to restore a
        // pre-scope basis snapshot, dropping post-snapshot rows; the
        // snapshot machinery is gone — see `Simplex::pop`.)
        assert_eq!(simplex.tableau.len(), rows_before_pop);
        assert_eq!(simplex.num_original_vars(), 3);
        assert!(simplex.get_lower(y).is_none());
        assert!(simplex.get_lower(z).is_none());
        assert!(simplex.check().is_ok());

        let mut again = LinExpr::new();
        again.add_term(x, Rational64::one());
        again.add_term(y, Rational64::one());
        again.add_constant(Rational64::from_integer(-4));
        simplex.add_eq(again, 1);
        // Re-asserting the first form re-uses the row while it is still
        // basic (its content-cache entry names a live defining row); if a
        // pivot removed it in the meantime, the re-intern rebuilds it —
        // one row either way, never a duplicate.
        assert!(simplex.tableau.len() >= rows_before_pop);
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

    // Audit regression (theories-arith, updated for the wide-row store):
    // a pivot whose substitution leaves `Rational64` width must NEVER
    // commit a silently-wrapped coefficient. With the wide store, the
    // overflowing row is captured EXACTLY (its meaning intact, pivoting
    // and propagation excluded from it) and the pivot succeeds — the old
    // contract (refuse + resource_limit) survives only for the genuinely
    // undecidable cases (a wide ENTERING row). What must hold either way:
    // no wrapped value in the narrow tableau, and the wide row's exact
    // content decidable back from the store.
    #[test]
    fn pivot_overflow_is_captured_not_silently_wrong() {
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
        // multiplies two `i64::MAX`-scale values together — the overflow
        // site.  The `+ d` term keeps the row's coefficient GCD at 1 so
        // canonicalization cannot shrink it.
        let mut row_c = LinExpr::new();
        row_c.terms.push((b, Rational64::new(i64::MAX, 1)));
        row_c.terms.push((d, Rational64::one()));
        row_c.constant = Rational64::zero();
        let c = simplex.intern_row(row_c);

        let ok = simplex.pivot(a, b, SnapBound::LowerPreferred);
        if ok {
            // The overflow was captured: row `c` left the narrow tableau
            // and lives exactly in the wide store (its `d`-coefficient is
            // ±i64::MAX·i64::MAX-scale — beyond `Rational64`, exactly
            // representable in `BigRational`).
            assert!(
                !simplex.tableau.contains_key(&c),
                "a captured wide row must not also hold a narrow entry"
            );
            let wide = simplex
                .wide_rows
                .get(&c)
                .expect("the overflowing row must be captured exactly in the wide store");
            let big_max =
                num_rational::BigRational::from_integer(num_bigint::BigInt::from(i64::MAX));
            // c_new = d + MAX·(s1 − MAX·d) = MAX·s1 + (1 − MAX²)·d.
            let expect_d = -&big_max * &big_max
                + num_rational::BigRational::from_integer(num_bigint::BigInt::from(1));
            assert_eq!(
                wide.terms
                    .iter()
                    .find(|(v, _)| *v == d)
                    .map(|(_, coef)| coef),
                Some(&expect_d),
                "row c's exact d-coefficient after substitution (MAX² + 1, sign per direction)"
            );
            assert!(
                !simplex.resource_limit_reached(),
                "a captured row is not a resource-limit condition"
            );
        } else {
            // Refused (e.g. the entering row itself was wide): must be the
            // honest refusal, never a silent wrap.
            assert!(
                simplex.resource_limit_reached(),
                "an overflow-refused pivot must be reported as a resource limit"
            );
        }
    }

    // Regression (2026-09-15, the last unchecked release-wrap site in the
    // simplex): `on_nonbasic_bound_change`'s delta propagation multiplied and
    // accumulated `DeltaRational`s with the bare `Ratio` operators — a
    // `Δ · c` past `i64` on a wide-coefficient row PANICKED in debug (the
    // debug-panic sweep's `mul_r64_fast` abort via `note_bound_change`) and
    // silently WRAPPED in release, corrupting the dependent basic's
    // assignment for every later decision. The fix is the item-14 pattern:
    // checked multiply/add, exact `BigRational` retry of that one row with a
    // narrowed final (the intermediates overflow while the row's final
    // value fits — magnitudes cancel), and a staleness-flag defer only when
    // the final itself does not fit.
    #[test]
    fn nonbasic_bound_change_delta_overflow_recovers_exact_and_never_wraps() {
        let mut simplex = Simplex::new();
        let x = simplex.new_var();
        let y = simplex.new_var();
        let z = simplex.new_var();

        // Row `s = MAX·x − MAX·y + z` (the `z` keeps the coefficient GCD at
        // 1 so intern-time canonicalization cannot shrink the wide factors).
        let max = Rational64::from_integer(i64::MAX);
        let mut row = LinExpr::new();
        row.terms.push((x, max));
        row.terms.push((y, -max));
        row.terms.push((z, Rational64::one()));
        row.constant = Rational64::zero();
        let s = simplex.intern_row(row);

        // y: 0 → 1. The delta `1 · (−MAX)` FITS, so this step runs the
        // ordinary fast path and lands `s = −MAX` — the pre-overflow state
        // the wide propagation then departs from.
        simplex.set_lower(y, Rational64::one(), 1);
        assert_eq!(simplex.assignment[s as usize].real, -max);

        // x: 0 → 2. The increment `Δ · c = 2·MAX` leaves `i64` — unchecked,
        // this is the abort/wrap site — but the row's final value
        // `MAX·2 − MAX·1 + 0 = MAX` fits, so the exact retry must recover it
        // incrementally: `assignment[s] = MAX`, no staleness, no wrap.
        simplex.set_lower(x, Rational64::from_integer(2), 2);
        assert_eq!(
            simplex.assignment[s as usize].real, max,
            "the exact retry must narrow the row's final (intermediates overflow, finals cancel)"
        );
        assert!(
            simplex.assignment_current,
            "a recovered (exact-retried) update must not leave the vector stale"
        );
        assert!(!simplex.resource_limit_reached());
        assert!(simplex.check().is_ok());
    }

    // Regression (same site, the snap delta): the `new − old` subtraction
    // itself can leave `i64` width when a non-basic jumps between deep
    // opposite bounds — a debug panic and a silent release wrap that would
    // have propagated a fabricated delta to every dependent. The fix defers
    // to the full re-derivation: the snapped value itself is committed (it
    // is a bound value, exact), the dependents are left for `crash_basis`.
    #[test]
    fn nonbasic_bound_change_snap_delta_overflow_defers_instead_of_wrapping() {
        let mut simplex = Simplex::new();
        let x = simplex.new_var();
        let y = simplex.new_var();

        // Row `s = x + y` — an ordinary narrow row whose basic assignment
        // would receive the (wrapped) snap delta.
        let mut row = LinExpr::new();
        row.terms.push((x, Rational64::one()));
        row.terms.push((y, Rational64::one()));
        row.constant = Rational64::zero();
        let s = simplex.intern_row(row);

        // x ∈ [−MAX, −MAX]: snaps x to −MAX (delta −MAX fits), s = −MAX.
        let max = Rational64::from_integer(i64::MAX);
        simplex.set_lower(x, -max, 1);
        simplex.set_upper(x, -max, 2);
        assert_eq!(simplex.assignment[s as usize].real, -max);

        // Loosen the upper, then tighten the lower to +MAX: the window is
        // [MAX, MAX] (not crossed) and the snap must move x from −MAX to
        // MAX — a delta of 2·MAX that `i64` cannot hold.
        simplex.set_upper(x, max, 3);
        simplex.set_lower(x, max, 4);

        // The snapped value is committed exactly (a bound value); the
        // propagation is skipped and the vector flagged stale for the next
        // consumer's `crash_basis` — never a wrapped delta.
        assert_eq!(
            simplex.assignment[x as usize].real, max,
            "the snapped non-basic value must be committed exactly, not wrapped"
        );
        assert!(
            !simplex.assignment_current,
            "an unrepresentable snap delta must defer via the staleness flag"
        );
        assert!(!simplex.resource_limit_reached());

        // The full re-derivation makes the state consistent again: s = MAX.
        assert!(simplex.check().is_ok());
        assert!(simplex.assignment_current);
        assert_eq!(simplex.assignment[s as usize].real, max);
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
                                    lo.value.cmp_narrow(&val) != core::cmp::Ordering::Greater,
                                    "seed={seed} n={n}: SOI model violates lower on var {v}"
                                );
                            }
                            if let Some(hi) = &soi.upper[v] {
                                assert!(
                                    hi.value.cmp_narrow(&val) != core::cmp::Ordering::Less,
                                    "seed={seed} n={n}: SOI model violates upper on var {v}"
                                );
                            }
                        }
                        let mut basics: Vec<VarId> = soi.tableau.keys().copied().collect();
                        basics.sort_unstable();
                        for b in basics {
                            let row = soi.row_lin(b).expect("row exists");
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
                            let row = soi.row_lin(b).expect("row exists");
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
                                && lo.value.cmp_narrow(&acc) == core::cmp::Ordering::Greater
                            {
                                panic!(
                                    "LOWER-VIOL b={b} acc={:?} lo={:?}",
                                    acc.real,
                                    lo.value.narrow()
                                );
                            }
                            if let Some(hi) = &soi.upper[b as usize]
                                && hi.value.cmp_narrow(&acc) == core::cmp::Ordering::Less
                            {
                                panic!(
                                    "UPPER-VIOL b={b} acc={:?} hi={:?}",
                                    acc.real,
                                    hi.value.narrow()
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
                    let row = s.row_lin(bv).expect("row exists");
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
                        assert!(
                            lo.value.cmp_narrow(&acc) != core::cmp::Ordering::Greater,
                            "lower violation seed={seed}"
                        );
                    }
                    if let Some(hi) = &s.upper[bv as usize] {
                        assert!(
                            hi.value.cmp_narrow(&acc) != core::cmp::Ordering::Less,
                            "upper violation seed={seed}"
                        );
                    }
                }
            }
        }
    }
}

#[cfg(test)]
mod soi_pivot_bench {

    /// Pivot-count comparison SOI vs standard on the random-harness systems
    /// (diagnostic only, run via NIXIE_SOI_BENCH=1; prints the counters the
    /// go/no-go metrics require).
    #[test]
    fn soi_pivot_counts() {
        if std::env::var("NIXIE_SOI_BENCH").is_err() {
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

#[cfg(test)]
mod canonical_form {
    use super::super::canonicalize_lin_form;
    use super::*;

    fn form(
        terms: Vec<(VarId, Rational64)>,
        constant: Rational64,
    ) -> (Vec<(VarId, Rational64)>, Rational64) {
        let mut terms = terms;
        let mut constant = constant;
        canonicalize_lin_form(&mut terms, &mut constant);
        (terms, constant)
    }

    fn r(n: i64, d: i64) -> Rational64 {
        Rational64::new(n, d)
    }

    #[test]
    fn scaled_gap_row_reduces_to_small_integers() {
        // The fuzzer's scaled `gap` shape: every coefficient a multiple of
        // 10^9.  gcd = 2·10^9 → the row collapses to single digits.
        let (terms, constant) = form(
            vec![
                (0, r(-6_000_000_000, 1)),
                (1, r(-12_000_000_000, 1)),
                (2, r(-8_000_000_000, 1)),
                (3, r(4_000_000_000, 1)),
                (4, r(2_000_000_000, 1)),
            ],
            r(-31_000_000_000, 1),
        );
        let expect = vec![
            (0, r(-3, 1)),
            (1, r(-6, 1)),
            (2, r(-4, 1)),
            (3, r(2, 1)),
            (4, r(1, 1)),
        ];
        assert_eq!(terms, expect);
        // -31e9 / 2e9 = -15.5 exactly.
        assert_eq!(constant, r(-31, 2));
    }

    #[test]
    fn fractional_coefficients_scale_by_denominator_lcm() {
        // x/2 + y/3 → (lcm 6, gcd(3,2)=1) → 3x + 2y.
        let (terms, _) = form(vec![(0, r(1, 2)), (1, r(1, 3))], Rational64::zero());
        assert_eq!(terms, vec![(0, r(3, 1)), (1, r(2, 1))]);
    }

    #[test]
    fn mixed_fractions_reduce_to_gcd_one() {
        // (2/3)x + 4y → lcm 3, numerators 2, 12, gcd 2 → scale 3/2 →
        // x + 6y.
        let (terms, _) = form(vec![(0, r(2, 3)), (1, r(4, 1))], Rational64::zero());
        assert_eq!(terms, vec![(0, r(1, 1)), (1, r(6, 1))]);
    }

    #[test]
    fn already_canonical_form_is_untouched() {
        let (terms, constant) = form(vec![(0, r(2, 1)), (1, r(-3, 1))], r(5, 2));
        assert_eq!(terms, vec![(0, r(2, 1)), (1, r(-3, 1))]);
        assert_eq!(constant, r(5, 2));
    }

    #[test]
    fn negative_scale_is_never_applied() {
        // All-negative coefficients: the factor is positive (gcd of
        // absolute values), so signs are preserved — negating would flip
        // the strict-bound meaning downstream.
        let (terms, _) = form(vec![(0, r(-4, 1)), (1, r(-6, 1))], Rational64::zero());
        assert_eq!(terms, vec![(0, r(-2, 1)), (1, r(-3, 1))]);
    }

    #[test]
    fn i64_min_numerator_bails_without_mutation() {
        // |i64::MIN| has no magnitude; the form must be left untouched
        // rather than wrap.
        let (terms, constant) = form(vec![(0, r(i64::MIN, 1)), (1, r(1, 1))], r(7, 1));
        assert_eq!(terms, vec![(0, r(i64::MIN, 1)), (1, r(1, 1))]);
        assert_eq!(constant, r(7, 1));
    }

    #[test]
    fn empty_form_is_canonical() {
        let (terms, constant) = form(vec![], r(3, 2));
        assert!(terms.is_empty());
        assert_eq!(constant, r(3, 2));
    }

    #[test]
    fn rows_differing_by_a_positive_multiple_share_one_slack() {
        // Content addressing through the canonical form: `2x+2y-4` and
        // `x+y-2` are the same row, so both atoms constrain one slack.
        let mut simplex = Simplex::new();
        let x = simplex.new_var();
        let y = simplex.new_var();

        let mut a = LinExpr::new();
        a.terms.push((x, r(2, 1)));
        a.terms.push((y, r(2, 1)));
        a.constant = r(-4, 1);
        let slack_a = simplex.intern_row_cached(&a);

        let mut b = LinExpr::new();
        b.terms.push((x, r(1, 1)));
        b.terms.push((y, r(1, 1)));
        b.constant = r(-2, 1);
        let slack_b = simplex.intern_row_cached(&b);

        assert_eq!(
            slack_a, slack_b,
            "positively-proportional forms must share a row"
        );
    }
}

// Regression (2026-09-15, the wide-store value fabrication): the exact
// value of a WIDE-basic variable must never be read from the raw
// `assignment` entry — that entry is only maintained while the exact
// value narrows, and an unrepresentable one leaves it stale on purpose
// (the false-`sat` class read a fabricated integral `0` for a variable
// whose true value was `−9 − 41/2⁶³`). `delta_value_exact` re-derives
// from the wide row and declines when the value does not narrow;
// `wide_floor_ceil_big` derives the branch bounds from the exact
// UN-NARROWED value (small integers even at 2⁶³-scale magnitudes, which
// is what keeps such searches decidable instead of honest-`unknown`).
#[test]
fn wide_basic_reads_and_branch_bounds_are_exact() {
    use num_bigint::BigInt;
    use num_rational::BigRational;
    let big = |n: i128, d: i128| BigRational::new(BigInt::from(n), BigInt::from(d));

    let mut s = Simplex::new();
    let x = s.new_var();
    let t = s.new_var();
    // Pin t = 3 through the ordinary bound machinery (snaps the
    // non-basic into its window).
    s.set_lower(t, Rational64::from_integer(3), 1);

    // Wide row: x = t/2⁶³ − 83010348301752982313/2⁶³. At t = 3 the
    // exact value is −9 − 41/2⁶³·… (numerator ≈ 8.3·10¹⁹ — beyond i64).
    s.wide_rows.insert(
        x,
        BigLinExpr {
            terms: vec![(t, big(1, 9223372036854775808))],
            constant: big(-83010348331692982313, 9223372036854775808),
        },
    );
    assert!(s.is_wide_basic(x));
    assert!(
        s.delta_value_exact(x).is_none(),
        "the exact value's numerator leaves i64: no honest narrow value exists"
    );
    // The branch bounds are small integers regardless: floor −10, ceil −9.
    assert_eq!(s.wide_floor_ceil_big(x), Some((-10, -9)));

    // A wide value that DOES narrow reads exactly (x = t/2 → 3/2), and
    // its floor/ceil follow the ordinary delta-aware rules.
    s.wide_rows.insert(
        x,
        BigLinExpr {
            terms: vec![(t, big(1, 2))],
            constant: big(0, 1),
        },
    );
    assert_eq!(
        s.delta_value_exact(x).map(|v| v.real),
        Some(Rational64::new(3, 2))
    );
    assert_eq!(s.wide_floor_ceil_big(x), Some((1, 2)));

    // A non-wide variable reads through the ordinary path (t itself).
    assert_eq!(
        s.delta_value_exact(t).map(|v| v.real),
        Some(Rational64::from_integer(3))
    );
}

// Regression (2026-09-15, the silent wide-dependent skip): a bound
// change on a non-basic whose dependent row lives in the WIDE store
// used to skip that dependent silently — no update, no staleness flag —
// leaving the wide basic's entry stale by exactly Δ·coef. The skip now
// flags the vector so the next guard re-derives everything.
#[test]
fn wide_dependent_bound_change_flags_staleness() {
    use num_bigint::BigInt;
    use num_rational::BigRational;
    let mut s = Simplex::new();
    let x = s.new_var();
    let t = s.new_var();
    // x is wide-basic over t (row x = 2·t), and t's column lists x as a
    // dependent (the column index covers both stores).
    s.wide_rows.insert(
        x,
        BigLinExpr {
            terms: vec![(t, BigRational::from_integer(BigInt::from(2)))],
            constant: BigRational::zero(),
        },
    );
    s.column_push_known(t, x);
    assert!(s.assignment_current);

    // t: 0 → 5. The dependent is wide (not in `tableau`): the delta
    // cannot land, so the vector must be flagged stale.
    s.set_lower(t, Rational64::from_integer(5), 1);
    assert!(
        !s.assignment_current,
        "a skipped wide dependent must flag staleness, not pass silently"
    );
}

// Regression (2026-09-16, the wide-chain false `unsat` root cause):
// `derive_basic_bound`'s mid-walk exact retry recomputes the WHOLE
// directional sum, but the walk used to CONTINUE adding the remaining
// terms on top of the full recomputation — double-counting the
// post-overflow terms. On the wide-chain shape the retry returned the
// correct full sum and the walk then re-added the remaining term,
// planting a bound that violated the model and refuting a satisfiable
// chain. The fix: after the retry the arithmetic is complete (the
// walk keeps iterating only to collect REASONS).
#[test]
fn basic_bound_exact_retry_does_not_double_count() {
    let mut simplex = Simplex::new();
    let x = simplex.new_var();
    let y = simplex.new_var();
    let z = simplex.new_var();
    // x = y = 1, z = 2.
    for v in [x, y] {
        simplex.set_lower(v, Rational64::one(), 1);
        simplex.set_upper(v, Rational64::one(), 1);
    }
    simplex.set_lower(z, Rational64::from_integer(2), 1);
    simplex.set_upper(z, Rational64::from_integer(2), 1);
    // Row: basic = 2^62·x + 2^62·y − 2^62·z + 1·w + 3 (the unit `w`
    // term keeps the coefficient GCD at 1, so intern-time
    // canonicalization cannot rescale the row). Walk: 3 + 2^62
    // (fits), + 2^62 → 2^63 + 3 OVERFLOWS the checked add; the exact
    // retry returns the full sum 3. The unfixed walk continued and
    // re-added the remaining `z` term (−2^63), reporting −2^63 + 3.
    let w = simplex.new_var();
    simplex.set_lower(w, Rational64::zero(), 1);
    let big = Rational64::from_integer(4611686018427387904i64);
    let mut row = LinExpr::new();
    row.terms.push((x, big));
    row.terms.push((y, big));
    row.terms.push((z, -big));
    row.terms.push((w, Rational64::one()));
    row.constant = Rational64::from_integer(3);
    let slack = simplex.intern_row(row);

    // The slack's bound slots are not allocated until a bound is
    // stored, and the propagation's apply loop (pre-existing behavior)
    // skips vars without slots — so the derivation itself is asserted
    // here, via the propagated bound it produces.
    simplex.propagate_bounds();
    let props = simplex.get_propagated();
    let want = DeltaRational::from_rational(Rational64::from_integer(3));
    assert!(
        props.iter().any(|p| p.var == slack
            && p.is_lower
            && p.value.cmp_narrow(&want) == core::cmp::Ordering::Equal),
        "the row's exact value at the pins is 3 (the exact-retry result);              a different propagated lower is the double-count: {props:?}"
    );
    // (`derive_basic_bound` returns at most one direction per call —
    // the lower; the upper derives on the next fixpoint pass.)
}

// Regression (2026-09-17, the item-54 false `unsat`): a row whose
// SUBSTITUTED constant exceeds `i64` — here `3·yi − md − dv + 1` with the
// pinned basic `yi = pin + 2^62`, whose substitution yields the constant
// `3·2^62 + 1` — is interned through the positive width rescale
// (`scale_big_to_narrow`).  The rescale preserves the zero-bound
// CONSTRAINT semantics but changes the slack's DEFINING FORM to
// `form / λ`, so integrality of the requested form must not transfer to
// the slack: treating it as integer let a Gomory cut fabricate
// `52 | (1 − s_axiom)` and refute a division axiom alone (a false
// `unsat` on a `sat` goal).  `intern_row_reported` exposes exactly this
// distinction.
#[test]
fn intern_row_reports_rescaled_for_width_rescale() {
    let mut s = Simplex::new();
    let yi = s.new_var();
    let pin = s.new_var();
    let md = s.new_var();
    let dv = s.new_var();
    // `yi` is basic with the post-pivot pin row `yi = pin + 2^62`
    // (mirrors the fi1 trajectory, where the pinned variable's row
    // carries the 2^62 constant).
    s.tableau.insert(
        yi,
        TableRow::Lin(std::sync::Arc::new(LinExpr {
            terms: smallvec::smallvec![(pin, Rational64::one())],
            constant: Rational64::from_integer(4611686018427387904),
        })),
    );
    s.basic.resize(yi as usize + 1, false);
    s.basic[yi as usize] = true;
    s.column_push_known(pin, yi);

    // The requested row is an INTEGRAL form (GCD 1): `3·yi − md − dv + 1`.
    let mut row = LinExpr::new();
    row.add_term(yi, Rational64::from_integer(3));
    row.add_term(md, Rational64::from_integer(-1));
    row.add_term(dv, Rational64::from_integer(-1));
    row.add_constant(Rational64::one());
    let (slack, mode) = s.intern_row_reported(row);
    assert_eq!(
        mode,
        RowInternMode::Rescaled,
        "the substituted constant 3·2^62+1 fits only under a width rescale"
    );
    // The slack's defining row is the RESCALED form: at least one
    // coefficient is fractional (the requested form's were all integral),
    // which is precisely why integrality does not transfer.
    let r = s
        .defining_row(slack)
        .expect("a rescaled row lands in the tableau");
    assert!(
        r.terms.iter().any(|(_, c)| *c.denom() != 1) || *r.constant.denom() != 1,
        "the rescaled row must actually be a non-integral multiple of the form: {r:?}"
    );

    // Control: the same shape with a small pin constant interns `Exact`
    // (the plain substitution path), and its row keeps integral
    // coefficients — the property Gomory cuts and branch-and-bound rely
    // on for integer-marked slacks.
    let mut s2 = Simplex::new();
    let yi2 = s2.new_var();
    let pin2 = s2.new_var();
    let md2 = s2.new_var();
    s2.tableau.insert(
        yi2,
        TableRow::Lin(std::sync::Arc::new(LinExpr {
            terms: smallvec::smallvec![(pin2, Rational64::one())],
            constant: Rational64::from_integer(4),
        })),
    );
    s2.basic.resize(yi2 as usize + 1, false);
    s2.basic[yi2 as usize] = true;
    s2.column_push_known(pin2, yi2);
    let mut row2 = LinExpr::new();
    row2.add_term(yi2, Rational64::from_integer(3));
    row2.add_term(md2, Rational64::from_integer(-1));
    row2.add_constant(Rational64::one());
    let (slack2, mode2) = s2.intern_row_reported(row2);
    assert_eq!(mode2, RowInternMode::Exact);
    let r2 = s2.defining_row(slack2).expect("plain intern keeps a row");
    assert!(
        r2.terms.iter().all(|(_, c)| *c.denom() == 1) && *r2.constant.denom() == 1,
        "an Exact intern of an integral form stays integral: {r2:?}"
    );
}

// Regression (2026-09-17, the `wisas_xs_8_13` livelock): the standard
// driver's repair pivot used to snap the leaving variable to its LOWER
// bound regardless of which bound it violated — an upper violation at
// `1/2` over `[-1,0]` snapped to `-1`, and the overshoot (the whole bound
// interval) landed on the entering variable through the row equation,
// manufacturing a mirrored violation of the same size.  With two-sided
// pins everywhere (the propagation-enriched bound sets), two mirrored rows
// then swapped basis positions forever: 100k pivots, budget exhausted, the
// whole solve degraded to `unknown` on a z3-certified `unsat` instance.
// The Dutertre–de Moura repair step snaps the leaving variable to the
// bound it VIOLATED, which here fully repairs (both variables land
// feasible).
#[test]
fn repair_pivot_snaps_the_leaving_var_to_its_violated_bound() {
    let mut s = Simplex::new();
    let a = s.new_var();
    let b = s.new_var();
    // a, b ∈ [-1, 0]; row(b): b = -1/2 - a  (a nonbasic).
    for v in [a, b] {
        s.set_lower(v, Rational64::from_integer(-1), 1);
        s.set_upper(v, Rational64::zero(), 2);
    }
    s.tableau.insert(
        b,
        TableRow::Lin(std::sync::Arc::new(LinExpr {
            terms: smallvec::smallvec![(a, Rational64::from_integer(-1))],
            constant: Rational64::new(-1, 2),
        })),
    );
    s.basic.resize(b as usize + 1, false);
    s.basic[b as usize] = true;
    s.column_push_known(a, b);

    // crash_basis snaps `a` to its lower (-1), so `b` derives 1/2 — above
    // its upper 0.  The repair pivot on (leaving=b, entering=a) must snap
    // b to the VIOLATED bound (0), landing a at -1/2: both feasible.
    // (Pre-fix: b snapped to -1, a derived 1/2 — violated; the mirrored
    // row re-derived the mirror image, and the pair cycled to the pivot
    // budget.)
    s.assignment_current = false;
    let verdict = s.check();
    assert!(
        verdict.is_ok(),
        "the system is feasible (a=-1/2, b=0): {verdict:?}"
    );
    assert!(
        !s.resource_limit_reached(),
        "no budget exhaustion on a 2-variable system"
    );
    let va = s.value(a);
    let vb = s.value(b);
    assert!(
        va >= Rational64::from_integer(-1)
            && va <= Rational64::zero()
            && vb >= Rational64::from_integer(-1)
            && vb <= Rational64::zero(),
        "both variables inside their bounds: a={va:?} b={vb:?}"
    );
}

// Regression (2026-09-17, the wide-driven repair step): a violated wide
// row whose achievable range OVERLAPS its bound window is repairable in
// principle, but wide rows had no pivot — the convergence classification
// declined the whole check (`resource_limit`, honest `unknown`; the
// wide-LP endgame's named residual, the wall the `NIXIE_S6_PINNED`
// trade analysis measured at site 1950).  The pivot's wide-leaving branch
// now solves the wide row exactly for an eligible entering column and
// snaps the leaving basic to the bound it violates, so the overlap case
// converges instead of declining.
//
// Shape: `t` is wide-basic over `a` (`t = W·a − 5W + 1`, W = 2^62), with
// `t ∈ [0,0]` and `a ∈ [0,10]`.  At `a = 0` the row value is `−5W + 1`
// (violates the lower 0) while the achievable range `[−5W+1, 5W+1]`
// straddles the window — the pre-fix classification hit exactly this arm
// and declined; the repair pivots (entering `a`), snaps `t` to 0, and `a`
// lands at `5 − 1/W` (inside its window, and the solved row narrows).
#[test]
fn violated_wide_row_with_overlapping_range_is_repaired() {
    use num_bigint::BigInt;
    use num_rational::BigRational;
    let mut s = Simplex::new();
    let t = s.new_var();
    let a = s.new_var();
    let w = BigRational::from_integer(BigInt::from(2).pow(62));
    let c = -(&w * BigInt::from(5)) + BigRational::from_integer(BigInt::from(1));
    s.wide_rows.insert(
        t,
        BigLinExpr {
            terms: vec![(a, w)],
            constant: c,
        },
    );
    s.column_push_known(a, t);
    let hi_var = t.max(a);
    s.basic.resize(hi_var as usize + 1, false);
    s.basic[t as usize] = true;
    s.set_lower(t, Rational64::zero(), 1);
    s.set_upper(t, Rational64::zero(), 2);
    s.set_lower(a, Rational64::zero(), 3);
    s.set_upper(a, Rational64::from_integer(10), 4);

    // Derive the initial assignment (a snaps to its lower 0; t's wide
    // value is re-derived exactly by the wide pass).
    s.assignment_current = false;
    let verdict = s.check();
    assert!(
        verdict.is_ok(),
        "the system is feasible (a = 5 - 1/2^62, t = 0): {verdict:?}"
    );
    assert!(
        !s.resource_limit_reached(),
        "an overlapping-range violation must be repaired, not declined"
    );
    let vt = s.value(t);
    assert_eq!(vt, Rational64::zero());
    let va = s.value(a);
    assert!(
        va >= Rational64::zero() && va <= Rational64::from_integer(10),
        "the repaired entering variable stays inside its window: {va:?}"
    );
}

// Regression (2026-09-17, found by the strengthened definitional invariant
// on the NLA interval probes): a scoped probe may tighten a bound PAST the
// opposite one (a crossed window is the probe's infeasibility signal), and
// the snap-into-window parks the nonbasic at a point only the TIGHTENED
// side justified — restoring that side at `pop` then widens the window
// away from the point, leaving the nonbasic OUTSIDE its restored window
// (invisible to `find_violating`, which scans basics only).  The pop now
// re-snaps every non-basic the undo left outside its window and flags the
// assignment stale for its dependents' re-derivation.
#[test]
fn pop_resnaps_a_nonbasic_left_outside_its_restored_window() {
    let mut s = Simplex::new();
    let x = s.new_var();
    s.set_lower(x, Rational64::from_integer(6), 1);
    s.set_upper(x, Rational64::from_integer(10), 2);
    // Snap x into its window (nonbasic at the lower 6).
    s.assignment_current = false;
    assert!(s.check().is_ok());
    assert_eq!(s.value(x), Rational64::from_integer(6));

    // The crossed probe: upper tightened past the lower.
    s.push();
    s.set_upper(x, Rational64::zero(), 3);
    // window [6, 0] is empty; the sequential clamp parks x at the upper 0
    // (below the surviving lower) — the probe's infeasibility shape.
    s.pop();

    // After the pop the upper is restored to 10; the nonbasic must be back
    // inside [6, 10] (pre-fix it stayed at 0 — below the lower, with no
    // search mechanism able to see or repair it).
    let viol = s.debug_verify_invariant();
    assert!(
        viol.is_none(),
        "the popped state must be definitional again: {viol:?}"
    );
    assert!(
        s.value(x) >= Rational64::from_integer(6) && s.value(x) <= Rational64::from_integer(10),
        "the nonbasic is re-snapped into its restored window: {:?}",
        s.value(x)
    );
    // And the system still solves (no phantom violation from the stale 0).
    assert!(s.check().is_ok());
}

// Regression (2026-09-17, the unsat-side gap's wide-classification
// members): `wide_row_refuted_by_bounds` bailed (`return None`) whenever
// ANY achievable-range endpoint was unbounded — including the side
// irrelevant to the violation.  `v2 = v1 + c` with `v1 >= 0` (unbounded
// above) and `v2 <= 0`: the MIN side alone refutes (`min = c > 0 =
// upper`), but the unbounded MAX side hid it, the repair found no
// eligible column (the only column sits at its lower), and the whole
// check declined an LP-infeasible goal to `unknown`.  Unboundedness now
// makes only ITS side's test vacuous.
#[test]
fn wide_row_refutation_survives_an_unbounded_irrelevant_side() {
    use num_bigint::BigInt;
    use num_rational::BigRational;
    let mut s = Simplex::new();
    let v1 = s.new_var();
    let v2 = s.new_var();
    // v2 (wide basic) = v1 + 2305843009213693941;  v1 ∈ [0, ∞); v2 ≤ 0.
    let c = BigRational::from_integer(BigInt::from(2_305_843_009_213_693_941i64));
    s.wide_rows.insert(
        v2,
        BigLinExpr {
            terms: vec![(v1, BigRational::from_integer(BigInt::from(1)))],
            constant: c,
        },
    );
    s.column_push_known(v1, v2);
    let hi_var = v1.max(v2);
    s.basic.resize(hi_var as usize + 1, false);
    s.basic[v2 as usize] = true;
    s.set_lower(v1, Rational64::zero(), 1);
    s.set_upper(v2, Rational64::zero(), 2);
    // The violated row (v2 = c > 0 = its upper) must REFUTE through the
    // min side: {v1's lower, v2's upper} force v2 >= c > 0.
    let verdict = s.check();
    assert!(
        verdict.is_err(),
        "the row system is infeasible (v1 >= 0 forces v2 = v1 + c > 0 = upper): {verdict:?}"
    );
    assert!(
        !s.resource_limit_reached(),
        "an unbounded irrelevant side must not turn a refutation into a decline"
    );
}

/// A derivation must DECLINE through a strictly crossed window (lower >
/// upper) instead of picking the pair's wrong-side endpoint: the crossed
/// state belongs to the crossing channel (`record_crossing` exports the
/// conflict), and an interval derivation over an EMPTY interval fabricates
/// a bound no antecedent implies — the `NIXIE_S6_NDIR2` false-`unsat`
/// (seed 20261123: a v19/v63-family crossed window fed dir2/dir1
/// derivations whose planted bounds refuted six atoms that are all TRUE
/// at z3's model `xi = 120`).
#[test]
fn derivation_through_a_crossed_window_declines_instead_of_fabricating() {
    let mut s = Simplex::new();
    let x = s.new_var();
    let y = s.new_var();

    // A crossed column window: lower 5 > upper 0.
    s.set_lower(x, Rational64::from_integer(5), 1);
    s.set_upper(x, Rational64::zero(), 2);

    // `derive_bound_big_parts` (the wide interval walk the slice-6
    // selectors share): a crossed COLUMN window must decline — pre-fix,
    // the `want_min == a_first` endpoint pick chose the pair's WRONG side
    // exactly when inverted, fabricating a bound no antecedent implies.
    // (`derive_basic_bound` is deliberately NOT tested here: it reads
    // stored bounds as-is, sound-input-sound-output; the fabrication site
    // is the pair-swap selectors alone.)
    let zero = num_rational::BigRational::from(num_bigint::BigInt::from(0));
    let one = num_rational::BigRational::from(num_bigint::BigInt::from(1));
    let terms = vec![(x, one.clone())];
    for lower in [true, false] {
        assert!(
            s.derive_bound_big_parts(&zero, &terms, lower).is_none(),
            "the interval walk must decline over a crossed window (lower={lower})"
        );
    }

    // Direction-2 (the general solve): a crossed BASIC window must
    // decline.  Cross y's window and solve the row `y = x + 0` for x.
    s.set_lower(y, Rational64::from_integer(7), 3);
    s.set_upper(y, Rational64::from_integer(2), 4);
    let wexpr = BigLinExpr {
        terms: vec![(x, one)],
        constant: zero,
    };
    for lower in [true, false] {
        assert!(
            s.derive_var_bound_big_parts(y, &wexpr, x, lower).is_none(),
            "direction-2 must decline over a crossed basic window (lower={lower})"
        );
    }
}

// ===== Z3 `patch_basic_columns` (the cheap integrality move) =====

#[test]
fn patching_deltas_solve_the_congruence() {
    // x + α·δ must be integral for the returned δ: verified directly and
    // against hand-solved cases.
    // x = 1/2, α = 3/4: 1/2 + (3/4)δ ∈ ℤ ⟺ δ ≡ 2 (mod 4).
    let (dp, dm) = Simplex::patching_deltas(&Rational64::new(1, 2), &Rational64::new(3, 4))
        .expect("solution exists (denom 2 | 4)");
    assert_eq!((dp, dm), (2, -2));
    for d in [dp, dm] {
        let v = Rational64::new(1, 2) + Rational64::new(3, 4) * Rational64::from_integer(d);
        assert!(
            v.is_integer(),
            "δ={d} must make the value integral, got {v}"
        );
    }
    // x = 2/3, α = 1/3: 2/3 + δ/3 ∈ ℤ ⟺ δ ≡ 1 (mod 3).
    let (dp, dm) = Simplex::patching_deltas(&Rational64::new(2, 3), &Rational64::new(1, 3))
        .expect("solution exists (denom 3 | 3)");
    assert_eq!((dp, dm), (1, -2));
    // No solution when denom(x) ∤ denom(α): x = 1/2, α = 1/3 (2 ∤ 3 —
    // 1/2 + δ/3 is never an integer for integral δ).
    assert!(Simplex::patching_deltas(&Rational64::new(1, 2), &Rational64::new(1, 3)).is_none());
    // The divided case DOES solve (2 | 4): 1/2 + (1/4)δ ∈ ℤ at δ = 2.
    let (dp, _) = Simplex::patching_deltas(&Rational64::new(1, 2), &Rational64::new(1, 4))
        .expect("2 | 4 admits solutions");
    let v = Rational64::new(1, 2) + Rational64::new(1, 4) * Rational64::from_integer(dp);
    assert!(
        v.is_integer(),
        "δ={dp} must make the value integral, got {v}"
    );
    // α integral (no fractional part): the caller never asks, but the math
    // degrades to δ ≡ 0 (mod 1) — decline rather than fabricate.
    assert!(Simplex::patching_deltas(&Rational64::new(1, 2), &Rational64::one()).is_none());
}

#[test]
fn patch_int_columns_makes_fractional_basic_integral() {
    // The genuine patchable shape: after feasibility, the integer basic x
    // sits at -1/3 with row `x = -1/3 + (1/3)·t1 - (2/3)·y`; moving the
    // integer nonbasic y by -2 lands x on 1 — a pure value move, no
    // pivot, no row added (Z3 `patch_basic_columns`).
    let mut s = Simplex::new();
    let x = s.new_var();
    let y = s.new_var();
    s.set_lower(x, Rational64::from_integer(-4), 0);
    s.set_upper(x, Rational64::from_integer(4), 1);
    s.set_lower(y, Rational64::from_integer(-4), 2);
    s.set_upper(y, Rational64::from_integer(4), 3);
    // 3x + 2y + 1 <= 0 ; y <= 0
    let mut e1 = LinExpr::new();
    e1.terms.push((x, Rational64::from_integer(3)));
    e1.terms.push((y, Rational64::from_integer(2)));
    e1.constant = Rational64::one();
    let t1 = s.intern_row(e1);
    s.set_upper(t1, Rational64::zero(), 4);
    let mut e2 = LinExpr::new();
    e2.terms.push((y, Rational64::one()));
    let t2 = s.intern_row(e2);
    s.set_upper(t2, Rational64::zero(), 5);
    assert!(s.check().is_ok());
    // The LP point has x fractional (x = -1/3): patchable via y.
    assert!(!s.delta_value(x).real.is_integer());
    let done = s.patch_int_columns(&|v| v == x || v == y);
    assert!(done, "the point is patchable: y by -2 lands x on 1");
    let xv = s.delta_value(x).real;
    let yv = s.delta_value(y).real;
    assert!(xv.is_integer() && yv.is_integer());
    // The patched point satisfies the source row 3x + 2y + 1 <= 0.
    let row_val =
        Rational64::from_integer(3) * xv + Rational64::from_integer(2) * yv + Rational64::one();
    assert!(
        row_val <= Rational64::zero(),
        "patched point violates the row: {row_val}"
    );
}

#[test]
fn patch_int_columns_declines_and_rolls_back_when_blocked() {
    // Same shape, but y's window is pinned to {0} so both patching deltas
    // are blocked: the pass must decline and RESTORE the pre-patch point.
    let mut s = Simplex::new();
    let x = s.new_var();
    let y = s.new_var();
    s.set_lower(x, Rational64::from_integer(-4), 0);
    s.set_upper(x, Rational64::from_integer(4), 1);
    s.set_lower(y, Rational64::zero(), 2);
    s.set_upper(y, Rational64::zero(), 3);
    let mut e1 = LinExpr::new();
    e1.terms.push((x, Rational64::from_integer(3)));
    e1.terms.push((y, Rational64::from_integer(2)));
    e1.constant = Rational64::one();
    let t1 = s.intern_row(e1);
    s.set_upper(t1, Rational64::zero(), 4);
    assert!(s.check().is_ok());
    let before = s.delta_value(x).real;
    let done = s.patch_int_columns(&|v| v == x || v == y);
    assert!(!done, "y cannot move: no patch exists");
    assert_eq!(
        s.delta_value(x).real,
        before,
        "rollback must restore the point"
    );
}

#[test]
fn patch_int_columns_declines_without_fractional_int_coefficients() {
    // x's row carries only INTEGRAL coefficients on integer nonbasics
    // (2x + 2y + 1 <= 0, x - y <= 0): nothing to patch through — decline
    // with the fractional value preserved.
    let mut s = Simplex::new();
    let x = s.new_var();
    let y = s.new_var();
    s.set_lower(x, Rational64::from_integer(-4), 0);
    s.set_upper(x, Rational64::from_integer(4), 1);
    s.set_lower(y, Rational64::from_integer(-4), 2);
    s.set_upper(y, Rational64::from_integer(4), 3);
    let mut e1 = LinExpr::new();
    e1.terms.push((x, Rational64::from_integer(2)));
    e1.terms.push((y, Rational64::from_integer(2)));
    e1.constant = Rational64::one();
    let t1 = s.intern_row(e1);
    s.set_upper(t1, Rational64::zero(), 4);
    let mut e2 = LinExpr::new();
    e2.terms.push((x, Rational64::one()));
    e2.terms.push((y, Rational64::from_integer(-1)));
    let t2 = s.intern_row(e2);
    s.set_upper(t2, Rational64::zero(), 5);
    assert!(s.check().is_ok());
    let done = s.patch_int_columns(&|v| v == x || v == y);
    assert!(
        !done,
        "no fractional integer coefficient exists to patch through"
    );
    assert!(!s.delta_value(x).real.is_integer() || !s.delta_value(y).real.is_integer());
}

#[test]
fn patch_int_columns_declines_on_fractional_nonbasic() {
    // A fractional nonbasic integer column can never be repaired by an
    // integral move — the pass must decline immediately.
    let mut s = Simplex::new();
    let x = s.new_var();
    s.set_lower(x, Rational64::new(1, 2), 0);
    assert!(s.check().is_ok());
    let done = s.patch_int_columns(&|v| v == x);
    assert!(!done, "fractional nonbasic x = 1/2 must decline the pass");
}
// scratch debug appended as a test

// ===== gcd kernels: the power-of-two fast path and the u64-range cast =====

#[test]
fn gcd_u64_matches_reference_and_fast_paths() {
    fn refgcd(a: u64, b: u64) -> u64 {
        if b == 0 { a } else { refgcd(b, a % b) }
    }
    let interesting = [
        0u64,
        1,
        2,
        3,
        4,
        5,
        6,
        7,
        8,
        12,
        15,
        16,
        17,
        31,
        32,
        48,
        63,
        64,
        100,
        127,
        128,
        255,
        256,
        999,
        1000,
        1023,
        1024,
        4095,
        4096,
        32768,
        65535,
        65536,
        1 << 20,
        (1 << 20) + 1,
        1 << 30,
        (1 << 30) - 1,
        (1u64 << 40) + 3,
        (1u64 << 50) + 5,
        1 << 52,
        (1u64 << 62) + 7,
        1 << 63,
        u64::MAX,
        i64::MAX as u64,
        (i64::MAX as u64) + 1,
        u64::MAX - 1,
    ];
    for &a in &interesting {
        for &b in &interesting {
            assert_eq!(gcd_u64(a, b), refgcd(a, b), "gcd_u64({a}, {b})");
        }
    }
    // The i128 delegation's range corner: values in (i64::MAX, u64::MAX]
    // must not truncate through the 64-bit kernel (the wide-literal
    // regressions caught exactly this cast when the delegation went
    // through `as i64`).
    let big = (i64::MAX as u64) + 12345;
    let big128 = big as i128;
    assert_eq!(gcd_i128(big128, big128), big128);
    assert_eq!(gcd_i128(big128 * 2, big128), big128);
    assert_eq!(gcd_i128(1 << 100, 1 << 100), 1 << 100);
    assert_eq!(gcd_i128((1 << 100) * 3, 1 << 100), 1 << 100);
    assert_eq!(gcd_i128(0, -7), 7);
}

/// Deterministic LCG for the fraction-free equivalence grids (no `rand`
/// dependency; the grid must be reproducible exactly across runs — a
/// property failure's seed is only meaningful that way).
struct FfLcg(u64);
impl FfLcg {
    fn new(seed: u64) -> Self {
        Self(seed ^ 0x9E37_79B9_7F4A_7C15)
    }
    fn next(&mut self) -> u64 {
        self.0 = self
            .0
            .wrapping_mul(6364136223846793005)
            .wrapping_add(1442695040888963407);
        self.0 >> 11
    }
    fn below(&mut self, n: u64) -> u64 {
        self.next() % n.max(1)
    }
    fn signed_below(&mut self, n: u64) -> i64 {
        self.below(2 * n + 1) as i64 - n as i64
    }
}

/// One randomized coefficient shaped like the measured pivot
/// distribution: mostly small integers and small fractions, occasionally a
/// wide numerator/denominator pair (the post-cut determinant-ratio tail).
fn ff_random_rational(rng: &mut FfLcg) -> Rational64 {
    let class = rng.below(10);
    let (n, d) = match class {
        0..=3 => (rng.signed_below(4), 1), // small integers (0 drops)
        4..=6 => (rng.signed_below(9), 1 + rng.below(7) as i64), // small fractions
        7..=8 => (rng.signed_below(1 << 20), 1 + rng.below(1 << 12) as i64),
        _ => (
            rng.signed_below(1 << 40),
            (1 + rng.below(1 << 16) as i64) * (1 + rng.below(4) as i64),
        ),
    };
    if n == 0 {
        return Rational64::zero();
    }
    Rational64::new(n, d.max(1))
}

/// A random canonical row over `nvars` variables (merged, zero-free,
/// reduced — the tableau's stored shape).  Merges go through the crate's
/// CHECKED rational add (the generator's wide class can produce additions
/// that overflow `i64` intermediates — those terms are simply dropped, the
/// grid only needs rows the canonical store itself could hold).
fn ff_random_row(rng: &mut FfLcg, nvars: u32) -> LinExpr {
    let mut e = LinExpr::new();
    let nterms = 1 + rng.below(6) as usize;
    for _ in 0..nterms {
        let v = rng.below(nvars as u64) as VarId;
        let c = ff_random_rational(rng);
        if c.is_zero() {
            continue;
        }
        match e.terms.iter_mut().find(|(tv, _)| *tv == v) {
            Some((_, tc)) => {
                if let Some(sum) = checked_add_r64(*tc, c) {
                    *tc = sum;
                }
            }
            None => e.terms.push((v, c)),
        }
        e.terms.retain(|(_, c)| !c.is_zero());
    }
    if let Some(sum) = checked_add_r64(e.constant, ff_random_rational(rng)) {
        e.constant = sum;
    }
    e
}

/// The cached `IntRow` mirrors the canonical row: every per-term value
/// `n/D` equals the stored coefficient, and the joint gcd is 1 (the
/// minimal common denominator).  Returns false when the row is over budget
/// (the honest tail — callers keep the per-term path for those).
fn ff_encoding_is_faithful(row: &LinExpr) -> Option<bool> {
    let enc = int_row_from_lin(row)?;
    let d = enc.denom as i128;
    // Minimal common denominator: nothing but 1 divides everything.
    let mut g = d;
    for (_, n) in &enc.terms {
        g = gcd_i128(g, *n);
        if g == 1 {
            break;
        }
    }
    g = gcd_i128(g, enc.const_num);
    assert_eq!(g, 1, "joint gcd must be 1 (minimal common denominator)");
    assert!(enc.denom > 0, "denominator is positive");
    for (v, n) in &enc.terms {
        let canonical = row
            .terms
            .iter()
            .find(|(cv, _)| cv == v)
            .map(|(_, c)| c)
            .expect("encoding only names the row's variables");
        // n/D == canonical, compared exactly through i256-free cross
        // multiplication in i128 (budgeted operands make it safe).
        assert_eq!(
            n * *canonical.denom() as i128,
            *canonical.numer() as i128 * d,
            "value mismatch on term {v}"
        );
        assert!(n.unsigned_abs() <= 1 << 62, "numerator budget");
    }
    assert_eq!(
        enc.const_num * *row.constant.denom() as i128,
        *row.constant.numer() as i128 * d,
        "constant value mismatch"
    );
    Some(true)
}

/// The fraction-free substitution is BIT-IDENTICAL to the historical
/// per-term rational fast path — same canonical coefficient values, same
/// term ORDER (row order first, appended entering terms after), same
/// zero-term dropping — and its declines are exactly the rational path's
/// declines (a final that does not fit `Rational64` refuses in both; the
/// rational path can additionally decline on intermediate overflow, where
/// the integer path still succeeds).  This is what lets it share the pivot
/// without perturbing the search trajectory.
#[test]
fn substitute_row_ff_matches_rational_reference_seeded_grid() {
    let mut rng = FfLcg::new(0xFACADE01);
    let mut both = 0usize;
    let mut both_declined = 0usize;
    let mut skipped = 0usize; // over-budget encodings (the honest tail)
    for _ in 0..4000 {
        const NVARS: u32 = 8;
        let mut row = ff_random_row(&mut rng, NVARS);
        let mut entering = ff_random_row(&mut rng, NVARS);
        // The entering (solved-form) row never references the entering
        // variable itself.
        let entering_var: VarId = rng.below(NVARS as u64) as VarId;
        entering.terms.retain(|(v, _)| *v != entering_var);
        if entering.terms.is_empty() {
            entering.add_term((entering_var + 1) % NVARS, Rational64::from_integer(2));
        }
        // The substituted row must reference the entering variable with a
        // nonzero coefficient.
        if !row
            .terms
            .iter()
            .any(|(v, c)| *v == entering_var && !c.is_zero())
        {
            row.terms.retain(|(v, _)| *v != entering_var);
            row.add_term(
                entering_var,
                Rational64::from_integer(1 + rng.below(3) as i64),
            );
        }
        let sc = row
            .terms
            .iter()
            .find(|(v, _)| *v == entering_var)
            .map(|(_, c)| *c)
            .expect("entering term guaranteed above");
        if ff_encoding_is_faithful(&row).is_none() {
            skipped += 1;
        }
        let (Some(r_int), Some(e_int)) = (int_row_from_lin(&row), int_row_from_lin(&entering))
        else {
            skipped += 1;
            continue;
        };
        let n_e = r_int
            .numerator_of(entering_var)
            .expect("encoded row has the term");
        let ff = substitute_row_ff(&r_int, n_e, &e_int, entering_var);
        let reference = Simplex::substitute_row_fast(&row, sc, &entering, entering_var);
        match (ff, reference) {
            (Some(new_int), Some(ref_row)) => {
                both += 1;
                // The INTEGER path's product materializes to exactly the
                // rational reference (value-identity, order included — the
                // laziness contract).
                let lin = materialize_lin(&new_int);
                assert_eq!(lin.terms, ref_row.terms, "term vector (order included)");
                assert_eq!(lin.constant, ref_row.constant);
                // Round-trip: the materialized canonical re-encodes to the
                // same integer form (joint-canonical both ways).
                let re_enc = int_row_from_lin(&lin);
                assert_eq!(
                    re_enc.as_ref(),
                    Some(&new_int),
                    "materialize/encode round-trip is the identity"
                );
            }
            (Some(_), None) => panic!("integer path succeeded where rational refused"),
            // The integer path's decline (result numerators past
            // INT_ROW_BUDGET but within i64, or either input over
            // budget) is NOT an error: the caller falls back to the
            // rational paths and derives the same canonical row.
            (None, _) => both_declined += 1,
        }
    }
    assert!(
        both > 2500,
        "grid must exercise the both-succeed mass: {both}"
    );
    assert!(
        skipped + both_declined > 0,
        "grid should touch the decline tails too (skipped {skipped}, declined {both_declined})"
    );
}

/// The joint-reduction walk's DIVISION-FIRST step must produce the exact
/// same accumulated gcd as the naive `gcd(g, n)` chain (Euclid's identity:
/// `gcd(g, n) = n % g == 0 ? g : gcd(g, n % g)` for `g > 0`).  This pins
/// the identity on the walk's four measured shapes directly against a
/// reference naive chain computed in the test:
/// * stabilized `g` — every merged numerator divisible (the 93 %-shape);
/// * mid-walk residue — one numerator reduces `g`, the rest divide it;
/// * early exit — a coprime numerator drives `g` to 1 (no reduction);
/// * wide operands — values past `u64::MAX` take the `gcd_i128` walk.
#[test]
fn substitute_row_ff_division_first_walk_matches_naive_chain() {
    // `row` = (nums, c_r, d_r) carrying `entering_var` with numerator
    // `n_e`; `entering` = (ms, c_e, d_e).  The output must equal the raw
    // union-merge arithmetic reduced by a NAIVE gcd chain (the
    // pre-division-first code), computed independently here.
    let check = |nums: &[(VarId, i128)],
                 c_r: i128,
                 d_r: i64,
                 n_e: i128,
                 entering_var: VarId,
                 ms: &[(VarId, i128)],
                 c_e: i128,
                 d_e: i64| {
        let row = IntRow {
            terms: nums.iter().copied().collect(),
            const_num: c_r,
            denom: d_r,
        };
        let entering = IntRow {
            terms: ms.iter().copied().collect(),
            const_num: c_e,
            denom: d_e,
        };
        let got = substitute_row_ff(&row, n_e, &entering, entering_var)
            .expect("budget-sized inputs never decline");
        let mut ref_nums: Vec<(VarId, i128)> = Vec::new();
        for &(v, n_v) in nums {
            if v == entering_var {
                continue;
            }
            let m_v = ms
                .iter()
                .find(|(w, _)| *w == v)
                .map(|(_, m)| *m)
                .unwrap_or(0);
            let n = d_e as i128 * n_v + n_e * m_v;
            if n != 0 {
                ref_nums.push((v, n));
            }
        }
        for &(v, m_v) in ms {
            if !nums.iter().any(|(w, _)| *w == v) {
                ref_nums.push((v, n_e * m_v));
            }
        }
        let ref_const = d_e as i128 * c_r + n_e * c_e;
        let ref_d = d_r as i128 * d_e as i128;
        let mut g = gcd_i128(ref_d, ref_const);
        if g > 1 {
            for &(_, n) in &ref_nums {
                g = gcd_i128(g, n);
                if g == 1 {
                    break;
                }
            }
        }
        if g > 1 {
            assert_eq!(got.denom as i128, ref_d / g, "denominator");
            assert_eq!(got.const_num, ref_const / g, "constant");
            assert_eq!(
                got.terms.as_slice(),
                &ref_nums
                    .iter()
                    .map(|&(v, n)| (v, n / g))
                    .collect::<Vec<_>>()[..],
                "numerators"
            );
        } else {
            assert_eq!(got.denom as i128, ref_d, "denominator (unreduced)");
            assert_eq!(got.const_num, ref_const, "constant (unreduced)");
            assert_eq!(
                got.terms.as_slice(),
                &ref_nums[..],
                "numerators (unreduced)"
            );
        }
    };

    // Stabilized g: d = 4*9 = 36, c = 24 -> g0 = 12; every merged
    // numerator (240, 336, append 12) divisible by 12 — the r == 0 fast
    // case at every step.
    check(
        &[(1, 24), (2, 36), (7, 3)],
        0,
        4,
        3,
        7,
        &[(1, 8), (3, 4)],
        8,
        9,
    );

    // Mid-walk residue: 240 is divisible by g0 = 12, 255 leaves r = 3 and
    // reduces g to 3, the appended 12 is divisible by the reduced g.
    check(
        &[(1, 24), (2, 28), (7, 3)],
        0,
        4,
        3,
        7,
        &[(1, 8), (2, 1), (3, 4)],
        8,
        9,
    );

    // Early exit: g0 = gcd(72, 8) = 8; 216 divisible, 300 reduces g to 4,
    // the appended 15 is coprime with 4 -> g = 1, NO reduction.
    check(
        &[(1, 24), (2, 36), (7, 3)],
        1,
        9,
        3,
        7,
        &[(1, 8), (2, 4), (3, 5)],
        0,
        8,
    );

    // Wide operands: every merged value is a multiple of 2^80 past
    // u64::MAX, so the whole walk runs the gcd_i128 fallback.
    let w = 1i128 << 40;
    check(
        &[(1, 5 * w), (2, 7 * w), (7, w)],
        3 * w,
        w as i64,
        w,
        7,
        &[(1, 3 * w), (3, 11 * w)],
        w,
        (3 * w) as i64,
    );
}

/// Budget boundaries: a row whose joint form fits 2^62 encodes; one step
/// past it declines honestly (the per-term rational path owns that row).
#[test]
fn int_row_budget_boundaries() {
    // Denominator exactly at budget: 2^62 with numerator 1 fits.
    let at = Rational64::new(1, 1 << 62);
    let mut row = LinExpr::new();
    row.add_term(0, at);
    assert!(int_row_from_lin(&row).is_some());
    // One denominator step past budget declines.
    let past = Rational64::new(1, ((1u64 << 62) + 2).try_into().unwrap());
    let mut row2 = LinExpr::new();
    row2.add_term(0, past);
    assert!(int_row_from_lin(&row2).is_none());
    // A numerator at the budget edge encodes; past it declines.
    let mut row3 = LinExpr::new();
    row3.add_term(1, Rational64::from_integer(1 << 62));
    assert!(int_row_from_lin(&row3).is_some());
    let mut row4 = LinExpr::new();
    row4.add_term(1, Rational64::from_integer((1i64 << 62) + 1));
    assert!(int_row_from_lin(&row4).is_none());
    // Coprime denominators multiply in the lcm: 2^61 and 3·2^61 -> joint
    // 3·2^61 over budget, though each term alone fits.
    let mut row5 = LinExpr::new();
    row5.add_term(2, Rational64::new(1, 1 << 61));
    row5.add_term(3, Rational64::new(1, 3 * (1i64 << 61)));
    assert!(int_row_from_lin(&row5).is_none());
}

/// Cache coherence invariant: after a solving session with real pivots
/// (and a push/pop cycle), every fraction-free cache entry points at the
/// tableau's CURRENT row for its variable.  Pointer validation is the
/// soundness argument for reading cached encodings — this pins that the
/// maintenance sites (pivot commits, wide captures, migrations, resets)
/// actually leave it true.
#[test]
fn integer_tableau_rows_materialize_consistently_after_pivots() {
    // After a solving session with real pivots (and a push/pop cycle),
    // every integer-form row must materialize to a canonical row whose
    // value matches the assignment the search maintained (the laziness
    // contract: materialization is a pure function of the content, and
    // the churn mass leaves rows in Int form).
    let mut simplex = Simplex::new();
    let x = simplex.new_var();
    let y = simplex.new_var();
    let z = simplex.new_var();
    simplex.set_lower(x, Rational64::zero(), 0);
    simplex.set_lower(y, Rational64::zero(), 1);
    simplex.set_lower(z, Rational64::zero(), 2);
    simplex.set_upper(x, Rational64::from_integer(6), 3);
    simplex.set_upper(y, Rational64::from_integer(6), 4);
    let mut e1 = LinExpr::new();
    e1.add_term(x, Rational64::from_integer(2));
    e1.add_term(y, Rational64::new(-3, 2));
    e1.add_constant(Rational64::from_integer(1));
    simplex.add_eq(e1, 10);
    let mut e2 = LinExpr::new();
    e2.add_term(y, Rational64::new(4, 3));
    e2.add_term(z, Rational64::from_integer(5));
    e2.add_constant(Rational64::from_integer(-2));
    simplex.add_eq(e2, 11);
    let mut e3 = LinExpr::new();
    e3.add_term(x, Rational64::from_integer(3));
    e3.add_term(z, Rational64::from_integer(-2));
    e3.add_constant(Rational64::from_integer(7));
    simplex.add_le(e3, 12);
    simplex.push();
    simplex.set_lower(x, Rational64::from_integer(1), 13);
    simplex.set_upper(z, Rational64::new(7, 2), 14);
    let _ = simplex.check();
    simplex.pop();
    let _ = simplex.check();
    let mut int_rows = 0usize;
    let keys: Vec<VarId> = simplex.tableau.keys().copied().collect();
    for var in keys {
        if !matches!(simplex.tableau.get(&var), Some(TableRow::Int(_))) {
            continue;
        }
        int_rows += 1;
        // Materialize and verify: the row evaluates (over the current
        // assignment) to the basic's own assignment value — the invariant
        // the delta propagation maintained.
        let lin = simplex.row_lin(var).expect("row exists");
        let vi = var as usize;
        let want = simplex.eval_expr(&lin);
        let got = simplex.assignment.get(vi).copied();
        if let (Some(w), Some(g)) = (want, got) {
            assert_eq!(w, g, "materialized row {var} disagrees with the assignment");
        }
    }
    assert!(
        int_rows >= 1,
        "session must have left integer-form rows: {int_rows}"
    );
}

/// The born-integer entering row is value-identical to the historical
/// `build_pivot_expr` solved form (Phase 3's equivalence: materializing
/// the born row yields exactly the canonical solved form, term order
/// included).
#[test]
fn born_entering_row_matches_the_canonical_solved_form() {
    let mut rng = FfLcg::new(0xB0D0_5EED);
    let mut checked = 0usize;
    let mut skipped = 0usize;
    for _ in 0..2000 {
        const NVARS: u32 = 6;
        let mut row = ff_random_row(&mut rng, NVARS);
        let entering_var: VarId = rng.below(NVARS as u64) as VarId;
        if !row
            .terms
            .iter()
            .any(|(v, c)| *v == entering_var && !c.is_zero())
        {
            row.terms.retain(|(v, _)| *v != entering_var);
            row.add_term(
                entering_var,
                Rational64::from_integer(1 + rng.below(4) as i64),
            );
        }
        let Some(leaving_int) = int_row_from_lin(&row) else {
            skipped += 1;
            continue;
        };
        let Some(n_e) = leaving_int.numerator_of(entering_var) else {
            skipped += 1;
            continue;
        };
        let born = born_entering_row(&leaving_int, n_e, 99, entering_var);
        // The reference: the historical solve over the materialized row.
        let lin = materialize_lin(&leaving_int);
        let coef = lin
            .terms
            .iter()
            .find(|(v, _)| *v == entering_var)
            .map(|(_, c)| *c)
            .expect("entering term present");
        let Some(reference) = Simplex::build_pivot_expr(&lin, coef, 99, entering_var)
            .or_else(|| Simplex::build_pivot_expr_exact(&lin, coef, 99, entering_var))
        else {
            skipped += 1;
            continue;
        };
        let born_lin = materialize_lin(&born);
        assert_eq!(
            born_lin.terms, reference.terms,
            "term vector (order included)"
        );
        assert_eq!(born_lin.constant, reference.constant);
        checked += 1;
    }
    assert!(
        checked > 1500,
        "grid must exercise the mass: {checked} (skipped {skipped})"
    );
    // `skipped` cases (degenerate rows) are expected to be a small
    // minority; pin that so the mass assertion cannot silently degrade
    // and the counter stays read (no dead bookkeeping).
    assert!(
        checked + skipped >= 2000,
        "every iteration must be accounted: {checked} checked, {skipped} skipped"
    );
}

// Regression (2026-09-21, the simplex pivot-cap/resource-limit family):
// a NON-BASIC resting at one of its current bounds — here its UPPER, parked
// by a tighten-then-loosen bound sequence — must keep its value through
// every re-derivation.  The historical `crash_basis` AND
// `update_assignment` entry loops re-snapped such a variable to the
// PREFERRED (lower) bound, silently relocating the search point: each wide
// repair that parked a leaving variable at its upper bound was un-done one
// re-derivation later (the update_assignment loop sits one call deeper
// than crash_basis, so fixing crash alone changed nothing), and the
// wide-repair loop orbited a period-2 limit cycle until the repair budget
// or the pivot cap declined the check (the `simplex-tail-i129` class).
// Z3's `lp_primal_core_solver` never re-preferences a positioned column.
#[test]
fn rederivation_preserves_nonbasic_parked_at_upper_bound() {
    let mut s = Simplex::new();
    let x = s.new_var();
    let y = s.new_var();

    // y fixed at 7; x window [0, 10].
    s.set_lower(y, Rational64::from_integer(7), 1);
    s.set_upper(y, Rational64::from_integer(7), 2);
    s.set_lower(x, Rational64::zero(), 3);
    s.set_upper(x, Rational64::from_integer(10), 4);

    // Park x (non-basic) at its UPPER bound: tighten the lower to 10 (the
    // bound writer snaps x onto it), then loosen the lower back to 0 — the
    // value 10 stays inside the window, so no re-snap fires, and x rests at
    // its upper bound exactly the way a repair's leaving snap would have
    // left it.
    s.push();
    s.set_lower(x, Rational64::from_integer(10), 5);
    s.set_lower(x, Rational64::zero(), 6);
    s.pop();

    // A slack row over the support makes the re-derivation real work.
    let mut e = LinExpr::new();
    e.terms.push((x, Rational64::from_integer(1)));
    e.terms.push((y, Rational64::from_integer(1)));
    e.constant = Rational64::from_integer(-17);
    let r = s.intern_row(e);
    s.set_lower(r, Rational64::zero(), 7);
    assert!(s.check().is_ok(), "x = 10 with y = 7 satisfies the row");
    assert_eq!(
        s.delta_value(x).real,
        Rational64::from_integer(10),
        "x rests at its upper bound after the parked check"
    );

    // The pinned contract, tested where it lives: the re-derivation entry
    // loops (both crash_basis's and update_assignment's) must not relocate
    // a positioned non-basic.  The historical code moved x to its
    // lower-preferred bound 0 here.
    s.assignment_current = false;
    s.update_assignment();
    assert_eq!(
        s.delta_value(x).real,
        Rational64::from_integer(10),
        "update_assignment must preserve a non-basic resting at its upper bound"
    );
    s.crash_basis();
    assert_eq!(
        s.delta_value(x).real,
        Rational64::from_integer(10),
        "crash_basis must preserve a non-basic resting at its upper bound"
    );
    // And the row over the preserved point stays satisfied.
    assert_eq!(
        s.delta_value(r).real,
        Rational64::zero(),
        "the row over the preserved point stays at its bound"
    );
}

// The same contract on the WIDE side: a non-basic whose exact point lives
// in the wide point store, resting at a wide bound, is preserved too (the
// `cmp_big` arm of `nonbasic_rests_at_bound`).
#[test]
fn rederivation_preserves_wide_point_at_wide_bound() {
    use crate::arithmetic::delta::BigDeltaRational;
    let mut s = Simplex::new();
    let x = s.new_var();
    // A lower bound beyond i64 width (2^63 + 5) parks x in the wide point
    // store at its (only, wide) bound.  A non-empty reason vector is
    // required: `set_lower_value` treats an empty one as a no-op.
    let wide_lo = num_rational::BigRational::from(
        num_bigint::BigInt::from(2).pow(63) + num_bigint::BigInt::from(5),
    );
    s.set_lower_exact(
        x,
        BigDeltaRational {
            real: wide_lo.clone(),
            delta: num_rational::BigRational::zero(),
        },
        smallvec::smallvec![0],
    );
    let parked = s.wide_points.get(&x).cloned();
    assert_eq!(
        parked.as_ref().map(|w| &w.real),
        Some(&wide_lo),
        "the wide bound writer parks x at its wide lower bound"
    );

    // The re-derivation loops must keep the wide point (the historical
    // lower-preferred re-snap here re-ran `snap_point_to` on every
    // re-derivation, churning the store; the preserve rule must hold on
    // the `cmp_big` path).
    s.assignment_current = false;
    s.update_assignment();
    s.crash_basis();
    let after = s.wide_points.get(&x).cloned();
    assert_eq!(
        after.as_ref().map(|w| &w.real),
        Some(&wide_lo),
        "the wide point at the wide bound survives the re-derivation"
    );
}

// The evaluation fast paths must preserve both exact values and the old
// checked-trait failure boundary: a changed None can alter a search trajectory.
#[test]
fn checked_integer_evaluation_matches_traits_and_big_rationals() {
    let mut values: Vec<i64> = (-32..=32).collect();
    values.extend([i64::MIN, i64::MIN + 1, i64::MAX - 1, i64::MAX, 1 << 32]);
    for &a in &values {
        for &b in &values {
            let ar = Rational64::from_integer(a);
            let br = Rational64::from_integer(b);
            let product = checked_eval_mul(&ar, &br);
            let sum = checked_eval_add(&ar, &br);
            assert_eq!(product, num_traits::CheckedMul::checked_mul(&ar, &br));
            assert_eq!(sum, num_traits::CheckedAdd::checked_add(&ar, &br));
            assert_eq!(product, narrow_big_r64(&(big_r64(&ar) * big_r64(&br))));
            assert_eq!(sum, narrow_big_r64(&(big_r64(&ar) + big_r64(&br))));
            for result in [product, sum].into_iter().flatten() {
                assert_eq!(*result.denom(), 1);
            }
        }
    }
}

#[test]
fn fractional_evaluation_preserves_checked_failure_boundary() {
    let mut values = Vec::new();
    for n in [-i64::MAX, -17, -1, 0, 1, 17, i64::MAX] {
        for d in [1, 2, 3, 17, i64::MAX] {
            values.push(Rational64::new(n, d));
        }
    }
    for a in &values {
        for b in &values {
            assert_eq!(
                checked_eval_mul(a, b),
                num_traits::CheckedMul::checked_mul(a, b)
            );
            assert_eq!(
                checked_eval_add(a, b),
                num_traits::CheckedAdd::checked_add(a, b)
            );
            if let Some(p) = checked_eval_mul(a, b) {
                assert_eq!(big_r64(&p), big_r64(a) * big_r64(b));
            }
            if let Some(s) = checked_eval_add(a, b) {
                assert_eq!(big_r64(&s), big_r64(a) + big_r64(b));
            }
        }
    }
    // The reduced sum fits, but the legacy trait rejects its intermediate.
    // Keep the rejection so the existing exact row retry stays responsible.
    let a = Rational64::new(i64::MAX, 2);
    assert_eq!(
        narrow_big_r64(&(big_r64(&a) + big_r64(&a))),
        Some(Rational64::from_integer(i64::MAX))
    );
    assert_eq!(checked_eval_add(&a, &a), None);
}

#[test]
fn delta_evaluation_keeps_overflow_and_partial_accumulation_contract() {
    let values = [
        DeltaRational::from(0),
        DeltaRational::from(i64::MIN),
        DeltaRational::from(i64::MAX),
        DeltaRational {
            real: Rational64::from_integer(1),
            delta: Rational64::from_integer(i64::MAX),
        },
        DeltaRational {
            real: Rational64::new(1, 3),
            delta: Rational64::new(-1, 2),
        },
    ];
    for initial in values {
        for value in values {
            for c in [-2, -1, 0, 1, 2] {
                let coef = Rational64::from_integer(c);
                let mut expected = initial;
                let legacy = (|| -> Option<()> {
                    let pr = num_traits::CheckedMul::checked_mul(&value.real, &coef)?;
                    let pd = num_traits::CheckedMul::checked_mul(&value.delta, &coef)?;
                    expected.real = num_traits::CheckedAdd::checked_add(&expected.real, &pr)?;
                    expected.delta = num_traits::CheckedAdd::checked_add(&expected.delta, &pd)?;
                    Some(())
                })();
                let mut actual = initial;
                assert_eq!(Simplex::delta_acc(&mut actual, &value, &coef), legacy);
                assert_eq!(actual, expected);
            }
        }
    }
}
