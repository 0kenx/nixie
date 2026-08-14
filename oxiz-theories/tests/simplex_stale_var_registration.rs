//! Regression tests for a P1 crash: `index out of bounds` in the Simplex
//! tableau when a variable index is handed to it without the per-variable
//! parallel arrays (`assignment`/`lower`/`upper`/`basic`) having been grown
//! for that index.
//!
//! Origin: a UFLRA problem with nested uninterpreted functions over reals,
//! solved through MBQI, backtracks (pops) the arithmetic context. A caller
//! that caches term -> variable-index mappings can then *replay* a variable
//! index that was created at a deeper level and has since been removed by the
//! pop – i.e. an index that now lies past the end of the bounds arrays. The
//! original benchmark (`bench/z3_parity/benchmarks/UFLRA/real_composition.smt2`)
//! panicked at `simplex/mod.rs` inside `can_increase` with
//! `index out of bounds: the len is N but the index is N`.
//!
//! The fix routes every variable-index-introducing code path
//! (`add_le`/`add_ge`/`add_strict_*` and every `set_lower`/`set_upper`
//! variant) through a central `ensure_var`, which grows all four parallel
//! arrays in lockstep with pop-safe undo records. These tests exercise the
//! Simplex directly at that boundary, since the panic is an internal
//! invariant of the tableau rather than a specific SMT logic.

use num_rational::Rational64;
use oxiz_theories::arithmetic::{LinExpr, Simplex};

fn int(n: i64) -> Rational64 {
    Rational64::from_integer(n)
}

/// A constraint that references a variable index far beyond the currently
/// allocated slots (as a stale, replayed index would) must not panic and must
/// yield the correct feasibility verdict.
///
/// `x5 >= 10` with `x5` never registered: the tableau row for the constraint's
/// slack references index 5 while no bounds slot exists for it. Before the fix
/// this indexed past `upper`/`assignment` during pricing and panicked. The
/// constraint is feasible (`x5` is unconstrained above), so `check` must
/// return `Ok`.
#[test]
fn add_ge_with_unregistered_variable_index_does_not_panic() {
    let mut simplex = Simplex::new();
    // No `new_var` calls at all: the arrays are empty, yet we reference index 5.
    let mut expr = LinExpr::new();
    expr.add_term(5, int(1));
    expr.add_constant(-int(10)); // x5 - 10 >= 0  <=>  x5 >= 10
    simplex.add_ge(expr, 0);

    // Must not panic; the system is satisfiable.
    assert!(
        simplex.check().is_ok(),
        "x5 >= 10 is feasible for an unconstrained x5"
    );
    // The pivot should have driven x5 up to its bound.
    assert!(simplex.value(5) >= int(10), "x5 must satisfy x5 >= 10");
}

/// Exercises the pricing path (`find_pivot_col` / `can_increase`) with an
/// out-of-range variable in an *infeasible* starting row, and – crucially –
/// verifies the constraint is actually *enforced* rather than silently dropped.
///
/// A registered variable `x0` is pinned to `x0 <= 0`, while `x0 + x_stale >= 10`
/// makes the constraint's slack infeasible at the start; the only way to
/// satisfy it is to raise the unregistered `x_stale`. Without the fix the row
/// referenced an index past `upper` (either panicking in `can_increase`, or –
/// via the `update_assignment` stale-ref guard – being dropped so `x_stale`
/// stayed 0). The value assertion catches the dropped-constraint case that a
/// bare "returns Ok" check would miss.
#[test]
fn infeasible_row_with_out_of_range_variable_prices_without_panic() {
    let mut simplex = Simplex::new();
    let x0 = simplex.new_var();
    simplex.set_upper(x0, int(0), 0); // x0 <= 0

    let mut expr = LinExpr::new();
    expr.add_term(x0, int(1));
    expr.add_term(7, int(1)); // index 7: never registered
    expr.add_constant(-int(10)); // x0 + x7 - 10 >= 0
    simplex.add_ge(expr, 1);

    assert!(
        simplex.check().is_ok(),
        "x0 <= 0 and x0 + x7 >= 10 is feasible (raise x7)"
    );
    // The constraint must genuinely hold: with x0 <= 0, x7 has to reach >= 10.
    // A silently dropped constraint would leave x7 at 0.
    assert!(
        simplex.value(7) + simplex.value(x0) >= int(10),
        "x0 + x7 >= 10 must be enforced, not dropped"
    );
}

/// The same for `add_le` / the substitution path, with an intervening gap in
/// the index space (index 8 while nothing is allocated), so `ensure_var` must
/// materialize several slots contiguously, not just one.
#[test]
fn add_le_with_gapped_unregistered_index_does_not_panic() {
    let mut simplex = Simplex::new();
    let mut expr = LinExpr::new();
    expr.add_term(8, int(1));
    expr.add_constant(-int(3)); // x8 - 3 <= 0  <=>  x8 <= 3
    simplex.add_le(expr, 0);

    assert!(simplex.check().is_ok(), "x8 <= 3 is feasible");
}

/// The bound setters must *apply* a bound on an unregistered index rather than
/// silently dropping it. Two contradictory bounds on a never-registered
/// variable must be detected as infeasible; before the fix the `if idx < len`
/// guards dropped both bounds and the solver wrongly reported feasibility.
#[test]
fn contradictory_bounds_on_unregistered_index_are_not_dropped() {
    let mut simplex = Simplex::new();
    // Variable index 10, never created via `new_var`.
    simplex.set_lower(10, int(5), 0); // x10 >= 5
    simplex.set_upper(10, int(3), 1); // x10 <= 3   (5 > 3 => infeasible)

    assert!(
        simplex.check().is_err(),
        "x10 in [5, 3] is infeasible; the bounds must not be silently dropped"
    );
}

/// End-to-end mirror of the MBQI backtrack path that produced the crash:
/// allocate variables, `push`, grow more variables through a constraint,
/// `pop` (which shrinks the arrays back), then replay a constraint that
/// references an index which existed only at the deeper level. The replayed
/// index now sits past the end of the shrunken arrays.
#[test]
fn replayed_index_after_pop_does_not_panic() {
    let mut simplex = Simplex::new();
    let x0 = simplex.new_var();
    let x1 = simplex.new_var();
    simplex.set_lower(x0, int(0), 0);
    simplex.set_upper(x1, int(100), 1);

    simplex.push();
    // Deeper level: create additional variables and a constraint whose slack
    // pushes the allocated length up (these get removed on pop).
    let x2 = simplex.new_var();
    let mut deep = LinExpr::new();
    deep.add_term(x2, int(1));
    deep.add_constant(-int(5));
    simplex.add_le(deep, 2); // allocates a slack beyond x2
    assert!(simplex.check().is_ok());
    simplex.pop(); // arrays shrink back to the shallow level

    // Replay a "stale" index that only existed at the deeper level (x2 and its
    // slack were 2 and 3; both are now gone). Referencing index 3 must grow the
    // arrays rather than index past them.
    let mut replay = LinExpr::new();
    replay.add_term(3, int(1));
    replay.add_constant(-int(7)); // x3 >= 7
    simplex.add_ge(replay, 3);

    assert!(
        simplex.check().is_ok(),
        "replaying a stale index must not panic and stays feasible"
    );
}

/// After growing via a replayed/stale index, a subsequent `pop` must still
/// leave the arrays internally consistent (all four parallel arrays the same
/// length) so later solving does not panic. We drive several push/pop rounds
/// with stale-index constraints interleaved.
#[test]
fn push_pop_rounds_with_stale_indices_stay_consistent() {
    let mut simplex = Simplex::new();
    let _x0 = simplex.new_var();

    for round in 0..5u32 {
        simplex.push();
        // Reference an ever-larger index that was never explicitly registered.
        let idx = 10 + round * 3;
        let mut e = LinExpr::new();
        e.add_term(idx, int(1));
        e.add_constant(-int(2));
        simplex.add_ge(e, round);
        assert!(simplex.check().is_ok(), "round {round} must be feasible");
        simplex.pop();
        // After the pop the solver must remain usable.
        assert!(simplex.check().is_ok(), "post-pop check for round {round}");
    }
}
