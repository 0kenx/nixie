//! Unit tests for the shared certifier entry point and the integer engine.
//!
//! Every test states a goal at term level and asks for a verdict.  The
//! positive ones pin capabilities the certifier must keep; the negative ones
//! pin the far more important property that it declines rather than guesses.

use nixie_core::ast::{TermId, TermManager};
use nixie_core::sort::SortId;

#[allow(unused_imports)]
use crate::prelude::*;

use super::certify;

/// A goal builder over `Int`.
struct IntGoal {
    manager: TermManager,
}

impl IntGoal {
    fn new() -> Self {
        Self {
            manager: TermManager::new(),
        }
    }

    fn sort(&self) -> SortId {
        self.manager.sorts.int_sort
    }

    fn lit(&mut self, value: i64) -> TermId {
        self.manager.mk_int(value)
    }

    fn var(&mut self, name: &str) -> TermId {
        let sort = self.sort();
        self.manager.mk_var(name, sort)
    }

    fn app(&mut self, name: &str, arg: TermId) -> TermId {
        let sort = self.sort();
        self.manager.mk_apply(name, [arg], sort)
    }
}

/// `forall x. f(f(x)) = f(x)` with pins that force a non-zero default: the
/// integer engine searches defaults instead of assuming one.
#[test]
fn idempotent_function_is_certified() {
    let mut goal = IntGoal::new();
    let int = goal.sort();
    let x = goal.var("x");
    let fx = goal.app("f", x);
    let ffx = goal.app("f", fx);
    let body = goal.manager.mk_eq(ffx, fx);
    let quantified = goal.manager.mk_forall([("x", int)], body);

    let zero = goal.lit(0);
    let five = goal.lit(5);
    let f_zero = goal.app("f", zero);
    let f_five = goal.app("f", five);
    let pin_a = goal.manager.mk_eq(f_zero, five);
    let pin_b = goal.manager.mk_eq(f_five, five);

    let mut model: FxHashMap<TermId, TermId> = FxHashMap::default();
    model.insert(f_zero, five);
    model.insert(f_five, five);

    let assertions = vec![quantified, pin_a, pin_b];
    assert!(certify(&assertions, &model, &goal.manager));
}

/// The same goal with a pin that breaks idempotence has no model.
#[test]
fn broken_idempotence_is_not_certified() {
    let mut goal = IntGoal::new();
    let int = goal.sort();
    let x = goal.var("x");
    let fx = goal.app("f", x);
    let ffx = goal.app("f", fx);
    let body = goal.manager.mk_eq(ffx, fx);
    let quantified = goal.manager.mk_forall([("x", int)], body);

    let zero = goal.lit(0);
    let five = goal.lit(5);
    let seven = goal.lit(7);
    let f_zero = goal.app("f", zero);
    let f_five = goal.app("f", five);
    let pin_a = goal.manager.mk_eq(f_zero, five);
    let pin_b = goal.manager.mk_eq(f_five, seven);

    let mut model: FxHashMap<TermId, TermId> = FxHashMap::default();
    model.insert(f_zero, five);
    model.insert(f_five, seven);

    let assertions = vec![quantified, pin_a, pin_b];
    assert!(!certify(&assertions, &model, &goal.manager));
}

/// A quantifier-free goal is the ground solver's business.
#[test]
fn quantifier_free_goal_is_declined() {
    // Ground goals are no longer blanket-declined: the big-constant `sat`
    // honesty gate certifies them by evaluating the assertions under the
    // recorded model (`certify`'s enumeration degenerates to one exhaustive
    // pass when there is nothing to enumerate).  What still declines is a
    // ground goal whose pinned model CONTRADICTS it — the certification
    // question, not a sat question.
    let mut goal = IntGoal::new();
    let zero = goal.lit(0);
    let one = goal.lit(1);
    let f_zero = goal.app("f", zero);
    let assertion = goal.manager.mk_eq(f_zero, zero);
    // Pin f(0) = 1 in the "model"; `(= (f 0) 0)` is false under it.
    let mut assignments = FxHashMap::default();
    assignments.insert(f_zero, one);
    assert!(!certify(&[assertion], &assignments, &goal.manager));
    // ...and the same pin the other way round certifies.
    let mut ok = FxHashMap::default();
    ok.insert(f_zero, zero);
    assert!(certify(&[assertion], &ok, &goal.manager));
}

/// An unsatisfiable universal must not certify however the default is chosen.
#[test]
fn unsatisfiable_universal_is_not_certified() {
    let mut goal = IntGoal::new();
    let int = goal.sort();
    let x = goal.var("x");
    let fx = goal.app("f", x);
    let zero = goal.lit(0);
    let one = goal.lit(1);
    let low = goal.manager.mk_eq(fx, zero);
    let high = goal.manager.mk_eq(fx, one);
    let body = goal.manager.mk_and([low, high]);
    let quantified = goal.manager.mk_forall([("x", int)], body);
    assert!(!certify(
        &[quantified],
        &FxHashMap::default(),
        &goal.manager
    ));
}

/// A goal outside both fragments – here a bit-vector – declines in both
/// engines, so the caller keeps its `unknown`.
#[test]
fn foreign_sort_is_declined_by_both_engines() {
    let mut manager = TermManager::new();
    let bv = manager.sorts.bitvec(8);
    let x = manager.mk_var("x", bv);
    let fx = manager.mk_apply("f", [x], bv);
    let body = manager.mk_eq(fx, x);
    let quantified = manager.mk_forall([("x", bv)], body);
    assert!(!certify(&[quantified], &FxHashMap::default(), &manager));
}

/// A real goal never reaches the integer engine: `Int` and `Real` goals are
/// disjoint, so each verdict rests on one completeness argument.
#[test]
fn real_goal_is_refused_by_the_integer_engine() {
    let mut manager = TermManager::new();
    let real = manager.sorts.real_sort;
    let x = manager.mk_var("x", real);
    let fx = manager.mk_apply("f", [x], real);
    let body = manager.mk_eq(fx, x);
    let quantified = manager.mk_forall([("x", real)], body);
    assert!(super::prepare(&[quantified], &FxHashMap::default(), &manager).is_none());
}

/// A ground goal mixing `Int` and `Real` values with Real literals
/// (`2.5`-shaped `RealConst`) certifies: the ground path evaluates every
/// assertion exactly under the model (`Int` promoted to `BigRational`), and
/// a model that satisfies the assertions is accepted.
///
/// Pins the ground-certification widening (2026-09-17): mixed LIRA goals
/// carrying a Real literal used to be declined by `harvest`'s vocabulary
/// (no `RealConst` arm), so a `sat` verdict over the big-constant
/// abstraction could never publish — `unknown` on a decidable goal.
#[test]
fn ground_mixed_real_arithmetic_certifies() {
    let mut manager = TermManager::new();
    let real = manager.sorts.real_sort;
    let int = manager.sorts.int_sort;
    let xr = manager.mk_var("xr", real);
    let xi = manager.mk_var("xi", int);
    // (* xr (/ 1 2)) with a symbolic dividend keeps the Mul shape; the
    // literals fold at construction.
    let half = manager.mk_real(num_rational::Rational64::new(1, 2));
    let lhs = manager.mk_mul([xr, half]);
    let rhs = manager.mk_real(num_rational::Rational64::new(3, 4));
    let atom = manager.mk_lt(lhs, rhs);
    // A model xr = 1, xi = 0 satisfies `xr/2 < 3/4`.
    let mut model: FxHashMap<TermId, TermId> = FxHashMap::default();
    model.insert(xr, manager.mk_real(num_rational::Rational64::from(1)));
    model.insert(xi, manager.mk_int(0));
    assert!(certify(&[atom], &model, &manager));
    // A model that contradicts the atom must not certify.
    let mut bad: FxHashMap<TermId, TermId> = FxHashMap::default();
    bad.insert(xr, manager.mk_real(num_rational::Rational64::new(3, 2)));
    bad.insert(xi, manager.mk_int(0));
    assert!(!certify(&[atom], &bad, &manager));
}

/// A Real-sorted `Div` over Int-valued operands evaluates to the exact
/// RATIONAL quotient — `(/ 7 2)` is `7/2`, never the Euclidean floor `3`.
///
/// The evaluator decides by the node's SORT, not by the operand value types:
/// dispatching on values floored every real quotient whose operands happened
/// to carry integer model values. (End-to-end goals reach the certifier only
/// through paths that gate such atoms first; this unit pins the evaluator's
/// own semantics.)
#[test]
fn ground_real_division_is_exact_not_floored() {
    let mut manager = TermManager::new();
    let int = manager.sorts.int_sort;
    let xi = manager.mk_var("xi", int);
    let yi = manager.mk_var("yi", int);
    let quotient = manager.mk_rdiv(xi, yi); // Real-sorted Div node
    assert_eq!(manager.get(quotient).unwrap().sort, manager.sorts.real_sort);
    // (= (/ xi yi) (/ 7 2)) with xi = 7, yi = 2 is TRUE.
    let seven_halves = manager.mk_real(num_rational::Rational64::new(7, 2));
    let eq_exact = manager.mk_eq(quotient, seven_halves);
    // (= (/ xi yi) 3) is FALSE — 7/2 is not 3, and not the floor 3 either.
    let three = manager.mk_int(3);
    let eq_floor = manager.mk_eq(quotient, three);
    let mut model: FxHashMap<TermId, TermId> = FxHashMap::default();
    model.insert(xi, manager.mk_int(7));
    model.insert(yi, manager.mk_int(2));
    assert!(certify(&[eq_exact], &model, &manager));
    assert!(!certify(&[eq_floor], &model, &manager));
    // Mixed comparison against the exact quotient: 3 < 7/2 holds, 4 < 7/2
    // does not.
    let three = manager.mk_int(3);
    let four = manager.mk_int(4);
    let lt_true = manager.mk_lt(three, quotient);
    let lt_false = manager.mk_lt(four, quotient);
    assert!(certify(&[lt_true], &model, &manager));
    assert!(!certify(&[lt_false], &model, &manager));
}

/// Quantified goals carrying a Real literal or a Real-sorted free constant
/// still decline at `prepare`: the region/critical-set argument the integer
/// engine's exhaustive domain rests on is written for `Int`, and a Real
/// value shifts atoms' crossing points off the critical set — an enumeration
/// over it would not be exhaustive, so no certification may rest on it.
#[test]
fn quantified_goal_with_real_values_still_declines() {
    let mut manager = TermManager::new();
    let int = manager.sorts.int_sort;
    let real = manager.sorts.real_sort;
    // forall yi. yi < 2.5 — a Real literal under a quantifier.
    let yi = manager.mk_var("yi", int);
    let two_five = manager.mk_real(num_rational::Rational64::new(5, 2));
    let body_lit = manager.mk_lt(yi, two_five);
    let q_lit = manager.mk_forall([("yi", int)], body_lit);
    assert!(super::prepare(&[q_lit], &FxHashMap::default(), &manager).is_none());
    // forall yi. yi < xr — a Real-sorted free constant under a quantifier.
    let xr = manager.mk_var("xr", real);
    let body_var = manager.mk_lt(yi, xr);
    let q_var = manager.mk_forall([("yi", int)], body_var);
    assert!(super::prepare(&[q_var], &FxHashMap::default(), &manager).is_none());
}
