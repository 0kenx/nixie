//! Unit tests for the real certifier, driven through term-level goals.

use num_bigint::BigInt;
use num_rational::Rational64;
use oxiz_core::ast::{TermId, TermManager};

#[allow(unused_imports)]
use crate::prelude::*;

use super::affine::Rat;
use super::synth::{affine_in, detect_macros};
use super::{certify, harvest};

/// A goal builder: a term manager plus the sorts the fragment uses.
struct Goal {
    manager: TermManager,
}

impl Goal {
    fn new() -> Self {
        Self {
            manager: TermManager::new(),
        }
    }

    fn real_sort(&self) -> oxiz_core::sort::SortId {
        self.manager.sorts.real_sort
    }

    fn lit(&mut self, numer: i64, denom: i64) -> TermId {
        self.manager.mk_real(Rational64::new(numer, denom))
    }

    fn var(&mut self, name: &str) -> TermId {
        let sort = self.real_sort();
        self.manager.mk_var(name, sort)
    }

    fn app(&mut self, name: &str, arg: TermId) -> TermId {
        let sort = self.real_sort();
        self.manager.mk_apply(name, [arg], sort)
    }
}

fn rat(numer: i64, denom: i64) -> Rat {
    Rat::new(BigInt::from(numer), BigInt::from(denom))
}

/// `forall x. f(x) = x` with pins that agree: certified by the identity
/// default, which no pins-plus-constant interpretation could supply.
#[test]
fn identity_function_is_certified() {
    let mut goal = Goal::new();
    let real = goal.real_sort();
    let x = goal.var("x");
    let fx = goal.app("f", x);
    let body = goal.manager.mk_eq(fx, x);
    let quantified = goal.manager.mk_forall([("x", real)], body);

    let pi = goal.lit(157, 50);
    let f_pi = goal.app("f", pi);
    let pin = goal.manager.mk_eq(f_pi, pi);

    let assertions = vec![quantified, pin];
    assert!(certify(&assertions, &FxHashMap::default(), &goal.manager));
}

/// The same goal with a pin that contradicts the quantifier must *not*
/// certify — the pin is verified, not assumed away.
#[test]
fn contradictory_pin_is_not_certified() {
    let mut goal = Goal::new();
    let real = goal.real_sort();
    let x = goal.var("x");
    let fx = goal.app("f", x);
    let body = goal.manager.mk_eq(fx, x);
    let quantified = goal.manager.mk_forall([("x", real)], body);

    let three = goal.lit(3, 1);
    let four = goal.lit(4, 1);
    let f_three = goal.app("f", three);
    let bad = goal.manager.mk_eq(f_three, four);

    let assertions = vec![quantified, bad];
    assert!(!certify(&assertions, &FxHashMap::default(), &goal.manager));
}

/// `forall x in [0,10]. g(x) = 2x + 1` is a macro definition: the affine
/// default is read off the goal and then verified.
#[test]
fn affine_macro_is_detected_and_certified() {
    let mut goal = Goal::new();
    let real = goal.real_sort();
    let x = goal.var("x");
    let zero = goal.lit(0, 1);
    let ten = goal.lit(10, 1);
    let two = goal.lit(2, 1);
    let one = goal.lit(1, 1);

    let lower = goal.manager.mk_ge(x, zero);
    let upper = goal.manager.mk_le(x, ten);
    let guard = goal.manager.mk_and([lower, upper]);
    let twice = goal.manager.mk_mul([two, x]);
    let rhs = goal.manager.mk_add([twice, one]);
    let gx = goal.app("g", x);
    let eq = goal.manager.mk_eq(gx, rhs);
    let body = goal.manager.mk_implies(guard, eq);
    let quantified = goal.manager.mk_forall([("x", real)], body);

    let macros = detect_macros(&[quantified], &goal.manager);
    assert_eq!(macros.by_func.len(), 1, "the definition of g was not found");

    let five = goal.lit(5, 1);
    let eleven = goal.lit(11, 1);
    let g_five = goal.app("g", five);
    let pin = goal.manager.mk_eq(g_five, eleven);

    let assertions = vec![quantified, pin];
    assert!(certify(&assertions, &FxHashMap::default(), &goal.manager));
}

/// A macro whose pin disagrees with the definition has no model, and the
/// certifier must say so rather than trust the macro.
#[test]
fn macro_with_conflicting_pin_is_not_certified() {
    let mut goal = Goal::new();
    let real = goal.real_sort();
    let x = goal.var("x");
    let two = goal.lit(2, 1);
    let one = goal.lit(1, 1);
    let twice = goal.manager.mk_mul([two, x]);
    let rhs = goal.manager.mk_add([twice, one]);
    let gx = goal.app("g", x);
    let body = goal.manager.mk_eq(gx, rhs);
    let quantified = goal.manager.mk_forall([("x", real)], body);

    let five = goal.lit(5, 1);
    let wrong = goal.lit(12, 1);
    let g_five = goal.app("g", five);
    let pin = goal.manager.mk_eq(g_five, wrong);

    let assertions = vec![quantified, pin];
    assert!(!certify(&assertions, &FxHashMap::default(), &goal.manager));
}

/// Nested applications: `forall x. f(g(x)) = g(f(x))` is decided by composing
/// the two candidate defaults symbolically.
#[test]
fn commuting_composition_is_certified() {
    let mut goal = Goal::new();
    let real = goal.real_sort();
    let x = goal.var("x");
    let gx = goal.app("g", x);
    let f_gx = goal.app("f", gx);
    let fx = goal.app("f", x);
    let g_fx = goal.app("g", fx);
    let body = goal.manager.mk_eq(f_gx, g_fx);
    let quantified = goal.manager.mk_forall([("x", real)], body);

    let one = goal.lit(1, 1);
    let f_one = goal.app("f", one);
    let g_one = goal.app("g", one);
    let pin_f = goal.manager.mk_eq(f_one, one);
    let pin_g = goal.manager.mk_eq(g_one, one);

    let assertions = vec![quantified, pin_f, pin_g];
    assert!(certify(&assertions, &FxHashMap::default(), &goal.manager));
}

/// An existential over `ℝ` is certified by *finding* the cell its witness lies
/// in — here the pinned point `f(1/2) = 1/2`.
#[test]
fn existential_witness_is_found() {
    let mut goal = Goal::new();
    let real = goal.real_sort();
    let x = goal.var("x");
    let fx = goal.app("f", x);
    let body = goal.manager.mk_eq(fx, x);
    let quantified = goal.manager.mk_exists([("x", real)], body);

    let half = goal.lit(1, 2);
    let f_half = goal.app("f", half);
    let pin = goal.manager.mk_eq(f_half, half);

    let assertions = vec![quantified, pin];
    assert!(certify(&assertions, &FxHashMap::default(), &goal.manager));
}

/// An unsatisfiable real goal must never certify.
#[test]
fn unsatisfiable_real_goal_is_not_certified() {
    let mut goal = Goal::new();
    let real = goal.real_sort();
    let x = goal.var("x");
    let fx = goal.app("f", x);
    let zero = goal.lit(0, 1);
    let positive = goal.manager.mk_ge(fx, zero);
    let negative = goal.manager.mk_le(fx, zero);
    let strict = goal.manager.mk_eq(fx, zero);
    let not_strict = goal.manager.mk_not(strict);
    let body = goal.manager.mk_and([positive, negative, not_strict]);
    let quantified = goal.manager.mk_forall([("x", real)], body);

    let assertions = vec![quantified];
    assert!(!certify(&assertions, &FxHashMap::default(), &goal.manager));
}

/// A goal with no quantifier belongs to the ground solver.
#[test]
fn quantifier_free_goal_is_declined() {
    let mut goal = Goal::new();
    let three = goal.lit(3, 1);
    let f_three = goal.app("f", three);
    let assertion = goal.manager.mk_eq(f_three, three);
    assert!(!certify(&[assertion], &FxHashMap::default(), &goal.manager));
}

/// An integer-sorted goal is not this engine's: it must decline so the integer
/// certifier's own completeness argument is the one that applies.
#[test]
fn integer_goal_leaves_the_real_fragment() {
    let mut manager = TermManager::new();
    let int = manager.sorts.int_sort;
    let x = manager.mk_var("x", int);
    let fx = manager.mk_apply("f", [x], int);
    let body = manager.mk_eq(fx, x);
    let quantified = manager.mk_forall([("x", int)], body);
    assert!(harvest::harvest(&[quantified], &manager).is_none());
}

/// A quantifier over two variables needs a two-dimensional decomposition this
/// engine does not compute, so the fragment scan refuses it.
#[test]
fn two_variable_quantifier_is_refused() {
    let mut goal = Goal::new();
    let real = goal.real_sort();
    let x = goal.var("x");
    let y = goal.var("y");
    let body = goal.manager.mk_ge(x, y);
    let quantified = goal.manager.mk_forall([("x", real), ("y", real)], body);
    assert!(harvest::harvest(&[quantified], &goal.manager).is_none());
}

/// A non-linear body leaves the affine fragment and must not certify.
#[test]
fn quadratic_body_is_declined() {
    let mut goal = Goal::new();
    let real = goal.real_sort();
    let x = goal.var("x");
    let square = goal.manager.mk_mul([x, x]);
    let zero = goal.lit(0, 1);
    let body = goal.manager.mk_ge(square, zero);
    let quantified = goal.manager.mk_forall([("x", real)], body);
    assert!(!certify(
        &[quantified],
        &FxHashMap::default(),
        &goal.manager
    ));
}

#[test]
fn affine_reader_accepts_only_linear_shapes() {
    let mut goal = Goal::new();
    let x = goal.var("x");
    let two = goal.lit(2, 1);
    let one = goal.lit(1, 1);
    let twice = goal.manager.mk_mul([two, x]);
    let shifted = goal.manager.mk_add([twice, one]);
    let name = goal.manager.intern_str("x");

    let form = affine_in(shifted, name, &goal.manager).expect("2x + 1 is affine");
    assert_eq!(form.a, rat(2, 1));
    assert_eq!(form.b, rat(1, 1));

    let square = goal.manager.mk_mul([x, x]);
    assert!(affine_in(square, name, &goal.manager).is_none());

    let applied = goal.app("f", x);
    assert!(affine_in(applied, name, &goal.manager).is_none());
}
