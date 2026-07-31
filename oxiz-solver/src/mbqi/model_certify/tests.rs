//! Unit tests for the shared certifier entry point and the integer engine.
//!
//! Every test states a goal at term level and asks for a verdict.  The
//! positive ones pin capabilities the certifier must keep; the negative ones
//! pin the far more important property that it declines rather than guesses.

use oxiz_core::ast::{TermId, TermManager};
use oxiz_core::sort::SortId;

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
    let mut goal = IntGoal::new();
    let zero = goal.lit(0);
    let f_zero = goal.app("f", zero);
    let assertion = goal.manager.mk_eq(f_zero, zero);
    assert!(!certify(&[assertion], &FxHashMap::default(), &goal.manager));
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

/// A goal outside both fragments — here a bit-vector — declines in both
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
