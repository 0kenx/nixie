//! Where a candidate real interpretation comes from.
//!
//! Three sources, in decreasing order of how much the goal commits to them:
//!
//! * **Pins** – points the goal states outright (`(= (f 3.14) 3.14)`) or the
//!   ground model already fixed.  They are copied into the interpretation
//!   verbatim.
//! * **Macros** – a quantifier of the shape `∀x. guard(x) ⇒ f(x) = t(x)` with
//!   `f` absent from `t` *defines* `f` on the guarded region.  When `t` is
//!   affine, `λy. t(y)` becomes the first default tried.  (Z3 calls these
//!   quasi-macros; the detection here is deliberately narrower – one variable,
//!   one affine right-hand side – because the certifier still verifies whatever
//!   it produces.)
//! * **Shapes** – the identity, an affine through two pins, the pinned values
//!   themselves, zero, and the goal's own literals.
//!
//! None of this has to be right.  Everything the synthesis proposes is checked
//! by [`super::eval::evaluate`] against every assertion before a `sat` is
//! claimed, so a bad guess costs a search step, never soundness.

use num_traits::Zero;
use oxiz_core::ast::{TermId, TermKind, TermManager};
use oxiz_core::interner::Spur;

#[allow(unused_imports)]
use crate::prelude::*;

use super::super::value::{CertValue, literal_value, rational_literal};
use super::affine::{Affine, Rat};
use super::harvest::RealHarvest;

/// Cap on the number of defaults tried per function symbol.
pub(crate) const MAX_CANDIDATES: usize = 8;

/// Pinned points and constant values gathered from the goal and the ground
/// model.
#[derive(Debug, Default)]
pub(crate) struct RealFacts {
    /// Real-valued pins, per function symbol.
    pub(crate) num_pins: FxHashMap<Spur, FxHashMap<Rat, Rat>>,
    /// Boolean-valued pins, per predicate symbol.
    pub(crate) bool_pins: FxHashMap<Spur, FxHashMap<Rat, bool>>,
    /// Real-valued free constants.
    pub(crate) consts: FxHashMap<Spur, Rat>,
    /// Boolean free constants.
    pub(crate) bool_consts: FxHashMap<Spur, bool>,
}

impl RealFacts {
    /// Record `func(arg) = value` when both sides are literal.
    fn add_pin(&mut self, func: Spur, arg: Rat, value: CertValue) {
        match value {
            CertValue::Real(number) => {
                self.num_pins.entry(func).or_default().insert(arg, number);
            }
            CertValue::Int(number) => {
                self.num_pins
                    .entry(func)
                    .or_default()
                    .insert(arg, Rat::from(number));
            }
            CertValue::Bool(flag) => {
                self.bool_pins.entry(func).or_default().insert(arg, flag);
            }
        }
    }

    /// Record `name = value`.
    fn add_const(&mut self, name: Spur, value: CertValue) {
        match value {
            CertValue::Real(number) => {
                self.consts.insert(name, number);
            }
            CertValue::Int(number) => {
                self.consts.insert(name, Rat::from(number));
            }
            CertValue::Bool(flag) => {
                self.bool_consts.insert(name, flag);
            }
        }
    }
}

/// Collect pins and constant values from the ground model and from the goal's
/// own literal equations.
///
/// Both sources are heuristic: a model entry may be missing and a syntactic
/// equation may be under a disjunction we do not inspect.  Neither can mislead
/// the verdict – a wrong pin makes the very assertion it came from evaluate to
/// `false`, and the search moves on.
pub(crate) fn collect_facts(
    assertions: &[TermId],
    assignments: &FxHashMap<TermId, TermId>,
    manager: &TermManager,
    harvested: &RealHarvest,
) -> RealFacts {
    let mut facts = RealFacts::default();

    for (&key, &value) in assignments {
        let Some(result) = literal_value(value, manager) else {
            continue;
        };
        match manager.get(key).map(|t| &t.kind) {
            Some(TermKind::Apply { func, args }) => {
                if let [arg] = args.as_slice()
                    && let Some(point) = rational_literal(*arg, manager)
                {
                    facts.add_pin(*func, point, result);
                }
            }
            Some(TermKind::Var(name)) if !harvested.bound_names.contains(name) => {
                facts.add_const(*name, result);
            }
            _ => {}
        }
    }

    // Ground equations the goal asserts at top level are pins the model may not
    // have materialised (an unconstrained application never reaches the
    // arithmetic solver, so no assignment is produced for it).
    let mut stack: Vec<TermId> = assertions.iter().rev().copied().collect();
    let mut seen: FxHashSet<TermId> = FxHashSet::default();
    while let Some(current) = stack.pop() {
        if !seen.insert(current) {
            continue;
        }
        match manager.get(current).map(|t| &t.kind) {
            Some(TermKind::And(args)) => stack.extend(args.iter().rev().copied()),
            Some(TermKind::Eq(left, right)) => {
                let (left, right) = (*left, *right);
                add_literal_equation(&mut facts, left, right, manager);
                add_literal_equation(&mut facts, right, left, manager);
            }
            _ => {}
        }
    }

    facts
}

/// Record `lhs = rhs` as a pin or a constant value when `lhs` is an
/// application of a literal argument (or a free constant) and `rhs` is literal.
fn add_literal_equation(facts: &mut RealFacts, lhs: TermId, rhs: TermId, manager: &TermManager) {
    let Some(value) =
        literal_value(rhs, manager).or_else(|| rational_literal(rhs, manager).map(CertValue::Real))
    else {
        return;
    };
    match manager.get(lhs).map(|t| &t.kind) {
        Some(TermKind::Apply { func, args }) => {
            if let [arg] = args.as_slice()
                && let Some(point) = rational_literal(*arg, manager)
            {
                facts.add_pin(*func, point, value);
            }
        }
        Some(TermKind::Var(name)) => facts.add_const(*name, value),
        _ => {}
    }
}

/// An affine definition a quantifier gives to a function symbol.
#[derive(Debug)]
pub(crate) struct MacroDefs {
    /// Affine right-hand sides found for each symbol, most recent last.
    pub(crate) by_func: FxHashMap<Spur, Vec<Affine>>,
}

/// Find functional definitions `∀x. … ⇒ f(x) = t(x)` with `t` affine in `x`.
///
/// Only conjunctive / implicative structure is descended: a definition hidden
/// under a disjunction does not hold unconditionally and would be a guess, not
/// a definition.
pub(crate) fn detect_macros(assertions: &[TermId], manager: &TermManager) -> MacroDefs {
    let mut out = MacroDefs {
        by_func: FxHashMap::default(),
    };

    for &assertion in assertions {
        let Some(TermKind::Forall { vars, body, .. }) = manager.get(assertion).map(|t| &t.kind)
        else {
            continue;
        };
        let &(name, _) = match vars.as_slice() {
            [single] => single,
            _ => continue,
        };
        let body = *body;

        let mut stack: Vec<TermId> = vec![body];
        let mut seen: FxHashSet<TermId> = FxHashSet::default();
        while let Some(current) = stack.pop() {
            if !seen.insert(current) {
                continue;
            }
            match manager.get(current).map(|t| &t.kind) {
                Some(TermKind::And(args)) => stack.extend(args.iter().copied()),
                // Only the consequent is a definition; the guard restricts
                // where it applies, and the default is checked everywhere
                // anyway.
                Some(TermKind::Implies(_, consequent)) => stack.push(*consequent),
                Some(TermKind::Eq(left, right)) => {
                    let (left, right) = (*left, *right);
                    record_definition(&mut out, name, left, right, manager);
                    record_definition(&mut out, name, right, left, manager);
                }
                _ => {}
            }
        }
    }

    out
}

/// Record `f(x) = rhs` as a definition of `f` when `rhs` is affine in `x`.
fn record_definition(
    out: &mut MacroDefs,
    var: Spur,
    lhs: TermId,
    rhs: TermId,
    manager: &TermManager,
) {
    let Some(TermKind::Apply { func, args }) = manager.get(lhs).map(|t| &t.kind) else {
        return;
    };
    let [arg] = args.as_slice() else { return };
    if !matches!(manager.get(*arg).map(|t| &t.kind), Some(TermKind::Var(n)) if *n == var) {
        return;
    }
    // `affine_in` refuses any application, so `f` cannot occur in `rhs`: the
    // definition is genuinely non-recursive.
    let Some(form) = affine_in(rhs, var, manager) else {
        return;
    };
    out.by_func.entry(*func).or_default().push(form);
}

/// Read `term` as an affine function of `var`, or `None`.
///
/// Literals, `var` itself and the affine operators are accepted; an
/// application, another variable, or a non-linear product is not.  Iterative,
/// because term depth is user input.
pub(crate) fn affine_in(term: TermId, var: Spur, manager: &TermManager) -> Option<Affine> {
    enum Task {
        Visit(TermId),
        Combine(TermId),
    }

    let mut tasks: Vec<Task> = vec![Task::Visit(term)];
    let mut stack: Vec<Affine> = Vec::new();
    let mut steps = 0usize;

    while let Some(task) = tasks.pop() {
        steps += 1;
        if steps > 10_000 {
            return None;
        }
        match task {
            Task::Visit(current) => {
                if let Some(value) = rational_literal(current, manager) {
                    stack.push(Affine::constant(value));
                    continue;
                }
                match manager.get(current).map(|t| &t.kind) {
                    Some(TermKind::Var(name)) if *name == var => stack.push(Affine::identity()),
                    Some(TermKind::Neg(inner)) => {
                        let inner = *inner;
                        tasks.push(Task::Combine(current));
                        tasks.push(Task::Visit(inner));
                    }
                    Some(TermKind::Add(args) | TermKind::Mul(args)) => {
                        let args: Vec<TermId> = args.iter().copied().collect();
                        tasks.push(Task::Combine(current));
                        for arg in args.into_iter().rev() {
                            tasks.push(Task::Visit(arg));
                        }
                    }
                    Some(TermKind::Sub(left, right)) => {
                        let (left, right) = (*left, *right);
                        tasks.push(Task::Combine(current));
                        tasks.push(Task::Visit(right));
                        tasks.push(Task::Visit(left));
                    }
                    _ => return None,
                }
            }
            Task::Combine(current) => {
                let kind = manager.get(current).map(|t| t.kind.clone())?;
                let form = match &kind {
                    TermKind::Neg(_) => stack.pop()?.neg(),
                    TermKind::Sub(_, _) => {
                        let right = stack.pop()?;
                        let left = stack.pop()?;
                        left.sub(&right)
                    }
                    TermKind::Add(args) => {
                        let start = stack.len().checked_sub(args.len())?;
                        let parts = stack.split_off(start);
                        let mut acc = Affine::constant(Rat::zero());
                        for part in &parts {
                            acc = acc.add(part);
                        }
                        acc
                    }
                    TermKind::Mul(args) => {
                        let start = stack.len().checked_sub(args.len())?;
                        let parts = stack.split_off(start);
                        let mut acc = Affine::constant(Rat::from_integer(1.into()));
                        for part in &parts {
                            acc = acc.mul(part)?;
                        }
                        acc
                    }
                    _ => return None,
                };
                stack.push(form);
            }
        }
    }

    match stack.as_slice() {
        [single] => Some(single.clone()),
        _ => None,
    }
}

/// The affine defaults worth trying for one real-valued function symbol, most
/// promising first.
pub(crate) fn num_candidates(
    func: Spur,
    facts: &RealFacts,
    macros: &MacroDefs,
    literals: &[Rat],
) -> Vec<Affine> {
    let mut out: Vec<Affine> = Vec::new();
    let push = |form: Affine, out: &mut Vec<Affine>| {
        if out.len() < MAX_CANDIDATES && !out.contains(&form) {
            out.push(form);
        }
    };

    // A definition the goal states is the interpretation the goal asked for.
    if let Some(forms) = macros.by_func.get(&func) {
        for form in forms {
            push(form.clone(), &mut out);
        }
    }

    let mut pins: Vec<(Rat, Rat)> = facts
        .num_pins
        .get(&func)
        .map(|table| table.iter().map(|(k, v)| (k.clone(), v.clone())).collect())
        .unwrap_or_default();
    pins.sort();

    // The affine through two pinned points reproduces both of them exactly, so
    // it is the shape most likely to keep the pinned equations true.
    for (i, (x0, y0)) in pins.iter().enumerate() {
        for (x1, y1) in pins.iter().skip(i + 1) {
            if x1 == x0 {
                continue;
            }
            let slope = (y1 - y0) / (x1 - x0);
            let intercept = y0 - &slope * x0;
            push(
                Affine {
                    a: slope,
                    b: intercept,
                },
                &mut out,
            );
        }
    }

    push(Affine::identity(), &mut out);
    for (_, value) in &pins {
        push(Affine::constant(value.clone()), &mut out);
    }
    push(Affine::constant(Rat::zero()), &mut out);
    for value in literals {
        push(Affine::constant(value.clone()), &mut out);
    }

    out
}
