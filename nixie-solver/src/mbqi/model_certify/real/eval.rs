//! The exact piecewise-affine evaluator for the real fragment.
//!
//! Given a candidate interpretation (finite pin tables plus one affine default
//! per function) this evaluates a closed formula to a truth value, deciding any
//! `∀`/`∃` over `ℝ` it contains – not by sampling, but by computing the body as
//! an exact piecewise function of the bound variable and reading every cell.
//!
//! Everything runs on an explicit heap stack, so formula depth is bounded by
//! the step budget rather than by the native call stack.

use nixie_core::ast::{TermId, TermKind, TermManager};
use nixie_core::interner::Spur;
use num_traits::{One, Signed, Zero};

#[allow(unused_imports)]
use crate::prelude::*;

use super::affine::{Affine, Partition, Piecewise, Rat, align};
use super::interp::{RealFunc, RealInterp};

/// Cap on the number of cuts one piecewise value may carry.
///
/// Every comparison and every application can add cuts, so this bounds the
/// whole evaluation's width.  Exceeding it declines, which costs completeness
/// only.
const MAX_CUTS: usize = 512;

/// Cap on the number of machine steps one evaluation may spend.
const MAX_STEPS: usize = 400_000;

/// Why a real evaluation stopped without a verdict.
#[derive(Debug, PartialEq, Eq)]
pub(crate) enum RealEvalError {
    /// The goal mentions something the real engine does not interpret.
    Unsupported,
    /// A width or step budget ran out.
    Exhausted,
}

/// The value of a sub-term as an exact function of the bound variable.
#[derive(Clone, Debug)]
pub(crate) enum SymValue {
    /// A piecewise-affine real.
    Num(Piecewise<Affine>),
    /// A piecewise-constant boolean.
    Bool(Piecewise<bool>),
}

impl SymValue {
    fn num(self) -> Result<Piecewise<Affine>, RealEvalError> {
        match self {
            SymValue::Num(p) => Ok(p),
            SymValue::Bool(_) => Err(RealEvalError::Unsupported),
        }
    }

    fn boolean(self) -> Result<Piecewise<bool>, RealEvalError> {
        match self {
            SymValue::Bool(p) => Ok(p),
            SymValue::Num(_) => Err(RealEvalError::Unsupported),
        }
    }
}

/// One pending obligation of the evaluation machine.
enum Step {
    /// Evaluate a term and push its value.
    Eval(TermId),
    /// Combine the operand values already on the value stack.
    Reduce(TermId),
    /// Fold the body's per-cell verdicts into the quantifier's own.
    QuantExit {
        /// Whether the quantifier is universal.
        is_forall: bool,
    },
}

/// The evaluation machine's mutable state.
struct Machine<'a> {
    steps: Vec<Step>,
    values: Vec<SymValue>,
    /// The bound variable currently in scope, if any.  The engine handles one
    /// at a time and declines a nested quantifier rather than guessing.
    bound: Option<Spur>,
    interp: &'a RealInterp,
    manager: &'a TermManager,
    budget: usize,
}

/// Decide the closed formula `term` under `interp`.
///
/// Answers `Ok(true)` only when the formula is true under the interpretation
/// *everywhere* – a genuine model check, quantifiers included.
pub(crate) fn evaluate(
    term: TermId,
    interp: &RealInterp,
    manager: &TermManager,
) -> Result<bool, RealEvalError> {
    let mut machine = Machine {
        steps: vec![Step::Eval(term)],
        values: Vec::new(),
        bound: None,
        interp,
        manager,
        budget: MAX_STEPS,
    };

    while let Some(step) = machine.steps.pop() {
        machine.budget = machine
            .budget
            .checked_sub(1)
            .ok_or(RealEvalError::Exhausted)?;
        match step {
            Step::Eval(t) => eval_step(&mut machine, t)?,
            Step::Reduce(t) => reduce_step(&mut machine, t)?,
            Step::QuantExit { is_forall } => quant_exit(&mut machine, is_forall)?,
        }
    }

    let Some(value) = machine.values.pop() else {
        return Err(RealEvalError::Unsupported);
    };
    if !machine.values.is_empty() {
        return Err(RealEvalError::Unsupported);
    }
    let verdict = value.boolean()?;
    Ok(verdict.cells().iter().all(|&cell| cell))
}

/// Expand one term into either a value or its operand obligations.
fn eval_step(machine: &mut Machine, term: TermId) -> Result<(), RealEvalError> {
    let node = machine
        .manager
        .get(term)
        .ok_or(RealEvalError::Unsupported)?;
    match &node.kind {
        TermKind::True => machine.values.push(uniform_bool(true)),
        TermKind::False => machine.values.push(uniform_bool(false)),
        TermKind::IntConst(_) | TermKind::RealConst(_) | TermKind::Neg(_) => {
            // `Neg` over a literal is itself a literal; anything else falls
            // through to the generic operand expansion below.
            match super::super::value::rational_literal(term, machine.manager) {
                Some(value) => machine.values.push(uniform_num(Affine::constant(value))),
                None => expand_operands(machine, term, &node.kind)?,
            }
        }
        TermKind::Var(name) => {
            let value = if machine.bound == Some(*name) {
                uniform_num(Affine::identity())
            } else if let Some(number) = machine.interp.consts.get(name) {
                uniform_num(Affine::constant(number.clone()))
            } else if let Some(&flag) = machine.interp.bool_consts.get(name) {
                uniform_bool(flag)
            } else {
                return Err(RealEvalError::Unsupported);
            };
            machine.values.push(value);
        }
        TermKind::Forall { vars, body, .. } | TermKind::Exists { vars, body, .. } => {
            let is_forall = matches!(node.kind, TermKind::Forall { .. });
            // One real variable at a time: a second, nested one would need a
            // two-dimensional decomposition this engine does not compute.
            let &(name, sort) = match vars.as_slice() {
                [single] => single,
                _ => return Err(RealEvalError::Unsupported),
            };
            if sort != machine.manager.sorts.real_sort || machine.bound.is_some() {
                return Err(RealEvalError::Unsupported);
            }
            machine.bound = Some(name);
            machine.steps.push(Step::QuantExit { is_forall });
            machine.steps.push(Step::Eval(*body));
        }
        TermKind::Apply { args, .. } => {
            let [arg] = args.as_slice() else {
                return Err(RealEvalError::Unsupported);
            };
            machine.steps.push(Step::Reduce(term));
            machine.steps.push(Step::Eval(*arg));
        }
        other => expand_operands(machine, term, other)?,
    }
    Ok(())
}

/// Push the reduce obligation for `term` and the evaluation of its operands.
fn expand_operands(
    machine: &mut Machine,
    term: TermId,
    kind: &TermKind,
) -> Result<(), RealEvalError> {
    let children = operands(kind).ok_or(RealEvalError::Unsupported)?;
    machine.steps.push(Step::Reduce(term));
    for &child in children.iter().rev() {
        machine.steps.push(Step::Eval(child));
    }
    Ok(())
}

/// The operand list of a supported non-leaf, non-`Apply`, non-quantifier node.
pub(crate) fn operands(kind: &TermKind) -> Option<Vec<TermId>> {
    let out: Vec<TermId> = match kind {
        TermKind::Not(a) | TermKind::Neg(a) => vec![*a],
        TermKind::And(args) | TermKind::Or(args) | TermKind::Add(args) | TermKind::Mul(args) => {
            args.iter().copied().collect()
        }
        TermKind::Distinct(args) => args.iter().copied().collect(),
        TermKind::Xor(l, r)
        | TermKind::Implies(l, r)
        | TermKind::Eq(l, r)
        | TermKind::Sub(l, r)
        | TermKind::Div(l, r)
        | TermKind::Lt(l, r)
        | TermKind::Le(l, r)
        | TermKind::Gt(l, r)
        | TermKind::Ge(l, r) => vec![*l, *r],
        TermKind::Ite(c, t, e) => vec![*c, *t, *e],
        _ => return None,
    };
    Some(out)
}

/// Pop this node's operand values and push the combined result.
fn reduce_step(machine: &mut Machine, term: TermId) -> Result<(), RealEvalError> {
    let node = machine
        .manager
        .get(term)
        .ok_or(RealEvalError::Unsupported)?;
    let kind = node.kind.clone();
    let arity = match &kind {
        TermKind::Apply { .. } => 1,
        other => operands(other).ok_or(RealEvalError::Unsupported)?.len(),
    };
    let start = machine
        .values
        .len()
        .checked_sub(arity)
        .ok_or(RealEvalError::Unsupported)?;
    let args: Vec<SymValue> = machine.values.split_off(start);

    let result = combine(&kind, args, machine.interp)?;
    check_width(&result)?;
    machine.values.push(result);
    Ok(())
}

/// Fold the body's per-cell verdicts into the quantifier's own.
///
/// Every cell of a [`Partition`] is non-empty, so "true on every cell" is
/// exactly `∀x. body` and "true on some cell" is exactly `∃x. body`.
fn quant_exit(machine: &mut Machine, is_forall: bool) -> Result<(), RealEvalError> {
    let body = machine
        .values
        .pop()
        .ok_or(RealEvalError::Unsupported)?
        .boolean()?;
    machine.bound = None;
    let verdict = if is_forall {
        body.cells().iter().all(|&cell| cell)
    } else {
        body.cells().iter().any(|&cell| cell)
    };
    machine.values.push(uniform_bool(verdict));
    Ok(())
}

/// Apply one operator to already-evaluated operands.
fn combine(
    kind: &TermKind,
    args: Vec<SymValue>,
    interp: &RealInterp,
) -> Result<SymValue, RealEvalError> {
    match kind {
        TermKind::Apply { func, .. } => {
            let interpretation = interp.funcs.get(func).ok_or(RealEvalError::Unsupported)?;
            let [arg] = <[SymValue; 1]>::try_from(args).map_err(|_| RealEvalError::Unsupported)?;
            apply_func(interpretation, arg.num()?)
        }
        TermKind::Not(_) => {
            let [a] = <[SymValue; 1]>::try_from(args).map_err(|_| RealEvalError::Unsupported)?;
            let a = a.boolean()?;
            map_bool(&a, |v| !v)
        }
        TermKind::And(_) => fold_bool(args, true, |acc, v| acc && v),
        TermKind::Or(_) => fold_bool(args, false, |acc, v| acc || v),
        TermKind::Xor(_, _) => binary_bool(args, |l, r| l ^ r),
        TermKind::Implies(_, _) => binary_bool(args, |l, r| !l || r),
        TermKind::Ite(_, _, _) => combine_ite(args),
        TermKind::Eq(_, _) => combine_eq(args),
        TermKind::Distinct(_) => combine_distinct(args),
        TermKind::Neg(_) => {
            let [a] = <[SymValue; 1]>::try_from(args).map_err(|_| RealEvalError::Unsupported)?;
            let a = a.num()?;
            map_num(&a, |form| Some(form.neg()))
        }
        TermKind::Add(_) => fold_num(args, Affine::constant(Rat::zero()), |acc, form| {
            Some(acc.add(form))
        }),
        TermKind::Sub(_, _) => binary_num(args, |l, r| Some(l.sub(r))),
        TermKind::Mul(_) => fold_num(args, Affine::constant(Rat::one()), Affine::mul),
        TermKind::Div(_, _) => binary_num(args, Affine::div),
        TermKind::Lt(_, _) => compare(args, |sign| sign.is_negative()),
        TermKind::Le(_, _) => compare(args, |sign| !sign.is_positive()),
        TermKind::Gt(_, _) => compare(args, |sign| sign.is_positive()),
        TermKind::Ge(_, _) => compare(args, |sign| !sign.is_negative()),
        _ => Err(RealEvalError::Unsupported),
    }
}

/// The value of `interpretation` at the piecewise-affine argument `arg`.
///
/// The argument is first cut wherever it *meets* a pinned argument value; after
/// that every remaining open cell either maps entirely into the default branch
/// (the argument is non-constant there and hits no pin) or is constant, so the
/// result is again exactly piecewise affine.
fn apply_func(
    interpretation: &RealFunc,
    arg: Piecewise<Affine>,
) -> Result<SymValue, RealEvalError> {
    let mut extra: Vec<Rat> = Vec::new();
    for (index, form) in arg.cells().iter().enumerate() {
        if form.as_constant().is_some() {
            continue;
        }
        for pin_arg in interpretation.pin_args() {
            // Solve `form(x) = pin_arg`; a non-constant affine meets each pin
            // value at exactly one point.
            let shifted = Affine {
                a: form.a.clone(),
                b: &form.b - pin_arg,
            };
            let Some(root) = shifted.root() else {
                continue;
            };
            if arg.partition().strictly_inside(index, &root) {
                extra.push(root);
            }
        }
    }

    let part = arg.partition().refined_by(&extra);
    if part.cuts().len() > MAX_CUTS {
        return Err(RealEvalError::Exhausted);
    }
    let arg = arg.refine(&part).ok_or(RealEvalError::Unsupported)?;

    match interpretation {
        RealFunc::Num { default, .. } => {
            let mut cells: Vec<Affine> = Vec::with_capacity(part.len());
            for (index, form) in arg.cells().iter().enumerate() {
                let concrete = concrete_argument(&part, index, form)?;
                let cell = match concrete {
                    Some(point) => match interpretation.pin_num(&point) {
                        Some(value) => Affine::constant(value.clone()),
                        None => Affine::constant(default.eval(&point)),
                    },
                    // Non-constant on an open cell: no pin is met strictly
                    // inside, so the default applies throughout.
                    None => default.compose(form),
                };
                cells.push(cell);
            }
            Ok(SymValue::Num(
                Piecewise::new(part, cells).ok_or(RealEvalError::Unsupported)?,
            ))
        }
        RealFunc::Bool { default, .. } => {
            let mut cells: Vec<bool> = Vec::with_capacity(part.len());
            for (index, form) in arg.cells().iter().enumerate() {
                let concrete = concrete_argument(&part, index, form)?;
                let cell = match concrete {
                    Some(point) => interpretation.pin_bool(&point).unwrap_or(*default),
                    None => *default,
                };
                cells.push(cell);
            }
            Ok(SymValue::Bool(
                Piecewise::new(part, cells).ok_or(RealEvalError::Unsupported)?,
            ))
        }
    }
}

/// The single value `form` takes on cell `index`, or `None` when it takes more
/// than one there.
fn concrete_argument(
    part: &Partition,
    index: usize,
    form: &Affine,
) -> Result<Option<Rat>, RealEvalError> {
    if let Some(value) = form.as_constant() {
        return Ok(Some(value.clone()));
    }
    let (point, is_point) = part.probe(index).ok_or(RealEvalError::Unsupported)?;
    if is_point {
        Ok(Some(form.eval(&point)))
    } else {
        Ok(None)
    }
}

/// Compare two piecewise-affine values, cutting wherever their difference
/// crosses zero so that each remaining cell has one constant sign.
fn compare(args: Vec<SymValue>, accept: impl Fn(&Rat) -> bool) -> Result<SymValue, RealEvalError> {
    let [left, right] = <[SymValue; 2]>::try_from(args).map_err(|_| RealEvalError::Unsupported)?;
    let (left, right) = (left.num()?, right.num()?);
    let (left, right) = align(&left, &right).ok_or(RealEvalError::Unsupported)?;

    let mut extra: Vec<Rat> = Vec::new();
    for index in 0..left.partition().len() {
        let l = left.cells().get(index).ok_or(RealEvalError::Unsupported)?;
        let r = right.cells().get(index).ok_or(RealEvalError::Unsupported)?;
        if let Some(root) = l.sub(r).root()
            && left.partition().strictly_inside(index, &root)
        {
            extra.push(root);
        }
    }

    let part = left.partition().refined_by(&extra);
    if part.cuts().len() > MAX_CUTS {
        return Err(RealEvalError::Exhausted);
    }
    let left = left.refine(&part).ok_or(RealEvalError::Unsupported)?;
    let right = right.refine(&part).ok_or(RealEvalError::Unsupported)?;

    let mut cells: Vec<bool> = Vec::with_capacity(part.len());
    for index in 0..part.len() {
        let l = left.cells().get(index).ok_or(RealEvalError::Unsupported)?;
        let r = right.cells().get(index).ok_or(RealEvalError::Unsupported)?;
        let (point, _) = part.probe(index).ok_or(RealEvalError::Unsupported)?;
        // No root lies strictly inside this cell any more, so the sign of the
        // difference is the same at every one of its points.
        let sign = l.sub(r).eval(&point);
        cells.push(accept(&sign));
    }
    Ok(SymValue::Bool(
        Piecewise::new(part, cells).ok_or(RealEvalError::Unsupported)?,
    ))
}

/// Equality, over either domain.
fn combine_eq(args: Vec<SymValue>) -> Result<SymValue, RealEvalError> {
    match args.as_slice() {
        [SymValue::Bool(_), SymValue::Bool(_)] => binary_bool(args, |l, r| l == r),
        [SymValue::Num(_), SymValue::Num(_)] => compare(args, Zero::is_zero),
        // A mixed comparison is a malformed term, not a false equality.
        _ => Err(RealEvalError::Unsupported),
    }
}

/// `distinct`, over either domain.
fn combine_distinct(args: Vec<SymValue>) -> Result<SymValue, RealEvalError> {
    let mut acc = uniform_bool(true);
    for (i, left) in args.iter().enumerate() {
        for right in args.iter().skip(i + 1) {
            let pair = vec![left.clone(), right.clone()];
            let equal = combine_eq(pair)?;
            let differ = match equal {
                SymValue::Bool(p) => map_bool(&p, |v| !v)?,
                SymValue::Num(_) => return Err(RealEvalError::Unsupported),
            };
            acc = binary_bool(vec![acc, differ], |l, r| l && r)?;
            check_width(&acc)?;
        }
    }
    Ok(acc)
}

/// `ite`, over either branch domain.
fn combine_ite(args: Vec<SymValue>) -> Result<SymValue, RealEvalError> {
    let [cond, then, other] =
        <[SymValue; 3]>::try_from(args).map_err(|_| RealEvalError::Unsupported)?;
    let cond = cond.boolean()?;
    match (then, other) {
        (SymValue::Num(then), SymValue::Num(other)) => {
            let (cond, then) = align(&cond, &then).ok_or(RealEvalError::Unsupported)?;
            let (cond, other) = align(&cond, &other).ok_or(RealEvalError::Unsupported)?;
            let then = then
                .refine(cond.partition())
                .ok_or(RealEvalError::Unsupported)?;
            let part = cond.partition().clone();
            let mut cells: Vec<Affine> = Vec::with_capacity(part.len());
            for index in 0..part.len() {
                let flag = *cond.cells().get(index).ok_or(RealEvalError::Unsupported)?;
                let source = if flag { &then } else { &other };
                cells.push(
                    source
                        .cells()
                        .get(index)
                        .ok_or(RealEvalError::Unsupported)?
                        .clone(),
                );
            }
            Ok(SymValue::Num(
                Piecewise::new(part, cells).ok_or(RealEvalError::Unsupported)?,
            ))
        }
        (SymValue::Bool(then), SymValue::Bool(other)) => {
            let (cond, then) = align(&cond, &then).ok_or(RealEvalError::Unsupported)?;
            let (cond, other) = align(&cond, &other).ok_or(RealEvalError::Unsupported)?;
            let then = then
                .refine(cond.partition())
                .ok_or(RealEvalError::Unsupported)?;
            let part = cond.partition().clone();
            let mut cells: Vec<bool> = Vec::with_capacity(part.len());
            for index in 0..part.len() {
                let flag = *cond.cells().get(index).ok_or(RealEvalError::Unsupported)?;
                let source = if flag { &then } else { &other };
                cells.push(
                    *source
                        .cells()
                        .get(index)
                        .ok_or(RealEvalError::Unsupported)?,
                );
            }
            Ok(SymValue::Bool(
                Piecewise::new(part, cells).ok_or(RealEvalError::Unsupported)?,
            ))
        }
        _ => Err(RealEvalError::Unsupported),
    }
}

/// A value that is `cell` on the whole line.
fn uniform_bool(cell: bool) -> SymValue {
    SymValue::Bool(Piecewise::uniform(cell))
}

/// A value that is `form` on the whole line.
fn uniform_num(form: Affine) -> SymValue {
    SymValue::Num(Piecewise::uniform(form))
}

/// Map a boolean piecewise value cell-by-cell.
fn map_bool(value: &Piecewise<bool>, op: impl Fn(bool) -> bool) -> Result<SymValue, RealEvalError> {
    let cells: Vec<bool> = value.cells().iter().map(|&cell| op(cell)).collect();
    Ok(SymValue::Bool(
        Piecewise::new(value.partition().clone(), cells).ok_or(RealEvalError::Unsupported)?,
    ))
}

/// Map a numeric piecewise value cell-by-cell.
fn map_num(
    value: &Piecewise<Affine>,
    op: impl Fn(&Affine) -> Option<Affine>,
) -> Result<SymValue, RealEvalError> {
    let mut cells: Vec<Affine> = Vec::with_capacity(value.cells().len());
    for form in value.cells() {
        cells.push(op(form).ok_or(RealEvalError::Unsupported)?);
    }
    Ok(SymValue::Num(
        Piecewise::new(value.partition().clone(), cells).ok_or(RealEvalError::Unsupported)?,
    ))
}

/// Combine two boolean operands cell-by-cell.
fn binary_bool(
    args: Vec<SymValue>,
    op: impl Fn(bool, bool) -> bool,
) -> Result<SymValue, RealEvalError> {
    let [left, right] = <[SymValue; 2]>::try_from(args).map_err(|_| RealEvalError::Unsupported)?;
    let (left, right) = (left.boolean()?, right.boolean()?);
    let (left, right) = align(&left, &right).ok_or(RealEvalError::Unsupported)?;
    let mut cells: Vec<bool> = Vec::with_capacity(left.cells().len());
    for index in 0..left.cells().len() {
        let l = *left.cells().get(index).ok_or(RealEvalError::Unsupported)?;
        let r = *right.cells().get(index).ok_or(RealEvalError::Unsupported)?;
        cells.push(op(l, r));
    }
    Ok(SymValue::Bool(
        Piecewise::new(left.partition().clone(), cells).ok_or(RealEvalError::Unsupported)?,
    ))
}

/// Combine two numeric operands cell-by-cell.
fn binary_num(
    args: Vec<SymValue>,
    op: impl Fn(&Affine, &Affine) -> Option<Affine>,
) -> Result<SymValue, RealEvalError> {
    let [left, right] = <[SymValue; 2]>::try_from(args).map_err(|_| RealEvalError::Unsupported)?;
    let (left, right) = (left.num()?, right.num()?);
    let (left, right) = align(&left, &right).ok_or(RealEvalError::Unsupported)?;
    let mut cells: Vec<Affine> = Vec::with_capacity(left.cells().len());
    for index in 0..left.cells().len() {
        let l = left.cells().get(index).ok_or(RealEvalError::Unsupported)?;
        let r = right.cells().get(index).ok_or(RealEvalError::Unsupported)?;
        cells.push(op(l, r).ok_or(RealEvalError::Unsupported)?);
    }
    Ok(SymValue::Num(
        Piecewise::new(left.partition().clone(), cells).ok_or(RealEvalError::Unsupported)?,
    ))
}

/// Left-fold an n-ary boolean operator.
fn fold_bool(
    args: Vec<SymValue>,
    unit: bool,
    op: impl Fn(bool, bool) -> bool + Copy,
) -> Result<SymValue, RealEvalError> {
    let mut acc = uniform_bool(unit);
    for arg in args {
        acc = binary_bool(vec![acc, arg], op)?;
        check_width(&acc)?;
    }
    Ok(acc)
}

/// Left-fold an n-ary numeric operator.
fn fold_num(
    args: Vec<SymValue>,
    unit: Affine,
    op: impl Fn(&Affine, &Affine) -> Option<Affine> + Copy,
) -> Result<SymValue, RealEvalError> {
    let mut acc = uniform_num(unit);
    for arg in args {
        acc = binary_num(vec![acc, arg], op)?;
        check_width(&acc)?;
    }
    Ok(acc)
}

/// Decline once a value's partition has grown past the width cap.
fn check_width(value: &SymValue) -> Result<(), RealEvalError> {
    let cuts = match value {
        SymValue::Num(p) => p.partition().cuts().len(),
        SymValue::Bool(p) => p.partition().cuts().len(),
    };
    if cuts > MAX_CUTS {
        Err(RealEvalError::Exhausted)
    } else {
        Ok(())
    }
}
