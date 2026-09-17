//! The exhaustive evaluator: decides a closed formula under a candidate
//! interpretation, quantifiers included.
//!
//! Quantifiers are decided by enumerating one representative per *region* of
//! the critical set (see [`super::harvest::region_stable`] for why that is
//! exhaustive, not a sample).  Everything runs on explicit heap stacks – a
//! term worklist, a value stack, an environment stack and a domain stack – so
//! neither formula depth nor quantifier nesting touches the native call stack.

use core::cmp::Ordering;
use nixie_core::ast::{TermId, TermKind, TermManager};
use nixie_core::interner::Spur;
use nixie_core::sort::SortId;
use num_bigint::BigInt;
use num_traits::{Euclid, One, Zero};
use smallvec::SmallVec;

#[allow(unused_imports)]
use crate::prelude::*;

use super::harvest::supported_children;
use super::value::{CertValue, Interpretation, ValueSort, value_sort};

/// Cap on the number of points one bound variable is enumerated over.
///
/// The domain has one entry per critical value plus one per gap between them,
/// so this bounds the critical set at roughly half its size.  A goal with more
/// critical values declines rather than enumerating a huge product.
const MAX_DOMAIN: usize = 256;

/// Cap on the magnitude (in bits) of an intermediate integer.
///
/// Guards against a `Mul` chain over model values blowing up allocation.  The
/// values a certified model deals in are small; exceeding this declines.
const MAX_INT_BITS: u64 = 4096;

/// Cap on the magnitude (in bits) of an intermediate rational's numerator and
/// denominator combined — the `Real` twin of [`MAX_INT_BITS`].
const MAX_RAT_BITS: u64 = 4096;

/// The arithmetic domain a node's RESULT lives in, read from its sort.
///
/// The evaluator is sort-driven, never value-driven: a Real-sorted `Div` over
/// two Int-valued operands is exact RATIONAL division (the SMT-LIB `/`,
/// `(/ 7 2)` is `7/2` — never the Euclidean `3`), while an Int-sorted `Div`
/// is Euclidean `div`. Deciding by operand value types instead would floor a
/// real quotient whenever both operands happen to carry integer model values
/// — a different value than the term denotes.
#[derive(Clone, Copy, PartialEq)]
enum ArithDomain {
    Int,
    Real,
}

/// Classify an arithmetic node's result sort; `None` for non-arithmetic
/// nodes (booleans, and everything the evaluator declines anyway).
fn arith_domain(sort: SortId, manager: &TermManager) -> Option<ArithDomain> {
    if sort == manager.sorts.real_sort {
        Some(ArithDomain::Real)
    } else if sort == manager.sorts.int_sort {
        Some(ArithDomain::Int)
    } else {
        None
    }
}

/// Why an evaluation stopped without a verdict.
#[derive(Debug, PartialEq, Eq)]
pub(crate) enum EvalError {
    /// The goal mentions something the certifier does not interpret (an
    /// unknown symbol, an unsupported operator, a sort mismatch).
    Unsupported,
    /// The step or domain budget ran out.
    Exhausted,
}

/// One pending obligation of the evaluation machine.
enum Step {
    /// Evaluate a term and push its value.
    Eval(TermId),
    /// Combine the operand values already on the value stack.
    Reduce(TermId),
    /// Build the enumeration domain for bound variable `var_pos` of a
    /// quantifier, then start looping over it.
    QuantEnter { term: TermId, var_pos: usize },
    /// One iteration of that loop.
    QuantIter {
        /// The quantifier node.
        term: TermId,
        /// Which of its bound variables this frame drives.
        var_pos: usize,
        /// Index of this frame's domain in the domain stack.
        domain_idx: usize,
        /// Next domain element to try.
        next: usize,
        /// Accumulated verdict so far.
        acc: bool,
        /// Environment length to restore before each binding.
        env_mark: usize,
    },
}

/// The evaluation machine's mutable state.
struct Machine {
    steps: Vec<Step>,
    values: Vec<CertValue>,
    env: Vec<(Spur, CertValue)>,
    domains: Vec<Vec<CertValue>>,
}

/// Decide `term` – which must be closed – under `interp`.
///
/// `critical` is the sorted, deduplicated set of integers that atoms can
/// distinguish (literals, pinned arguments and results, constant values,
/// defaults); the quantifier domains are derived from it plus the values of
/// enclosing bound variables.  `budget` bounds the total number of machine
/// steps and is decremented in place so a caller can spend one budget across
/// several assertions.
pub(crate) fn evaluate(
    term: TermId,
    interp: &Interpretation,
    manager: &TermManager,
    critical: &[BigInt],
    budget: &mut usize,
) -> Result<CertValue, EvalError> {
    let mut machine = Machine {
        steps: vec![Step::Eval(term)],
        values: Vec::new(),
        env: Vec::new(),
        domains: Vec::new(),
    };

    while let Some(step) = machine.steps.pop() {
        *budget = budget.checked_sub(1).ok_or(EvalError::Exhausted)?;
        match step {
            Step::Eval(t) => eval_step(&mut machine, t, interp, manager)?,
            Step::Reduce(t) => reduce_step(&mut machine, t, interp, manager)?,
            Step::QuantEnter { term, var_pos } => {
                quant_enter(&mut machine, term, var_pos, manager, critical)?;
            }
            Step::QuantIter {
                term,
                var_pos,
                domain_idx,
                next,
                acc,
                env_mark,
            } => {
                quant_iter(
                    &mut machine,
                    term,
                    var_pos,
                    domain_idx,
                    next,
                    acc,
                    env_mark,
                    manager,
                )?;
            }
        }
    }

    match machine.values.pop() {
        Some(value) if machine.values.is_empty() => Ok(value),
        _ => Err(EvalError::Unsupported),
    }
}

/// Expand one term into either a value or its operand obligations.
fn eval_step(
    machine: &mut Machine,
    term: TermId,
    interp: &Interpretation,
    manager: &TermManager,
) -> Result<(), EvalError> {
    let node = manager.get(term).ok_or(EvalError::Unsupported)?;
    match &node.kind {
        TermKind::True => machine.values.push(CertValue::Bool(true)),
        TermKind::False => machine.values.push(CertValue::Bool(false)),
        TermKind::IntConst(n) => machine.values.push(CertValue::Int(n.clone())),
        TermKind::RealConst(r) => machine
            .values
            .push(CertValue::Real(super::value::rational_of(*r))),
        TermKind::Var(name) => {
            let value = machine
                .env
                .iter()
                .rev()
                .find(|(n, _)| n == name)
                .map(|(_, v)| v.clone())
                .or_else(|| interp.consts.get(name).cloned())
                .ok_or(EvalError::Unsupported)?;
            machine.values.push(value);
        }
        TermKind::Forall { .. } | TermKind::Exists { .. } => {
            machine.steps.push(Step::QuantEnter { term, var_pos: 0 });
        }
        TermKind::Apply { args, .. } => {
            machine.steps.push(Step::Reduce(term));
            for &arg in args.iter().rev() {
                machine.steps.push(Step::Eval(arg));
            }
        }
        other => {
            let children = supported_children(other).ok_or(EvalError::Unsupported)?;
            machine.steps.push(Step::Reduce(term));
            for &child in children.iter().rev() {
                machine.steps.push(Step::Eval(child));
            }
        }
    }
    Ok(())
}

/// Pop this node's operand values and push the combined result.
fn reduce_step(
    machine: &mut Machine,
    term: TermId,
    interp: &Interpretation,
    manager: &TermManager,
) -> Result<(), EvalError> {
    let node = manager.get(term).ok_or(EvalError::Unsupported)?;
    let arity = match &node.kind {
        TermKind::Apply { args, .. } => args.len(),
        other => supported_children(other)
            .ok_or(EvalError::Unsupported)?
            .len(),
    };
    let start = machine
        .values
        .len()
        .checked_sub(arity)
        .ok_or(EvalError::Unsupported)?;
    let args: Vec<CertValue> = machine.values.split_off(start);

    // The node's own sort decides which arithmetic its result lives in (see
    // `ArithDomain`): comparisons and boolean operators pass `None`.
    let domain = arith_domain(node.sort, manager);
    let result = combine(&node.kind, &args, interp, domain)?;
    machine.values.push(result);
    Ok(())
}

/// Apply one operator to already-evaluated operands.
fn combine(
    kind: &TermKind,
    args: &[CertValue],
    interp: &Interpretation,
    domain: Option<ArithDomain>,
) -> Result<CertValue, EvalError> {
    let bool_at = |i: usize| -> Result<bool, EvalError> {
        args.get(i)
            .and_then(CertValue::as_bool)
            .ok_or(EvalError::Unsupported)
    };
    let int_at = |i: usize| -> Result<&BigInt, EvalError> {
        args.get(i)
            .and_then(CertValue::as_int)
            .ok_or(EvalError::Unsupported)
    };
    // Exact rational read with `Int` promotion — the value semantics of
    // mixed SMT-LIB arithmetic.
    let rat_at = |i: usize| -> Result<num_rational::BigRational, EvalError> {
        args.get(i)
            .and_then(|v| match v {
                CertValue::Int(n) => Some(num_rational::BigRational::from(n.clone())),
                CertValue::Real(r) => Some(r.clone()),
                CertValue::Bool(_) => None,
            })
            .ok_or(EvalError::Unsupported)
    };
    let rat_bits_ok = |r: &num_rational::BigRational| -> bool {
        r.numer().bits() + r.denom().bits() <= MAX_RAT_BITS
    };
    let order = |i: usize, j: usize| -> Result<Ordering, EvalError> {
        args.get(i)
            .zip(args.get(j))
            .and_then(|(l, r)| l.compare_numeric(r))
            .ok_or(EvalError::Unsupported)
    };

    let value = match kind {
        TermKind::Apply { func, .. } => {
            let interpretation = interp.funcs.get(func).ok_or(EvalError::Unsupported)?;
            interpretation.apply(args).clone()
        }
        TermKind::Not(_) => CertValue::Bool(!bool_at(0)?),
        TermKind::And(_) => {
            let mut acc = true;
            for i in 0..args.len() {
                acc &= bool_at(i)?;
            }
            CertValue::Bool(acc)
        }
        TermKind::Or(_) => {
            let mut acc = false;
            for i in 0..args.len() {
                acc |= bool_at(i)?;
            }
            CertValue::Bool(acc)
        }
        TermKind::Xor(_, _) => CertValue::Bool(bool_at(0)? ^ bool_at(1)?),
        TermKind::Implies(_, _) => CertValue::Bool(!bool_at(0)? || bool_at(1)?),
        TermKind::Ite(_, _, _) => {
            let branch = if bool_at(0)? { 1 } else { 2 };
            args.get(branch).ok_or(EvalError::Unsupported)?.clone()
        }
        TermKind::Eq(_, _) => {
            let (l, r) = (
                args.first().ok_or(EvalError::Unsupported)?,
                args.get(1).ok_or(EvalError::Unsupported)?,
            );
            // Numeric operands compare exactly with `Int`→`Real` promotion
            // (`3 = 3.0` is true); booleans only with booleans. A mixed
            // boolean/numeric pair is a malformed term, not a false
            // equality: decline rather than invent a verdict.
            let eq = l.numeric_eq(r).ok_or(EvalError::Unsupported)?;
            CertValue::Bool(eq)
        }
        TermKind::Distinct(_) => {
            let mut all_distinct = true;
            for (i, l) in args.iter().enumerate() {
                for r in args.iter().skip(i + 1) {
                    let ne = l.numeric_eq(r).ok_or(EvalError::Unsupported)?;
                    if !ne {
                        all_distinct = false;
                    }
                }
            }
            CertValue::Bool(all_distinct)
        }
        TermKind::Neg(_) => match domain {
            Some(ArithDomain::Real) => {
                let v = -rat_at(0)?;
                CertValue::Real(v)
            }
            _ => CertValue::Int(-int_at(0)?.clone()),
        },
        TermKind::Add(_) => match domain {
            Some(ArithDomain::Real) => {
                let mut acc = num_rational::BigRational::zero();
                for i in 0..args.len() {
                    acc += rat_at(i)?;
                    if !rat_bits_ok(&acc) {
                        return Err(EvalError::Exhausted);
                    }
                }
                CertValue::Real(acc)
            }
            _ => {
                let mut acc = BigInt::from(0);
                for i in 0..args.len() {
                    acc += int_at(i)?;
                }
                CertValue::Int(acc)
            }
        },
        TermKind::Sub(_, _) => match domain {
            Some(ArithDomain::Real) => {
                let v = rat_at(0)? - rat_at(1)?;
                if !rat_bits_ok(&v) {
                    return Err(EvalError::Exhausted);
                }
                CertValue::Real(v)
            }
            _ => CertValue::Int(int_at(0)? - int_at(1)?),
        },
        TermKind::Div(_, _) => {
            // SMT-LIB Euclidean integer division (the exact semantics the
            // builder's constant folder and `arith_axioms` use: the unique
            // `q` with `m = n·q + r`, `0 ≤ r < |n|`) for an Int-sorted
            // node, or exact rational division for a Real-sorted one —
            // decided by the node's SORT, never by the operand values
            // (see `ArithDomain`). A zero divisor is UNINTERPRETED per
            // SMT-LIB — decline rather than invent a value, so a model
            // resting on it stays uncertified (`Unknown`), never wrongly
            // trusted.
            match domain {
                Some(ArithDomain::Real) => {
                    let (a, b) = (rat_at(0)?, rat_at(1)?);
                    if b.is_zero() {
                        return Err(EvalError::Unsupported);
                    }
                    let v = a / b;
                    if !rat_bits_ok(&v) {
                        return Err(EvalError::Exhausted);
                    }
                    CertValue::Real(v)
                }
                _ => {
                    let (a, b) = (int_at(0)?, int_at(1)?);
                    if b.is_zero() {
                        return Err(EvalError::Unsupported);
                    }
                    CertValue::Int(a.div_euclid(b))
                }
            }
        }
        TermKind::Mod(_, _) => {
            // Euclidean remainder, `0 ≤ r < |n|` — Int-sort only (a
            // Real-sorted `Mod` is not an SMT-LIB term).  Zero divisor:
            // uninterpreted, decline.
            let (a, b) = (int_at(0)?, int_at(1)?);
            if b.is_zero() {
                return Err(EvalError::Unsupported);
            }
            CertValue::Int(a.rem_euclid(b))
        }
        TermKind::Mul(_) => match domain {
            Some(ArithDomain::Real) => {
                let mut acc = num_rational::BigRational::one();
                for i in 0..args.len() {
                    acc *= rat_at(i)?;
                    if !rat_bits_ok(&acc) {
                        return Err(EvalError::Exhausted);
                    }
                }
                CertValue::Real(acc)
            }
            _ => {
                let mut acc = BigInt::from(1);
                for i in 0..args.len() {
                    acc *= int_at(i)?;
                    if acc.bits() > MAX_INT_BITS {
                        return Err(EvalError::Exhausted);
                    }
                }
                CertValue::Int(acc)
            }
        },
        TermKind::Lt(_, _) => CertValue::Bool(order(0, 1)? == Ordering::Less),
        TermKind::Le(_, _) => CertValue::Bool(order(0, 1)? != Ordering::Greater),
        TermKind::Gt(_, _) => CertValue::Bool(order(0, 1)? == Ordering::Greater),
        TermKind::Ge(_, _) => CertValue::Bool(order(0, 1)? != Ordering::Less),
        _ => return Err(EvalError::Unsupported),
    };

    match (&value, domain) {
        (CertValue::Int(n), _) => {
            if n.bits() > MAX_INT_BITS {
                return Err(EvalError::Exhausted);
            }
        }
        (CertValue::Real(r), _) => {
            if !rat_bits_ok(r) {
                return Err(EvalError::Exhausted);
            }
        }
        (CertValue::Bool(_), _) => {}
    }
    Ok(value)
}

/// A quantifier node taken apart: its bound variables, its body, and whether it
/// is universal.
type QuantParts = (SmallVec<[(Spur, SortId); 2]>, TermId, bool);

/// Read a quantifier node's bound variables and body.
fn quant_parts(term: TermId, manager: &TermManager) -> Result<QuantParts, EvalError> {
    match manager.get(term).map(|t| &t.kind) {
        Some(TermKind::Forall { vars, body, .. }) => Ok((vars.clone(), *body, true)),
        Some(TermKind::Exists { vars, body, .. }) => Ok((vars.clone(), *body, false)),
        _ => Err(EvalError::Unsupported),
    }
}

/// Build the domain for one bound variable and open its iteration frame.
fn quant_enter(
    machine: &mut Machine,
    term: TermId,
    var_pos: usize,
    manager: &TermManager,
    critical: &[BigInt],
) -> Result<(), EvalError> {
    let (vars, _body, is_forall) = quant_parts(term, manager)?;
    let &(_, sort) = vars.get(var_pos).ok_or(EvalError::Unsupported)?;
    let domain = build_domain(sort, manager, critical, &machine.env)?;

    machine.domains.push(domain);
    let domain_idx = machine.domains.len() - 1;
    let env_mark = machine.env.len();
    machine.steps.push(Step::QuantIter {
        term,
        var_pos,
        domain_idx,
        next: 0,
        acc: is_forall,
        env_mark,
    });
    Ok(())
}

/// Advance one quantifier iteration: fold in the previous body verdict, then
/// either bind the next domain element or publish the accumulated result.
#[allow(clippy::too_many_arguments)]
fn quant_iter(
    machine: &mut Machine,
    term: TermId,
    var_pos: usize,
    domain_idx: usize,
    next: usize,
    acc: bool,
    env_mark: usize,
    manager: &TermManager,
) -> Result<(), EvalError> {
    let (vars, body, is_forall) = quant_parts(term, manager)?;
    let &(name, _) = vars.get(var_pos).ok_or(EvalError::Unsupported)?;

    let mut acc = acc;
    let mut settled = false;
    if next > 0 {
        let verdict = machine
            .values
            .pop()
            .and_then(|v| v.as_bool())
            .ok_or(EvalError::Unsupported)?;
        if is_forall {
            acc &= verdict;
            settled = !verdict;
        } else {
            acc |= verdict;
            settled = verdict;
        }
    }

    let domain_len = machine
        .domains
        .get(domain_idx)
        .ok_or(EvalError::Unsupported)?
        .len();

    if !settled && next < domain_len {
        let value = machine
            .domains
            .get(domain_idx)
            .and_then(|d| d.get(next))
            .ok_or(EvalError::Unsupported)?
            .clone();
        machine.env.truncate(env_mark);
        machine.env.push((name, value));
        machine.steps.push(Step::QuantIter {
            term,
            var_pos,
            domain_idx,
            next: next + 1,
            acc,
            env_mark,
        });
        if var_pos + 1 < vars.len() {
            machine.steps.push(Step::QuantEnter {
                term,
                var_pos: var_pos + 1,
            });
        } else {
            machine.steps.push(Step::Eval(body));
        }
    } else {
        machine.env.truncate(env_mark);
        // Every domain an inner variable opened is finished by now; truncating
        // is what releases them (and this frame's own domain).
        machine.domains.truncate(domain_idx);
        machine.values.push(CertValue::Bool(acc));
    }
    Ok(())
}

/// Build the exhaustive enumeration domain for a bound variable of `sort`.
///
/// `Bool` enumerates its whole domain.  `Int` enumerates every critical value
/// plus one representative of every non-empty gap between (and beyond) them –
/// the critical set being `critical` extended with the integer values of the
/// enclosing bound variables, which is what makes an inner variable able to
/// land below, on, and above an outer one.
fn build_domain(
    sort: SortId,
    manager: &TermManager,
    critical: &[BigInt],
    env: &[(Spur, CertValue)],
) -> Result<Vec<CertValue>, EvalError> {
    match value_sort(sort, manager).ok_or(EvalError::Unsupported)? {
        ValueSort::Bool => Ok(vec![CertValue::Bool(false), CertValue::Bool(true)]),
        // `Real` has no "next" element, so the gap representatives this domain
        // is built from do not exist; the real engine ([`super::real`]) decides
        // those goals symbolically instead.
        ValueSort::Real => Err(EvalError::Unsupported),
        ValueSort::Int => {
            let mut points: Vec<BigInt> = critical.to_vec();
            for (_, value) in env {
                if let CertValue::Int(n) = value {
                    points.push(n.clone());
                }
            }
            points.sort();
            points.dedup();

            if points.is_empty() {
                return Ok(vec![CertValue::Int(BigInt::from(0))]);
            }
            if points.len() * 2 + 2 > MAX_DOMAIN {
                return Err(EvalError::Exhausted);
            }

            let mut domain: Vec<CertValue> = Vec::with_capacity(points.len() * 2 + 2);
            let first = points.first().ok_or(EvalError::Unsupported)?;
            domain.push(CertValue::Int(first - 1));
            for (i, point) in points.iter().enumerate() {
                domain.push(CertValue::Int(point.clone()));
                if let Some(next) = points.get(i + 1)
                    && next - point >= BigInt::from(2)
                {
                    domain.push(CertValue::Int(point + 1));
                }
            }
            let last = points.last().ok_or(EvalError::Unsupported)?;
            domain.push(CertValue::Int(last + 1));
            Ok(domain)
        }
    }
}
