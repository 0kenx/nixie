//! Model validation utilities
//!
//! This module provides functionality to validate that a model satisfies
//! a set of assertions, which is crucial for correctness checking.

use crate::ast::{Model, ModelValue, TermId, TermKind, TermManager};
use crate::error::{OxizError, Result};
#[allow(unused_imports)]
use crate::prelude::*;
use num_bigint::{BigInt, BigUint};
use num_rational::BigRational;
use num_traits::{CheckedEuclid, One, ToPrimitive, Zero};

/// Work item of the iterative model evaluator.
enum EvalFrame {
    /// Classify a term and schedule whatever operands it needs.
    Enter(TermId),
    /// Sequential, short-circuiting fold of an `and`/`or` operand list.
    BoolFold {
        /// The `and`/`or` term being folded.
        id: TermId,
        /// Index of the operand whose value is now available.
        idx: usize,
        /// `true` for `and` (neutral value `true`), `false` for `or`.
        conjunction: bool,
    },
    /// The condition of an `ite` has been evaluated; pick a branch.
    IteBranch(TermId),
    /// Copy the value of the taken `ite` branch to the `ite` itself.
    IteResult {
        /// The `ite` term.
        id: TermId,
        /// The branch that was taken.
        branch: TermId,
    },
    /// Combine the values of all (strictly evaluated) operands.
    Combine(TermId),
}

/// Evaluate a term under a model with an explicit stack and a value cache.
///
/// This is the single implementation behind both [`eval_term`] and
/// [`CachedEvaluator`]. It replaces two structurally identical recursive
/// evaluators that had no depth bound at all – and the public `eval_term`
/// had no cache either, so it re-evaluated shared sub-terms once per path,
/// which is exponential on a hash-consed DAG.
///
/// The lazy evaluation order of the recursive form is preserved exactly:
/// `and`/`or` stop at the first decisive operand (so a `false` conjunct
/// still yields `false` even when a later conjunct is not evaluable), and
/// `ite` evaluates only the branch its condition selects.
fn eval_cached(
    root: TermId,
    manager: &TermManager,
    model: &Model,
    cache: &mut FxHashMap<TermId, Option<ModelValue>>,
) -> Option<ModelValue> {
    let mut stack = vec![EvalFrame::Enter(root)];

    while let Some(frame) = stack.pop() {
        match frame {
            EvalFrame::Enter(id) => {
                if cache.contains_key(&id) {
                    continue;
                }
                let Some(term) = manager.get(id) else {
                    cache.insert(id, None);
                    continue;
                };

                match &term.kind {
                    // Constants
                    TermKind::True => {
                        cache.insert(id, Some(ModelValue::Bool(true)));
                    }
                    TermKind::False => {
                        cache.insert(id, Some(ModelValue::Bool(false)));
                    }
                    TermKind::IntConst(n) => {
                        cache.insert(id, Some(ModelValue::Int(n.clone())));
                    }
                    TermKind::RealConst(r) => {
                        // Convert Rational<i64> to BigRational
                        let numer = BigInt::from(*r.numer());
                        let denom = BigInt::from(*r.denom());
                        cache.insert(id, Some(ModelValue::Real(BigRational::new(numer, denom))));
                    }
                    TermKind::BitVecConst { value, width } => {
                        // `ModelValue::BitVec` carries a `BigUint`, so every
                        // width is representable exactly. An earlier form took
                        // `value.iter_u64_digits().next()` – the *low 64 bits*
                        // – regardless of the declared width, so a 128-bit
                        // constant silently became a different value of the
                        // same declared width, and `validate_assertion` could
                        // certify a model that does not satisfy the assertion.
                        cache.insert(id, bitvec_const_value(value, *width));
                    }

                    // Variables - look up in model
                    TermKind::Var(_) => {
                        let value = model.get_assignment(id).cloned();
                        cache.insert(id, value);
                    }

                    // Uninterpreted function application: its value is
                    // whatever the model assigns to the application term
                    // (per-application lookup). As a *certificate* this is
                    // sound only together with the caller's congruence
                    // check: the lookups define the function's graph, which
                    // must be well-defined on equal argument values (see
                    // the certified-mode gate in oxiz-solver, which runs
                    // exactly that check before accepting a `Sat`).
                    TermKind::Apply { .. } => {
                        let value = model.get_assignment(id).cloned();
                        cache.insert(id, value);
                    }

                    // Distinct: evaluate every operand; the pairwise check
                    // happens in `Combine`. Zero or one operand is trivially
                    // distinct (SMT-LIB semantics).
                    TermKind::Distinct(args) => match args.first() {
                        None => {
                            cache.insert(id, Some(ModelValue::Bool(true)));
                        }
                        Some(_) => {
                            stack.push(EvalFrame::Combine(id));
                            for &arg in args.iter() {
                                stack.push(EvalFrame::Enter(arg));
                            }
                        }
                    },

                    // Short-circuiting boolean connectives
                    TermKind::And(args) | TermKind::Or(args) => {
                        let conjunction = matches!(&term.kind, TermKind::And(_));
                        match args.first() {
                            None => {
                                cache.insert(id, Some(ModelValue::Bool(conjunction)));
                            }
                            Some(&first) => {
                                stack.push(EvalFrame::BoolFold {
                                    id,
                                    idx: 0,
                                    conjunction,
                                });
                                stack.push(EvalFrame::Enter(first));
                            }
                        }
                    }

                    TermKind::Ite(cond, _, _) => {
                        stack.push(EvalFrame::IteBranch(id));
                        stack.push(EvalFrame::Enter(*cond));
                    }

                    // Strictly evaluated operators
                    TermKind::Not(arg)
                    | TermKind::Neg(arg)
                    | TermKind::BvNot(arg)
                    | TermKind::BvExtract { arg, .. } => {
                        stack.push(EvalFrame::Combine(id));
                        stack.push(EvalFrame::Enter(*arg));
                    }
                    TermKind::Implies(lhs, rhs)
                    | TermKind::Xor(lhs, rhs)
                    | TermKind::Eq(lhs, rhs)
                    | TermKind::Lt(lhs, rhs)
                    | TermKind::Le(lhs, rhs)
                    | TermKind::Gt(lhs, rhs)
                    | TermKind::Ge(lhs, rhs)
                    | TermKind::Sub(lhs, rhs)
                    | TermKind::Div(lhs, rhs)
                    | TermKind::Mod(lhs, rhs)
                    | TermKind::BvConcat(lhs, rhs)
                    | TermKind::BvAnd(lhs, rhs)
                    | TermKind::BvOr(lhs, rhs)
                    | TermKind::BvXor(lhs, rhs)
                    | TermKind::BvAdd(lhs, rhs)
                    | TermKind::BvSub(lhs, rhs)
                    | TermKind::BvMul(lhs, rhs)
                    | TermKind::BvUdiv(lhs, rhs)
                    | TermKind::BvSdiv(lhs, rhs)
                    | TermKind::BvUrem(lhs, rhs)
                    | TermKind::BvSrem(lhs, rhs)
                    | TermKind::BvShl(lhs, rhs)
                    | TermKind::BvLshr(lhs, rhs)
                    | TermKind::BvAshr(lhs, rhs)
                    | TermKind::BvUlt(lhs, rhs)
                    | TermKind::BvUle(lhs, rhs)
                    | TermKind::BvSlt(lhs, rhs)
                    | TermKind::BvSle(lhs, rhs) => {
                        stack.push(EvalFrame::Combine(id));
                        stack.push(EvalFrame::Enter(*lhs));
                        stack.push(EvalFrame::Enter(*rhs));
                    }
                    TermKind::Add(args) | TermKind::Mul(args) => {
                        stack.push(EvalFrame::Combine(id));
                        for &arg in args.iter() {
                            stack.push(EvalFrame::Enter(arg));
                        }
                    }
                    // `Distinct` operands are scheduled the same way; its
                    // `Combine` case performs the pairwise comparison.

                    // For other operations, we can't evaluate without more
                    // information: an honest "unknown", never a default value.
                    _ => {
                        cache.insert(id, None);
                    }
                }
            }

            EvalFrame::BoolFold {
                id,
                idx,
                conjunction,
            } => {
                let Some(term) = manager.get(id) else {
                    cache.insert(id, None);
                    continue;
                };
                let args = match &term.kind {
                    TermKind::And(args) | TermKind::Or(args) => args,
                    // `BoolFold` is only ever scheduled for `and`/`or`.
                    _ => {
                        cache.insert(id, None);
                        continue;
                    }
                };
                let Some(&current) = args.get(idx) else {
                    cache.insert(id, Some(ModelValue::Bool(conjunction)));
                    continue;
                };

                match cache.get(&current).cloned().flatten() {
                    Some(ModelValue::Bool(b)) if b != conjunction => {
                        // Decisive operand: `false` in a conjunction, `true`
                        // in a disjunction.
                        cache.insert(id, Some(ModelValue::Bool(b)));
                    }
                    Some(ModelValue::Bool(_)) => match args.get(idx + 1) {
                        Some(&next) => {
                            stack.push(EvalFrame::BoolFold {
                                id,
                                idx: idx + 1,
                                conjunction,
                            });
                            stack.push(EvalFrame::Enter(next));
                        }
                        None => {
                            cache.insert(id, Some(ModelValue::Bool(conjunction)));
                        }
                    },
                    _ => {
                        cache.insert(id, None);
                    }
                }
            }

            EvalFrame::IteBranch(id) => {
                let Some(term) = manager.get(id) else {
                    cache.insert(id, None);
                    continue;
                };
                let TermKind::Ite(cond, then_branch, else_branch) = &term.kind else {
                    cache.insert(id, None);
                    continue;
                };
                let branch = match cache.get(cond).cloned().flatten() {
                    Some(ModelValue::Bool(true)) => *then_branch,
                    Some(ModelValue::Bool(false)) => *else_branch,
                    _ => {
                        cache.insert(id, None);
                        continue;
                    }
                };
                stack.push(EvalFrame::IteResult { id, branch });
                stack.push(EvalFrame::Enter(branch));
            }

            EvalFrame::IteResult { id, branch } => {
                let value = cache.get(&branch).cloned().flatten();
                cache.insert(id, value);
            }

            EvalFrame::Combine(id) => {
                let Some(term) = manager.get(id) else {
                    cache.insert(id, None);
                    continue;
                };
                let operand = |child: &TermId,
                               cache: &FxHashMap<TermId, Option<ModelValue>>|
                 -> Option<ModelValue> {
                    cache.get(child).cloned().flatten()
                };

                let value = match &term.kind {
                    TermKind::Not(arg) => match operand(arg, cache) {
                        Some(ModelValue::Bool(b)) => Some(ModelValue::Bool(!b)),
                        _ => None,
                    },
                    TermKind::Implies(lhs, rhs) => {
                        match (operand(lhs, cache), operand(rhs, cache)) {
                            (Some(ModelValue::Bool(a)), Some(ModelValue::Bool(b))) => {
                                Some(ModelValue::Bool(!a || b))
                            }
                            _ => None,
                        }
                    }
                    TermKind::Xor(lhs, rhs) => match (operand(lhs, cache), operand(rhs, cache)) {
                        (Some(ModelValue::Bool(a)), Some(ModelValue::Bool(b))) => {
                            Some(ModelValue::Bool(a != b))
                        }
                        _ => None,
                    },
                    TermKind::Eq(lhs, rhs) => match (operand(lhs, cache), operand(rhs, cache)) {
                        (Some(a), Some(b)) => Some(ModelValue::Bool(a == b)),
                        _ => None,
                    },
                    TermKind::Distinct(args) => {
                        // Every operand must be fully evaluated — no partial
                        // judgement on a partial table. The comparison is
                        // structural over `ModelValue` (derived `Eq`):
                        // uninterpreted values compare by (sort, id), so two
                        // witnesses are equal exactly when they denote the
                        // same domain element.
                        let values: Option<Vec<ModelValue>> =
                            args.iter().map(|a| operand(a, cache)).collect();
                        values.map(|vs| {
                            ModelValue::Bool((1..vs.len()).all(|i| (0..i).all(|j| vs[i] != vs[j])))
                        })
                    }
                    TermKind::Lt(lhs, rhs) => match (operand(lhs, cache), operand(rhs, cache)) {
                        (Some(a), Some(b)) => compare_lt(&a, &b).map(ModelValue::Bool),
                        _ => None,
                    },
                    TermKind::Le(lhs, rhs) => match (operand(lhs, cache), operand(rhs, cache)) {
                        (Some(a), Some(b)) => compare_le(&a, &b).map(ModelValue::Bool),
                        _ => None,
                    },
                    TermKind::Gt(lhs, rhs) => match (operand(lhs, cache), operand(rhs, cache)) {
                        (Some(a), Some(b)) => compare_lt(&b, &a).map(ModelValue::Bool),
                        _ => None,
                    },
                    TermKind::Ge(lhs, rhs) => match (operand(lhs, cache), operand(rhs, cache)) {
                        (Some(a), Some(b)) => compare_le(&b, &a).map(ModelValue::Bool),
                        _ => None,
                    },
                    TermKind::Add(args) => {
                        fold_operands(args, ModelValue::Int(BigInt::zero()), add_values, cache)
                    }
                    TermKind::Mul(args) => {
                        fold_operands(args, ModelValue::Int(BigInt::one()), mul_values, cache)
                    }
                    TermKind::Sub(lhs, rhs) => match (operand(lhs, cache), operand(rhs, cache)) {
                        (Some(a), Some(b)) => sub_values(&a, &b),
                        _ => None,
                    },
                    TermKind::Neg(arg) => operand(arg, cache).and_then(|v| neg_value(&v)),
                    TermKind::Div(lhs, rhs) => match (operand(lhs, cache), operand(rhs, cache)) {
                        (Some(a), Some(b)) => div_values(&a, &b),
                        _ => None,
                    },
                    TermKind::Mod(lhs, rhs) => match (operand(lhs, cache), operand(rhs, cache)) {
                        (Some(a), Some(b)) => mod_values(&a, &b),
                        _ => None,
                    },
                    // Bit-vector operations (simplified - full implementation
                    // would be more complex)
                    TermKind::BvNot(arg) => match operand(arg, cache) {
                        // Complementing within the declared width is exact at
                        // any width: XOR with the all-ones mask. Only width 0
                        // (not a legal bit-vector sort) is refused.
                        Some(ModelValue::BitVec { value, width }) => {
                            bitvec_width_mask(width).map(|mask| ModelValue::BitVec {
                                value: (value & &mask) ^ mask,
                                width,
                            })
                        }
                        _ => None,
                    },
                    TermKind::BvAnd(lhs, rhs) => match (operand(lhs, cache), operand(rhs, cache)) {
                        (
                            Some(ModelValue::BitVec {
                                value: v1,
                                width: w1,
                            }),
                            Some(ModelValue::BitVec {
                                value: v2,
                                width: w2,
                            }),
                        ) if w1 == w2 => bitvec_width_mask(w1).map(|mask| ModelValue::BitVec {
                            value: v1 & v2 & mask,
                            width: w1,
                        }),
                        _ => None,
                    },
                    TermKind::BvOr(lhs, rhs) => {
                        bv_binary(operand(lhs, cache), operand(rhs, cache), ExactBvOp::Or)
                    }
                    TermKind::BvXor(lhs, rhs) => {
                        bv_binary(operand(lhs, cache), operand(rhs, cache), ExactBvOp::Xor)
                    }
                    TermKind::BvAdd(lhs, rhs) => {
                        bv_binary(operand(lhs, cache), operand(rhs, cache), ExactBvOp::Add)
                    }
                    TermKind::BvSub(lhs, rhs) => {
                        bv_binary(operand(lhs, cache), operand(rhs, cache), ExactBvOp::Sub)
                    }
                    TermKind::BvMul(lhs, rhs) => {
                        bv_binary(operand(lhs, cache), operand(rhs, cache), ExactBvOp::Mul)
                    }
                    TermKind::BvUdiv(lhs, rhs) => {
                        bv_binary(operand(lhs, cache), operand(rhs, cache), ExactBvOp::Udiv)
                    }
                    TermKind::BvSdiv(lhs, rhs) => {
                        bv_binary(operand(lhs, cache), operand(rhs, cache), ExactBvOp::Sdiv)
                    }
                    TermKind::BvUrem(lhs, rhs) => {
                        bv_binary(operand(lhs, cache), operand(rhs, cache), ExactBvOp::Urem)
                    }
                    TermKind::BvSrem(lhs, rhs) => {
                        bv_binary(operand(lhs, cache), operand(rhs, cache), ExactBvOp::Srem)
                    }
                    TermKind::BvShl(lhs, rhs) => {
                        bv_binary(operand(lhs, cache), operand(rhs, cache), ExactBvOp::Shl)
                    }
                    TermKind::BvLshr(lhs, rhs) => {
                        bv_binary(operand(lhs, cache), operand(rhs, cache), ExactBvOp::Lshr)
                    }
                    TermKind::BvAshr(lhs, rhs) => {
                        bv_binary(operand(lhs, cache), operand(rhs, cache), ExactBvOp::Ashr)
                    }
                    TermKind::BvUlt(lhs, rhs) => {
                        bv_binary(operand(lhs, cache), operand(rhs, cache), ExactBvOp::Ult)
                    }
                    TermKind::BvUle(lhs, rhs) => {
                        bv_binary(operand(lhs, cache), operand(rhs, cache), ExactBvOp::Ule)
                    }
                    TermKind::BvSlt(lhs, rhs) => {
                        bv_binary(operand(lhs, cache), operand(rhs, cache), ExactBvOp::Slt)
                    }
                    TermKind::BvSle(lhs, rhs) => {
                        bv_binary(operand(lhs, cache), operand(rhs, cache), ExactBvOp::Sle)
                    }
                    TermKind::BvConcat(lhs, rhs) => {
                        bv_concat(operand(lhs, cache), operand(rhs, cache))
                    }
                    TermKind::BvExtract { high, low, arg } => {
                        bv_extract(operand(arg, cache), *high, *low)
                    }
                    // `Combine` is only ever scheduled for the kinds above.
                    _ => None,
                };
                cache.insert(id, value);
            }
        }
    }

    cache.get(&root).cloned().flatten()
}

/// The all-ones mask for `width` bits, or `None` if `width` is 0.
///
/// [`ModelValue::BitVec`] stores an arbitrary-precision bit pattern, so every
/// legal width is representable exactly. `width == 0` is not a legal
/// bit-vector sort, and refusing it is an honest failure rather than a
/// silently clamped mask.
fn bitvec_width_mask(width: u32) -> Option<BigUint> {
    match width {
        0 => None,
        w => Some(crate::ast::model::bitvec_mask(w)),
    }
}

/// Convert a bit-vector constant into a model value.
///
/// The mathematical value is reduced modulo `2^width` (the standard SMT-LIB
/// bit-vector interpretation, which also gives negative literals their
/// two's-complement bit pattern). The reduction is exact at every width, so
/// wide constants are evaluated rather than reported as unknown; only the
/// illegal `width == 0` sort yields `None`.
fn bitvec_const_value(value: &BigInt, width: u32) -> Option<ModelValue> {
    if width == 0 {
        return None;
    }
    Some(ModelValue::from_bitvec_int(value, width))
}

#[derive(Clone, Copy)]
enum ExactBvOp {
    Or,
    Xor,
    Add,
    Sub,
    Mul,
    Udiv,
    Sdiv,
    Urem,
    Srem,
    Shl,
    Lshr,
    Ashr,
    Ult,
    Ule,
    Slt,
    Sle,
}

fn bv_binary(
    lhs: Option<ModelValue>,
    rhs: Option<ModelValue>,
    op: ExactBvOp,
) -> Option<ModelValue> {
    let (
        ModelValue::BitVec { value: lhs, width },
        ModelValue::BitVec {
            value: rhs,
            width: rhs_width,
        },
    ) = (lhs?, rhs?)
    else {
        return None;
    };
    if width == 0 || width != rhs_width {
        return None;
    }

    let mask = bitvec_width_mask(width)?;
    let modulus = &mask + BigUint::one();
    let lhs = lhs & &mask;
    let rhs = rhs & &mask;
    let lhs_negative = bv_is_negative(&lhs, width);
    let rhs_negative = bv_is_negative(&rhs, width);
    let bits = |value: BigUint| Some(ModelValue::from_bitvec_bits(value, width));
    let signed_cmp = || match (lhs_negative, rhs_negative) {
        (false, false) | (true, true) => lhs.cmp(&rhs),
        (true, false) => core::cmp::Ordering::Less,
        (false, true) => core::cmp::Ordering::Greater,
    };

    match op {
        ExactBvOp::Or => bits(lhs | rhs),
        ExactBvOp::Xor => bits(lhs ^ rhs),
        ExactBvOp::Add => bits((lhs + rhs) % &modulus),
        ExactBvOp::Sub => bits((&lhs + &modulus - rhs) % &modulus),
        ExactBvOp::Mul => bits((lhs * rhs) % &modulus),
        ExactBvOp::Udiv => {
            if rhs.is_zero() {
                bits(mask)
            } else {
                bits(lhs / rhs)
            }
        }
        ExactBvOp::Urem => {
            if rhs.is_zero() {
                bits(lhs)
            } else {
                bits(lhs % rhs)
            }
        }
        ExactBvOp::Sdiv => {
            if rhs.is_zero() {
                return if lhs_negative {
                    bits(BigUint::one())
                } else {
                    bits(mask)
                };
            }
            let abs_lhs = if lhs_negative {
                bv_negate(&lhs, &modulus)
            } else {
                lhs
            };
            let abs_rhs = if rhs_negative {
                bv_negate(&rhs, &modulus)
            } else {
                rhs
            };
            let quotient = abs_lhs / abs_rhs;
            bits(if lhs_negative != rhs_negative {
                bv_negate(&quotient, &modulus)
            } else {
                quotient
            })
        }
        ExactBvOp::Srem => {
            if rhs.is_zero() {
                return bits(lhs);
            }
            let abs_lhs = if lhs_negative {
                bv_negate(&lhs, &modulus)
            } else {
                lhs
            };
            let abs_rhs = if rhs_negative {
                bv_negate(&rhs, &modulus)
            } else {
                rhs
            };
            let remainder = abs_lhs % abs_rhs;
            bits(if lhs_negative {
                bv_negate(&remainder, &modulus)
            } else {
                remainder
            })
        }
        ExactBvOp::Shl | ExactBvOp::Lshr | ExactBvOp::Ashr => {
            if rhs >= BigUint::from(width) {
                return match op {
                    ExactBvOp::Ashr if lhs_negative => bits(mask),
                    _ => bits(BigUint::ZERO),
                };
            }
            let shift = rhs.to_u32()?;
            match op {
                ExactBvOp::Shl => bits((lhs << shift) & mask),
                ExactBvOp::Lshr => bits(lhs >> shift),
                ExactBvOp::Ashr if lhs_negative => {
                    let shifted = &lhs >> shift;
                    let fill = &mask ^ (&mask >> shift);
                    bits(shifted | fill)
                }
                ExactBvOp::Ashr => bits(lhs >> shift),
                _ => None,
            }
        }
        ExactBvOp::Ult => Some(ModelValue::Bool(lhs < rhs)),
        ExactBvOp::Ule => Some(ModelValue::Bool(lhs <= rhs)),
        ExactBvOp::Slt => Some(ModelValue::Bool(signed_cmp() == core::cmp::Ordering::Less)),
        ExactBvOp::Sle => Some(ModelValue::Bool(
            signed_cmp() != core::cmp::Ordering::Greater,
        )),
    }
}

fn bv_is_negative(value: &BigUint, width: u32) -> bool {
    width != 0 && ((value >> (width - 1)) & BigUint::one()) == BigUint::one()
}

fn bv_negate(value: &BigUint, modulus: &BigUint) -> BigUint {
    if value.is_zero() {
        BigUint::ZERO
    } else {
        modulus - value
    }
}

fn bv_concat(lhs: Option<ModelValue>, rhs: Option<ModelValue>) -> Option<ModelValue> {
    let (
        ModelValue::BitVec {
            value: lhs,
            width: lhs_width,
        },
        ModelValue::BitVec {
            value: rhs,
            width: rhs_width,
        },
    ) = (lhs?, rhs?)
    else {
        return None;
    };
    if lhs_width == 0 || rhs_width == 0 {
        return None;
    }
    let width = lhs_width.checked_add(rhs_width)?;
    Some(ModelValue::from_bitvec_bits(
        (lhs << rhs_width) | rhs,
        width,
    ))
}

fn bv_extract(value: Option<ModelValue>, high: u32, low: u32) -> Option<ModelValue> {
    let ModelValue::BitVec {
        value,
        width: source_width,
    } = value?
    else {
        return None;
    };
    if high < low || high >= source_width {
        return None;
    }
    let width = high.checked_sub(low)?.checked_add(1)?;
    Some(ModelValue::from_bitvec_bits(value >> low, width))
}

/// Left-fold the already-evaluated operands of an n-ary arithmetic term.
///
/// An empty operand list yields the neutral element, exactly as the
/// recursive evaluator did.
fn fold_operands(
    args: &[TermId],
    neutral: ModelValue,
    combine: fn(&ModelValue, &ModelValue) -> Option<ModelValue>,
    cache: &FxHashMap<TermId, Option<ModelValue>>,
) -> Option<ModelValue> {
    let Some((first, rest)) = args.split_first() else {
        return Some(neutral);
    };
    let mut result = cache.get(first).cloned().flatten()?;
    for arg in rest {
        let value = cache.get(arg).cloned().flatten()?;
        result = combine(&result, &value)?;
    }
    Some(result)
}

/// Evaluate a term under a given model
///
/// Returns `None` if the term cannot be fully evaluated (e.g., uninterpreted function
/// without interpretation, or variable without assignment).
pub fn eval_term(term_id: TermId, manager: &TermManager, model: &Model) -> Option<ModelValue> {
    let mut cache = FxHashMap::default();
    eval_cached(term_id, manager, model, &mut cache)
}

/// Validate that a model satisfies an assertion
pub fn validate_assertion(assertion: TermId, manager: &TermManager, model: &Model) -> Result<bool> {
    match eval_term(assertion, manager, model) {
        Some(ModelValue::Bool(b)) => Ok(b),
        Some(_) => Err(OxizError::Internal(
            "Assertion did not evaluate to a boolean value".to_string(),
        )),
        None => Err(OxizError::Internal(
            "Could not fully evaluate assertion under model".to_string(),
        )),
    }
}

/// Validate that a model satisfies all assertions
pub fn validate_model(assertions: &[TermId], manager: &TermManager, model: &Model) -> Result<bool> {
    for &assertion in assertions {
        if !validate_assertion(assertion, manager, model)? {
            return Ok(false);
        }
    }
    Ok(true)
}

/// Cached term evaluator for improved performance
///
/// This evaluator maintains a cache of already-evaluated terms to avoid
/// redundant computation when the same subterms appear multiple times.
pub struct CachedEvaluator<'a> {
    manager: &'a TermManager,
    model: &'a Model,
    cache: FxHashMap<TermId, Option<ModelValue>>,
}

impl<'a> CachedEvaluator<'a> {
    /// Create a new cached evaluator
    #[must_use]
    pub fn new(manager: &'a TermManager, model: &'a Model) -> Self {
        Self {
            manager,
            model,
            cache: FxHashMap::default(),
        }
    }

    /// Evaluate a term using the cache
    pub fn eval(&mut self, term_id: TermId) -> Option<ModelValue> {
        // Check cache first
        if let Some(cached) = self.cache.get(&term_id) {
            return cached.clone();
        }

        // Evaluate and cache the result
        let result = eval_term_internal(term_id, self.manager, self.model, &mut self.cache);
        self.cache.insert(term_id, result.clone());
        result
    }

    /// Validate an assertion using the cached evaluator
    pub fn validate_assertion(&mut self, assertion: TermId) -> Result<bool> {
        match self.eval(assertion) {
            Some(ModelValue::Bool(b)) => Ok(b),
            Some(_) => Err(OxizError::Internal(
                "Assertion did not evaluate to a boolean value".to_string(),
            )),
            None => Err(OxizError::Internal(
                "Could not fully evaluate assertion under model".to_string(),
            )),
        }
    }

    /// Validate multiple assertions using the cached evaluator
    pub fn validate_assertions(&mut self, assertions: &[TermId]) -> Result<bool> {
        for &assertion in assertions {
            if !self.validate_assertion(assertion)? {
                return Ok(false);
            }
        }
        Ok(true)
    }

    /// Get the number of cached evaluations
    #[must_use]
    pub fn cache_size(&self) -> usize {
        self.cache.len()
    }

    /// Clear the evaluation cache
    pub fn clear_cache(&mut self) {
        self.cache.clear();
    }
}

/// Internal evaluation function that uses the cache
fn eval_term_internal(
    term_id: TermId,
    manager: &TermManager,
    model: &Model,
    cache: &mut FxHashMap<TermId, Option<ModelValue>>,
) -> Option<ModelValue> {
    eval_cached(term_id, manager, model, cache)
}

// Helper functions for arithmetic operations

fn compare_lt(lhs: &ModelValue, rhs: &ModelValue) -> Option<bool> {
    match (lhs, rhs) {
        (ModelValue::Int(a), ModelValue::Int(b)) => Some(a < b),
        (ModelValue::Real(a), ModelValue::Real(b)) => Some(a < b),
        _ => None,
    }
}

fn compare_le(lhs: &ModelValue, rhs: &ModelValue) -> Option<bool> {
    match (lhs, rhs) {
        (ModelValue::Int(a), ModelValue::Int(b)) => Some(a <= b),
        (ModelValue::Real(a), ModelValue::Real(b)) => Some(a <= b),
        _ => None,
    }
}

fn add_values(lhs: &ModelValue, rhs: &ModelValue) -> Option<ModelValue> {
    match (lhs, rhs) {
        (ModelValue::Int(a), ModelValue::Int(b)) => Some(ModelValue::Int(a + b)),
        (ModelValue::Real(a), ModelValue::Real(b)) => Some(ModelValue::Real(a + b)),
        _ => None,
    }
}

fn mul_values(lhs: &ModelValue, rhs: &ModelValue) -> Option<ModelValue> {
    match (lhs, rhs) {
        (ModelValue::Int(a), ModelValue::Int(b)) => Some(ModelValue::Int(a * b)),
        (ModelValue::Real(a), ModelValue::Real(b)) => Some(ModelValue::Real(a * b)),
        _ => None,
    }
}

fn sub_values(lhs: &ModelValue, rhs: &ModelValue) -> Option<ModelValue> {
    match (lhs, rhs) {
        (ModelValue::Int(a), ModelValue::Int(b)) => Some(ModelValue::Int(a - b)),
        (ModelValue::Real(a), ModelValue::Real(b)) => Some(ModelValue::Real(a - b)),
        _ => None,
    }
}

fn neg_value(val: &ModelValue) -> Option<ModelValue> {
    match val {
        ModelValue::Int(n) => Some(ModelValue::Int(-n)),
        ModelValue::Real(r) => Some(ModelValue::Real(-r)),
        _ => None,
    }
}

fn div_values(lhs: &ModelValue, rhs: &ModelValue) -> Option<ModelValue> {
    match (lhs, rhs) {
        (ModelValue::Int(a), ModelValue::Int(b)) if !b.is_zero() => {
            a.checked_div_euclid(b).map(ModelValue::Int)
        }
        (ModelValue::Real(a), ModelValue::Real(b)) if !b.is_zero() => Some(ModelValue::Real(a / b)),
        _ => None,
    }
}

fn mod_values(lhs: &ModelValue, rhs: &ModelValue) -> Option<ModelValue> {
    match (lhs, rhs) {
        (ModelValue::Int(a), ModelValue::Int(b)) if !b.is_zero() => {
            a.checked_rem_euclid(b).map(ModelValue::Int)
        }
        _ => None,
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use num_bigint::BigInt;

    #[test]
    fn test_eval_constants() {
        let mut manager = TermManager::new();
        let model = Model::new();

        let true_term = manager.mk_true();
        assert_eq!(
            eval_term(true_term, &manager, &model),
            Some(ModelValue::Bool(true))
        );

        let false_term = manager.mk_false();
        assert_eq!(
            eval_term(false_term, &manager, &model),
            Some(ModelValue::Bool(false))
        );

        let int_term = manager.mk_int(42);
        assert_eq!(
            eval_term(int_term, &manager, &model),
            Some(ModelValue::Int(BigInt::from(42)))
        );
    }

    #[test]
    fn test_eval_variable() {
        let mut manager = TermManager::new();
        let mut model = Model::new();

        let x = manager.mk_var("x", manager.sorts.int_sort);
        model.assign_int(x, BigInt::from(10));

        assert_eq!(
            eval_term(x, &manager, &model),
            Some(ModelValue::Int(BigInt::from(10)))
        );
    }

    #[test]
    fn test_eval_arithmetic() {
        let mut manager = TermManager::new();
        let model = Model::new();

        // 2 + 3 = 5
        let two = manager.mk_int(2);
        let three = manager.mk_int(3);
        let sum = manager.mk_add(vec![two, three]);

        assert_eq!(
            eval_term(sum, &manager, &model),
            Some(ModelValue::Int(BigInt::from(5)))
        );

        // 2 * 3 = 6
        let prod = manager.mk_mul(vec![two, three]);
        assert_eq!(
            eval_term(prod, &manager, &model),
            Some(ModelValue::Int(BigInt::from(6)))
        );
    }

    #[test]
    fn test_eval_comparison() {
        let mut manager = TermManager::new();
        let model = Model::new();

        let two = manager.mk_int(2);
        let three = manager.mk_int(3);

        // 2 < 3 = true
        let lt = manager.mk_lt(two, three);
        assert_eq!(
            eval_term(lt, &manager, &model),
            Some(ModelValue::Bool(true))
        );

        // 2 > 3 = false
        let gt = manager.mk_gt(two, three);
        assert_eq!(
            eval_term(gt, &manager, &model),
            Some(ModelValue::Bool(false))
        );
    }

    #[test]
    fn test_validate_assertion_simple() {
        let manager = TermManager::new();
        let model = Model::new();

        // true
        let assertion = manager.mk_true();
        assert!(
            validate_assertion(assertion, &manager, &model).expect("test operation should succeed")
        );

        // false
        let assertion = manager.mk_false();
        assert!(
            !validate_assertion(assertion, &manager, &model)
                .expect("test operation should succeed")
        );
    }

    #[test]
    fn test_validate_assertion_with_variable() {
        let mut manager = TermManager::new();
        let mut model = Model::new();

        let x = manager.mk_var("x", manager.sorts.int_sort);
        let five = manager.mk_int(5);

        // x = 5
        let eq = manager.mk_eq(x, five);

        // Model: x = 5
        model.assign_int(x, BigInt::from(5));
        assert!(validate_assertion(eq, &manager, &model).expect("test operation should succeed"));

        // Model: x = 10
        model.assign_int(x, BigInt::from(10));
        assert!(!validate_assertion(eq, &manager, &model).expect("test operation should succeed"));
    }

    #[test]
    fn test_validate_model_multiple_assertions() {
        let mut manager = TermManager::new();
        let mut model = Model::new();

        let x = manager.mk_var("x", manager.sorts.int_sort);
        let y = manager.mk_var("y", manager.sorts.int_sort);

        // x > 0
        let zero = manager.mk_int(0);
        let assertion1 = manager.mk_gt(x, zero);

        // y < 10
        let ten = manager.mk_int(10);
        let assertion2 = manager.mk_lt(y, ten);

        // x + y = 15
        let sum = manager.mk_add(vec![x, y]);
        let fifteen = manager.mk_int(15);
        let assertion3 = manager.mk_eq(sum, fifteen);

        let assertions = vec![assertion1, assertion2, assertion3];

        // Model: x = 5, y = 10 (doesn't satisfy y < 10)
        model.assign_int(x, BigInt::from(5));
        model.assign_int(y, BigInt::from(10));
        assert!(
            !validate_model(&assertions, &manager, &model).expect("test operation should succeed")
        );

        // Model: x = 7, y = 8 (satisfies all)
        model.assign_int(x, BigInt::from(7));
        model.assign_int(y, BigInt::from(8));
        assert!(
            validate_model(&assertions, &manager, &model).expect("test operation should succeed")
        );
    }

    #[test]
    fn test_eval_ite() {
        let mut manager = TermManager::new();
        let model = Model::new();

        let cond = manager.mk_true();
        let then_val = manager.mk_int(1);
        let else_val = manager.mk_int(2);

        let ite = manager.mk_ite(cond, then_val, else_val);

        assert_eq!(
            eval_term(ite, &manager, &model),
            Some(ModelValue::Int(BigInt::from(1)))
        );
    }

    #[test]
    fn test_cached_evaluator_basic() {
        let manager = TermManager::new();
        let model = Model::new();

        let mut evaluator = CachedEvaluator::new(&manager, &model);

        let true_term = manager.mk_true();
        assert_eq!(evaluator.eval(true_term), Some(ModelValue::Bool(true)));

        // Evaluating again should use the cache
        assert_eq!(evaluator.eval(true_term), Some(ModelValue::Bool(true)));
        assert_eq!(evaluator.cache_size(), 1);
    }

    #[test]
    fn test_cached_evaluator_shared_subterms() {
        let mut manager = TermManager::new();
        let mut model = Model::new();

        let x = manager.mk_var("x", manager.sorts.int_sort);
        model.assign_int(x, BigInt::from(5));

        let two = manager.mk_int(2);
        let x_plus_2 = manager.mk_add(vec![x, two]);

        // Build two terms that share the x+2 subterm
        // (x+2) * 3 and (x+2) + 4
        let three = manager.mk_int(3);
        let four = manager.mk_int(4);
        let term1 = manager.mk_mul(vec![x_plus_2, three]);
        let term2 = manager.mk_add(vec![x_plus_2, four]);

        let mut evaluator = CachedEvaluator::new(&manager, &model);

        // Evaluate first term - should cache x+2
        let result1 = evaluator.eval(term1);
        assert_eq!(result1, Some(ModelValue::Int(BigInt::from(21)))); // (5+2)*3 = 21

        // Evaluate second term - should reuse cached x+2
        let result2 = evaluator.eval(term2);
        assert_eq!(result2, Some(ModelValue::Int(BigInt::from(11)))); // (5+2)+4 = 11

        // Cache should contain entries for x, two, x+2, three, term1, four, term2
        assert!(evaluator.cache_size() >= 5);
    }

    #[test]
    fn test_cached_evaluator_validate_assertions() {
        let mut manager = TermManager::new();
        let mut model = Model::new();

        let x = manager.mk_var("x", manager.sorts.int_sort);
        let y = manager.mk_var("y", manager.sorts.int_sort);

        model.assign_int(x, BigInt::from(5));
        model.assign_int(y, BigInt::from(10));

        // Create assertions
        let zero = manager.mk_int(0);
        let fifteen = manager.mk_int(15);

        let assertion1 = manager.mk_gt(x, zero); // x > 0
        let assertion2 = manager.mk_gt(y, x); // y > x
        let sum = manager.mk_add(vec![x, y]);
        let assertion3 = manager.mk_eq(sum, fifteen); // x + y = 15

        let assertions = vec![assertion1, assertion2, assertion3];

        let mut evaluator = CachedEvaluator::new(&manager, &model);

        // All assertions should be satisfied
        assert!(
            evaluator
                .validate_assertions(&assertions)
                .expect("test operation should succeed")
        );
    }

    #[test]
    fn test_cached_evaluator_clear_cache() {
        let manager = TermManager::new();
        let model = Model::new();

        let mut evaluator = CachedEvaluator::new(&manager, &model);

        let true_term = manager.mk_true();
        evaluator.eval(true_term);
        assert_eq!(evaluator.cache_size(), 1);

        evaluator.clear_cache();
        assert_eq!(evaluator.cache_size(), 0);
    }

    #[test]
    fn test_cached_evaluator_complex_formula() {
        let mut manager = TermManager::new();
        let mut model = Model::new();

        let x = manager.mk_var("x", manager.sorts.int_sort);
        model.assign_int(x, BigInt::from(3));

        // Build formula: (x * x) + (x * x) = 18
        let x_squared = manager.mk_mul(vec![x, x]);
        let sum = manager.mk_add(vec![x_squared, x_squared]);
        let eighteen = manager.mk_int(18);
        let formula = manager.mk_eq(sum, eighteen);

        let mut evaluator = CachedEvaluator::new(&manager, &model);

        // Should evaluate to true: (3*3) + (3*3) = 9 + 9 = 18
        assert!(
            evaluator
                .validate_assertion(formula)
                .expect("test operation should succeed")
        );

        // x_squared should only be evaluated once and cached
        assert!(evaluator.cache_size() >= 3); // At least x, x_squared, and sum
    }
}

#[cfg(test)]
mod bitvec_const_tests {
    use super::*;
    use crate::ast::{Model, TermManager};

    fn bv(value: u128, width: u32) -> ModelValue {
        ModelValue::from_bitvec_bits(BigUint::from(value), width)
    }

    #[test]
    fn test_bitvec_const_wider_than_64_is_not_truncated() {
        // `2^64 + 5` in 128 bits shares its low 64 bits with plain `5`.
        // Truncating to the low 64 bits made the two constants equal, so a
        // model could be certified against an assertion it does not satisfy.
        let mut manager = TermManager::new();
        let big = BigInt::from(1u128 << 64) + BigInt::from(5);
        let wide = manager.mk_bitvec(big, 128);

        // The constant now evaluates exactly instead of being squeezed into
        // a `u64` (or refused for being too wide).
        let model = Model::new();
        assert_eq!(
            eval_term(wide, &manager, &model),
            Some(bv((1u128 << 64) + 5, 128))
        );

        // The wrong-certification path: a model claiming `x = 5` used to
        // satisfy `x = 2^64 + 5`, because the constant was truncated to its
        // low 64 bits before the comparison. It is now decisively refuted.
        let bv128 = manager.sorts.bitvec(128);
        let x = manager.mk_var("x", bv128);
        let eq = manager.mk_eq(x, wide);
        let mut wrong = Model::new();
        wrong.assign_bitvec(x, 5, 128);

        assert_eq!(
            eval_term(eq, &manager, &wrong),
            Some(ModelValue::Bool(false))
        );
        // The assertion is now decided, and decided *against* the model:
        // `Ok(false)`, not the "cannot evaluate" error it used to be.
        assert_eq!(validate_assertion(eq, &manager, &wrong).ok(), Some(false));
        assert_eq!(validate_model(&[eq], &manager, &wrong).ok(), Some(false));

        // ... and the model that really does assign `2^64 + 5` validates.
        let mut right = Model::new();
        right.assign_bitvec_big(x, (BigUint::one() << 64u32) + BigUint::from(5u32), 128);
        assert_eq!(
            eval_term(eq, &manager, &right),
            Some(ModelValue::Bool(true))
        );
        assert_eq!(validate_assertion(eq, &manager, &right).ok(), Some(true));
        assert_eq!(validate_model(&[eq], &manager, &right).ok(), Some(true));
    }

    #[test]
    fn test_bitvec_const_is_reduced_modulo_width() {
        let mut manager = TermManager::new();
        let model = Model::new();

        // 260 mod 2^8 = 4
        let over = manager.mk_bitvec(BigInt::from(260), 8);
        assert_eq!(eval_term(over, &manager, &model), Some(bv(4, 8)));

        // -1 mod 2^8 = 255 (two's-complement bit pattern)
        let neg = manager.mk_bitvec(BigInt::from(-1), 8);
        assert_eq!(eval_term(neg, &manager, &model), Some(bv(255, 8)));

        // -1 in 128 bits is 128 one-bits, not 64.
        let neg_wide = manager.mk_bitvec(BigInt::from(-1), 128);
        assert_eq!(
            eval_term(neg_wide, &manager, &model),
            Some(ModelValue::BitVec {
                value: crate::ast::model::bitvec_mask(128),
                width: 128
            })
        );
    }

    #[test]
    fn test_bitvec_const_width_64_is_exact() {
        let mut manager = TermManager::new();
        let model = Model::new();
        let value = BigInt::from(u64::MAX);
        let term = manager.mk_bitvec(value, 64);
        assert_eq!(
            eval_term(term, &manager, &model),
            Some(bv(u128::from(u64::MAX), 64))
        );
    }

    #[test]
    fn test_bitvec_width_mask_rejects_only_width_zero() {
        assert_eq!(bitvec_width_mask(0), None);
        assert_eq!(bitvec_width_mask(1), Some(BigUint::one()));
        assert_eq!(bitvec_width_mask(64), Some(BigUint::from(u64::MAX)));
        assert_eq!(bitvec_width_mask(128), Some(BigUint::from(u128::MAX)));
        // Widths past 64 are masks, not failures, any more.
        assert_eq!(bitvec_width_mask(256).map(|m| m.count_ones()), Some(256));
    }

    #[test]
    fn test_bv_not_of_wide_value_is_exact() {
        let mut manager = TermManager::new();
        let bv128 = manager.sorts.bitvec(128);
        let x = manager.mk_var("x", bv128);
        let not_x = manager.mk_bv_not(x);

        let mut model = Model::new();
        model.assign_bitvec(x, 0, 128);
        // `!0` at 128 bits is 128 one-bits – the full width, not the low 64.
        assert_eq!(
            eval_term(not_x, &manager, &model),
            Some(ModelValue::BitVec {
                value: crate::ast::model::bitvec_mask(128),
                width: 128
            })
        );
    }

    #[test]
    fn test_bv_and_of_wide_values_is_exact() {
        let mut manager = TermManager::new();
        let bv128 = manager.sorts.bitvec(128);
        let x = manager.mk_var("x", bv128);
        let y = manager.mk_var("y", bv128);
        let and = manager.mk_bv_and(x, y);

        let mut model = Model::new();
        let high = BigUint::one() << 100u32;
        model.assign_bitvec_big(x, high.clone() + BigUint::from(3u32), 128);
        model.assign_bitvec_big(y, high.clone() + BigUint::from(1u32), 128);
        assert_eq!(
            eval_term(and, &manager, &model),
            Some(ModelValue::BitVec {
                value: high + BigUint::one(),
                width: 128
            })
        );
    }

    #[test]
    fn test_wide_bitvec_arithmetic_and_signed_operations_are_exact() {
        let mut manager = TermManager::new();
        let bv128 = manager.sorts.bitvec(128);
        let x = manager.mk_var("x", bv128);
        let one = manager.mk_bitvec(BigInt::one(), 128);
        let zero = manager.mk_bitvec(BigInt::zero(), 128);
        let max = manager.mk_bitvec(BigInt::from(-1), 128);
        let min_bits = BigUint::one() << 127u32;

        let mut model = Model::new();
        model.assign_bitvec_big(x, min_bits.clone(), 128);

        let wrap = manager.mk_bv_add(max, one);
        assert_eq!(eval_term(wrap, &manager, &model), Some(bv(0, 128)));

        let signed_lt = manager.mk_bv_slt(x, one);
        assert_eq!(
            eval_term(signed_lt, &manager, &model),
            Some(ModelValue::Bool(true))
        );

        let shift = manager.mk_bitvec(BigInt::from(127), 128);
        let ashr = manager.mk_bv_ashr(x, shift);
        assert_eq!(
            eval_term(ashr, &manager, &model),
            Some(ModelValue::BitVec {
                value: crate::ast::model::bitvec_mask(128),
                width: 128,
            })
        );

        // SMT-LIB's totalized signed division maps a negative dividend divided
        // by zero to one (the negation of the unsigned all-ones quotient).
        let sdiv_zero = manager.mk_bv_sdiv(x, zero);
        assert_eq!(eval_term(sdiv_zero, &manager, &model), Some(bv(1, 128)));
    }

    #[test]
    fn test_wide_bitvec_concat_and_extract_are_exact() {
        let mut manager = TermManager::new();
        let hi = manager.mk_bitvec(BigInt::from(0x12_3456_789au64), 40);
        let lo = manager.mk_bitvec(BigInt::from(0xbc_def0_1234u64), 40);
        let concat = manager.mk_bv_concat(hi, lo);
        let extracted = manager.mk_bv_extract(75, 36, concat);
        let expected = ((BigUint::from(0x12_3456_789au64) << 40u32)
            | BigUint::from(0xbc_def0_1234u64))
            >> 36u32;

        assert_eq!(
            eval_term(extracted, &manager, &Model::new()),
            Some(ModelValue::from_bitvec_bits(expected, 40))
        );
    }

    #[test]
    fn test_ast_validator_uses_euclidean_integer_division() {
        let mut manager = TermManager::new();
        let minus_seven = manager.mk_int(-7);
        let two = manager.mk_int(2);
        let div = manager.mk_div(minus_seven, two);
        let modulo = manager.mk_mod(minus_seven, two);

        assert_eq!(
            eval_term(div, &manager, &Model::new()),
            Some(ModelValue::Int(BigInt::from(-4)))
        );
        assert_eq!(
            eval_term(modulo, &manager, &Model::new()),
            Some(ModelValue::Int(BigInt::one()))
        );
    }
}

#[cfg(test)]
mod deep_walk_tests {
    use super::*;
    use crate::ast::{Model, TermManager};

    #[test]
    fn test_eval_term_shared_dag_is_fast() {
        // 55 levels of a two-strand DAG: each level has two nodes, each
        // referencing both nodes of the level below, so an evaluator without
        // a cache performs 2^55 evaluations.
        let mut manager = TermManager::new();
        let bool_sort = manager.sorts.bool_sort;
        let p = manager.mk_var("p", bool_sort);
        let q = manager.mk_var("q", bool_sort);
        let (mut a, mut b) = (p, q);
        for _ in 0..55 {
            let next_a = manager.mk_implies(a, b);
            let next_b = manager.mk_implies(b, a);
            a = next_a;
            b = next_b;
        }

        let mut model = Model::new();
        model.assign_bool(p, true);
        model.assign_bool(q, false);
        assert!(matches!(
            eval_term(a, &manager, &model),
            Some(ModelValue::Bool(_))
        ));
    }

    #[test]
    fn test_eval_term_short_circuits_conjunction() {
        // `false ∧ unassigned` is `false`, not "unknown": the recursive
        // evaluator short-circuited and so must the iterative one.
        let mut manager = TermManager::new();
        let bool_sort = manager.sorts.bool_sort;
        let unassigned = manager.mk_var("q", bool_sort);
        let f = manager.mk_bool(false);
        let conj = manager.mk_and([f, unassigned]);

        let model = Model::new();
        assert_eq!(
            eval_term(conj, &manager, &model),
            Some(ModelValue::Bool(false))
        );

        let t = manager.mk_bool(true);
        let disj = manager.mk_or([t, unassigned]);
        assert_eq!(
            eval_term(disj, &manager, &model),
            Some(ModelValue::Bool(true))
        );
    }

    #[test]
    fn test_eval_term_ite_only_takes_selected_branch() {
        let mut manager = TermManager::new();
        let bool_sort = manager.sorts.bool_sort;
        let cond = manager.mk_var("c", bool_sort);
        let unassigned = manager.mk_var("q", bool_sort);
        let t = manager.mk_bool(true);
        let ite = manager.mk_ite(cond, t, unassigned);

        let mut model = Model::new();
        model.assign_bool(cond, true);
        assert_eq!(
            eval_term(ite, &manager, &model),
            Some(ModelValue::Bool(true))
        );

        model.assign_bool(cond, false);
        assert_eq!(eval_term(ite, &manager, &model), None);
    }

    #[test]
    fn test_eval_term_deep_nesting_does_not_overflow() {
        let handle = std::thread::Builder::new()
            .stack_size(1 << 20)
            .spawn(|| {
                let mut manager = TermManager::new();
                let bool_sort = manager.sorts.bool_sort;
                let p = manager.mk_var("p", bool_sort);
                let mut term = p;
                for _ in 0..60_000 {
                    term = manager.mk_not(term);
                }

                let mut model = Model::new();
                model.assign_bool(p, true);
                eval_term(term, &manager, &model)
            })
            .expect("thread spawn should succeed");

        // An even number of negations of `true`.
        assert_eq!(
            handle.join().expect("deep evaluation must not overflow"),
            Some(ModelValue::Bool(true))
        );
    }
}

// ======== UF certificate evaluation (2026-09 extension) ========
//
// `Apply` evaluates by per-application model lookup and `Distinct` by exact
// pairwise comparison — the two arms the certified-mode UF model
// certificate depends on. These units pin their semantics directly.

#[cfg(test)]
mod uf_eval_tests {
    use super::*;
    use crate::sort::SortId;

    fn uninterpreted_sort(manager: &mut TermManager) -> SortId {
        let name = manager.intern_str("S");
        manager
            .sorts
            .intern(crate::sort::SortKind::Uninterpreted(name))
    }

    #[test]
    fn apply_evaluates_from_model_lookup() {
        let mut manager = TermManager::new();
        let sort = uninterpreted_sort(&mut manager);
        let a = manager.mk_var("a", sort);
        let f_a = manager.mk_apply("f", [a], sort);

        // Without an assignment the application is unevaluable (fail
        // closed), never a default.
        let empty = Model::new();
        assert_eq!(eval_term(f_a, &manager, &empty), None);

        // With per-application assignments the table evaluates.
        let mut model = Model::new();
        model.assign_uninterpreted(a, sort, 0);
        model.assign_uninterpreted(f_a, sort, 7);
        assert_eq!(
            eval_term(f_a, &manager, &model),
            Some(ModelValue::Uninterpreted { sort, id: 7 })
        );
        // The constant itself also looks up.
        assert_eq!(
            eval_term(a, &manager, &model),
            Some(ModelValue::Uninterpreted { sort, id: 0 })
        );
    }

    #[test]
    fn distinct_over_uninterpreted_witnesses() {
        let mut manager = TermManager::new();
        let sort = uninterpreted_sort(&mut manager);
        let a = manager.mk_var("a", sort);
        let b = manager.mk_var("b", sort);
        let c = manager.mk_var("c", sort);

        let mut model = Model::new();
        model.assign_uninterpreted(a, sort, 0);
        model.assign_uninterpreted(b, sort, 0); // same element as a
        model.assign_uninterpreted(c, sort, 1);

        let d = manager.mk_distinct([a, b, c]);
        assert_eq!(
            eval_term(d, &manager, &model),
            Some(ModelValue::Bool(false)), // a and b denote one element
        );

        let d2 = manager.mk_distinct([a, c]);
        assert_eq!(
            eval_term(d2, &manager, &model),
            Some(ModelValue::Bool(true))
        );

        // Singleton distinct is trivially true; unevaluated operands are
        // never guessed.
        let d3 = manager.mk_distinct([a]);
        assert_eq!(
            eval_term(d3, &manager, &model),
            Some(ModelValue::Bool(true))
        );
        let orphan = manager.mk_var("orphan", sort);
        let d4 = manager.mk_distinct([a, orphan]);
        assert_eq!(eval_term(d4, &manager, &model), None);
    }

    #[test]
    fn distinct_mixed_concrete_kinds() {
        let mut manager = TermManager::new();
        let one = manager.mk_int(1);
        let two = manager.mk_int(2);
        let d = manager.mk_distinct([one, two]);
        assert_eq!(
            eval_term(d, &manager, &Model::new()),
            Some(ModelValue::Bool(true))
        );

        let one_again = manager.mk_int(1);
        let d2 = manager.mk_distinct([one, one_again, two]);
        assert_eq!(
            eval_term(d2, &manager, &Model::new()),
            Some(ModelValue::Bool(false))
        );
    }
}
