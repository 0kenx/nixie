//! Bounded enumeration for binary extensions. No prime polynomial or GB API
//! accepts these fields. Evaluation uses shift-and-reduce multiplication,
//! independently of core's carryless convolution and polynomial division.

use super::*;
use nixie_core::sort::binary_field::BinaryField;

pub(super) fn check(
    manager: &TermManager,
    field: FieldId,
    assertions: &[TermId],
    mut budget: u64,
) -> FfOutcome {
    let Some(binary) = manager.sorts.field_desc(field).and_then(|d| d.binary()) else {
        return FfOutcome::InvalidModel("not a binary field".into());
    };
    let vars = match collect_field_variables(manager, field, assertions) {
        Ok(vars) => vars,
        Err(error) => return FfOutcome::InvalidModel(error),
    };
    // Bound the space before exponentiation; no huge p^n allocation.
    let bits = u64::from(binary.degree()).saturating_mul(vars.len() as u64);
    if bits > 22 {
        return FfOutcome::OutOfBudget {
            where_: "binary enumeration space",
        };
    }
    let mut assignment = FxHashMap::default();
    let mask = binary.order() - 1u8;
    for counter in 0..(1u64 << bits) {
        let Some(left) = budget.checked_sub(1) else {
            return FfOutcome::OutOfBudget {
                where_: "binary enumeration",
            };
        };
        budget = left;
        let mut rest = BigUint::from(counter);
        for &var in &vars {
            assignment.insert(var, &rest & &mask);
            rest >>= binary.degree();
        }
        let mut satisfied = true;
        for &assertion in assertions {
            let mut root = assertion;
            let mut negative = false;
            // A heap-free iterative not-chain (no recursion on input).
            let result = loop {
                let Some(left) = budget.checked_sub(1) else {
                    return FfOutcome::OutOfBudget {
                        where_: "binary literal evaluation",
                    };
                };
                budget = left;
                match manager.get(root).map(|t| &t.kind) {
                    Some(TermKind::Not(inner)) => {
                        root = *inner;
                        negative = !negative;
                    }
                    Some(TermKind::True) => break Some(true),
                    Some(TermKind::False) => break Some(false),
                    Some(TermKind::Eq(a, b)) => {
                        break eval(manager, field, *a, &assignment, &mut budget)
                            .zip(eval(manager, field, *b, &assignment, &mut budget))
                            .map(|(a, b)| a == b);
                    }
                    _ => break None,
                }
            };
            match result {
                Some(value) if value != negative => {}
                Some(_) => {
                    satisfied = false;
                    break;
                }
                None => {
                    return FfOutcome::OutOfBudget {
                        where_: "binary evaluation or unsupported term",
                    };
                }
            }
        }
        if satisfied {
            return FfOutcome::Model(FfModel { values: assignment });
        }
    }
    // Enumeration is complete, but has no exported algebraic certificate.
    FfOutcome::Exhausted { certificate: None }
}

// Independently implemented multiplication: maintain a reduced running
// multiple of a, and accumulate it for each set coefficient of b.
fn multiply(f: &BinaryField, a: &BigUint, b: &BigUint, budget: &mut u64) -> Option<BigUint> {
    let mut shifted = a.clone();
    let mut result = BigUint::zero();
    for i in 0..f.degree() {
        *budget = budget.checked_sub(1)?;
        if b.bit(u64::from(i)) {
            result ^= &shifted;
        }
        shifted <<= 1;
        if shifted.bit(u64::from(f.degree())) {
            shifted ^= f.polynomial();
        }
    }
    Some(result)
}

pub(super) fn eval(
    manager: &TermManager,
    field: FieldId,
    root: TermId,
    assignment: &FxHashMap<TermId, BigUint>,
    budget: &mut u64,
) -> Option<BigUint> {
    let f = manager.sorts.field_desc(field)?.binary()?;
    let mut cache: FxHashMap<TermId, BigUint> = FxHashMap::default();
    let mut stack = vec![(root, false)];
    while let Some((id, combine)) = stack.pop() {
        *budget = budget.checked_sub(1)?;
        if cache.contains_key(&id) {
            continue;
        }
        let term = manager.get(id)?;
        if !matches!(manager.sorts.get(term.sort)?.kind, SortKind::FiniteField(seen) if seen == field)
        {
            return None;
        }
        let result = match &term.kind {
            TermKind::FfConst { value, field: seen } if *seen == field => value.to_biguint()?,
            TermKind::Var(_) | TermKind::Apply { .. } => assignment.get(&id)?.clone(),
            TermKind::FfAdd(args) | TermKind::FfMul(args) | TermKind::FfBitsum(args) => {
                if !combine {
                    stack.push((id, true));
                    stack.extend(args.iter().rev().map(|&a| (a, false)));
                    continue;
                }
                match &term.kind {
                    TermKind::FfAdd(_) => {
                        let mut sum = BigUint::zero();
                        for a in args {
                            *budget = budget.checked_sub(1)?;
                            sum ^= cache.get(a)?;
                        }
                        sum
                    }
                    TermKind::FfMul(_) => {
                        let mut product = BigUint::one();
                        for a in args {
                            product = multiply(f, &product, cache.get(a)?, budget)?;
                        }
                        product
                    }
                    TermKind::FfBitsum(_) => cache.get(args.first()?)?.clone(),
                    _ => return None,
                }
            }
            TermKind::FfNeg(a) => {
                if !combine {
                    stack.push((id, true));
                    stack.push((*a, false));
                    continue;
                }
                cache.get(a)?.clone()
            }
            _ => return None,
        };
        if !f.contains(&result) {
            return None;
        }
        cache.insert(id, result);
    }
    cache.remove(&root)
}
