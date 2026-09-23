//! Affine F2 solving, then bounded enumeration for binary extensions.
//! No prime polynomial or GB API
//! accepts these fields. Evaluation uses shift-and-reduce multiplication,
//! independently of core's carryless convolution and polynomial division.

mod affine;

use super::*;
use nixie_core::sort::binary_field::BinaryField;
use num_traits::ToPrimitive;

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
    if let Some(outcome) = affine::check(manager, field, binary, &vars, assertions, &mut budget) {
        return outcome;
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
    // All enumerable fields fit here (the search space is at most 2^22).
    // Keep the same shift/reduce algorithm and charge every coefficient,
    // including zero coefficients: changing ticks would change exhaustion.
    // Canonical inputs have <=32 bits; the monic polynomial and each
    // unreduced shift have <=33 bits. Every conversion is checked.
    if f.degree() <= 32 {
        let mut shifted = u64::from(a.to_u32()?);
        let multiplier = b.to_u32()?;
        let polynomial = f.polynomial().to_u64()?;
        let high_bit = 1u64 << f.degree();
        let mut result = 0u64;
        for i in 0..f.degree() {
            *budget = budget.checked_sub(1)?;
            if (multiplier >> i) & 1 != 0 {
                result ^= shifted;
            }
            shifted <<= 1;
            if shifted & high_bit != 0 {
                shifted ^= polynomial;
            }
        }
        return Some(BigUint::from(result));
    }
    multiply_big(f, a, b, budget)
}

fn multiply_big(f: &BinaryField, a: &BigUint, b: &BigUint, budget: &mut u64) -> Option<BigUint> {
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

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn word_products_match_independent_core_and_biguint() {
        for polynomial in [7u32, 11, 13, 19, 37, 67, 131, 283] {
            let f = BinaryField::new(polynomial.into()).unwrap();
            let q = 1u32 << f.degree();
            for a in 0..q {
                for b in 0..q {
                    let (a, b) = (BigUint::from(a), BigUint::from(b));
                    let mut word_budget = u64::from(f.degree()) + 1;
                    let mut big_budget = word_budget;
                    let word = multiply(&f, &a, &b, &mut word_budget);
                    assert_eq!(word, multiply_big(&f, &a, &b, &mut big_budget));
                    assert_eq!(word, f.mul(&a, &b));
                    assert_eq!(word_budget, big_budget);
                }
            }
        }
    }

    #[test]
    fn word_boundary_wide_fallback_and_exact_budget_exhaustion() {
        // Find checked representations at both sides of the word boundary.
        // The arithmetic oracle remains core's independent convolution/division.
        let mut fields = Vec::new();
        for degree in [2, 8, 31, 32, 33] {
            let field = (1u32..4096)
                .step_by(2)
                .find_map(|low| {
                    BinaryField::new((BigUint::one() << degree) | BigUint::from(low)).ok()
                })
                .expect("an irreducible polynomial in the finite search range");
            assert_eq!(field.degree(), degree);
            fields.push(field);
        }
        fields.push(BinaryField::new((BigUint::one() << 128) | BigUint::from(135u8)).unwrap());
        for f in fields {
            let values = [
                BigUint::zero(),
                BigUint::one(),
                BigUint::from(2u8),
                BigUint::one() << (f.degree() - 1),
                f.order() - 1u8,
            ];
            for a in &values {
                for b in &values {
                    for budget in [0, 1, u64::from(f.degree()) - 1, u64::from(f.degree()), 1000] {
                        let (mut small, mut big) = (budget, budget);
                        let value = multiply(&f, a, b, &mut small);
                        assert_eq!(value, multiply_big(&f, a, b, &mut big));
                        assert_eq!(small, big);
                        if budget >= u64::from(f.degree()) {
                            assert_eq!(value, f.mul(a, b));
                            assert_eq!(small, budget - u64::from(f.degree()));
                        } else {
                            assert!(value.is_none());
                            assert_eq!(small, 0);
                        }
                    }
                }
            }
        }
    }
}
