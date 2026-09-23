//! Exact affine equations over the prime subfield F2.
//!
//! An expression is c + sum_i a_i b_i, where each b_i is a Boolean
//! coefficient of an input field variable. Squaring maps every a_i to a_i²
//! because b_i²=b_i and cross terms vanish in characteristic two. Products
//! are admitted only when one operand is constant or both affine maps agree.
//! See docs/studies/2026-09-23-ff-affine.md for algorithm references.

use super::*;

type Affine = Vec<u32>;

#[derive(Clone, Copy)]
enum Stop {
    Unsupported,
    Budget,
}

fn charge(budget: &mut u64, work: usize) -> Result<(), Stop> {
    let work = u64::try_from(work).map_err(|_| Stop::Budget)?;
    *budget = budget.checked_sub(work).ok_or(Stop::Budget)?;
    Ok(())
}

struct Encoder<'a> {
    manager: &'a TermManager,
    field: FieldId,
    binary: &'a BinaryField,
    vars: &'a [TermId],
    columns: usize,
    cache: FxHashMap<TermId, Affine>,
}

impl Encoder<'_> {
    fn product(&self, a: &Affine, b: &Affine, budget: &mut u64) -> Result<Affine, Stop> {
        charge(budget, self.columns * 3)?;
        let constant_a = a[1..].iter().all(|&v| v == 0);
        let constant_b = b[1..].iter().all(|&v| v == 0);
        if !constant_a && !constant_b && a != b {
            return Err(Stop::Unsupported);
        }
        a.iter()
            .zip(b)
            .map(|(&x, &y)| {
                let (left, right) = if constant_a {
                    (a[0], y)
                } else if constant_b {
                    (x, b[0])
                } else {
                    (x, x)
                };
                multiply(self.binary, &left.into(), &right.into(), budget)
                    .and_then(|v| v.to_u32())
                    .ok_or(Stop::Budget)
            })
            .collect()
    }

    // The AST flattens products: c*(x*x) becomes [c,x,x]. Separate
    // constants and recognize identical factors with power-of-two multiplicity.
    fn factors(&self, args: &[TermId], budget: &mut u64) -> Result<Affine, Stop> {
        let mut scalar = 1u32;
        let mut factor: Option<&Affine> = None;
        let mut count = 0usize;
        for a in args {
            charge(budget, self.columns * 2)?;
            let child = self.cache.get(a).ok_or(Stop::Unsupported)?;
            if child[1..].iter().all(|&v| v == 0) {
                scalar = multiply(self.binary, &scalar.into(), &child[0].into(), budget)
                    .and_then(|v| v.to_u32())
                    .ok_or(Stop::Budget)?;
            } else {
                if factor.is_some_and(|previous| previous != child) {
                    return Err(Stop::Unsupported);
                }
                factor = Some(child);
                count += 1;
            }
        }
        charge(budget, self.columns)?;
        let mut constant = vec![0; self.columns];
        constant[0] = scalar;
        let Some(factor) = factor else {
            return Ok(constant);
        };
        if !count.is_power_of_two() {
            return Err(Stop::Unsupported);
        }
        let mut power = factor.clone();
        for _ in 0..count.trailing_zeros() {
            power = self.product(&power, &power, budget)?;
        }
        self.product(&constant, &power, budget)
    }

    fn encode(&mut self, root: TermId, budget: &mut u64) -> Result<Affine, Stop> {
        let mut stack = vec![(root, false)];
        while let Some((id, combine)) = stack.pop() {
            charge(budget, 1)?;
            if self.cache.contains_key(&id) {
                continue;
            }
            let term = self.manager.get(id).ok_or(Stop::Unsupported)?;
            if !matches!(self.manager.sorts.get(term.sort).map(|s| &s.kind),
                Some(SortKind::FiniteField(f)) if *f == self.field)
            {
                return Err(Stop::Unsupported);
            }
            charge(budget, self.columns)?;
            let mut value = vec![0; self.columns];
            match &term.kind {
                TermKind::FfConst { value: c, field } if *field == self.field => {
                    let c = c.to_biguint().ok_or(Stop::Unsupported)?;
                    if !self.binary.contains(&c) {
                        return Err(Stop::Unsupported);
                    }
                    value[0] = c.to_u32().ok_or(Stop::Unsupported)?;
                }
                TermKind::Var(_) | TermKind::Apply { .. } => {
                    let index = self
                        .vars
                        .binary_search(&id)
                        .map_err(|_| Stop::Unsupported)?;
                    let degree = self.binary.degree() as usize;
                    for bit in 0..degree {
                        value[1 + index * degree + bit] = 1 << bit;
                    }
                }
                TermKind::FfAdd(args) | TermKind::FfMul(args) | TermKind::FfBitsum(args) => {
                    if !combine {
                        charge(budget, args.len())?;
                        stack.push((id, true));
                        stack.extend(args.iter().rev().map(|&a| (a, false)));
                        continue;
                    }
                    match &term.kind {
                        TermKind::FfAdd(_) => {
                            for a in args {
                                charge(budget, self.columns)?;
                                let child = self.cache.get(a).ok_or(Stop::Unsupported)?;
                                for (v, &c) in value.iter_mut().zip(child) {
                                    *v ^= c;
                                }
                            }
                        }
                        TermKind::FfMul(_) => {
                            value = self.factors(args, budget)?;
                        }
                        TermKind::FfBitsum(_) => {
                            let first = args.first().ok_or(Stop::Unsupported)?;
                            value.clone_from(self.cache.get(first).ok_or(Stop::Unsupported)?);
                        }
                        _ => return Err(Stop::Unsupported),
                    }
                }
                TermKind::FfNeg(a) => {
                    if !combine {
                        stack.push((id, true));
                        stack.push((*a, false));
                        continue;
                    }
                    value.clone_from(self.cache.get(a).ok_or(Stop::Unsupported)?);
                }
                _ => return Err(Stop::Unsupported),
            }
            self.cache.insert(id, value);
        }
        charge(budget, self.columns)?;
        self.cache.get(&root).cloned().ok_or(Stop::Unsupported)
    }
}

/// Echelon rows indexed by their least significant nonzero coefficient.
/// The augmented RHS is bit `rows.len()`. XOR is an invertible row operation.
fn insert(rows: &mut [u32], mut row: u32, budget: &mut u64) -> Result<bool, Stop> {
    let rhs = 1u32 << rows.len();
    for (bit, pivot) in rows.iter_mut().enumerate() {
        charge(budget, 1)?;
        if row & (1 << bit) != 0 {
            if *pivot == 0 {
                *pivot = row;
                return Ok(true);
            }
            row ^= *pivot;
        }
    }
    Ok(row & rhs == 0)
}

fn solve(rows: &[u32], budget: &mut u64) -> Result<u32, Stop> {
    let mut solution = 0;
    let rhs = 1u32 << rows.len();
    for (bit, &row) in rows.iter().enumerate().rev() {
        charge(budget, 1)?;
        // Free coefficients remain zero. All dependencies of this pivot
        // are higher coefficients, already assigned by back substitution.
        let parity = (row & solution).count_ones() & 1;
        if row != 0 && parity != u32::from(row & rhs != 0) {
            solution |= 1 << bit;
        }
    }
    Ok(solution)
}

fn attempt(
    encoder: &mut Encoder<'_>,
    assertions: &[TermId],
    budget: &mut u64,
) -> Result<FfOutcome, Stop> {
    let bits = encoder.columns - 1;
    let mut rows = vec![0; bits];
    for &literal in assertions {
        let mut root = literal;
        let mut negative = false;
        let (a, b) = loop {
            charge(budget, 1)?;
            match encoder.manager.get(root).map(|t| &t.kind) {
                Some(TermKind::Not(inner)) => {
                    root = *inner;
                    negative = !negative;
                }
                Some(TermKind::Eq(a, b)) if !negative => break (*a, *b),
                Some(TermKind::True) if !negative => break (root, root),
                Some(TermKind::False) if negative => break (root, root),
                Some(TermKind::True | TermKind::False) => {
                    return Ok(FfOutcome::Exhausted { certificate: None });
                }
                _ => return Err(Stop::Unsupported),
            }
        };
        if a == b {
            continue;
        }
        let a = encoder.encode(a, budget)?;
        let b = encoder.encode(b, budget)?;
        for bit in 0..encoder.binary.degree() {
            charge(budget, encoder.columns)?;
            let mut row = ((a[0] ^ b[0]) >> bit & 1) << bits;
            for column in 0..bits {
                row |= ((a[column + 1] ^ b[column + 1]) >> bit & 1) << column;
            }
            if !insert(&mut rows, row, budget)? {
                return Ok(FfOutcome::Exhausted { certificate: None });
            }
        }
    }
    let solution = solve(&rows, budget)?;
    let degree = encoder.binary.degree() as usize;
    let mask = (1u32 << degree) - 1;
    let values = encoder
        .vars
        .iter()
        .enumerate()
        .map(|(i, &var)| (var, BigUint::from((solution >> (i * degree)) & mask)))
        .collect();
    Ok(FfOutcome::Model(FfModel { values }))
}

/// None requests enumeration with the remaining budget. No unchecked proof
/// is exported: certified arithmetic UNSAT still degrades to Unknown.
pub(super) fn check(
    manager: &TermManager,
    field: FieldId,
    binary: &BinaryField,
    vars: &[TermId],
    assertions: &[TermId],
    budget: &mut u64,
) -> Option<FfOutcome> {
    let bits = (binary.degree() as usize).checked_mul(vars.len())?;
    // Keep the existing finite-search bound and leave wide ground terms alone.
    if bits == 0 || bits > 22 {
        return None;
    }
    let mut encoder = Encoder {
        manager,
        field,
        binary,
        vars,
        columns: bits + 1,
        cache: FxHashMap::default(),
    };
    match attempt(&mut encoder, assertions, budget) {
        Ok(outcome) => Some(outcome),
        Err(Stop::Unsupported) => None,
        Err(Stop::Budget) => Some(FfOutcome::OutOfBudget {
            where_: "binary affine solving",
        }),
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn all_three_row_binary_systems_through_three_columns() {
        for bits in 0..=3 {
            let bound = 1u32 << (bits + 1);
            for a in 0..bound {
                for b in 0..bound {
                    for c in 0..bound {
                        let original = [a, b, c];
                        let expected = (0..1u32 << bits).find(|&x| {
                            original
                                .iter()
                                .all(|&r| (r & x).count_ones() & 1 == r >> bits)
                        });
                        let mut rows = vec![0; bits];
                        let mut budget = 100;
                        let consistent = original
                            .iter()
                            .all(|&r| insert(&mut rows, r, &mut budget).is_ok_and(|v| v));
                        assert_eq!(consistent, expected.is_some());
                        if consistent {
                            assert_eq!(solve(&rows, &mut budget).ok(), expected);
                        }
                    }
                }
            }
        }
    }

    #[test]
    fn affine_translation_matches_every_tiny_assignment() {
        for polynomial in [7u32, 11, 13, 19] {
            let mut manager = TermManager::new();
            let sort = manager.sorts.binary_field(polynomial.into()).unwrap();
            let field = manager.sorts.get(sort).unwrap().finite_field().unwrap();
            let x = manager.mk_var("x", sort);
            let y = manager.mk_var("y", sort);
            let two = manager.mk_ff_const(field, 2.into()).unwrap();
            let sum = manager.mk_ff_add([x, y, two]).unwrap();
            let square = manager.mk_ff_mul([sum, sum]).unwrap();
            let fourth = manager.mk_ff_mul([two, x, x, x, x]).unwrap();
            let scaled = manager.mk_ff_mul([two, square]).unwrap();
            let neg = manager.mk_ff_neg(scaled).unwrap();
            let bitsum = manager.mk_ff_bitsum([neg, fourth]).unwrap();
            let nonlinear = manager.mk_ff_mul([x, y]).unwrap();
            let binary = manager.sorts.field_desc(field).unwrap().binary().unwrap();
            let degree = binary.degree() as usize;
            let vars = [x, y];
            let mut encoder = Encoder {
                manager: &manager,
                field,
                binary,
                vars: &vars,
                columns: 2 * degree + 1,
                cache: FxHashMap::default(),
            };
            for term in [sum, square, fourth, scaled, neg, bitsum] {
                let map = encoder.encode(term, &mut 1_000_000).ok().unwrap();
                for a in 0..1u32 << degree {
                    for b in 0..1u32 << degree {
                        let input = a | (b << degree);
                        let value = map[1..].iter().enumerate().fold(map[0], |acc, (i, &c)| {
                            if input & (1 << i) != 0 { acc ^ c } else { acc }
                        });
                        // The core evaluator uses independent coefficient convolution.
                        let mut model = nixie_core::ast::Model::new();
                        model.assign_ff(x, a.into(), field);
                        model.assign_ff(y, b.into(), field);
                        let mut evaluator = nixie_core::ast::CachedEvaluator::new(&manager, &model);
                        assert_eq!(
                            evaluator.eval(term),
                            Some(nixie_core::ast::ModelValue::FiniteField {
                                value: value.into(),
                                field
                            })
                        );
                    }
                }
            }
            assert!(matches!(
                encoder.encode(nonlinear, &mut 1_000_000),
                Err(Stop::Unsupported)
            ));
            assert!(matches!(encoder.encode(sum, &mut 0), Err(Stop::Budget)));
        }
    }
}

#[cfg(test)]
mod boundary_tests {
    use super::*;

    #[test]
    fn all_twenty_two_coefficients_and_shared_budget_are_checked() {
        let mut manager = TermManager::new();
        let sort = manager.sorts.binary_field(7u32.into()).unwrap();
        let field = manager.sorts.get(sort).unwrap().finite_field().unwrap();
        let target = manager.mk_ff_const(field, 2.into()).unwrap();
        let vars: Vec<_> = (0..11)
            .map(|i| manager.mk_var(&format!("x{i}"), sort))
            .collect();
        let assertions: Vec<_> = vars
            .iter()
            .map(|&x| {
                let square = manager.mk_ff_mul([x, x]).unwrap();
                manager.mk_eq(square, target)
            })
            .collect();
        let binary = manager.sorts.field_desc(field).unwrap().binary().unwrap();
        let mut budget = 100_000;
        let outcome = check(&manager, field, binary, &vars, &assertions, &mut budget).unwrap();
        let FfOutcome::Model(model) = outcome else {
            panic!("{outcome:?}");
        };
        validate_model(&manager, field, &assertions, &model).unwrap();
        assert!(
            vars.iter()
                .all(|&v| model.value_of(v) == Some(&BigUint::from(3u8)))
        );
        let used = 100_000 - budget;
        for limit in [0, 1, used - 1] {
            assert!(matches!(
                check(&manager, field, binary, &vars, &assertions, &mut { limit }),
                Some(FfOutcome::OutOfBudget { .. })
            ));
        }
        assert!(matches!(
            check(&manager, field, binary, &vars, &assertions, &mut { used }),
            Some(FfOutcome::Model(_))
        ));
    }

    #[test]
    fn nonlinear_and_disequality_fallback_do_not_reset_the_work_budget() {
        let mut manager = TermManager::new();
        let sort = manager.sorts.binary_field(7u32.into()).unwrap();
        let field = manager.sorts.get(sort).unwrap().finite_field().unwrap();
        let x = manager.mk_var("x", sort);
        let y = manager.mk_var("y", sort);
        let one = manager.mk_ff_const(field, 1.into()).unwrap();
        let product = manager.mk_ff_mul([x, y]).unwrap();
        let cube = manager.mk_ff_mul([x, x, x]).unwrap();
        let eq = manager.mk_eq(x, one);
        let neq = manager.mk_not(eq);
        for assertion in [manager.mk_eq(product, one), manager.mk_eq(cube, one), neq] {
            let vars = collect_field_variables(&manager, field, &[assertion]).unwrap();
            let binary = manager.sorts.field_desc(field).unwrap().binary().unwrap();
            let mut budget = 10_000;
            assert!(check(&manager, field, binary, &vars, &[assertion], &mut budget).is_none());
            assert!(budget < 10_000);
            let FfOutcome::Model(model) =
                super::super::check(&manager, field, &[assertion], 10_000)
            else {
                panic!("fallback lost a satisfiable goal");
            };
            validate_model(&manager, field, &[assertion], &model).unwrap();
        }
    }
}
