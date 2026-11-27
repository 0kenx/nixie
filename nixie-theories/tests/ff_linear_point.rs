//! A goal whose generators are all linear is decided by the linear core:
//! the reduced rows give the point, and an inconsistent row is the
//! certified UNSAT it always was – at any number of variables, with
//! neither enumeration nor the Gröbner cascade.
//!
//! Before this, a *consistent* linear system fell through to enumeration
//! (seven variables of 𝔽₇, 7⁷ points) or to the cascade (eight and
//! more: pⁿ > 2²²), where eight pinned variables ran for minutes with no
//! verdict. Every verdict here is checked against the exact validator
//! and, on random systems, against a Gaussian elimination written for the
//! test.

use nixie_core::ast::{TermId, TermManager};
use nixie_core::sort::SortKind;
use nixie_core::sort::field::FieldId;
use nixie_theories::ff_theory::{FfOutcome, check_conjunction, validate_model};
use num_bigint::{BigInt, BigUint};
use num_traits::Zero;

fn field(manager: &mut TermManager, p: u32) -> FieldId {
    let sort = manager
        .sorts
        .finite_field(BigUint::from(p))
        .expect("a prime modulus");
    match manager.sorts.get(sort).map(|s| s.kind.clone()) {
        Some(SortKind::FiniteField(id)) => id,
        _ => panic!("field sort"),
    }
}

fn constant(manager: &mut TermManager, f: FieldId, v: u64) -> TermId {
    manager.mk_ff_const(f, v.into()).expect("constant")
}

fn equation(
    manager: &mut TermManager,
    f: FieldId,
    coeffs: &[(TermId, u64)],
    constant_term: u64,
) -> TermId {
    // Σ cᵢ·xᵢ = c₀, spelled with `ff.mul` by a numeral and `ff.add`.
    let mut parts: Vec<TermId> = Vec::new();
    for &(x, c) in coeffs {
        if c == 0 {
            continue;
        }
        let term = if c == 1 {
            x
        } else {
            let c_term = constant(manager, f, c);
            manager.mk_ff_mul([c_term, x]).expect("field terms")
        };
        parts.push(term);
    }
    let sum = match parts.as_slice() {
        [] => constant(manager, f, 0),
        [only] => *only,
        many => manager
            .mk_ff_add(many.iter().copied())
            .expect("field terms"),
    };
    let rhs = constant(manager, f, constant_term);
    manager.mk_eq(sum, rhs)
}

/// n variables pinned to 1 and n more to 0: decided, validated, every
/// value as pinned – for n past the enumeration cap (7 for 𝔽₇) and far
/// past it.
#[test]
fn pinned_variables_are_decided_at_any_count() {
    for (p, ns) in [(7u32, &[4usize, 8, 64, 256][..]), (65_537, &[1, 8, 64][..])] {
        for &n in ns {
            let mut manager = TermManager::new();
            let f = field(&mut manager, p);
            let mut xs = Vec::new();
            let mut vs = Vec::new();
            let mut assertions = Vec::new();
            for i in 0..n {
                let x = manager.mk_var(
                    &format!("x{i}"),
                    manager
                        .sorts
                        .find_finite_field(&BigUint::from(p))
                        .expect("field"),
                );
                let v = manager.mk_var(
                    &format!("v{i}"),
                    manager
                        .sorts
                        .find_finite_field(&BigUint::from(p))
                        .expect("field"),
                );
                let one = constant(&mut manager, f, 1);
                assertions.push(manager.mk_eq(x, one));
                let zero = constant(&mut manager, f, 0);
                assertions.push(manager.mk_eq(v, zero));
                xs.push(x);
                vs.push(v);
            }
            let FfOutcome::Model(model) = check_conjunction(&manager, f, &assertions, 1 << 24)
            else {
                panic!("p = {p}, n = {n}: not a model");
            };
            validate_model(&manager, f, &assertions, &model)
                .expect("the model satisfies every literal");
            for (i, (&x, &v)) in xs.iter().zip(&vs).enumerate() {
                assert_eq!(
                    model.value_of(x),
                    Some(&BigUint::from(1u8)),
                    "p = {p}, x{i}"
                );
                assert_eq!(
                    model.value_of(v),
                    Some(&BigUint::from(0u8)),
                    "p = {p}, v{i}"
                );
            }
        }
    }
}

/// An inconsistent linear system is the certified UNSAT it always was,
/// at any count; one contradiction among 512 pinned variables is found.
#[test]
fn an_inconsistent_linear_system_is_a_certified_unsat_at_any_count() {
    for n in [2usize, 8, 256] {
        let mut manager = TermManager::new();
        let f = field(&mut manager, 7);
        let sort = manager
            .sorts
            .find_finite_field(&BigUint::from(7u32))
            .expect("field");
        let mut assertions = Vec::new();
        let mut first = None;
        for i in 0..n {
            let x = manager.mk_var(&format!("x{i}"), sort);
            let one = constant(&mut manager, f, 1);
            assertions.push(manager.mk_eq(x, one));
            if first.is_none() {
                first = Some(x);
            }
        }
        let x0 = first.expect("a variable");
        let last = manager.mk_var("last", sort);
        assertions.push(manager.mk_eq(last, x0));
        let two = constant(&mut manager, f, 2);
        assertions.push(manager.mk_eq(last, two));
        let FfOutcome::Unsat(core) = check_conjunction(&manager, f, &assertions, 1 << 24) else {
            panic!("n = {n}: not unsat");
        };
        assert!(
            core.certificate.is_some(),
            "n = {n}: the refutation is certified"
        );
        assert!(!core.fact_indices.is_empty(), "n = {n}: a core");
    }
}

/// Random sparse linear systems over 𝔽₇ and 𝔽₆₅₅₃₇, one to twelve
/// variables, one to twenty equations: the verdict equals a Gaussian
/// elimination written for the test, every model validates, every UNSAT
/// carries a certificate.
#[test]
fn random_linear_systems_agree_with_an_independent_elimination() {
    struct Lcg(u64);
    let mut rng = Lcg(0x1ea5_2026_1127);
    let next = |rng: &mut Lcg| -> u64 {
        rng.0 = rng
            .0
            .wrapping_mul(6364136223846793005)
            .wrapping_add(1442695040888963407);
        rng.0 >> 33
    };
    // Independent reference: Gaussian elimination over `Z_p` on a dense
    // matrix; true exactly for an inconsistent system.
    let inconsistent = |p: u64, rows: &[Vec<u64>]| -> bool {
        let mut rows: Vec<Vec<BigInt>> = rows
            .iter()
            .map(|r| r.iter().map(|&c| BigInt::from(c)).collect())
            .collect();
        let n_vars = rows[0].len() - 1;
        let modulus = BigInt::from(p);
        let mut rank = 0usize;
        for col in 0..n_vars {
            let pivot = (rank..rows.len()).find(|&r| !(rows[r][col].clone() % &modulus).is_zero());
            let Some(pivot) = pivot else { continue };
            rows.swap(rank, pivot);
            // p is prime: the inverse by Fermat.
            let inv = num_traits::Pow::pow(&rows[rank][col], &BigUint::from(p - 2)) % &modulus;
            for x in &mut rows[rank] {
                *x = (x.clone() * &inv) % &modulus;
            }
            let pivot_row = rows[rank].clone();
            for (r, row) in rows.iter_mut().enumerate() {
                if r == rank {
                    continue;
                }
                let factor = row[col].clone();
                if factor.is_zero() {
                    continue;
                }
                for (x, p) in row.iter_mut().zip(&pivot_row) {
                    *x = ((x.clone() - &factor * p) % &modulus + &modulus) % &modulus;
                }
            }
            rank += 1;
        }
        rows.iter().any(|r| {
            r[..n_vars].iter().all(|c| c.is_zero()) && !(r[n_vars].clone() % &modulus).is_zero()
        })
    };

    let mut checked = 0;
    let mut models = 0;
    for p in [7u64, 65_537] {
        for n in 1..=12usize {
            for _ in 0..6 {
                let mut manager = TermManager::new();
                let f = field(&mut manager, p as u32);
                let sort = manager
                    .sorts
                    .find_finite_field(&BigUint::from(p))
                    .expect("field");
                let vars: Vec<TermId> = (0..n)
                    .map(|i| manager.mk_var(&format!("x{i}"), sort))
                    .collect();
                let m = 1 + (next(&mut rng) % 20) as usize;
                let mut assertions = Vec::new();
                let mut dense = Vec::new();
                let mut folded_false = false;
                for _ in 0..m {
                    let mut coeffs = Vec::new();
                    let mut row = vec![0u64; n + 1];
                    for (i, &x) in vars.iter().enumerate() {
                        let c = if next(&mut rng) % 3 == 0 {
                            0
                        } else {
                            next(&mut rng) % p
                        };
                        if c != 0 {
                            coeffs.push((x, c));
                        }
                        row[i] = c;
                    }
                    let c0 = next(&mut rng) % p;
                    *row.last_mut().unwrap() = c0;
                    let literal = equation(&mut manager, f, &coeffs, c0);
                    // `0 = c₀` with c₀ ≠ 0 folds to `false` in the term
                    // builder: the one UNSAT that carries no field
                    // certificate, by design (the Boolean skeleton refutes it).
                    folded_false |= literal == manager.false_id;
                    assertions.push(literal);
                    dense.push(row);
                }
                let expected_inconsistent = inconsistent(p, &dense);
                match check_conjunction(&manager, f, &assertions, 1 << 24) {
                    FfOutcome::Model(model) => {
                        assert!(
                            !expected_inconsistent,
                            "p = {p}, n = {n}: a model of an inconsistent system"
                        );
                        validate_model(&manager, f, &assertions, &model)
                            .unwrap_or_else(|e| panic!("p = {p}, n = {n}: {e}"));
                        models += 1;
                    }
                    FfOutcome::Unsat(core) => {
                        assert!(
                            expected_inconsistent,
                            "p = {p}, n = {n}: unsat on a consistent system"
                        );
                        assert!(
                            folded_false || core.certificate.is_some(),
                            "p = {p}, n = {n}: certified"
                        );
                    }
                    other => panic!("p = {p}, n = {n}: {other:?}"),
                }
                checked += 1;
            }
        }
    }
    assert_eq!(checked, 144);
    // Over-drawn systems (up to twenty equations in one variable) are
    // mostly inconsistent; both verdicts must have been exercised.
    assert!(
        (30..=114).contains(&models),
        "both verdicts exercised: {models} models of 144"
    );
}

/// Compound terms on the left of a linear equation: sums, products by a
/// numeral, and a bitsum (whose definition joins the linear system) all
/// read their parts' values in the model.
#[test]
fn compound_linear_terms_read_their_parts() {
    let mut manager = TermManager::new();
    let f = field(&mut manager, 7);
    let sort = manager
        .sorts
        .find_finite_field(&BigUint::from(7u32))
        .expect("field");
    let x = manager.mk_var("x", sort);
    let y = manager.mk_var("y", sort);
    let z = manager.mk_var("z", sort);
    let w = manager.mk_var("w", sort);
    let a = manager.mk_var("a", sort);
    let b = manager.mk_var("b", sort);
    let two = constant(&mut manager, f, 2);
    let six = constant(&mut manager, f, 6);
    let one = constant(&mut manager, f, 1);
    let x_plus_y = manager.mk_ff_add([x, y]).expect("field terms");
    let two_x = manager.mk_ff_mul([two, x]).expect("field terms");
    let bitsum = manager.mk_ff_bitsum([a, b, x]).expect("field terms");
    let assertions = vec![
        manager.mk_eq(x, two),
        manager.mk_eq(y, six),
        // (ff.add x y) = z
        manager.mk_eq(x_plus_y, z),
        // (ff.mul #f2m7 x) = w
        manager.mk_eq(two_x, w),
        manager.mk_eq(a, one),
        // (ff.bitsum a b x) = a + 2b + 4x = 1 + 0 + 8 = 2
        manager.mk_eq(bitsum, two),
    ];
    let FfOutcome::Model(model) = check_conjunction(&manager, f, &assertions, 1 << 24) else {
        panic!("not a model");
    };
    validate_model(&manager, f, &assertions, &model).expect("a model of the goal");
    let value = |t: TermId| model.value_of(t).cloned().expect("assigned");
    assert_eq!(value(z), BigUint::from(1u8), "2 + 6 = 1 in 𝔽₇");
    assert_eq!(value(w), BigUint::from(4u8), "2·2");
    // b is free: it takes 0, and the bitsum reads 1 + 0 + 4·2 = 9 = 2.
    assert_eq!(value(b), BigUint::from(0u8));
}

/// A disequality keeps the goal on the enumeration path and is still
/// decided: a pinned variable that must differ from another constant.
#[test]
fn a_disequality_is_still_decided() {
    let mut manager = TermManager::new();
    let f = field(&mut manager, 7);
    let sort = manager
        .sorts
        .find_finite_field(&BigUint::from(7u32))
        .expect("field");
    let x = manager.mk_var("x", sort);
    let one = constant(&mut manager, f, 1);
    let zero = constant(&mut manager, f, 0);
    let pinned = manager.mk_eq(x, one);
    let is_zero = manager.mk_eq(x, zero);
    let not_zero = manager.mk_not(is_zero);
    let assertions = vec![pinned, not_zero];
    let FfOutcome::Model(model) = check_conjunction(&manager, f, &assertions, 1 << 24) else {
        panic!("not a model");
    };
    validate_model(&manager, f, &assertions, &model).expect("a model");
    assert_eq!(model.value_of(x), Some(&BigUint::from(1u8)));
}

#[test]
fn no_generators_is_the_all_zero_model() {
    let mut manager = TermManager::new();
    let f = field(&mut manager, 7);
    let sort = manager
        .sorts
        .find_finite_field(&BigUint::from(7u32))
        .expect("field");
    let x = manager.mk_var("x", sort);
    let assertions = vec![manager.mk_true()];
    let FfOutcome::Model(model) = check_conjunction(&manager, f, &assertions, 1 << 24) else {
        panic!("not a model");
    };
    validate_model(&manager, f, &assertions, &model).expect("a model");
    // A variable the goal never mentions has no entry: the validator
    // never asks for one.
    assert_eq!(model.value_of(x), None);
}
