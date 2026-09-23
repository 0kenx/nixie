//! Exhaustive root oracle independent of production field arithmetic, plus
//! raw AST checks so constant folding cannot mask evaluation defects.
use nixie_core::ast::{CachedEvaluator, Model, ModelValue, TermKind, TermManager};
use nixie_core::sort::field::FieldId;
use nixie_math::ff::{FieldCtx, poly::MPoly};
use nixie_theories::ff_theory::{
    FfCertificate, FfOutcome, check_conjunction, evaluate_term_exact, validate_model,
};
use num_bigint::BigUint;
use rustc_hash::FxHashMap;
use smallvec::smallvec;

fn multiply(a: u32, b: u32, f: u32) -> u32 {
    let k = f.ilog2();
    let mut coefficients = vec![0u8; (2 * k + 1) as usize];
    for i in 0..k {
        for j in 0..k {
            coefficients[(i + j) as usize] ^= ((a >> i) & (b >> j) & 1) as u8;
        }
    }
    for i in (k..2 * k).rev() {
        if coefficients[i as usize] != 0 {
            for j in 0..=k {
                coefficients[(i - k + j) as usize] ^= ((f >> j) & 1) as u8;
            }
        }
    }
    (0..k).fold(0, |v, i| v | (u32::from(coefficients[i as usize]) << i))
}

#[test]
fn all_quadratic_root_sets_over_f4_f8_f16() {
    for f in [7u32, 11, 13, 19] {
        let mut m = TermManager::new();
        let sort = m.sorts.binary_field(f.into()).unwrap();
        let field = m.sorts.get(sort).unwrap().finite_field().unwrap();
        let x = m.mk_var("x", sort);
        let xx = m.mk_ff_mul([x, x]).unwrap();
        let q = 1 << f.ilog2();
        for a in 0..q {
            for b in 0..q {
                for c in 0..q {
                    let aa = m.mk_ff_const(field, a.into()).unwrap();
                    let bb = m.mk_ff_const(field, b.into()).unwrap();
                    let cc = m.mk_ff_const(field, c.into()).unwrap();
                    let axx = m.mk_ff_mul([aa, xx]).unwrap();
                    let bx = m.mk_ff_mul([bb, x]).unwrap();
                    let sum = m.mk_ff_add([axx, bx]).unwrap();
                    let literal = m.mk_eq(sum, cc);
                    let roots: Vec<_> = (0..q)
                        .filter(|&v| multiply(a, multiply(v, v, f), f) ^ multiply(b, v, f) == c)
                        .collect();
                    match check_conjunction(&m, field, &[literal], 100_000) {
                        FfOutcome::Model(model) => {
                            assert!(!roots.is_empty(), "f={f} a={a} b={b} c={c}");
                            validate_model(&m, field, &[literal], &model).unwrap();
                            if let Some(value) = model.value_of(x) {
                                assert!(roots.iter().any(|&v| BigUint::from(v) == *value));
                            }
                        }
                        FfOutcome::Unsat(_) | FfOutcome::Exhausted { .. } => {
                            assert!(roots.is_empty(), "f={f} a={a} b={b} c={c}")
                        }
                        other => panic!("unexpected {other:?}"),
                    }
                    // Check EVERY root, including repeated roots (zero derivative).
                    for v in 0..q {
                        let assignment = FxHashMap::from_iter([(x, BigUint::from(v))]);
                        let value = evaluate_term_exact(&m, field, sum, &assignment).unwrap();
                        assert_eq!(value == BigUint::from(c), roots.contains(&v));
                    }
                }
            }
        }
    }
}

#[test]
fn raw_ast_arithmetic_validation_and_budget_failure() {
    let mut m = TermManager::new();
    let sort = m.sorts.binary_field(7u8.into()).unwrap();
    let field = m.sorts.get(sort).unwrap().finite_field().unwrap();
    let x = m.mk_var("x", sort);
    let y = m.mk_var("y", sort);
    let nodes = [
        m.intern_term(TermKind::FfAdd(smallvec![x, y]), sort),
        m.intern_term(TermKind::FfMul(smallvec![x, y]), sort),
        m.intern_term(TermKind::FfNeg(x), sort),
        m.intern_term(TermKind::FfBitsum(smallvec![x, y]), sort),
    ];
    for a in 0u32..4 {
        for b in 0u32..4 {
            let expected = [a ^ b, multiply(a, b, 7), a, a];
            let assignments = FxHashMap::from_iter([(x, a.into()), (y, b.into())]);
            let mut model = Model::new();
            model.assign_ff(x, a.into(), field);
            model.assign_ff(y, b.into(), field);
            let mut evaluator = CachedEvaluator::new(&m, &model);
            for (&node, &value) in nodes.iter().zip(&expected) {
                assert_eq!(
                    evaluate_term_exact(&m, field, node, &assignments),
                    Some(value.into())
                );
                assert_eq!(
                    evaluator.eval(node),
                    Some(ModelValue::FiniteField {
                        value: value.into(),
                        field
                    })
                );
            }
        }
    }
    let bad = FxHashMap::from_iter([(x, 4u8.into()), (y, 0u8.into())]);
    assert!(evaluate_term_exact(&m, field, nodes[0], &bad).is_none());
    let zero = m.mk_ff_const(field, 0.into()).unwrap();
    let assertion = m.mk_eq(nodes[1], zero);
    assert!(matches!(
        check_conjunction(&m, field, &[assertion], 0),
        FfOutcome::OutOfBudget { .. }
    ));
    assert!(matches!(
        check_conjunction(&m, field, &[assertion], 1),
        FfOutcome::OutOfBudget { .. }
    ));
    let foreign = m.sorts.binary_field(11u8.into()).unwrap();
    let foreign_x = m.mk_var("foreign", foreign);
    assert!(
        evaluate_term_exact(
            &m,
            field,
            foreign_x,
            &FxHashMap::from_iter([(foreign_x, 0u8.into())])
        )
        .is_none()
    );
}

#[test]
fn prime_polynomial_certificates_cannot_replay_in_extension_fields() {
    let mut m = TermManager::new();
    let sort = m.sorts.binary_field(7u8.into()).unwrap();
    let field = m.sorts.get(sort).unwrap().finite_field().unwrap();
    let prime = FieldCtx::new(7u8.into()).unwrap();
    let one = MPoly::constant(&prime, &prime.one());
    for certificate in [
        FfCertificate::IdealMembership {
            field,
            generators: vec![(Some(0), one.clone())],
            cofactors: vec![one],
        },
        FfCertificate::CaseTree {
            field,
            literals: vec![],
            entries: vec![],
        },
        FfCertificate::Cardinality {
            field,
            literal: 0,
            k: 5,
        },
    ] {
        assert!(!certificate.verify(&m, &[m.false_id]));
    }
    // An invalid raw field id must not manufacture either a field or a verdict.
    assert!(matches!(
        check_conjunction(&m, FieldId::from_raw(u32::MAX), &[], 100),
        FfOutcome::InvalidModel(_)
    ));
}

#[test]
fn deep_shared_dags_and_invalid_model_leaves() {
    let mut m = TermManager::new();
    let sort = m.sorts.binary_field(7u8.into()).unwrap();
    let field = m.sorts.get(sort).unwrap().finite_field().unwrap();
    let x = m.mk_var("x", sort);
    let mut deep = x;
    for _ in 0..20_000 {
        deep = m.intern_term(TermKind::FfNeg(deep), sort);
    }
    // Shared squaring DAG must be linear in node count, not path count.
    for _ in 0..100 {
        deep = m.intern_term(TermKind::FfMul(smallvec![deep, deep]), sort);
    }
    assert_eq!(
        evaluate_term_exact(&m, field, deep, &FxHashMap::from_iter([(x, 2u8.into())])),
        Some(2u8.into())
    );
    for value in [-1, 4] {
        let mut model = Model::new();
        model.assign_ff(x, value.into(), field);
        assert!(CachedEvaluator::new(&m, &model).eval(x).is_none());
    }
    let sort2 = m.sorts.binary_field(11u8.into()).unwrap();
    let field2 = m.sorts.get(sort2).unwrap().finite_field().unwrap();
    let mut model = Model::new();
    model.assign_ff(x, 1.into(), field2);
    assert!(CachedEvaluator::new(&m, &model).eval(x).is_none());
}

#[test]
fn cardinality_certificate_binds_every_argument_to_claimed_field() {
    let mut m = TermManager::new();
    let prime = m.sorts.finite_field(2u8.into()).unwrap();
    let field = m.sorts.get(prime).unwrap().finite_field().unwrap();
    for actual in [
        m.sorts.binary_field(7u8.into()).unwrap(),
        m.sorts.finite_field(3u8.into()).unwrap(),
    ] {
        let vars = (0..3)
            .map(|i| m.mk_var(&format!("v{i}"), actual))
            .collect::<Vec<_>>();
        let literal = m.mk_distinct(vars.clone());
        // The statement is SAT, but claiming F_2 used to certify it UNSAT.
        let forged = FfCertificate::Cardinality {
            field,
            literal: 0,
            k: 3,
        };
        assert!(!forged.verify(&m, &[literal]));
        let actual_field = m.sorts.get(actual).unwrap().finite_field().unwrap();
        let pairs = (0..3)
            .flat_map(|i| (i + 1..3).map(move |j| (i, j)))
            .map(|(i, j)| {
                let eq = m.mk_eq(vars[i], vars[j]);
                m.mk_not(eq)
            })
            .collect::<Vec<_>>();
        assert!(matches!(
            check_conjunction(&m, actual_field, &pairs, 100_000),
            FfOutcome::Model(_)
        ));
    }
    let x = m.mk_var("a", prime);
    let y = m.mk_var("b", prime);
    let z = m.mk_var("c", prime);
    let genuine = m.mk_distinct([x, y, z]);
    assert!(
        FfCertificate::Cardinality {
            field,
            literal: 0,
            k: 3
        }
        .verify(&m, &[genuine])
    );
}

#[test]
fn coupled_affine_systems_match_exhaustive_f4_oracle() {
    let mut m = TermManager::new();
    let sort = m.sorts.binary_field(7u8.into()).unwrap();
    let field = m.sorts.get(sort).unwrap().finite_field().unwrap();
    let x = m.mk_var("x", sort);
    let y = m.mk_var("y", sort);
    let xx = m.mk_ff_mul([x, x]).unwrap();
    let yy = m.mk_ff_mul([y, y]).unwrap();
    for a in 0u32..4 {
        for b in 0u32..4 {
            let aa = m.mk_ff_const(field, a.into()).unwrap();
            let bb = m.mk_ff_const(field, b.into()).unwrap();
            let axx = m.mk_ff_mul([aa, xx]).unwrap();
            let byy = m.mk_ff_mul([bb, yy]).unwrap();
            let left = m.mk_ff_add([axx, y]).unwrap();
            let right = m.mk_ff_add([x, byy]).unwrap();
            for c in 0u32..4 {
                for d in 0u32..4 {
                    let cc = m.mk_ff_const(field, c.into()).unwrap();
                    let dd = m.mk_ff_const(field, d.into()).unwrap();
                    let assertions = [m.mk_eq(left, cc), m.mk_eq(right, dd)];
                    let solutions = (0..16u32)
                        .filter(|&v| {
                            let (x, y) = (v & 3, v >> 2);
                            multiply(a, multiply(x, x, 7), 7) ^ y == c
                                && x ^ multiply(b, multiply(y, y, 7), 7) == d
                        })
                        .collect::<Vec<_>>();
                    match check_conjunction(&m, field, &assertions, 100_000) {
                        FfOutcome::Model(model) => {
                            assert!(!solutions.is_empty());
                            validate_model(&m, field, &assertions, &model).unwrap();
                        }
                        FfOutcome::Exhausted { certificate: None } => assert!(solutions.is_empty()),
                        other => panic!("unexpected {other:?}"),
                    }
                }
            }
        }
    }
}
