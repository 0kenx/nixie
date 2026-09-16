//! Concrete truth-table tests of untrusted exactly-one witnesses and callbacks.
#![allow(clippy::unwrap_used)]
use nixie_core::ast::{TermId, TermManager};
use nixie_theories::cp::{
    CpModel,
    domain_proof::{DomainCertificate, DomainRule as R, DomainStatement},
};
use nixie_theories::user_propagator::{PropagatorResult, UserPropagatorManager};
use num_bigint::BigInt;

fn domain(tm: &mut TermManager, n: usize) -> (CpModel, Vec<TermId>, DomainStatement) {
    let mut cp = CpModel::new(tm);
    let atoms: Vec<_> = (0..n)
        .map(|i| tm.mk_var(&format!("v{i}"), tm.sorts.bool_sort))
        .collect();
    cp.variable(
        atoms
            .iter()
            .enumerate()
            .map(|(i, &a)| ((BigInt::from(1) << 131) + BigInt::from(i), a))
            .collect(),
        tm,
    )
    .unwrap();
    let original = cp.domain_statements().remove(0);
    (cp, atoms, original)
}

fn products<T: Clone>(items: &[T], len: usize) -> Vec<Vec<T>> {
    let mut rows = vec![vec![]];
    for _ in 0..len {
        rows = rows
            .iter()
            .flat_map(|row| {
                items.iter().map(move |item| {
                    let mut next = row.clone();
                    next.push(item.clone());
                    next
                })
            })
            .collect();
    }
    rows
}

#[test]
fn adversarial_domain_witnesses_match_concrete_one_hot_assignments() {
    let mut candidates = 0usize;
    let mut accepted = 0usize;
    for n in 0..=3 {
        let mut tm = TermManager::new();
        let (_, atoms, original) = domain(&mut tm, n);
        let foreign = tm.mk_var("foreign", tm.sorts.bool_sort);
        let mut literals = vec![tm.mk_false(), tm.mk_true(), foreign];
        for &a in &atoms {
            literals.extend([a, tm.mk_not(a)]);
        }
        let indexes = [0, 1, 2, usize::MAX];
        let mut rules = Vec::new();
        for &first in &indexes {
            rules.push(R::Exclusion { fixed: first });
            for &second in &indexes {
                rules.push(R::DistinctFixed { first, second });
            }
        }
        // Exact covers plus missing and surplus coverage.
        for len in 0..=n + 1 {
            rules.extend(products(&indexes, len).into_iter().map(R::Exhausted));
        }
        let truth = |term, chosen, other| {
            if term == tm.mk_false() {
                false
            } else if term == tm.mk_true() {
                true
            } else if term == foreign {
                other
            } else {
                let index = literals.iter().position(|&p| p == term).unwrap() - 3;
                (chosen == index / 2) == index.is_multiple_of(2)
            }
        };
        for len in 0..=3 {
            for premises in products(&literals, len) {
                for &conclusion in &literals {
                    for rule in &rules {
                        candidates += 1;
                        let cert = DomainCertificate::new(original.clone(), rule.clone());
                        if cert.check(&original, conclusion, &premises).is_err() {
                            continue;
                        }
                        accepted += 1;
                        for chosen in 0..n {
                            for other in [false, true] {
                                assert!(
                                    !premises.iter().all(|&p| truth(p, chosen, other))
                                        || truth(conclusion, chosen, other),
                                    "accepted false implication: {cert:?}, {premises:?} => {conclusion:?}"
                                );
                            }
                        }
                    }
                }
            }
        }
    }
    eprintln!("Domain certificate adversarial candidates={candidates}, accepted={accepted}");
    assert!(candidates > 1_000_000 && accepted > 100);
}

#[test]
fn every_domain_callback_step_has_a_certificate_across_nested_scopes() {
    let mut checked = 0;
    for n in 0..=3 {
        let mut tm = TermManager::new();
        let (mut cp, atoms, original) = domain(&mut tm, n);
        let extra = tm.mk_var("extra", tm.sorts.bool_sort);
        cp.variable(vec![(7.into(), extra)], &mut tm).unwrap();
        assert!(cp.domain_statements()[0] == original);
        let (_, watches, callback) = cp.into_propagator();
        let mut manager = UserPropagatorManager::new();
        manager.register_propagator(callback);
        for a in watches {
            manager.watch_term(a);
        }
        for states in products(&[None, Some(false), Some(true)], n) {
            manager.push();
            for (&a, value) in atoms.iter().zip(&states) {
                if let Some(value) = value {
                    manager.notify_fixed(a, tm.mk_bool(*value));
                }
            }
            let result = manager.final_check();
            let steps = manager.get_consequences();
            let feasible = (0..n).any(|chosen| {
                states
                    .iter()
                    .enumerate()
                    .all(|(i, v)| v.is_none_or(|b| b == (chosen == i)))
            });
            assert_eq!(matches!(result, PropagatorResult::Unsat(_)), !feasible);
            for step in &steps {
                let cert = step.domain_certificate.as_ref().unwrap();
                assert!(cert.is_for(&original));
                cert.check(&original, step.term, &step.justification)
                    .unwrap();
                checked += 1;
            }
            manager.push();
            manager.notify_fixed(extra, tm.mk_true());
            manager.pop(1);
            assert!(!manager.has_consequences());
            manager.pop(1);
            assert!(!manager.has_consequences());
            // Conditional proofs stay valid after their premises cease to be fixed.
            for step in steps {
                step.domain_certificate
                    .unwrap()
                    .check(&original, step.term, &step.justification)
                    .unwrap();
            }
            for &a in &atoms {
                assert_eq!(manager.get_fixed_value(a), None);
            }
        }
    }
    eprintln!("Domain callback certificates checked={checked}");
    assert!(checked > 30);
}

#[test]
fn mutations_and_foreign_statements_cannot_authorize_a_domain_lemma() {
    let mut tm = TermManager::new();
    let (_, atoms, original) = domain(&mut tm, 2);
    let conclusion = tm.mk_not(atoms[1]);
    let cert = DomainCertificate::new(original.clone(), R::Exclusion { fixed: 0 });
    cert.check(&original, conclusion, &[atoms[0]]).unwrap();
    assert!(cert.check(&original, conclusion, &[]).is_err());
    assert!(cert.check(&original, tm.mk_false(), &[atoms[0]]).is_err());
    assert!(
        cert.check(&original, tm.mk_not(atoms[0]), &[atoms[0]])
            .is_err()
    );
    let (_, _, other) = domain(&mut tm, 1);
    assert!(!cert.is_for(&other));
    assert!(cert.check(&other, conclusion, &[atoms[0]]).is_err());
    let duplicate = DomainCertificate::new(
        original.clone(),
        R::DistinctFixed {
            first: 0,
            second: 1,
        },
    );
    assert!(
        duplicate
            .check(&original, tm.mk_false(), &[atoms[0], atoms[0]])
            .is_err()
    );
    let incomplete = DomainCertificate::new(original.clone(), R::Exhausted(vec![0, 0]));
    assert!(
        incomplete
            .check(&original, tm.mk_false(), &[tm.mk_not(atoms[0])])
            .is_err()
    );
}

#[test]
fn non_boolean_callback_values_cannot_manufacture_a_domain_conflict() {
    let mut tm = TermManager::new();
    let (cp, atoms, _) = domain(&mut tm, 2);
    let (_, watches, callback) = cp.into_propagator();
    let mut manager = UserPropagatorManager::new();
    manager.register_propagator(callback);
    for atom in watches {
        manager.watch_term(atom);
    }
    manager.notify_fixed(atoms[0], tm.mk_int(123));
    assert_eq!(manager.final_check(), PropagatorResult::Unknown);
    assert!(!manager.has_consequences());
}
