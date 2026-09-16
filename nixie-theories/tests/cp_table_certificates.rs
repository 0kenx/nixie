//! Adversarial checks of the standalone table checker, without CP filtering.
#![allow(clippy::unwrap_used)]
use nixie_core::ast::{TermId, TermManager};
use nixie_theories::cp::CpModel;
use nixie_theories::cp::table_proof::{TableCertificate, TableRowBlocker as B, TableStatement};
use nixie_theories::user_propagator::{PropagatorResult, UserPropagatorManager};
use num_bigint::BigInt;

fn equality_table(tm: &mut TermManager) -> (CpModel, Vec<Vec<TermId>>, TableStatement) {
    let mut cp = CpModel::new(tm);
    let mut atoms = Vec::new();
    let mut vars = Vec::new();
    for v in 0..2 {
        let row: Vec<_> = (0..2)
            .map(|i| tm.mk_var(&format!("v{v}_{i}"), tm.sorts.bool_sort))
            .collect();
        vars.push(
            cp.variable(
                row.iter()
                    .enumerate()
                    .map(|(i, &a)| (i.into(), a))
                    .collect(),
                tm,
            )
            .unwrap(),
        );
        atoms.push(row);
    }
    cp.table(
        vars,
        vec![vec![0.into(), 0.into()], vec![1.into(), 1.into()]],
    )
    .unwrap();
    let statement = cp.table_statements().remove(0);
    (cp, atoms, statement)
}

#[test]
fn checked_witnesses_survive_snapshot_and_nested_rollback() {
    let mut tm = TermManager::new();
    let (mut cp, atoms, original) = equality_table(&mut tm);
    // Adding a later domain must not mutate the retained original table.
    let extra = tm.mk_var("extra", tm.sorts.bool_sort);
    cp.variable(vec![(42.into(), extra)], &mut tm).unwrap();
    let (_, watches, prop) = cp.into_propagator();
    let mut manager = UserPropagatorManager::new();
    manager.register_propagator(prop);
    for atom in watches {
        manager.watch_term(atom);
    }
    manager.push();
    manager.notify_fixed(extra, tm.mk_true());
    manager.notify_fixed(atoms[0][0], tm.mk_true());
    let reductions = manager.get_consequences();
    let step = reductions
        .iter()
        .find(|c| c.term == tm.mk_not(atoms[1][1]))
        .unwrap();
    let cert = step.table_certificate.as_ref().unwrap();
    cert.check(&original, step.term, &step.justification)
        .unwrap();
    assert!(cert.is_for(&original));
    assert!(cert.check(&original, step.term, &[]).is_err());
    assert!(
        cert.check(&original, tm.mk_false(), &step.justification)
            .is_err()
    );
    let mut incomplete = cert.clone();
    incomplete.blockers.pop();
    assert!(
        incomplete
            .check(&original, step.term, &step.justification)
            .is_err()
    );
    manager.push();
    manager.notify_fixed(atoms[1][1], tm.mk_true());
    manager.get_consequences();
    assert!(matches!(manager.final_check(), PropagatorResult::Unsat(_)));
    // In particular, a direct final-check conflict has its own attached witness.
    let conflicts = manager.get_consequences();
    let conflict = conflicts.iter().find(|c| c.term == tm.mk_false()).unwrap();
    conflict
        .table_certificate
        .as_ref()
        .unwrap()
        .check(&original, conflict.term, &conflict.justification)
        .unwrap();
    manager.pop(1);
    assert!(!manager.has_consequences());
    manager.pop(1);
    assert_eq!(manager.get_fixed_value(atoms[0][0]), None);
    assert!(!manager.has_consequences());
    // It remains a valid conditional lemma even after its premise is no longer
    // fixed. Current truth is a separate obligation of the SAT adapter.
    cert.check(&original, step.term, &step.justification)
        .unwrap();
    assert_eq!(manager.final_check(), PropagatorResult::Unknown);
}

#[test]
fn original_statement_aliases_empty_arity_and_wide_values() {
    let mut tm = TermManager::new();
    let (mut cp, _, original) = equality_table(&mut tm);
    cp.table(Vec::new(), Vec::new()).unwrap();
    let empty = cp.table_statements().remove(1);
    let cert = TableCertificate::new(empty.clone(), vec![]);
    cert.check(&empty, tm.mk_false(), &[]).unwrap();
    assert!(cert.check(&original, tm.mk_false(), &[]).is_err());
    cp.table(Vec::new(), vec![vec![]]).unwrap();
    let inhabited = cp.table_statements().remove(2);
    assert!(
        TableCertificate::new(inhabited.clone(), vec![])
            .check(&inhabited, tm.mk_false(), &[])
            .is_err()
    );
    assert!(
        TableCertificate::new(inhabited.clone(), vec![B::OutsideDomain { column: 0 }])
            .check(&inhabited, tm.mk_false(), &[])
            .is_err()
    );

    let huge = BigInt::from(1) << 130usize;
    let a = tm.mk_var("wide_a", tm.sorts.bool_sort);
    let b = tm.mk_var("wide_b", tm.sorts.bool_sort);
    let mut wide = CpModel::new(&tm);
    let v = wide
        .variable(vec![(huge.clone(), a), (-&huge, b)], &mut tm)
        .unwrap();
    wide.table(
        vec![v, v],
        vec![vec![huge.clone(), -&huge], vec![&huge + 1, huge]],
    )
    .unwrap();
    let statement = wide.table_statements().remove(0);
    let cert = TableCertificate::new(
        statement.clone(),
        vec![
            B::Alias {
                first: 0,
                second: 1,
            },
            B::OutsideDomain { column: 0 },
        ],
    );
    cert.check(&statement, tm.mk_false(), &[]).unwrap();
    for bad in [
        B::Alias {
            first: 0,
            second: 0,
        },
        B::OutsideDomain { column: usize::MAX },
        B::Premise {
            column: 0,
            premise: usize::MAX,
        },
        B::NegatedConclusion { column: 0 },
    ] {
        let mut mutated = cert.clone();
        mutated.blockers[0] = bad;
        assert!(mutated.check(&statement, tm.mk_false(), &[]).is_err());
    }
}

#[test]
fn exhaustive_untrusted_witnesses_never_prove_a_false_implication() {
    let mut tm = TermManager::new();
    let (_, atoms, original) = equality_table(&mut tm);
    let unknown = tm.mk_var("foreign", tm.sorts.bool_sort);
    let mut literals = vec![tm.mk_false(), tm.mk_true(), unknown];
    for &a in atoms.iter().flatten() {
        literals.extend([a, tm.mk_not(a)]);
    }
    let mut premises = vec![vec![]];
    for &a in &literals {
        premises.push(vec![a]);
        for &b in &literals {
            premises.push(vec![a, b]);
        }
    }
    let mut choices = Vec::new();
    for column in 0..3 {
        choices.push(B::OutsideDomain { column });
        choices.push(B::NegatedConclusion { column });
        for index in 0..3 {
            choices.push(B::Alias {
                first: column,
                second: index,
            });
            choices.push(B::Premise {
                column,
                premise: index,
            });
        }
    }
    // Independently interpret the only two satisfying assignments (0,0)/(1,1),
    // and both possible truth values for the unrelated foreign atom.
    let truth = |lit, value: usize, foreign: bool| {
        if lit == tm.mk_true() {
            return true;
        }
        if lit == tm.mk_false() {
            return false;
        }
        if lit == unknown {
            return foreign;
        }
        for row in &atoms {
            for (i, &a) in row.iter().enumerate() {
                if lit == a {
                    return value == i;
                }
                // mk_not is already interned but takes &mut; use the supplied
                // literal's position instead of asking the checker to decode it.
                if lit == literals[3 + atoms.iter().position(|r| r == row).unwrap() * 4 + i * 2 + 1]
                {
                    return value != i;
                }
            }
        }
        panic!("unrecognized test literal")
    };
    let mut accepted = 0;
    let mut tried = 0;
    for reasons in &premises {
        for &conclusion in &literals {
            let valid = (0..2).all(|value| {
                [false, true].into_iter().all(|foreign| {
                    !reasons.iter().all(|&p| truth(p, value, foreign))
                        || truth(conclusion, value, foreign)
                })
            });
            for first in &choices {
                for second in &choices {
                    let cert = TableCertificate::new(
                        original.clone(),
                        vec![first.clone(), second.clone()],
                    );
                    tried += 1;
                    if cert.check(&original, conclusion, reasons).is_ok() {
                        accepted += 1;
                        assert!(
                            valid,
                            "unsound witness {cert:?}, premises={reasons:?}, conclusion={conclusion:?}"
                        );
                    }
                }
            }
        }
    }
    assert!(accepted > 100);
    eprintln!(
        "Checked {tried} untrusted table witnesses; {accepted} accepted implications independently validated"
    );
}
