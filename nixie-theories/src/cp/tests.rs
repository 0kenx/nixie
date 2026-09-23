#![allow(clippy::unwrap_used)]

use super::*;
use crate::user_propagator::UserPropagatorManager;

#[test]
fn indexed_domain_exclusions_match_search_for_every_partial_assignment() {
    let mut tm = TermManager::new();
    let mut cp = CpModel::new(&tm);
    let mut rows = Vec::new();
    for (i, width) in [2, 3, 1].into_iter().enumerate() {
        let entries: Vec<_> = (0..width)
            .map(|j| {
                let atom = tm.mk_var(&format!("d{i}_{j}"), tm.sorts.bool_sort);
                ((BigInt::from(1) << 140) + BigInt::from(j), atom)
            })
            .collect();
        rows.push(entries.iter().map(|(_, a)| *a).collect::<Vec<_>>());
        cp.variable(entries, &mut tm).unwrap();
    }
    // A presence alias repeats a domain premise at the end of the reason
    // list. The witness must still select the first, domain-order occurrence.
    cp.cumulative_optional(
        vec![OptionalTask {
            presence: rows[0][0],
            start: CpVar(1),
            duration: 0.into(),
            demand: 1.into(),
        }],
        0.into(),
        &mut tm,
    )
    .unwrap();
    let originals = cp.domain_statements();
    let atoms: Vec<_> = rows.iter().flatten().copied().collect();
    let malformed = tm.mk_int(7);
    // Unknown, false, true, malformed for all six indicators: 4^6 states.
    for state in 0..4096usize {
        let mut fixed = FxHashMap::default();
        for (i, &atom) in atoms.iter().enumerate() {
            match state / 4usize.pow(i as u32) % 4 {
                0 => {}
                1 => {
                    fixed.insert(atom, tm.mk_false());
                }
                2 => {
                    fixed.insert(atom, tm.mk_true());
                }
                3 => {
                    fixed.insert(atom, malformed);
                }
                _ => unreachable!(),
            }
        }
        let mut queue = VecDeque::new();
        let mut journal = Vec::new();
        let equalities = FxHashSet::default();
        let mut ctx = PropagatorContext::new(&mut queue, &mut journal, &fixed, &equalities);
        let snapshot = cp.domains(&ctx);
        for (i, domain) in cp.domains.iter().enumerate() {
            let positives: Vec<_> = domain
                .atoms
                .iter()
                .enumerate()
                .filter(|(_, a)| fixed.get(a) == Some(&tm.mk_true()))
                .collect();
            let expected: Vec<_> = if let Some(&(j, _)) = positives.last() {
                vec![domain.values[j].clone()]
            } else {
                domain
                    .atoms
                    .iter()
                    .zip(&domain.values)
                    .filter(|(a, _)| !fixed.contains_key(a))
                    .map(|(_, v)| v.clone())
                    .collect()
            };
            assert_eq!(snapshot.values[i], expected);
            assert_eq!(
                snapshot.fixed_premises[i].map(|j| snapshot.reasons[j]),
                positives.last().map(|(_, a)| **a)
            );
        }
        let result = cp.run(&mut ctx);
        if fixed.values().any(|&v| v == malformed) {
            assert_eq!(result, PropagatorResult::Unknown);
            assert!(queue.is_empty());
            continue;
        }
        let inconsistent = rows.iter().any(|row| {
            row.iter()
                .filter(|a| fixed.get(a) == Some(&tm.mk_true()))
                .count()
                > 1
                || row.iter().all(|a| fixed.get(a) == Some(&tm.mk_false()))
        });
        assert_eq!(matches!(result, PropagatorResult::Unsat(_)), inconsistent);
        if !inconsistent {
            let expected: Vec<_> = rows
                .iter()
                .flat_map(|row| {
                    let has_true = row.iter().any(|a| fixed.get(a) == Some(&tm.mk_true()));
                    row.iter()
                        .filter(|a| has_true && !fixed.contains_key(a))
                        .map(|&a| tm.mk_not(a))
                        .collect::<Vec<_>>()
                })
                .collect();
            assert_eq!(queue.iter().map(|c| c.term).collect::<Vec<_>>(), expected);
        }
        for consequence in queue {
            let old = cp
                .explain(None, consequence.term, &consequence.justification)
                .unwrap();
            let old = old.domain_certificate.unwrap();
            let new = consequence.domain_certificate.unwrap();
            assert_eq!(new.statement(), old.statement());
            assert_eq!(new.rule, old.rule);
            let original = originals.iter().find(|o| new.is_for(o)).unwrap();
            new.check(original, consequence.term, &consequence.justification)
                .unwrap();
            cp.statement()
                .check_lemma(consequence.term, &consequence.justification, &mut 100_000)
                .unwrap();
        }
    }
}

#[test]
fn indexed_domain_exclusion_rejects_bad_premise_hints() {
    let mut tm = TermManager::new();
    let mut cp = CpModel::new(&tm);
    let a = tm.mk_var("a", tm.sorts.bool_sort);
    let b = tm.mk_var("b", tm.sorts.bool_sort);
    let foreign = tm.mk_var("foreign", tm.sorts.bool_sort);
    cp.variable(vec![(0.into(), a), (1.into(), b)], &mut tm)
        .unwrap();
    let statement = &cp.domain_statements()[0];
    let premises = [foreign, tm.mk_not(a), a, b, a];
    let conclusion = tm.mk_not(b);
    for index in [0, 1, 3, premises.len(), usize::MAX] {
        assert!(
            statement
                .explain_fixed(conclusion, &premises, index)
                .is_none()
        );
    }
    assert!(statement.explain_fixed(conclusion, &premises, 2).is_some());
    assert!(statement.explain_fixed(conclusion, &premises, 4).is_some());
    assert!(
        statement
            .explain_fixed(tm.mk_false(), &premises, 2)
            .is_none()
    );
    assert!(statement.explain_fixed(foreign, &premises, 2).is_none());
}

#[test]
fn indexed_domain_exclusion_preserves_first_global_witness() {
    let mut tm = TermManager::new();
    let mut cp = CpModel::new(&tm);
    let x0 = tm.mk_var("x0", tm.sorts.bool_sort);
    let x1 = tm.mk_var("x1", tm.sorts.bool_sort);
    let y1 = tm.mk_var("y1", tm.sorts.bool_sort);
    let x = cp
        .variable(vec![(0.into(), x0), (1.into(), x1)], &mut tm)
        .unwrap();
    let y = cp.variable(vec![(1.into(), y1)], &mut tm).unwrap();
    cp.alldifferent(vec![x, y]).unwrap();
    let fixed = FxHashMap::from_iter([(x0, tm.mk_true()), (y1, tm.mk_true())]);
    let mut queue = VecDeque::new();
    let mut journal = Vec::new();
    let equalities = FxHashSet::default();
    let mut ctx = PropagatorContext::new(&mut queue, &mut journal, &fixed, &equalities);
    assert_eq!(cp.run(&mut ctx), PropagatorResult::Sat);
    assert_eq!(queue.len(), 1);
    let consequence = queue.pop_front().unwrap();
    assert_eq!(consequence.term, tm.mk_not(x1));
    assert_eq!(consequence.justification, vec![x0, y1]);
    // Both exactly-one and the global exclude x=1. Preserve the old global
    // witness selection instead of short-circuiting on the snapshot's flag.
    assert!(consequence.domain_certificate.is_none());
    cp.statement()
        .check_lemma(consequence.term, &consequence.justification, &mut 100_000)
        .unwrap();
}

// Independent exhaustive oracle: check every emitted explanation against
// every concrete assignment compatible with its antecedents, not just the
// solver's selected model. Covers 5 * 7^3 partial domain states.
#[test]
fn every_partial_domain_reduction_has_a_valid_explanation() {
    for kind in 0..5 {
        for masks in 0..343 {
            let mut tm = TermManager::new();
            let mut cp = CpModel::new(&tm);
            let mut vars = Vec::new();
            let mut atoms = Vec::new();
            for i in 0..3 {
                let row: Vec<_> = (0..3)
                    .map(|j| tm.mk_var(&format!("v{i}_{j}"), tm.sorts.bool_sort))
                    .collect();
                vars.push(
                    cp.variable(
                        row.iter()
                            .enumerate()
                            .map(|(j, &a)| (j.into(), a))
                            .collect(),
                        &mut tm,
                    )
                    .unwrap(),
                );
                atoms.push(row);
            }
            match kind {
                0 => cp.alldifferent(vars.clone()).unwrap(),
                1 => cp
                    .table(
                        vars.clone(),
                        vec![
                            vec![0.into(), 1.into(), 2.into()],
                            vec![2.into(), 0.into(), 1.into()],
                        ],
                    )
                    .unwrap(),
                2 => cp
                    .regular(
                        vars.clone(),
                        0,
                        vec![0],
                        (0..3)
                            .flat_map(|q| {
                                (0..3).map(move |a| Transition {
                                    source: q,
                                    symbol: a.into(),
                                    destination: (q + a) % 3,
                                })
                            })
                            .collect(),
                    )
                    .unwrap(),
                3 => cp.circuit(vars.clone()).unwrap(),
                4 => cp
                    .cumulative(
                        vars.iter()
                            .map(|&start| Task {
                                start,
                                duration: 2.into(),
                                demand: 1.into(),
                            })
                            .collect(),
                        2.into(),
                    )
                    .unwrap(),
                _ => unreachable!(),
            }
            let (_, watches, prop) = cp.into_propagator();
            let mut manager = UserPropagatorManager::new();
            manager.register_propagator(prop);
            for a in watches {
                manager.watch_term(a);
            }
            let domains = [masks % 7 + 1, (masks / 7) % 7 + 1, masks / 49 + 1];
            for (i, row) in atoms.iter().enumerate() {
                for (j, &atom) in row.iter().enumerate() {
                    if domains[i] & (1 << j) == 0 {
                        manager.notify_fixed(atom, tm.mk_false());
                    }
                }
            }
            let result = manager.final_check();
            let mut consequences = manager.get_consequences();
            if let PropagatorResult::Unsat(reasons) = result {
                consequences.push(Consequence::new(tm.mk_false(), reasons));
            }
            for a in 0..3 {
                for b in 0..3 {
                    for c in 0..3 {
                        let assignment = [a, b, c];
                        let satisfies = match kind {
                            0 => a != b && b != c && a != c,
                            1 => assignment == [0, 1, 2] || assignment == [2, 0, 1],
                            2 => (a + b + c) % 3 == 0,
                            3 => assignment == [1, 2, 0] || assignment == [2, 0, 1],
                            4 => (0..5).all(|t| {
                                assignment.iter().filter(|&&s| s <= t && t < s + 2).count() <= 2
                            }),
                            _ => unreachable!(),
                        };
                        if !satisfies {
                            continue;
                        }
                        let mut truth = HashMap::new();
                        truth.insert(tm.mk_true(), true);
                        truth.insert(tm.mk_false(), false);
                        for (i, row) in atoms.iter().enumerate() {
                            for (j, &atom) in row.iter().enumerate() {
                                truth.insert(atom, assignment[i] == j);
                                truth.insert(tm.mk_not(atom), assignment[i] != j);
                            }
                        }
                        for consequence in &consequences {
                            if consequence
                                .justification
                                .iter()
                                .all(|r| truth.get(r) == Some(&true))
                            {
                                assert_eq!(
                                    truth.get(&consequence.term),
                                    Some(&true),
                                    "kind={kind}, masks={masks}, assignment={assignment:?}"
                                );
                            }
                        }
                    }
                }
            }
        }
    }
}

#[test]
fn hall_set_forces_a_value_before_any_variable_is_fixed() {
    let mut tm = TermManager::new();
    let mut cp = CpModel::new(&tm);
    let mut vars = Vec::new();
    let mut atoms = Vec::new();
    for (i, n) in [2, 2, 3].into_iter().enumerate() {
        let row: Vec<_> = (0..n)
            .map(|j| tm.mk_var(&format!("v{i}_{j}"), tm.sorts.bool_sort))
            .collect();
        vars.push(
            cp.variable(
                row.iter()
                    .enumerate()
                    .map(|(j, &a)| (j.into(), a))
                    .collect(),
                &mut tm,
            )
            .unwrap(),
        );
        atoms.push(row);
    }
    cp.alldifferent(vars).unwrap();
    let (_, watches, prop) = cp.into_propagator();
    let mut manager = UserPropagatorManager::new();
    manager.register_propagator(prop);
    for a in watches {
        manager.watch_term(a);
    }
    manager.final_check();
    let consequences = manager.get_consequences();
    for &a in &atoms[2][..2] {
        assert!(
            consequences
                .iter()
                .any(|c| c.term == tm.mk_not(a) && c.justification.is_empty())
        );
    }
}
