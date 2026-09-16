#![allow(clippy::unwrap_used)]

use super::*;
use crate::user_propagator::UserPropagatorManager;

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
