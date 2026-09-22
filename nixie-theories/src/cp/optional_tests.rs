#![allow(clippy::unwrap_used)]
use super::*;
use crate::user_propagator::UserPropagatorManager;

fn install(cp: CpModel) -> UserPropagatorManager {
    let (_, watches, callback) = cp.into_propagator();
    let mut manager = UserPropagatorManager::new();
    manager.register_propagator(callback);
    for watch in watches {
        manager.watch_term(watch);
    }
    manager
}

// Two tasks, every duration/demand in 0..=2, capacity -1..=2,
// independent/shared/complementary presence, all nonempty start subdomains,
// and every unknown/false/true presence state. The oracle uses unit time
// slots, not mandatory parts, event sweeps, or the certificate checker.
#[test]
fn exhaustive_optional_scheduling_explanations_and_models() {
    let mut states = 0;
    for shape in 0..3 {
        for parameters in 0..324 {
            let durations = [parameters % 3, parameters / 3 % 3];
            let demands = [parameters / 9 % 3, parameters / 27 % 3];
            let capacity = (parameters / 81) as i32 - 1;
            let mut tm = TermManager::new();
            let mut cp = CpModel::new(&tm);
            let atoms: Vec<Vec<_>> = (0..2)
                .map(|i| {
                    (0..2)
                        .map(|j| tm.mk_var(&format!("s{i}_{j}"), tm.sorts.bool_sort))
                        .collect()
                })
                .collect();
            let vars: Vec<_> = atoms
                .iter()
                .map(|row| {
                    cp.variable(
                        row.iter()
                            .enumerate()
                            .map(|(i, &a)| (i.into(), a))
                            .collect(),
                        &mut tm,
                    )
                    .unwrap()
                })
                .collect();
            let p = tm.mk_var("p", tm.sorts.bool_sort);
            let q = tm.mk_var("q", tm.sorts.bool_sort);
            let second = match shape {
                0 => q,
                1 => p,
                2 => tm.mk_not(p),
                _ => unreachable!(),
            };
            cp.cumulative_optional(
                (0..2)
                    .map(|i| OptionalTask {
                        presence: [p, second][i],
                        start: vars[i],
                        duration: durations[i].into(),
                        demand: demands[i].into(),
                    })
                    .collect(),
                capacity.into(),
                &mut tm,
            )
            .unwrap();
            let statement = cp.statement();
            statement.check_encoding(&mut tm).unwrap();
            let mut solutions = Vec::new();
            for assignment in 0..16 {
                let starts = [assignment & 1, assignment >> 1 & 1];
                let pv = assignment & 4 != 0;
                let qv = assignment & 8 != 0;
                let present = [
                    pv,
                    match shape {
                        0 => qv,
                        1 => pv,
                        2 => !pv,
                        _ => unreachable!(),
                    },
                ];
                let valid = capacity >= 0
                    && (0..4).all(|time| {
                        (0..2)
                            .filter(|&i| {
                                present[i] && starts[i] <= time && time < starts[i] + durations[i]
                            })
                            .map(|i| demands[i] as i32)
                            .sum::<i32>()
                            <= capacity
                    });
                let mut truth = HashMap::from([(tm.mk_true(), true), (tm.mk_false(), false)]);
                for (i, row) in atoms.iter().enumerate() {
                    for (j, &a) in row.iter().enumerate() {
                        truth.insert(a, starts[i] == j);
                        truth.insert(tm.mk_not(a), starts[i] != j);
                    }
                }
                for (a, v) in [(p, pv), (q, qv)] {
                    truth.insert(a, v);
                    truth.insert(tm.mk_not(a), !v);
                }
                assert_eq!(
                    statement
                        .check_model(|t| truth.get(&t).copied(), &mut 100_000)
                        .is_ok(),
                    valid
                );
                if valid {
                    solutions.push(truth);
                }
            }
            let mut manager = install(cp);
            for masks in 0..9 {
                for presence_state in 0..if shape == 0 { 9 } else { 3 } {
                    states += 1;
                    manager.push();
                    for (i, row) in atoms.iter().enumerate() {
                        let mask = (masks / 3usize.pow(i as u32)) % 3 + 1;
                        for (j, &atom) in row.iter().enumerate() {
                            if mask & (1 << j) == 0 {
                                manager.notify_fixed(atom, tm.mk_false());
                            }
                        }
                    }
                    for (i, atom) in [p, q]
                        .into_iter()
                        .take(if shape == 0 { 2 } else { 1 })
                        .enumerate()
                    {
                        match presence_state / 3usize.pow(i as u32) % 3 {
                            0 => {}
                            1 => manager.notify_fixed(atom, tm.mk_false()),
                            2 => manager.notify_fixed(atom, tm.mk_true()),
                            _ => unreachable!(),
                        }
                    }
                    let verdict = manager.final_check();
                    let mut consequences = manager.get_consequences();
                    if let PropagatorResult::Unsat(reasons) = verdict {
                        consequences.push(Consequence::new(tm.mk_false(), reasons));
                    }
                    for consequence in consequences {
                        statement
                            .check_lemma(consequence.term, &consequence.justification, &mut 100_000)
                            .unwrap();
                        for truth in &solutions {
                            if consequence.justification.iter().all(|r| truth[r]) {
                                assert!(
                                    truth[&consequence.term],
                                    "shape={shape} params={parameters} masks={masks} presence={presence_state}"
                                );
                            }
                        }
                    }
                    manager.pop(1);
                    assert!(manager.get_consequences().is_empty());
                }
            }
        }
    }
    assert_eq!(states, 43_740);
}

#[test]
fn presence_is_required_in_start_explanations_and_absence_preserves_starts() {
    let mut tm = TermManager::new();
    let mut cp = CpModel::new(&tm);
    let a = tm.mk_var("a", tm.sorts.bool_sort);
    let b = tm.mk_var("b", tm.sorts.bool_sort);
    let fixed = tm.mk_var("fixed", tm.sorts.bool_sort);
    let p = tm.mk_var("p", tm.sorts.bool_sort);
    let start = cp
        .variable(vec![(0.into(), a), (1.into(), b)], &mut tm)
        .unwrap();
    let other = cp.variable(vec![(0.into(), fixed)], &mut tm).unwrap();
    cp.cumulative_optional(
        vec![
            OptionalTask {
                presence: p,
                start,
                duration: 1.into(),
                demand: 1.into(),
            },
            OptionalTask {
                presence: tm.mk_true(),
                start: other,
                duration: 1.into(),
                demand: 1.into(),
            },
        ],
        1.into(),
        &mut tm,
    )
    .unwrap();
    let statement = cp.statement();
    let mut manager = install(cp);
    manager.final_check();
    assert!(
        !manager
            .get_consequences()
            .iter()
            .any(|c| c.term == tm.mk_not(a))
    );
    manager.push();
    manager.notify_fixed(p, tm.mk_true());
    manager.final_check();
    let consequence = manager
        .get_consequences()
        .into_iter()
        .find(|c| c.term == tm.mk_not(a))
        .unwrap();
    assert!(consequence.justification.contains(&p));
    statement
        .check_lemma(consequence.term, &consequence.justification, &mut 100_000)
        .unwrap();
    let without_presence: Vec<_> = consequence
        .justification
        .into_iter()
        .filter(|&r| r != p)
        .collect();
    assert!(
        statement
            .check_lemma(consequence.term, &without_presence, &mut 100_000)
            .is_err()
    );
    manager.pop(1);
    manager.push();
    manager.notify_fixed(p, tm.mk_false());
    manager.final_check();
    assert!(
        !manager
            .get_consequences()
            .iter()
            .any(|c| [tm.mk_not(a), tm.mk_not(b)].contains(&c.term))
    );
    manager.pop(1);
    manager.push();
    manager.notify_fixed(a, tm.mk_true());
    manager.final_check();
    assert!(
        manager
            .get_consequences()
            .iter()
            .any(|c| c.term == tm.mk_not(p))
    );
    manager.pop(1);
    assert!(
        statement
            .check_model(|t| if t == p { None } else { Some(t != b) }, &mut 100_000)
            .is_err()
    );
}

#[test]
fn invalid_optional_construction_is_atomic_and_presence_encoding_is_checked() {
    let mut tm = TermManager::new();
    let mut cp = CpModel::new(&tm);
    let a = tm.mk_var("a", tm.sorts.bool_sort);
    let start = cp.variable(vec![(0.into(), a)], &mut tm).unwrap();
    let before = cp.statement();
    for (presence, duration, demand, start) in [
        (tm.mk_int(0), 1, 1, start),
        (a, -1, 1, start),
        (a, 1, -1, start),
        (a, 1, 1, CpVar(999)),
        (TermId(u32::MAX), 1, 1, start),
    ] {
        assert!(
            cp.cumulative_optional(
                vec![OptionalTask {
                    presence,
                    start,
                    duration: duration.into(),
                    demand: demand.into()
                }],
                1.into(),
                &mut tm
            )
            .is_err()
        );
        assert_eq!(cp.statement(), before);
    }
    cp.cumulative_optional(
        vec![OptionalTask {
            presence: a,
            start,
            duration: 1.into(),
            demand: 1.into(),
        }],
        1.into(),
        &mut tm,
    )
    .unwrap();
    let mut bad = cp.statement();
    bad.presences[0].negation = a;
    assert!(bad.check_encoding(&mut tm).is_err());
}

#[test]
fn exhausting_all_candidate_starts_forces_absence_without_a_mandatory_part() {
    let mut tm = TermManager::new();
    let mut cp = CpModel::new(&tm);
    let p = tm.mk_var("p", tm.sorts.bool_sort);
    let a = tm.mk_var("a", tm.sorts.bool_sort);
    let b = tm.mk_var("b", tm.sorts.bool_sort);
    let c = tm.mk_var("c", tm.sorts.bool_sort);
    let x = cp
        .variable(vec![(0.into(), a), (2.into(), b)], &mut tm)
        .unwrap();
    let y = cp.variable(vec![(0.into(), c)], &mut tm).unwrap();
    cp.cumulative_optional(
        vec![
            OptionalTask {
                presence: p,
                start: x,
                duration: 1.into(),
                demand: 1.into(),
            },
            OptionalTask {
                presence: tm.mk_true(),
                start: y,
                duration: 3.into(),
                demand: 1.into(),
            },
        ],
        1.into(),
        &mut tm,
    )
    .unwrap();
    let statement = cp.statement();
    let mut manager = install(cp);
    manager.final_check();
    let consequences = manager.get_consequences();
    let absence = consequences
        .iter()
        .find(|c| c.term == tm.mk_not(p))
        .unwrap();
    statement
        .check_lemma(absence.term, &absence.justification, &mut 100_000)
        .unwrap();
    assert!(
        !consequences
            .iter()
            .any(|c| c.term == tm.mk_not(a) || c.term == tm.mk_not(b))
    );
}
