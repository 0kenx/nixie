#![allow(clippy::unwrap_used)]
use nixie_core::ast::{TermId, TermManager};
use nixie_solver::{CpProof, Solver, SolverConfig, SolverResult};
use nixie_theories::cp::{CpModel, CpVar, OptionalTask};
use num_bigint::BigInt;

fn start(
    cp: &mut CpModel,
    tm: &mut TermManager,
    name: &str,
    values: &[BigInt],
) -> (CpVar, Vec<TermId>) {
    let atoms: Vec<_> = values
        .iter()
        .enumerate()
        .map(|(i, _)| tm.mk_var(&format!("{name}{i}"), tm.sorts.bool_sort))
        .collect();
    let var = cp
        .variable(
            values.iter().cloned().zip(atoms.iter().copied()).collect(),
            tm,
        )
        .unwrap();
    (var, atoms)
}

fn checked(solver: &mut Solver, tm: &mut TermManager, expected: bool) {
    assert_eq!(
        solver.check(tm),
        if expected {
            SolverResult::Sat
        } else {
            SolverResult::Unsat
        },
        "{:?}",
        solver.certification_failure()
    );
    if !expected {
        let inputs = solver.cp_proof_inputs();
        let proof = solver.get_cp_proof().unwrap();
        let imported = CpProof::from_text(&proof.to_text()).unwrap();
        imported
            .check(&inputs.0, &inputs.1, &inputs.2, tm, 1_000_000)
            .unwrap();
    }
}

#[test]
fn exhaustive_public_optional_oracle_with_checked_proofs_and_nested_scopes() {
    // Unknown/false/true conditions crossed with both start assignments,
    // durations and demands 0..=2, and independent/shared/complemented guards.
    for shape in 0..3 {
        for parameters in 0..81 {
            let duration = [parameters % 3, parameters / 3 % 3];
            let demand = [parameters / 9 % 3, parameters / 27 % 3];
            let mut tm = TermManager::new();
            let mut cp = CpModel::new(&tm);
            let (x, xa) = start(&mut cp, &mut tm, "x", &[0.into(), 1.into()]);
            let (y, ya) = start(&mut cp, &mut tm, "y", &[0.into(), 1.into()]);
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
                        start: [x, y][i],
                        duration: duration[i].into(),
                        demand: demand[i].into(),
                    })
                    .collect(),
                1.into(),
                &mut tm,
            )
            .unwrap();
            let mut solver = Solver::with_config(SolverConfig::default().certified());
            solver.register_cp(cp, &mut tm).unwrap();
            for pv in 0..3 {
                for qv in 0..if shape == 0 { 3 } else { 1 } {
                    solver.push();
                    for (atom, state) in [(p, pv), (q, qv)] {
                        if state != 0 {
                            solver.assert(if state == 1 { tm.mk_not(atom) } else { atom }, &mut tm);
                        }
                    }
                    for (xv, &x_atom) in xa.iter().enumerate() {
                        for (yv, &y_atom) in ya.iter().enumerate() {
                            solver.push();
                            solver.assert(x_atom, &mut tm);
                            solver.assert(y_atom, &mut tm);
                            let expected = (0..4).any(|bits| {
                                let present = [bits & 1 != 0, bits & 2 != 0];
                                if [(pv, present[0]), (qv, present[1])]
                                    .iter()
                                    .any(|&(s, p)| s != 0 && (s == 2) != p)
                                {
                                    return false;
                                }
                                let active = [
                                    present[0],
                                    match shape {
                                        0 => present[1],
                                        1 => present[0],
                                        2 => !present[0],
                                        _ => unreachable!(),
                                    },
                                ];
                                (0..4).all(|t| {
                                    (0..2)
                                        .filter(|&i| {
                                            active[i]
                                                && [xv, yv][i] <= t
                                                && t < [xv, yv][i] + duration[i]
                                        })
                                        .map(|i| demand[i])
                                        .sum::<usize>()
                                        <= 1
                                })
                            });
                            checked(&mut solver, &mut tm, expected);
                            solver.pop();
                            assert!(solver.model().is_none());
                            assert!(solver.get_cp_proof().is_none());
                        }
                    }
                    solver.pop();
                }
            }
        }
    }
}

#[test]
fn wide_optional_endpoints_formulas_and_saved_proofs() {
    for proof_mode in [false, true] {
        let mut tm = TermManager::new();
        let mut cp = CpModel::new(&tm);
        let wide = BigInt::from(1) << 140usize;
        let (x, _) = start(&mut cp, &mut tm, "x", &[-&wide]);
        let (y, ya) = start(&mut cp, &mut tm, "y", &[0.into(), -&wide]);
        let p = tm.mk_var("p", tm.sorts.bool_sort);
        let q = tm.mk_var("q", tm.sorts.bool_sort);
        let guard = tm.mk_and([p, q]);
        cp.cumulative_optional(
            vec![
                OptionalTask {
                    presence: tm.mk_true(),
                    start: x,
                    duration: wide.clone(),
                    demand: wide.clone(),
                },
                OptionalTask {
                    presence: guard,
                    start: y,
                    duration: wide.clone(),
                    demand: wide.clone(),
                },
                OptionalTask {
                    presence: tm.mk_false(),
                    start: x,
                    duration: wide.clone(),
                    demand: &wide + 1,
                },
                OptionalTask {
                    presence: guard,
                    start: x,
                    duration: 0.into(),
                    demand: &wide + 1,
                },
                OptionalTask {
                    presence: guard,
                    start: x,
                    duration: wide.clone(),
                    demand: 0.into(),
                },
            ],
            wide,
            &mut tm,
        )
        .unwrap();
        let config = if proof_mode {
            SolverConfig::default().with_proof()
        } else {
            SolverConfig::default().certified()
        };
        let mut solver = Solver::with_config(config);
        solver.register_cp(cp, &mut tm).unwrap();
        solver.assert(p, &mut tm);
        solver.assert(q, &mut tm);
        checked(&mut solver, &mut tm, true); // Half-open endpoint at zero.
        solver.push();
        solver.assert(ya[1], &mut tm);
        checked(&mut solver, &mut tm, false);
        let inputs = solver.cp_proof_inputs();
        let proof = solver.get_cp_proof().unwrap().clone();
        let mut bad = proof.clone();
        for lemma in &mut bad.lemmas {
            lemma.premises.retain(|&r| r != guard);
        }
        assert!(
            bad.check(&inputs.0, &inputs.1, &inputs.2, &mut tm, 1_000_000)
                .is_err()
        );
        solver.pop();
        checked(&mut solver, &mut tm, true);
        proof
            .check(&inputs.0, &inputs.1, &inputs.2, &mut tm, 1_000_000)
            .unwrap();
    }
}

#[test]
fn presence_can_alias_a_start_indicator_and_absent_start_can_be_selected() {
    for absent in [false, true] {
        let mut tm = TermManager::new();
        let mut cp = CpModel::new(&tm);
        let (x, atoms) = start(&mut cp, &mut tm, "x", &[0.into(), 10.into()]);
        cp.cumulative_optional(
            vec![OptionalTask {
                presence: atoms[0],
                start: x,
                duration: 1.into(),
                demand: 2.into(),
            }],
            1.into(),
            &mut tm,
        )
        .unwrap();
        let mut solver = Solver::with_config(SolverConfig::default().certified());
        solver.register_cp(cp, &mut tm).unwrap();
        solver.assert(atoms[usize::from(absent)], &mut tm);
        checked(&mut solver, &mut tm, absent);
    }
}

#[test]
fn checked_refutation_without_application_assertions_and_empty_negative_capacity() {
    for empty in [false, true] {
        let mut tm = TermManager::new();
        let mut cp = CpModel::new(&tm);
        let tasks = if empty {
            vec![]
        } else {
            let (x, _) = start(&mut cp, &mut tm, "x", &[0.into(), 10.into()]);
            let p = tm.mk_var("p", tm.sorts.bool_sort);
            [p, tm.mk_not(p)]
                .into_iter()
                .map(|presence| OptionalTask {
                    presence,
                    start: x,
                    duration: 1.into(),
                    demand: 2.into(),
                })
                .collect()
        };
        cp.cumulative_optional(tasks, if empty { (-1).into() } else { 1.into() }, &mut tm)
            .unwrap();
        // Reconstruct after a search which did not record proof leaves.
        let mut solver = Solver::new();
        solver.register_cp(cp, &mut tm).unwrap();
        assert_eq!(solver.check(&mut tm), SolverResult::Unsat);
        solver.set_config(SolverConfig::default().certified());
        checked(&mut solver, &mut tm, false);
    }
}
