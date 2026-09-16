#![allow(clippy::unwrap_used)]

use nixie_core::ast::{TermId, TermManager};
use nixie_solver::{Solver, SolverResult};
use nixie_theories::cp::{CpModel, CpVar, Task, Transition};
use num_bigint::BigInt;

fn variable(
    cp: &mut CpModel,
    tm: &mut TermManager,
    name: &str,
    values: &[i64],
) -> (CpVar, Vec<TermId>) {
    let atoms: Vec<_> = values
        .iter()
        .map(|v| tm.mk_var(&format!("{name}_{v}"), tm.sorts.bool_sort))
        .collect();
    let var = cp
        .variable(
            values
                .iter()
                .zip(&atoms)
                .map(|(&v, &a)| (BigInt::from(v), a))
                .collect(),
            tm,
        )
        .unwrap();
    (var, atoms)
}

#[test]
fn hall_sets_and_repeated_checks_and_scopes() {
    let mut tm = TermManager::new();
    let mut cp = CpModel::new(&tm);
    let (x, _) = variable(&mut cp, &mut tm, "x", &[1, 2]);
    let (y, _) = variable(&mut cp, &mut tm, "y", &[1, 2]);
    let (z, za) = variable(&mut cp, &mut tm, "z", &[1, 2, 3]);
    cp.alldifferent(vec![x, y, z]).unwrap();
    let mut solver = Solver::new();
    solver.register_cp(cp, &mut tm).unwrap();
    assert_eq!(solver.check(&mut tm), SolverResult::Sat);
    assert_eq!(solver.check(&mut tm), SolverResult::Sat);
    solver.push();
    solver.assert(tm.mk_not(za[2]), &mut tm);
    assert_eq!(solver.check(&mut tm), SolverResult::Unsat);
    solver.pop();
    assert!(solver.model().is_none());
    assert_eq!(solver.check(&mut tm), SolverResult::Sat);
}

#[test]
fn all_five_constraints_reject_and_accept_complete_assignments() {
    for kind in 0..5 {
        for xval in 0..3 {
            for yval in 0..3 {
                for zval in 0..3 {
                    let mut tm = TermManager::new();
                    let mut cp = CpModel::new(&tm);
                    let (x, xa) = variable(&mut cp, &mut tm, "x", &[0, 1, 2]);
                    let (y, ya) = variable(&mut cp, &mut tm, "y", &[0, 1, 2]);
                    let (z, za) = variable(&mut cp, &mut tm, "z", &[0, 1, 2]);
                    let expected = match kind {
                        0 => {
                            cp.alldifferent(vec![x, y, z]).unwrap();
                            xval != yval && xval != zval && yval != zval
                        }
                        1 => {
                            cp.table(
                                vec![x, y, z],
                                vec![
                                    vec![0.into(), 1.into(), 2.into()],
                                    vec![2.into(), 0.into(), 1.into()],
                                ],
                            )
                            .unwrap();
                            [xval, yval, zval] == [0, 1, 2] || [xval, yval, zval] == [2, 0, 1]
                        }
                        2 => {
                            let transitions = (0..3)
                                .flat_map(|state| {
                                    (0..3).map(move |symbol| Transition {
                                        source: state,
                                        symbol: symbol.into(),
                                        destination: (state + symbol) % 3,
                                    })
                                })
                                .collect();
                            cp.regular(vec![x, y, z], 0, vec![0], transitions).unwrap();
                            (xval + yval + zval) % 3 == 0
                        }
                        3 => {
                            cp.circuit(vec![x, y, z]).unwrap();
                            [xval, yval, zval] == [1, 2, 0] || [xval, yval, zval] == [2, 0, 1]
                        }
                        4 => {
                            cp.cumulative(
                                vec![x, y, z]
                                    .into_iter()
                                    .map(|start| Task {
                                        start,
                                        duration: 2.into(),
                                        demand: 1.into(),
                                    })
                                    .collect(),
                                2.into(),
                            )
                            .unwrap();
                            (0..5).all(|time| {
                                [xval, yval, zval]
                                    .iter()
                                    .filter(|&&s| s <= time && time < s + 2)
                                    .count()
                                    <= 2
                            })
                        }
                        _ => unreachable!(),
                    };
                    let mut solver = Solver::new();
                    solver.register_cp(cp, &mut tm).unwrap();
                    for atom in [xa[xval], ya[yval], za[zval]] {
                        solver.assert(atom, &mut tm);
                    }
                    assert_eq!(
                        solver.check(&mut tm),
                        if expected {
                            SolverResult::Sat
                        } else {
                            SolverResult::Unsat
                        },
                        "kind={kind}, assignment={xval},{yval},{zval}"
                    );
                }
            }
        }
    }
}

#[test]
fn integer_binding_combines_with_arithmetic() {
    let mut tm = TermManager::new();
    let mut cp = CpModel::new(&tm);
    let (x, _) = variable(&mut cp, &mut tm, "x", &[1, 2]);
    let (y, _) = variable(&mut cp, &mut tm, "y", &[1, 2]);
    let xi = tm.mk_var("xi", tm.sorts.int_sort);
    let yi = tm.mk_var("yi", tm.sorts.int_sort);
    cp.bind_integer(x, xi, &mut tm).unwrap();
    cp.bind_integer(y, yi, &mut tm).unwrap();
    cp.alldifferent(vec![x, y]).unwrap();
    let mut solver = Solver::with_config(nixie_solver::SolverConfig::default().certified());
    solver.register_cp(cp, &mut tm).unwrap();
    solver.assert(tm.mk_eq(xi, yi), &mut tm);
    assert_eq!(
        solver.check(&mut tm),
        SolverResult::Unsat,
        "{:?}",
        solver.certification_failure()
    );
    let (originals, assertions) = solver.cp_proof_inputs();
    solver
        .get_cp_proof()
        .unwrap()
        .check(&originals, &assertions, &mut tm, 10_000_000)
        .unwrap();
    let mut incomplete = solver.get_cp_proof().unwrap().clone();
    assert!(!incomplete.theory_lemmas.is_empty());
    incomplete.theory_lemmas.clear();
    assert!(
        incomplete
            .check(&originals, &assertions, &mut tm, 10_000_000)
            .is_err()
    );
}

#[test]
fn table_aliases_and_empty_relations() {
    let mut tm = TermManager::new();
    let mut cp = CpModel::new(&tm);
    let (x, _) = variable(&mut cp, &mut tm, "x", &[0, 1]);
    cp.table(
        vec![x, x],
        vec![vec![0.into(), 1.into()], vec![1.into(), 0.into()]],
    )
    .unwrap();
    let mut solver = Solver::new();
    solver.register_cp(cp, &mut tm).unwrap();
    assert_eq!(solver.check(&mut tm), SolverResult::Unsat);
    for tuples in [vec![], vec![vec![]]] {
        let expected = if tuples.is_empty() {
            SolverResult::Unsat
        } else {
            SolverResult::Sat
        };
        let mut cp = CpModel::new(&tm);
        cp.table(vec![], tuples).unwrap();
        let mut solver = Solver::new();
        solver.register_cp(cp, &mut tm).unwrap();
        assert_eq!(solver.check(&mut tm), expected);
    }
}

#[test]
fn cumulative_bigints_and_half_open_zero_duration() {
    let mut tm = TermManager::new();
    let mut cp = CpModel::new(&tm);
    let huge: BigInt = BigInt::from(1) << 100;
    let a = tm.mk_var("a", tm.sorts.bool_sort);
    let b = tm.mk_var("b", tm.sorts.bool_sort);
    let x = cp.variable(vec![(huge.clone(), a)], &mut tm).unwrap();
    let y = cp.variable(vec![(&huge + 2, b)], &mut tm).unwrap();
    cp.cumulative(
        vec![
            Task {
                start: x,
                duration: 2.into(),
                demand: huge.clone(),
            },
            Task {
                start: y,
                duration: 2.into(),
                demand: huge.clone(),
            },
            Task {
                start: x,
                duration: 0.into(),
                demand: &huge + 1,
            },
        ],
        huge,
    )
    .unwrap();
    let mut solver = Solver::new();
    solver.register_cp(cp, &mut tm).unwrap();
    assert_eq!(solver.check(&mut tm), SolverResult::Sat);
}

#[test]
fn circuit_subtours_and_unsat_search() {
    let mut tm = TermManager::new();
    let mut cp = CpModel::new(&tm);
    let (a, _) = variable(&mut cp, &mut tm, "a", &[1]);
    let (b, _) = variable(&mut cp, &mut tm, "b", &[0]);
    let (c, _) = variable(&mut cp, &mut tm, "c", &[3]);
    let (d, _) = variable(&mut cp, &mut tm, "d", &[2]);
    cp.circuit(vec![a, b, c, d]).unwrap();
    let mut solver = Solver::new();
    solver.register_cp(cp, &mut tm).unwrap();
    assert_eq!(solver.check(&mut tm), SolverResult::Unsat);
}

#[test]
fn user_callbacks_fail_closed_on_bad_reasons_and_incomplete_checks() {
    use nixie_theories::user_propagator::{
        Consequence, PropagatorContext, PropagatorResult, UserPropagator,
    };
    struct BadReason {
        false_term: TermId,
        reason: TermId,
    }
    impl UserPropagator for BadReason {
        fn on_fixed(&mut self, _: TermId, _: TermId, ctx: &mut PropagatorContext) {
            ctx.propagate(Consequence::new(self.false_term, vec![self.reason]));
        }
        fn final_check(&mut self, _: &mut PropagatorContext) -> PropagatorResult {
            PropagatorResult::Sat
        }
    }
    struct Incomplete;
    impl UserPropagator for Incomplete {}
    for unregistered in [false, true] {
        let mut tm = TermManager::new();
        let p = tm.mk_var("p", tm.sorts.bool_sort);
        let q = tm.mk_var("q", tm.sorts.bool_sort);
        let reason = if unregistered { q } else { tm.mk_not(p) };
        let mut solver = Solver::new();
        solver
            .register_user_propagator(
                Box::new(BadReason {
                    false_term: tm.mk_false(),
                    reason,
                }),
                &[p],
                &mut tm,
            )
            .unwrap();
        solver.assert(p, &mut tm);
        assert_eq!(solver.check(&mut tm), SolverResult::Unknown);
        assert!(solver.model().is_none());
    }
    let mut tm = TermManager::new();
    let mut solver = Solver::new();
    solver
        .register_user_propagator(Box::new(Incomplete), &[], &mut tm)
        .unwrap();
    assert_eq!(solver.check(&mut tm), SolverResult::Unknown);
}

#[test]
fn registration_lifecycle_reset_and_certification() {
    use nixie_solver::SolverConfig;
    let mut tm = TermManager::new();
    let mut solver = Solver::new();
    solver.push();
    assert!(solver.register_cp(CpModel::new(&tm), &mut tm).is_err());
    solver.pop();
    assert_eq!(solver.check(&mut tm), SolverResult::Sat);
    assert!(solver.register_cp(CpModel::new(&tm), &mut tm).is_err());
    solver.reset();
    solver.register_cp(CpModel::new(&tm), &mut tm).unwrap();
    assert_eq!(solver.check_sat_only(&mut tm), SolverResult::Sat);
    let mut solver = Solver::with_config(SolverConfig {
        proof: true,
        ..Default::default()
    });
    solver.register_cp(CpModel::new(&tm), &mut tm).unwrap();
    assert_eq!(solver.check(&mut tm), SolverResult::Sat);
    assert!(solver.get_proof().is_none());
}

#[test]
fn search_combines_propagators_and_boolean_constraints() {
    // Each table alone has supports. Their conjunction forces x != x, so
    // deciding values must learn explained conflicts and backtrack.
    let mut tm = TermManager::new();
    let mut cp = CpModel::new(&tm);
    let (x, _) = variable(&mut cp, &mut tm, "x", &[0, 1]);
    let (y, _) = variable(&mut cp, &mut tm, "y", &[0, 1]);
    let (z, _) = variable(&mut cp, &mut tm, "z", &[0, 1]);
    let equal = vec![vec![0.into(), 0.into()], vec![1.into(), 1.into()]];
    cp.table(vec![x, y], equal.clone()).unwrap();
    cp.table(vec![y, z], equal).unwrap();
    cp.alldifferent(vec![x, z]).unwrap();
    let mut solver = Solver::new();
    solver.register_cp(cp, &mut tm).unwrap();
    assert_eq!(solver.check(&mut tm), SolverResult::Unsat);
}

#[test]
fn domain_exactly_one_and_invalid_construction() {
    let mut tm = TermManager::new();
    let mut cp = CpModel::new(&tm);
    let (_, atoms) = variable(&mut cp, &mut tm, "x", &[0, 1]);
    let mut solver = Solver::new();
    solver.register_cp(cp, &mut tm).unwrap();
    for atom in atoms {
        solver.assert(atom, &mut tm);
    }
    assert_eq!(solver.check(&mut tm), SolverResult::Unsat);
    let mut cp = CpModel::new(&tm);
    let (x, _) = variable(&mut cp, &mut tm, "empty", &[]);
    assert!(
        cp.cumulative(
            vec![Task {
                start: x,
                duration: (-1).into(),
                demand: 0.into()
            }],
            0.into()
        )
        .is_err()
    );
    assert!(cp.table(vec![x], vec![vec![]]).is_err());
    let mut solver = Solver::new();
    solver.register_cp(cp, &mut tm).unwrap();
    assert_eq!(solver.check(&mut tm), SolverResult::Unsat);
}

#[test]
fn specialized_shortcuts_cannot_skip_user_constraints() {
    let mut tm = TermManager::new();
    let mut cp = CpModel::new(&tm);
    cp.table(vec![], vec![]).unwrap(); // Unconditionally false client axiom.
    let mut solver = Solver::new();
    solver.set_logic("QF_NIA");
    solver.register_cp(cp, &mut tm).unwrap();
    let x = tm.mk_var("x", tm.sorts.int_sort);
    let square = tm.mk_mul([x, x]);
    let one = tm.mk_int(1);
    solver.assert(tm.mk_eq(square, one), &mut tm);
    // A specialized NIA engine can decide the SMT assertions without calling
    // the user propagator. Its satisfying model must still be rejected.
    assert!(matches!(
        solver.check(&mut tm),
        SolverResult::Unsat | SolverResult::Unknown
    ));
    assert!(solver.model().is_none());
}
