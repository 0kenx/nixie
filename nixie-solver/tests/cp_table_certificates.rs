//! The SAT adapter must authenticate/check certificate data before any conflict.
#![allow(clippy::unwrap_used)]
use nixie_core::ast::{TermId, TermManager};
use nixie_solver::{Solver, SolverResult};
use nixie_theories::cp::CpModel;
use nixie_theories::cp::table_proof::{TableCertificate, TableRowBlocker as B};
use nixie_theories::user_propagator::{
    Consequence, PropagatorContext, PropagatorResult, UserPropagator,
};

struct Replay {
    step: Consequence,
    on_fixed: bool,
    conflict: bool,
}
impl UserPropagator for Replay {
    fn on_fixed(&mut self, _: TermId, _: TermId, ctx: &mut PropagatorContext) {
        if self.on_fixed {
            ctx.propagate(self.step.clone());
        }
    }
    fn final_check(&mut self, ctx: &mut PropagatorContext) -> PropagatorResult {
        ctx.propagate(self.step.clone());
        if self.conflict {
            PropagatorResult::Unsat(vec![])
        } else {
            PropagatorResult::Sat
        }
    }
}

#[test]
fn forged_and_mutated_certificates_fail_closed_on_assignment_and_final_conflict() {
    for on_fixed in [false, true] {
        for substituted in [false, true] {
            let mut tm = TermManager::new();
            let a = tm.mk_var("a", tm.sorts.bool_sort);
            let b = tm.mk_var("b", tm.sorts.bool_sort);
            let mut cp = CpModel::new(&tm);
            let v = cp
                .variable(vec![(0.into(), a), (1.into(), b)], &mut tm)
                .unwrap();
            cp.table(vec![v], vec![vec![0.into()]]).unwrap();
            let original = cp.table_statements().remove(0);
            let certificate = if substituted {
                let mut fake = CpModel::new(&tm);
                let v = fake
                    .variable(vec![(0.into(), a), (1.into(), b)], &mut tm)
                    .unwrap();
                fake.table(vec![v], vec![]).unwrap();
                let other = fake.table_statements().remove(0);
                let cert = TableCertificate::new(other.clone(), vec![]);
                cert.check(&other, tm.mk_false(), &[]).unwrap();
                cert
            } else {
                // Valid for !b, invalid after changing the conclusion to false.
                let cert = TableCertificate::new(
                    original.clone(),
                    vec![B::NegatedConclusion { column: 0 }],
                );
                cert.check(&original, tm.mk_not(b), &[]).unwrap();
                cert
            };
            let mut step = Consequence::new(tm.mk_false(), vec![]);
            step.table_certificate = Some(certificate);
            let mut solver = Solver::new();
            solver.register_cp(cp, &mut tm).unwrap();
            solver
                .register_user_propagator(
                    Box::new(Replay {
                        step,
                        on_fixed,
                        conflict: true,
                    }),
                    &[a, b],
                    &mut tm,
                )
                .unwrap();
            assert_eq!(solver.check(&mut tm), SolverResult::Unknown);
            assert!(solver.model().is_none());
            assert!(solver.get_proof().is_none());
        }
    }
}

#[test]
fn valid_certificate_does_not_authorize_a_false_current_premise() {
    let mut tm = TermManager::new();
    let a = tm.mk_var("a", tm.sorts.bool_sort);
    let b = tm.mk_var("b", tm.sorts.bool_sort);
    let mut cp = CpModel::new(&tm);
    let v = cp
        .variable(vec![(0.into(), a), (1.into(), b)], &mut tm)
        .unwrap();
    cp.table(vec![v], vec![vec![0.into()], vec![1.into()]])
        .unwrap();
    let original = cp.table_statements().remove(0);
    let cert = TableCertificate::new(
        original.clone(),
        vec![
            B::NegatedConclusion { column: 0 },
            B::Premise {
                column: 0,
                premise: 0,
            },
        ],
    );
    let conclusion = tm.mk_not(b);
    cert.check(&original, conclusion, &[a]).unwrap();
    let mut step = Consequence::new(conclusion, vec![a]);
    step.table_certificate = Some(cert);
    let mut solver = Solver::new();
    solver.register_cp(cp, &mut tm).unwrap();
    solver
        .register_user_propagator(
            Box::new(Replay {
                step,
                on_fixed: false,
                conflict: false,
            }),
            &[a, b],
            &mut tm,
        )
        .unwrap();
    solver.assert(b, &mut tm);
    assert_eq!(solver.check(&mut tm), SolverResult::Unknown);
}

#[test]
fn table_certificate_does_not_enable_an_incomplete_sat_proof_chain() {
    use nixie_solver::SolverConfig;
    let mut tm = TermManager::new();
    let mut cp = CpModel::new(&tm);
    cp.table(vec![], vec![]).unwrap();
    let statement = cp.table_statements().remove(0);
    TableCertificate::new(statement.clone(), vec![])
        .check(&statement, tm.mk_false(), &[])
        .unwrap();
    let mut solver = Solver::with_config(SolverConfig {
        proof: true,
        ..Default::default()
    });
    solver.register_cp(cp, &mut tm).unwrap();
    assert_eq!(solver.check(&mut tm), SolverResult::Unknown);
    assert!(solver.get_proof().is_none());
}

#[test]
fn reset_drops_certificate_statement_authority() {
    let mut tm = TermManager::new();
    let mut cp = CpModel::new(&tm);
    cp.table(vec![], vec![]).unwrap();
    let statement = cp.table_statements().remove(0);
    let cert = TableCertificate::new(statement.clone(), vec![]);
    cert.check(&statement, tm.mk_false(), &[]).unwrap();
    let mut solver = Solver::new();
    solver.register_cp(cp, &mut tm).unwrap();
    solver.reset();
    let mut step = Consequence::new(tm.mk_false(), vec![]);
    step.table_certificate = Some(cert);
    solver
        .register_user_propagator(
            Box::new(Replay {
                step,
                on_fixed: false,
                conflict: true,
            }),
            &[],
            &mut tm,
        )
        .unwrap();
    assert_eq!(solver.check(&mut tm), SolverResult::Unknown);
}
