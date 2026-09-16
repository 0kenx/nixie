//! Domain witness authentication and exact implication checks in the SAT adapter.
#![allow(clippy::unwrap_used)]
use nixie_core::ast::{TermId, TermManager};
use nixie_solver::{Solver, SolverConfig, SolverResult};
use nixie_theories::cp::{
    CpModel,
    domain_proof::{DomainCertificate, DomainRule as R},
};
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
fn pair(tm: &mut TermManager) -> (CpModel, TermId, TermId) {
    let a = tm.mk_var("a", tm.sorts.bool_sort);
    let b = tm.mk_var("b", tm.sorts.bool_sort);
    let mut cp = CpModel::new(tm);
    cp.variable(vec![(0.into(), a), (1.into(), b)], tm).unwrap();
    (cp, a, b)
}
#[test]
fn forged_and_mutated_domain_witnesses_fail_closed_in_assignment_and_final_check() {
    for on_fixed in [false, true] {
        for substituted in [false, true] {
            let mut tm = TermManager::new();
            let (cp, a, b) = pair(&mut tm);
            let original = cp.domain_statements().remove(0);
            let cert = if substituted {
                let mut fake = CpModel::new(&tm);
                fake.variable(vec![], &mut tm).unwrap();
                let foreign = fake.domain_statements().remove(0);
                let cert = DomainCertificate::new(foreign.clone(), R::Exhausted(vec![]));
                cert.check(&foreign, tm.mk_false(), &[]).unwrap();
                cert
            } else {
                let cert = DomainCertificate::new(original.clone(), R::Exclusion { fixed: 0 });
                cert.check(&original, tm.mk_not(b), &[a]).unwrap();
                cert
            };
            let mut step = Consequence::new(tm.mk_false(), vec![]);
            step.domain_certificate = Some(cert);
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
fn valid_domain_certificate_requires_true_current_premises() {
    let mut tm = TermManager::new();
    let (cp, a, b) = pair(&mut tm);
    let original = cp.domain_statements().remove(0);
    let cert = DomainCertificate::new(original.clone(), R::Exclusion { fixed: 0 });
    let conclusion = tm.mk_not(b);
    cert.check(&original, conclusion, &[a]).unwrap();
    let mut step = Consequence::new(conclusion, vec![a]);
    step.domain_certificate = Some(cert);
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
fn reset_revokes_domain_statement_authority() {
    let mut tm = TermManager::new();
    let mut cp = CpModel::new(&tm);
    cp.variable(vec![], &mut tm).unwrap();
    let statement = cp.domain_statements().remove(0);
    let cert = DomainCertificate::new(statement.clone(), R::Exhausted(vec![]));
    cert.check(&statement, tm.mk_false(), &[]).unwrap();
    let mut solver = Solver::new();
    solver.register_cp(cp, &mut tm).unwrap();
    solver.reset();
    let mut step = Consequence::new(tm.mk_false(), vec![]);
    step.domain_certificate = Some(cert);
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
#[test]
fn domain_certificates_do_not_enable_incomplete_unsat_proof_export() {
    let mut tm = TermManager::new();
    let (cp, a, b) = pair(&mut tm);
    let mut solver = Solver::with_config(SolverConfig {
        proof: true,
        ..Default::default()
    });
    solver.register_cp(cp, &mut tm).unwrap();
    solver.assert(a, &mut tm);
    solver.assert(b, &mut tm);
    assert_eq!(solver.check(&mut tm), SolverResult::Unknown);
    assert!(solver.get_proof().is_none());
}

#[test]
fn a_valid_table_witness_cannot_hide_an_invalid_domain_witness() {
    use nixie_theories::cp::table_proof::{TableCertificate, TableRowBlocker};
    let mut tm = TermManager::new();
    let a = tm.mk_var("selected", tm.sorts.bool_sort);
    let b = tm.mk_var("excluded", tm.sorts.bool_sort);
    let mut cp = CpModel::new(&tm);
    let var = cp
        .variable(vec![(0.into(), a), (1.into(), b)], &mut tm)
        .unwrap();
    cp.table(vec![var], vec![vec![0.into()]]).unwrap();
    let table = cp.table_statements().remove(0);
    let domain = cp.domain_statements().remove(0);
    let conclusion = tm.mk_not(b);
    let cert = TableCertificate::new(
        table.clone(),
        vec![TableRowBlocker::NegatedConclusion { column: 0 }],
    );
    cert.check(&table, conclusion, &[]).unwrap();
    let mut step = Consequence::new(conclusion, vec![]);
    step.table_certificate = Some(cert);
    step.domain_certificate = Some(DomainCertificate::new(
        domain,
        R::Exclusion { fixed: usize::MAX },
    ));
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
    assert_eq!(solver.check(&mut tm), SolverResult::Unknown);
}
