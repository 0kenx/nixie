#![allow(clippy::unwrap_used)]
use nixie_core::ast::{TermId, TermManager};
use nixie_solver::{CpLemma, CpProof};
use nixie_solver::{Solver, SolverConfig, SolverResult};
use nixie_theories::cp::{CpModel, CpVar};
use nixie_theories::user_propagator::{PropagatorContext, PropagatorResult, UserPropagator};

fn variable(cp: &mut CpModel, tm: &mut TermManager, name: &str) -> (CpVar, [TermId; 2]) {
    let atoms = [
        tm.mk_var(&format!("{name}0"), tm.sorts.bool_sort),
        tm.mk_var(&format!("{name}1"), tm.sorts.bool_sort),
    ];
    (
        cp.variable(vec![(0.into(), atoms[0]), (1.into(), atoms[1])], tm)
            .unwrap(),
        atoms,
    )
}

fn hall(tm: &mut TermManager) -> Solver {
    let mut cp = CpModel::new(tm);
    let (x, _) = variable(&mut cp, tm, "x");
    let (y, _) = variable(&mut cp, tm, "y");
    let (z, _) = variable(&mut cp, tm, "z");
    cp.alldifferent(vec![x, y, z]).unwrap();
    let mut solver = Solver::with_config(SolverConfig::default().with_proof());
    solver.register_cp(cp, tm).unwrap();
    solver
}

#[test]
fn full_export_roundtrip_and_tampering_fail_closed() {
    let mut tm = TermManager::new();
    let mut solver = hall(&mut tm);
    let (originals, graphs, assertions) = solver.cp_proof_inputs();
    let _ = &graphs;
    assert_eq!(
        solver.check(&mut tm),
        SolverResult::Unsat,
        "{:?}",
        solver.certification_failure()
    );
    let proof = solver.get_cp_proof().unwrap().clone();
    assert!(!proof.lemmas.is_empty());
    assert!(!proof.lrat.is_empty());
    let exported = proof.to_text();
    assert_eq!(CpProof::from_text(&exported).unwrap(), proof);
    proof
        .check(&originals, &graphs, &assertions, &mut tm, 1_000_000)
        .unwrap();
    let cnf = proof
        .dimacs(&originals, &graphs, &assertions, &mut tm, 1_000_000)
        .unwrap();
    let clauses: Vec<Vec<i32>> = cnf
        .lines()
        .skip(1)
        .map(|line| {
            let mut lits: Vec<i32> = line
                .split_whitespace()
                .map(|s| s.parse().unwrap())
                .collect();
            assert_eq!(lits.pop(), Some(0));
            lits
        })
        .collect();
    assert!(nixie_proof::lrat_check::check_lrat_proof(&clauses, &proof.lrat).verified);

    let mut bad = proof.clone();
    bad.lemmas.clear();
    assert!(
        bad.check(&originals, &graphs, &assertions, &mut tm, 1_000_000)
            .is_err()
    );
    let mut bad = proof.clone();
    bad.lemmas[0].declaration = usize::MAX;
    assert!(
        bad.check(&originals, &graphs, &assertions, &mut tm, 1_000_000)
            .is_err()
    );
    let mut bad = proof.clone();
    bad.lrat.clear();
    assert!(
        bad.check(&originals, &graphs, &assertions, &mut tm, 1_000_000)
            .is_err()
    );
    let mut bad = proof.clone();
    bad.lrat = "999999 0 0\n".into();
    assert!(
        bad.check(&originals, &graphs, &assertions, &mut tm, 1_000_000)
            .is_err()
    );
    let mut bad = proof.clone();
    bad.theory_lemmas.push(vec![(tm.mk_true(), false)]);
    assert!(
        bad.check(&originals, &graphs, &assertions, &mut tm, 1_000_000)
            .is_err()
    );
    assert!(
        proof
            .check(&originals, &graphs, &assertions, &mut tm, 0)
            .is_err()
    );
    assert!(
        proof
            .check(&[], &graphs, &assertions, &mut tm, 1_000_000)
            .is_err()
    );
    let replacement = CpModel::new(&tm).statement();
    assert!(
        proof
            .check(&[replacement], &graphs, &assertions, &mut tm, 1_000_000)
            .is_err()
    );
    for input in [
        "",
        "nixie-cp-proof 2\n",
        "nixie-cp-proof 1\ncp -1 0\nlrat\n",
        "nixie-cp-proof 1\nsmt 0 2\nlrat\n",
        "nixie-cp-proof 1\ncnf 0\nlrat\n",
    ] {
        assert!(CpProof::from_text(input).is_err());
    }
}

#[test]
fn no_unjustified_leaf_can_enter_lrat() {
    let mut tm = TermManager::new();
    let mut cp = CpModel::new(&tm);
    let (_, atoms) = variable(&mut cp, &mut tm, "x");
    let original = cp.statement();
    let graphs: [nixie_theories::graph::GraphStatement; 0] = [];
    for conclusion in [tm.mk_false(), atoms[0], tm.mk_not(atoms[1])] {
        let proof = CpProof {
            graph_lemmas: vec![],
            lemmas: vec![CpLemma {
                declaration: 0,
                conclusion,
                premises: vec![],
            }],
            theory_lemmas: vec![],
            lrat: "1 0 0\n".into(),
        };
        assert!(
            proof
                .check(
                    std::slice::from_ref(&original),
                    &graphs,
                    &[],
                    &mut tm,
                    1_000_000
                )
                .is_err()
        );
    }
    // Unused foreign premises can weaken a valid implication, but cannot
    // make an invalid implication provable. Neither can a foreign conclusion.
    let foreign = tm.mk_var("foreign", tm.sorts.bool_sort);
    assert!(
        original
            .check_lemma(tm.mk_false(), &[foreign], &mut 1_000_000)
            .is_err()
    );
    assert!(
        original
            .check_lemma(foreign, &[atoms[0]], &mut 1_000_000)
            .is_err()
    );
    original
        .check_lemma(tm.mk_not(atoms[1]), &[atoms[0], foreign], &mut 1_000_000)
        .unwrap();
}

#[test]
fn proofs_follow_scopes_settings_reset_and_cached_checks() {
    let mut tm = TermManager::new();
    let mut cp = CpModel::new(&tm);
    let (_, atoms) = variable(&mut cp, &mut tm, "x");
    let mut solver = Solver::with_config(SolverConfig::default().certified());
    solver.register_cp(cp, &mut tm).unwrap();
    assert_eq!(solver.check(&mut tm), SolverResult::Sat);
    solver.push();
    solver.assert(atoms[0], &mut tm);
    solver.assert(atoms[1], &mut tm);
    let inputs = solver.cp_proof_inputs();
    assert_eq!(solver.check(&mut tm), SolverResult::Unsat);
    let proof = solver.get_cp_proof().unwrap().clone();
    assert_eq!(solver.check(&mut tm), SolverResult::Unsat);
    assert_eq!(solver.get_cp_proof(), Some(&proof));
    solver.pop();
    assert!(solver.get_cp_proof().is_none());
    assert_eq!(solver.check(&mut tm), SolverResult::Sat);
    proof
        .check(&inputs.0, &inputs.1, &inputs.2, &mut tm, 1_000_000)
        .unwrap();
    let current = solver.cp_proof_inputs();
    assert!(
        proof
            .check(&current.0, &current.1, &current.2, &mut tm, 1_000_000)
            .is_err()
    );
    assert_eq!(
        solver.check_with_assumptions(&atoms, &mut tm),
        SolverResult::Unsat
    );
    assert!(solver.get_cp_proof().is_none()); // pop discards assumption-scoped proof
    assert_eq!(solver.check(&mut tm), SolverResult::Sat);
    solver.reset();
    assert!(solver.cp_proof_inputs().0.is_empty());
    assert!(solver.get_cp_proof().is_none());
    let mut solver = hall(&mut tm);
    assert_eq!(solver.check(&mut tm), SolverResult::Unsat);
    solver.set_config(SolverConfig::default().certified());
    assert!(solver.get_cp_proof().is_none());
    assert_eq!(solver.check(&mut tm), SolverResult::Unsat);
    assert!(solver.get_cp_proof().is_some());
}

struct TrustedConflict;
impl UserPropagator for TrustedConflict {
    fn final_check(&mut self, _: &mut PropagatorContext) -> PropagatorResult {
        PropagatorResult::Unsat(vec![])
    }
}

#[test]
fn registering_cp_does_not_authorize_arbitrary_callbacks() {
    for cp_first in [false, true] {
        let mut tm = TermManager::new();
        let mut solver = Solver::with_config(SolverConfig::default().certified());
        if cp_first {
            solver.register_cp(CpModel::new(&tm), &mut tm).unwrap();
        }
        solver
            .register_user_propagator(Box::new(TrustedConflict), &[], &mut tm)
            .unwrap();
        if !cp_first {
            solver.register_cp(CpModel::new(&tm), &mut tm).unwrap();
        }
        assert_eq!(solver.check(&mut tm), SolverResult::Unknown);
        assert!(solver.get_cp_proof().is_none());
        assert!(solver.get_proof().is_none());
        assert!(solver.model().is_none());
    }
}

#[test]
fn enabling_proofs_after_an_unrecorded_search_reconstructs_the_chain() {
    let mut tm = TermManager::new();
    let mut solver = hall(&mut tm);
    solver.set_config(SolverConfig::default());
    assert_eq!(solver.check(&mut tm), SolverResult::Unsat);
    assert!(solver.get_cp_proof().is_none());
    solver.set_config(SolverConfig::default().certified());
    assert_eq!(solver.check(&mut tm), SolverResult::Unsat);
    let inputs = solver.cp_proof_inputs();
    solver
        .get_cp_proof()
        .unwrap()
        .check(&inputs.0, &inputs.1, &inputs.2, &mut tm, 1_000_000)
        .unwrap();
}

#[test]
fn multiple_declarations_with_shared_indicators_keep_their_own_meanings() {
    let mut tm = TermManager::new();
    let mut first = CpModel::new(&tm);
    let (x, [a, b]) = variable(&mut first, &mut tm, "shared");
    first.table(vec![x], vec![vec![0.into()]]).unwrap();
    let mut second = CpModel::new(&tm);
    let y = second
        .variable(vec![(1.into(), a), (0.into(), b)], &mut tm)
        .unwrap();
    second.table(vec![y], vec![vec![0.into()]]).unwrap();
    let mut solver = Solver::with_config(SolverConfig::default().certified());
    solver.register_cp(first, &mut tm).unwrap();
    solver.register_cp(second, &mut tm).unwrap();
    let (originals, graphs, assertions) = solver.cp_proof_inputs();
    let _ = &graphs;
    assert_eq!(
        solver.check(&mut tm),
        SolverResult::Unsat,
        "{:?}",
        solver.certification_failure()
    );
    let proof = solver.get_cp_proof().unwrap();
    proof
        .check(&originals, &graphs, &assertions, &mut tm, 1_000_000)
        .unwrap();
    assert!(
        proof
            .check(
                &[originals[0].clone(), originals[0].clone()],
                &graphs,
                &assertions,
                &mut tm,
                1_000_000
            )
            .is_err()
    );
    assert!(
        proof
            .check(
                &[originals[1].clone(), originals[1].clone()],
                &graphs,
                &assertions,
                &mut tm,
                1_000_000
            )
            .is_err()
    );
}
