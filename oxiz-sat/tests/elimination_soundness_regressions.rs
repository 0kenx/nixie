//! Soundness regressions for the inprocessing bounded-variable-elimination
//! port (`solver/eliminate.rs`), each locking in a bug the differential fuzz
//! / CaDiCaL sweep caught. Ground-truth verdicts are CaDiCaL's (verified
//! against the inputs).

use oxiz_sat::{DimacsParser, Lit, Solver, SolverConfig, SolverResult};

/// `crn_11_99_u.cnf` (satcomp2024) is UNSAT (CaDiCaL) and reproduced two
/// distinct false-SAT bugs in the eliminator:
///
/// 1. Learned clauses over eliminated variables left live: v57 was
///    eliminated while a live learned `(57 ∨ 1101)` still mentioned it; the
///    reconstructed model falsified that entailed clause (and therefore an
///    original clause). Fixed by retiring learned clauses with eliminated
///    variables at the end of each round (cadical
///    `mark_redundant_clauses_with_eliminated_variables_as_garbage`).
/// 2. Original clauses subsumed by learned clauses without promotion: the
///    learned binary subsumer of `(37 ∨ 57 ∨ 1101)` was later removed,
///    losing the deleted original's obligation. Fixed with cadical's
///    `subsume_clause` promotion rule (learned subsumer of an original
///    becomes permanent).
#[test]
fn elimination_crn_11_99_u_is_unsat() {
    let solver_cfg = SolverConfig {
        enable_bve: true,
        ..SolverConfig::default()
    };
    let mut solver = Solver::with_config(solver_cfg);
    let mut parser = DimacsParser::new();
    let path = concat!(
        env!("CARGO_MANIFEST_DIR"),
        "/tests/fixtures/crn_11_99_u.cnf"
    );
    parser.parse_file(path, &mut solver).expect("parse crn");
    assert_eq!(solver.solve(), SolverResult::Unsat);
}

/// The ELS fallback-decision bug (pre-existing, exposed by the elimination
/// work): after equivalent-literal substitution folds `b` into `a` (from
/// `a≡b`), `pick_branch_var`'s heap-exhaustion fallback could *decide* the
/// eliminated variable `b` with a saved phase. That bogus trail value then
/// blocked model reconstruction, so the model handed back after
/// `add_clause(b ∨ c)` falsified that reintroduced clause.
#[test]
fn eliminated_variable_is_never_a_fallback_decision() {
    let solver_cfg = SolverConfig {
        enable_equiv_substitution: true,
        // Lucky pre-solving answers this instance outright before the ELS
        // fold runs (it is scheduled first, matching cadical `luckyearly`);
        // disable it so the substitution path is actually exercised.
        enable_lucky: false,
        ..SolverConfig::default()
    };
    let mut solver = Solver::with_config(solver_cfg);
    let a = solver.new_var();
    let b = solver.new_var();
    solver.add_clause([Lit::neg(a), Lit::pos(b)]);
    solver.add_clause([Lit::neg(b), Lit::pos(a)]);
    assert_eq!(solver.solve(), SolverResult::Sat);
    assert!(
        solver.var_eliminated(a) || solver.var_eliminated(b),
        "ELS must fold one of the equivalent variables"
    );

    let c = solver.new_var();
    assert!(solver.add_clause([Lit::pos(b), Lit::pos(c)]));
    assert_eq!(solver.solve(), SolverResult::Sat);
    let b_ok = solver.model_value(b) == oxiz_sat::LBool::True;
    let c_ok = solver.model_value(c) == oxiz_sat::LBool::True;
    assert!(
        b_ok || c_ok,
        "model must satisfy the reintroduced (b ∨ c): b={:?} c={:?}",
        solver.model_value(b),
        solver.model_value(c)
    );
}

/// The pre-search elimination fixpoint loop spun forever when elimination is
/// refused (LRAT proof attached): `eliminate_phase` returned without
/// advancing the phase counter while the loop gate stayed true. Pigeonhole
/// (6,5) under LRAT + `enable_bve` is the reproducer (it must terminate and
/// answer UNSAT with a verifiable proof).
#[test]
fn elimination_refused_under_lrat_terminates() {
    let solver_cfg = SolverConfig {
        enable_bve: true,
        ..SolverConfig::default()
    };
    let mut solver = Solver::with_config(solver_cfg);
    solver
        .enable_lrat_proof("/tmp/oxiz_sat_elim_lrat_regression.lrat")
        .expect("enable LRAT before clauses");
    // Pigeonhole(6,5): UNSAT.
    let pigeons = 6usize;
    let holes = 5usize;
    for _ in 0..pigeons * holes {
        solver.new_var();
    }
    let var = |p: usize, h: usize| (p * holes + h + 1) as i32;
    for p in 0..pigeons {
        let clause: Vec<i32> = (0..holes).map(|h| var(p, h)).collect();
        solver.add_clause_dimacs(&clause);
    }
    for h in 0..holes {
        for p1 in 0..pigeons {
            for p2 in (p1 + 1)..pigeons {
                solver.add_clause_dimacs(&[-var(p1, h), -var(p2, h)]);
            }
        }
    }
    let result = solver.solve();
    solver.disable_lrat_proof();
    let _ = std::fs::remove_file("/tmp/oxiz_sat_elim_lrat_regression.lrat");
    assert_eq!(result, SolverResult::Unsat);
}
