//! Regression tests for the "sat-final" fix wave.
//!
//! Covers two guarantees that live behind the public [`Solver`] API:
//!  1. `solve_with_assumptions` returns a *complete* unsat core – every
//!     assumption that contributes to the conflict, not just the directly
//!     falsified one.
//!  2. DRAT proof logging emits a well-formed, empty-clause-terminated trace for
//!     an unconditional UNSAT solve.

use nixie_sat::{Lit, Solver, SolverConfig, SolverResult};

#[test]
fn assumption_core_contains_all_contributors() {
    // Completeness: the core of (a ∧ b ∧ (¬a ∨ ¬b)) under assumptions [a, b] must
    // contain BOTH a and b. Asserting a propagates ¬b via (¬a ∨ ¬b), so b is
    // directly falsified; a correct analyzeFinal traversal resolves that
    // propagation back to the a assumption rather than blaming only b.
    let mut solver = Solver::new();
    let a = solver.new_var();
    let b = solver.new_var();

    solver.add_clause([Lit::neg(a), Lit::neg(b)]);

    let assumptions = [Lit::pos(a), Lit::pos(b)];
    let (result, core) = solver.solve_with_assumptions(&assumptions);
    assert_eq!(result, SolverResult::Unsat);
    let core = core.expect("UNSAT under assumptions must return a core");
    assert!(
        core.contains(&Lit::pos(a)),
        "core must contain assumption a, got {core:?}"
    );
    assert!(
        core.contains(&Lit::pos(b)),
        "core must contain assumption b, got {core:?}"
    );
}

#[test]
fn assumption_core_complete_through_implication_chain() {
    // A longer implication chain: assume a and c, with (¬a ∨ b) and (¬b ∨ ¬c).
    // Asserting a ⇒ b ⇒ ¬c, so c is falsified through a two-step propagation. The
    // core must still recover a (the ultimate cause) and c.
    let mut solver = Solver::new();
    let a = solver.new_var();
    let b = solver.new_var();
    let c = solver.new_var();

    solver.add_clause([Lit::neg(a), Lit::pos(b)]); // a → b
    solver.add_clause([Lit::neg(b), Lit::neg(c)]); // b → ¬c

    let assumptions = [Lit::pos(a), Lit::pos(c)];
    let (result, core) = solver.solve_with_assumptions(&assumptions);
    assert_eq!(result, SolverResult::Unsat);
    let core = core.expect("UNSAT under assumptions must return a core");
    assert!(
        core.contains(&Lit::pos(a)),
        "core must contain root cause a, got {core:?}"
    );
    assert!(
        core.contains(&Lit::pos(c)),
        "core must contain c, got {core:?}"
    );
}

#[test]
fn drat_proof_emits_wellformed_unsat_trace() {
    use std::io::Read as _;

    // PHP(3,2) is UNSAT and forces conflicts / learned clauses, so the DRAT trace
    // exercises additions, deletions, and the terminating empty clause.
    let path = std::env::temp_dir().join("nixie_sat_drat_php32.drat");
    let mut solver = Solver::with_config(SolverConfig {
        clause_deletion_threshold: 5,
        ..SolverConfig::default()
    });
    for _ in 0..6 {
        solver.new_var();
    }
    solver
        .enable_drat_proof(&path)
        .expect("enable DRAT proof logging");
    assert!(solver.drat_proof_enabled());

    solver.add_clause_dimacs(&[1, 2]);
    solver.add_clause_dimacs(&[3, 4]);
    solver.add_clause_dimacs(&[5, 6]);
    solver.add_clause_dimacs(&[-1, -3]);
    solver.add_clause_dimacs(&[-1, -5]);
    solver.add_clause_dimacs(&[-3, -5]);
    solver.add_clause_dimacs(&[-2, -4]);
    solver.add_clause_dimacs(&[-2, -6]);
    solver.add_clause_dimacs(&[-4, -6]);

    assert_eq!(solver.solve(), SolverResult::Unsat);
    solver.disable_drat_proof();

    let mut contents = String::new();
    std::fs::File::open(&path)
        .expect("proof file must exist")
        .read_to_string(&mut contents)
        .expect("read proof file");
    std::fs::remove_file(&path).ok();

    assert!(!contents.trim().is_empty(), "DRAT proof must not be empty");

    let mut saw_empty_clause = false;
    for line in contents.lines() {
        let line = line.trim();
        if line.is_empty() {
            continue;
        }
        // Every DRAT line (addition or `d`-prefixed deletion) is terminated by a
        // `0` sentinel.
        assert!(
            line.ends_with('0'),
            "malformed DRAT line (missing 0 terminator): {line:?}"
        );
        if line == "0" {
            saw_empty_clause = true;
        }
    }
    assert!(
        saw_empty_clause,
        "a complete UNSAT DRAT proof must end by deriving the empty clause"
    );
}
