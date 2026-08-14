//! Regression tests for `Solver::set_random_seed` – the wiring that makes the
//! SMT-LIB `:random-seed` option enforceable rather than a silent no-op.
//!
//! The seed feeds the CDCL engine's phase-randomization PRNG (sampled with
//! probability `random_polarity_prob`).  These tests pin the two guarantees the
//! higher layers rely on:
//!   1. Seeding never changes a decidable verdict (soundness is seed-independent).
//!   2. The same seed is deterministic; the degenerate seed `0` is safe (it must
//!      not freeze the xorshift PRNG at its fixed point).

use oxiz_sat::{Solver, SolverResult};

/// Build a satisfiable 3-SAT instance over `n` variables (DIMACS 1-based).
fn add_sat_instance(solver: &mut Solver) {
    for _ in 0..6 {
        solver.new_var();
    }
    // A deliberately non-trivial but satisfiable clause set (x1..x6).
    solver.add_clause_dimacs(&[1, 2, 3]);
    solver.add_clause_dimacs(&[-1, 4, 5]);
    solver.add_clause_dimacs(&[-2, -4, 6]);
    solver.add_clause_dimacs(&[-3, -5, -6]);
    solver.add_clause_dimacs(&[1, -4, 6]);
    solver.add_clause_dimacs(&[-1, 2, -5]);
}

#[test]
fn seeding_preserves_sat_verdict() {
    // Every seed – including the degenerate 0 and widely separated values – must
    // yield the same SAT verdict for a satisfiable instance.
    for seed in [0u64, 1, 42, 12345, u64::MAX] {
        let mut solver = Solver::new();
        solver.set_random_seed(seed);
        add_sat_instance(&mut solver);
        assert_eq!(
            solver.solve(),
            SolverResult::Sat,
            "instance must stay SAT under seed {seed}"
        );
    }
}

#[test]
fn seeding_preserves_unsat_verdict() {
    // PHP(3,2): 3 pigeons into 2 holes – UNSAT regardless of seed.
    for seed in [0u64, 7, 99991] {
        let mut solver = Solver::new();
        solver.set_random_seed(seed);
        for _ in 0..6 {
            solver.new_var();
        }
        // pigeon i in some hole
        solver.add_clause_dimacs(&[1, 2]);
        solver.add_clause_dimacs(&[3, 4]);
        solver.add_clause_dimacs(&[5, 6]);
        // no two pigeons share a hole
        solver.add_clause_dimacs(&[-1, -3]);
        solver.add_clause_dimacs(&[-1, -5]);
        solver.add_clause_dimacs(&[-3, -5]);
        solver.add_clause_dimacs(&[-2, -4]);
        solver.add_clause_dimacs(&[-2, -6]);
        solver.add_clause_dimacs(&[-4, -6]);
        assert_eq!(
            solver.solve(),
            SolverResult::Unsat,
            "PHP(3,2) must stay UNSAT under seed {seed}"
        );
    }
}

#[test]
fn same_seed_is_deterministic() {
    // Two independently-constructed solvers with the same seed must agree, both
    // on verdict and on the reported statistics of the run.
    let run = |seed: u64| {
        let mut solver = Solver::new();
        solver.set_random_seed(seed);
        add_sat_instance(&mut solver);
        let result = solver.solve();
        let decisions = solver.stats().decisions;
        (result, decisions)
    };
    assert_eq!(run(2026), run(2026));
}
