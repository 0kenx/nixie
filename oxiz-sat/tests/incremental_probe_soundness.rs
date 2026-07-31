//! Regression tests for the incremental *probe* pattern's soundness.
//!
//! `BvSolver::check` and the floating-point solver drive this SAT engine
//! incrementally: snapshot the committed prefix, `solve`, roll the trail back
//! with [`Solver::restore_to_trail_size`], drop the probe's lemmas with
//! [`Solver::forget_learned_since`], assert more clauses, `solve` again.  Every
//! probe therefore runs against a solver that has already searched.
//!
//! The invariant that makes this safe is the trail's propagation-queue
//! contract: every literal *strictly before* the propagation head has had all of
//! its consequences computed.  `propagate()` breaks that contract whenever it
//! aborts — the conflict is found part way through a literal's watch list, so
//! that literal's remaining watchers are never examined even though the head has
//! moved past it.
//!
//! Ordinary CDCL repairs this implicitly, because conflict analysis is always
//! followed by a backtrack that clamps the head below the half-processed
//! literal.  A conflict at decision level 0 has no such backtrack: `solve()`
//! returns `Unsat` on the spot.  The head was then left past a literal whose
//! conflicting clause was never re-examined, so the *next* `solve()` resumed
//! propagation after it, never revisited the clause, and reported **`Sat` on a
//! formula refuted by unit propagation alone** — handing the caller a model that
//! does not satisfy the clause database.
//!
//! `(3)`, `(¬3 ∨ 4)`, `(¬4)` is the shrunk witness: two level-0 units sit on the
//! trail, and each `solve()` consumed exactly one of them before hitting the
//! conflict, so the third `solve()` found an empty propagation queue and
//! branched its way to a bogus model.

use oxiz_sat::{LBool, Lit, Solver, SolverConfig, SolverResult, Var};

/// A minimal engine: no side heuristic may add clauses, so a verdict change is
/// attributable to the incremental machinery rather than to preprocessing.
fn probe_config() -> SolverConfig {
    SolverConfig {
        enable_chronological_backtrack: true,
        chrono_backtrack_threshold: 0,
        enable_lazy_hyper_binary: false,
        enable_inprocessing: false,
        random_polarity_prob: 0.0,
        restart_interval: 20,
        ..SolverConfig::default()
    }
}

/// The shrunk witness: unsatisfiable by unit propagation alone.
const UNIT_PROP_UNSAT: [&[i32]; 3] = [&[-3, 4], &[3], &[-4]];

fn new_solver(num_vars: usize, config: SolverConfig) -> Solver {
    let mut solver = Solver::with_config(config);
    for _ in 0..num_vars {
        solver.new_var();
    }
    solver
}

/// Does the solver's saved model satisfy every clause of `cnf`?
fn model_satisfies(solver: &Solver, cnf: &[Vec<i32>]) -> Option<Vec<i32>> {
    cnf.iter()
        .find(|clause| {
            !clause.iter().any(|&lit| {
                let value = solver.model_value(Var::new(lit.unsigned_abs() - 1));
                if lit > 0 {
                    value.is_true()
                } else {
                    value.is_false()
                }
            })
        })
        .cloned()
}

/// Exhaustive oracle over all `2^num_vars` assignments.
fn brute_force_is_sat(num_vars: usize, cnf: &[Vec<i32>]) -> bool {
    assert!(num_vars <= 20, "brute-force oracle is exponential");
    (0u32..(1u32 << num_vars)).any(|mask| {
        cnf.iter().all(|clause| {
            clause.iter().any(|&lit| {
                let var_bit = (mask >> (lit.unsigned_abs() as usize - 1)) & 1 == 1;
                (lit > 0) == var_bit
            })
        })
    })
}

/// An instance refuted by unit propagation alone must stay `Unsat` across every
/// probe of the incremental sequence, however many times it is re-solved.
#[test]
fn test_incremental_probe_unit_propagation_unsat() {
    // The probe pattern, exactly as `BvSolver::check` drives it.
    let mut solver = new_solver(6, probe_config());
    for clause in UNIT_PROP_UNSAT {
        solver.add_clause_dimacs(clause);
    }

    for probe in 0..6 {
        let trail_mark = solver.trail_size();
        let learned_mark = solver.learned_clause_count();
        assert_eq!(
            solver.solve(),
            SolverResult::Unsat,
            "probe {probe}: (3) & (¬3 ∨ 4) & (¬4) is refuted by unit propagation; \
             a later probe must not resume propagation past the conflicting clause"
        );
        solver.restore_to_trail_size(trail_mark);
        solver.forget_learned_since(learned_mark);
    }

    // The same defect needs no incremental call at all: a bare `solve()` loop is
    // enough, because nothing rewinds the propagation head when `solve()`
    // returns `Unsat` from a level-0 conflict.
    let mut solver = new_solver(6, probe_config());
    for clause in UNIT_PROP_UNSAT {
        solver.add_clause_dimacs(clause);
    }
    for repeat in 0..6 {
        assert_eq!(
            solver.solve(),
            SolverResult::Unsat,
            "repeat {repeat}: repeated solve() on the same solver must be stable"
        );
    }

    // Smallest witness of the same shape, and with chronological backtracking
    // off — the fix must not depend on that heuristic.
    let mut plain = probe_config();
    plain.enable_chronological_backtrack = false;
    for config in [probe_config(), plain] {
        let mut solver = new_solver(2, config);
        solver.add_clause_dimacs(&[1]);
        solver.add_clause_dimacs(&[-1, 2]);
        solver.add_clause_dimacs(&[-2]);
        for repeat in 0..4 {
            assert_eq!(
                solver.solve(),
                SolverResult::Unsat,
                "(1) & (¬1 ∨ 2) & (¬2), repeat {repeat}"
            );
        }
    }
}

/// Whenever a probe reports `Sat`, the model it saved must satisfy every clause
/// asserted so far.  A `Sat` verdict backed by a model that violates a clause is
/// strictly worse than a false `Unsat`: the caller trusts it.
#[test]
fn test_incremental_probe_model_is_valid() {
    let mut solver = new_solver(6, probe_config());
    let mut asserted: Vec<Vec<i32>> = Vec::new();

    // Batches chosen so the accumulated formula stays satisfiable while forcing
    // level-0 units, conflicts and backjumps along the way.
    let batches: [&[&[i32]]; 5] = [
        &[&[1, 2], &[-1, 3]],
        &[&[3], &[-3, 4, 5]],
        &[&[-4, 5], &[-5, 6], &[1, -2]],
        &[&[6], &[-6, 1, 4]],
        &[&[2, 4], &[-2, -4, 5]],
    ];

    for (probe, batch) in batches.iter().enumerate() {
        for clause in *batch {
            solver.add_clause_dimacs(clause);
            asserted.push(clause.to_vec());
        }

        let trail_mark = solver.trail_size();
        let learned_mark = solver.learned_clause_count();
        let result = solver.solve();

        assert_eq!(
            result,
            SolverResult::Sat,
            "probe {probe}: accumulated formula is satisfiable"
        );
        assert!(
            brute_force_is_sat(6, &asserted),
            "probe {probe}: the oracle must agree the formula is satisfiable"
        );
        if let Some(violated) = model_satisfies(&solver, &asserted) {
            panic!("probe {probe}: reported Sat but the model falsifies {violated:?}");
        }
        // A `Sat` model must be total over the declared variables.
        for var_index in 0..6u32 {
            assert_ne!(
                solver.model_value(Var::new(var_index)),
                LBool::Undef,
                "probe {probe}: variable {var_index} is unassigned in a Sat model"
            );
        }

        solver.restore_to_trail_size(trail_mark);
        solver.forget_learned_since(learned_mark);
    }
}

/// Bounded randomised differential test: small CNFs driven through the exact
/// `solve` / `restore_to_trail_size` / `forget_learned_since` / `add_clause`
/// sequence the bit-vector and floating-point solvers use, checked against an
/// exhaustive oracle after every probe.
///
/// Deterministic (fixed seed, no wall-clock dependence) and sized to stay well
/// inside a normal CI budget.  Any non-zero mismatch count is a soundness bug.
#[test]
fn test_incremental_probe_matches_reference() {
    // xorshift64* — deterministic and dependency-free.
    let mut state: u64 = 0x2026_0728_5A7F_1200;
    let mut next = move || {
        state ^= state >> 12;
        state ^= state << 25;
        state ^= state >> 27;
        state = state.wrapping_mul(0x2545_F491_4F6C_DD1D);
        state
    };

    let mut mismatches: Vec<String> = Vec::new();
    let mut probes_run = 0usize;
    let mut unsat_seen = 0usize;

    for instance in 0..400 {
        let num_vars = 4 + (next() % 7) as usize; // 4..=10
        let num_probes = 3 + (next() % 4) as usize; // 3..=6

        let mut solver = new_solver(num_vars, probe_config());
        let mut asserted: Vec<Vec<i32>> = Vec::new();

        for probe in 0..num_probes {
            let batch = 1 + (next() % 4) as usize; // 1..=4 clauses per probe
            for _ in 0..batch {
                let len = 1 + (next() % 3) as usize; // 1..=3 literals
                let mut clause: Vec<i32> = Vec::with_capacity(len);
                for _ in 0..len {
                    let var = 1 + (next() % num_vars as u64) as i32;
                    let lit = if next() % 2 == 0 { var } else { -var };
                    if !clause.contains(&lit) && !clause.contains(&(-lit)) {
                        clause.push(lit);
                    }
                }
                if !clause.is_empty() {
                    solver.add_clause_dimacs(&clause);
                    asserted.push(clause);
                }
            }

            let trail_mark = solver.trail_size();
            let learned_mark = solver.learned_clause_count();
            let got = solver.solve();
            probes_run += 1;

            let expected = if brute_force_is_sat(num_vars, &asserted) {
                SolverResult::Sat
            } else {
                unsat_seen += 1;
                SolverResult::Unsat
            };

            if got != expected {
                mismatches.push(format!(
                    "instance {instance} probe {probe}: got {got:?} want {expected:?} \
                     on {asserted:?}"
                ));
            } else if got == SolverResult::Sat
                && let Some(violated) = model_satisfies(&solver, &asserted)
            {
                mismatches.push(format!(
                    "instance {instance} probe {probe}: Sat model falsifies {violated:?} \
                     in {asserted:?}"
                ));
            }

            solver.restore_to_trail_size(trail_mark);
            solver.forget_learned_since(learned_mark);
        }
    }

    assert!(
        mismatches.is_empty(),
        "{} mismatch(es) in {probes_run} probes:\n{}",
        mismatches.len(),
        mismatches.join("\n")
    );

    // Guard against the generator drifting into instances that never reach the
    // level-0-conflict path this test exists to cover.
    assert!(
        unsat_seen > 100,
        "expected the random instances to hit refutations often; only {unsat_seen} \
         of {probes_run} probes were Unsat"
    );
}

/// A `Sat` verdict must always rest on a **total** assignment.
///
/// This guards a second, independent defect on the same reuse path.
/// `pick_branch_var` consumes its candidates destructively (`pop_max` /
/// `select`), and the no-phase-saving `backtrack` — which every
/// `solve_with_assumptions` probe unwinds through, as do the vivification and
/// distillation probes — used not to hand the freed variables back to the
/// decision heaps.  Successive probes therefore drained the heaps a little
/// further each time; once they ran dry the search had nothing left to branch
/// on, read the empty heap as "all variables assigned", and saved a model with
/// `Undef` entries that falsified clauses it had never looked at.
#[test]
fn test_repeated_assumption_probes_keep_total_models() {
    let cnf: Vec<Vec<i32>> = vec![vec![1, 2], vec![3, 4]];
    let mut solver = new_solver(4, probe_config());
    for clause in &cnf {
        solver.add_clause_dimacs(clause);
    }

    assert_eq!(solver.solve(), SolverResult::Sat);

    // Two independent free choices, so every single-literal assumption is
    // satisfiable and each probe must produce a complete, satisfying model.
    for lit in [1i32, -1, 2, -2, 3, -3, 4, -4] {
        let (result, _core) = solver.solve_with_assumptions(&[Lit::from_dimacs(lit)]);
        assert_eq!(
            result,
            SolverResult::Sat,
            "assumption {lit} is satisfiable on (1 ∨ 2) ∧ (3 ∨ 4)"
        );

        for var_index in 0..4u32 {
            assert_ne!(
                solver.model_value(Var::new(var_index)),
                LBool::Undef,
                "assumption {lit}: variable {var_index} left unassigned in a Sat model"
            );
        }
        if let Some(violated) = model_satisfies(&solver, &cnf) {
            panic!("assumption {lit}: reported Sat but the model falsifies {violated:?}");
        }

        let value = solver.model_value(Var::new(lit.unsigned_abs() - 1));
        assert!(
            if lit > 0 {
                value.is_true()
            } else {
                value.is_false()
            },
            "assumption {lit} must itself hold in the model it justifies"
        );
    }
}
