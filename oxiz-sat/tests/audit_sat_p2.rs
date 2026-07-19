//! Regression tests for the `sat-p2` audit findings.
//!
//! Each test targets one confirmed soundness defect:
//!   1. `add_clause` watch selection (mod.rs)
//!   2. Inprocessing clause strengthening direction (learn.rs)
//!   3. Pure-literal-elimination model reconstruction (preprocessing_core.rs + learn.rs)
//!   4. Binary-implication-graph liveness after pop() (propagate.rs + mod.rs)
//!   5. Verified symmetry generators only (symmetry.rs)

use oxiz_sat::{
    AutomorphismDetector, ClauseDatabase, LBool, Lit, Preprocessor, Solver, SolverConfig,
    SolverResult, Var,
};

fn v(i: u32) -> Var {
    Var::new(i)
}

/// Check that `model` satisfies every clause in `clauses` (each clause a list of
/// (var, polarity) literals). Returns the first violated clause index, if any.
fn first_violated(solver: &Solver, clauses: &[Vec<Lit>]) -> Option<usize> {
    for (idx, clause) in clauses.iter().enumerate() {
        let satisfied = clause.iter().any(|lit| {
            let val = solver.model_value(lit.var());
            match val {
                LBool::True => lit.is_pos(),
                LBool::False => !lit.is_pos(),
                LBool::Undef => false,
            }
        });
        if !satisfied {
            return Some(idx);
        }
    }
    None
}

/// Finding 1: after a completed solve() leaves a full trail, a clause added with
/// an unassigned literal must be watched on that literal, not on already-false
/// literals. Otherwise the next solve() returns Sat on a model violating it.
#[test]
fn add_clause_after_solve_watches_non_false_literal() {
    let mut solver = Solver::new();

    // Force x0 = false, x1 = false at level 0.
    assert!(solver.add_clause([Lit::neg(v(0))]));
    assert!(solver.add_clause([Lit::neg(v(1))]));
    assert_eq!(solver.solve(), SolverResult::Sat);

    // Now add (x0 v x1 v x2): the two lowest-code literals (x0, x1) are already
    // false; x2 is a brand-new, unassigned variable. The clause is effectively
    // unit (x2 must be true). The old code watched x0/x1 and silently dropped it.
    assert!(solver.add_clause([Lit::pos(v(0)), Lit::pos(v(1)), Lit::pos(v(2))]));

    assert_eq!(solver.solve(), SolverResult::Sat);
    // x0 and x1 are pinned false, so the clause forces x2 = true.
    assert_eq!(
        solver.model_value(v(2)),
        LBool::True,
        "model must satisfy the newly added clause"
    );
}

/// Finding 1 (conflict variant): the same mis-watched clause must not let an
/// actually-UNSAT formula be reported Sat.
#[test]
fn add_clause_after_solve_detects_conflict() {
    let mut solver = Solver::new();

    assert!(solver.add_clause([Lit::neg(v(0))]));
    assert!(solver.add_clause([Lit::neg(v(1))]));
    assert_eq!(solver.solve(), SolverResult::Sat);

    // (x0 v x1 v x2) forces x2 = true, but then ¬x2 makes it UNSAT.
    assert!(solver.add_clause([Lit::pos(v(0)), Lit::pos(v(1)), Lit::pos(v(2))]));
    assert!(solver.add_clause([Lit::neg(v(2))]));

    assert_eq!(
        solver.solve(),
        SolverResult::Unsat,
        "conflict on the added clause must be detected"
    );
}

/// Finding 4: pop() must retract binary implications. After a binary clause is
/// removed by pop(), its stale implication-graph edge must not force a false
/// UNSAT on the next solve().
#[test]
fn pop_retracts_binary_implications() {
    let mut solver = Solver::new();

    solver.push();
    // Binary clause (¬x0 v ¬x1) installs edges x0 -> ¬x1 and x1 -> ¬x0.
    assert!(solver.add_clause([Lit::neg(v(0)), Lit::neg(v(1))]));
    let _ = solver.solve();
    solver.pop();

    // The binary clause is gone; x0 = x1 = true is now perfectly consistent.
    assert!(solver.add_clause([Lit::pos(v(0))]));
    assert!(solver.add_clause([Lit::pos(v(1))]));

    assert_eq!(
        solver.solve(),
        SolverResult::Sat,
        "retracted binary clause must not force a false UNSAT"
    );
    assert_eq!(solver.model_value(v(0)), LBool::True);
    assert_eq!(solver.model_value(v(1)), LBool::True);
}

/// Finding 3 (unit level): pure_literal_elimination must record eliminated pure
/// literals so the caller can reconstruct a correct model.
#[test]
fn pure_literal_elimination_records_pure_literal() {
    let mut db = ClauseDatabase::new();
    // p (=v2) appears only positively -> pure. It shares clause (p v y) with y.
    db.add_original([Lit::pos(v(2)), Lit::pos(v(1))]);
    // y (=v1) also appears negatively so it is not pure.
    db.add_original([Lit::neg(v(1)), Lit::pos(v(0))]);

    let mut prep = Preprocessor::new(3);
    let eliminated = prep.pure_literal_elimination(&mut db);

    assert!(eliminated >= 1, "the pure clause should be eliminated");
    let pure = prep.eliminated_pure_literals();
    assert!(
        pure.iter().any(|l| l.var() == v(2) && l.is_pos()),
        "pure literal p must be recorded for reconstruction, got {pure:?}"
    );
}

/// Finding 3 (end to end): with inprocessing enabled, pure-literal elimination
/// may delete a clause mid-search; the reported model must still satisfy that
/// original clause via reconstruction.
#[test]
fn inprocessing_pure_literal_model_is_valid() {
    let config = SolverConfig {
        enable_inprocessing: true,
        inprocessing_interval: 1,
        random_polarity_prob: 0.0,
        ..SolverConfig::default()
    };
    let mut solver = Solver::with_config(config);

    // Conflict gadget forcing v0 = true (default phase tries v0 = false first):
    //   (v0 v v1) & (v0 v ¬v1)
    let clauses: Vec<Vec<Lit>> = vec![
        vec![Lit::pos(v(0)), Lit::pos(v(1))],
        vec![Lit::pos(v(0)), Lit::neg(v(1))],
        // (v3 v v2): v3 is pure-positive, so pure-literal elimination deletes it.
        vec![Lit::pos(v(3)), Lit::pos(v(2))],
    ];
    for c in &clauses {
        assert!(solver.add_clause(c.iter().copied()));
    }

    assert_eq!(solver.solve(), SolverResult::Sat);
    assert_eq!(
        first_violated(&solver, &clauses),
        None,
        "reported model must satisfy every original clause"
    );
}

/// Finding 2: inprocessing strengthening must not flip a satisfiable formula to
/// UNSAT. This drives a SAT instance with inprocessing enabled and asserts the
/// result and model stay valid.
#[test]
fn inprocessing_strengthening_preserves_sat() {
    let config = SolverConfig {
        enable_inprocessing: true,
        inprocessing_interval: 1,
        random_polarity_prob: 0.0,
        ..SolverConfig::default()
    };
    let mut solver = Solver::with_config(config);

    // A satisfiable instance with enough structure to learn clauses.
    let clauses: Vec<Vec<Lit>> = vec![
        vec![Lit::pos(v(0)), Lit::pos(v(1)), Lit::pos(v(2))],
        vec![Lit::neg(v(0)), Lit::pos(v(1)), Lit::pos(v(3))],
        vec![Lit::pos(v(0)), Lit::neg(v(1)), Lit::pos(v(4))],
        vec![Lit::neg(v(2)), Lit::neg(v(3)), Lit::pos(v(4))],
        vec![Lit::pos(v(2)), Lit::neg(v(4)), Lit::pos(v(0))],
        vec![Lit::neg(v(3)), Lit::pos(v(1)), Lit::neg(v(4))],
    ];
    for c in &clauses {
        assert!(solver.add_clause(c.iter().copied()));
    }

    assert_eq!(
        solver.solve(),
        SolverResult::Sat,
        "inprocessing must not turn a SAT formula UNSAT"
    );
    assert_eq!(first_violated(&solver, &clauses), None);
}

/// Finding 5: detect_symmetries must only emit generators that are genuine
/// automorphisms of the clause set.
#[test]
fn symmetry_emits_only_verified_automorphisms() {
    let mut det = AutomorphismDetector::new(4);
    // (a v b) & (c v d): all four vars share the weak signature, but a<->c is
    // NOT an automorphism ((a v b) would map to (c v b), absent from the set).
    det.add_clause(vec![Lit::pos(v(0)), Lit::pos(v(1))]);
    det.add_clause(vec![Lit::pos(v(2)), Lit::pos(v(3))]);

    let group = det.detect_symmetries();

    // Build the canonical clause set for verification.
    let clause_set: std::collections::HashSet<Vec<u32>> = [
        vec![Lit::pos(v(0)), Lit::pos(v(1))],
        vec![Lit::pos(v(2)), Lit::pos(v(3))],
    ]
    .iter()
    .map(|c| {
        let mut codes: Vec<u32> = c.iter().map(|l| l.code()).collect();
        codes.sort_unstable();
        codes
    })
    .collect();

    for perm in group.generators() {
        // Every emitted generator must map each clause onto a clause of the set.
        for clause in [
            vec![Lit::pos(v(0)), Lit::pos(v(1))],
            vec![Lit::pos(v(2)), Lit::pos(v(3))],
        ] {
            let mut mapped: Vec<u32> = clause.iter().map(|&l| perm.apply_lit(l).code()).collect();
            mapped.sort_unstable();
            assert!(
                clause_set.contains(&mapped),
                "emitted generator is not an automorphism"
            );
        }
        // The bogus cross-block swaps must never be emitted.
        assert_ne!(perm.apply(v(0)), v(2), "non-automorphism a<->c was emitted");
        assert_ne!(perm.apply(v(0)), v(3), "non-automorphism a<->d was emitted");
    }
}
