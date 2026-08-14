//! Regression test for SAT-2: `Solver::inprocess()`'s pure-literal and
//! subsumption elimination passes used to delete original clauses without
//! ever recording a DRAT deletion line for them, leaving the emitted proof
//! non-minimal (it kept referencing clauses the live database no longer
//! had). This drives a real `solve()` with inprocessing and DRAT logging
//! both enabled and checks that the specific clauses expected to be
//! eliminated during inprocessing actually show up as `d`-lines in the
//! resulting proof.

use oxiz_sat::{Solver, SolverConfig, SolverResult};

#[test]
fn solved_instance_with_inprocessing_logs_pure_and_subsumed_deletions_to_drat() {
    use std::io::Read as _;

    let path = std::env::temp_dir().join("oxiz_sat_inprocess_drat_deletion_solve.drat");

    let mut solver = Solver::with_config(SolverConfig {
        enable_inprocessing: true,
        inprocessing_interval: 1,
        clause_deletion_threshold: 5,
        // Disable failed-literal probing so this test exercises the pure-literal
        // and subsumption passes in isolation (FLP would otherwise deduce the
        // PHP(3,2) unsat directly via propagation, short-circuiting them).
        enable_failed_literal_probing: false,
        enable_hyper_binary_probing: false,
        // Disable lucky phases for the same reason: lucky's discrepancy search
        // refutes PHP(3,2) before inprocessing ever runs, which would skip the
        // pure-literal/subsumption deletions this test checks for.
        enable_lucky: false,
        ..SolverConfig::default()
    });

    // PHP(3,2): 3 pigeons, 2 holes – UNSAT, and small enough to solve
    // quickly while still forcing multiple conflicts (reusing the same
    // construction the DRAT well-formedness regression test uses, which
    // reliably drives several conflicts / backjumps to decision level 0).
    for _ in 0..6 {
        solver.new_var();
    }
    solver.add_clause_dimacs(&[1, 2]);
    solver.add_clause_dimacs(&[3, 4]);
    solver.add_clause_dimacs(&[5, 6]);
    solver.add_clause_dimacs(&[-1, -3]);
    solver.add_clause_dimacs(&[-1, -5]);
    solver.add_clause_dimacs(&[-3, -5]);
    solver.add_clause_dimacs(&[-2, -4]);
    solver.add_clause_dimacs(&[-2, -6]);
    solver.add_clause_dimacs(&[-4, -6]);

    // Helper clauses on fresh, disjoint variables (7..12), present from
    // decision level 0 onward so the very first `inprocess()` call (however
    // it gets triggered during the PHP search above) finds them.
    //
    // Pure-literal family: var 7 occurs only positively, across two
    // clauses that pure_literal_elimination must delete.
    solver.add_clause_dimacs(&[7, 8]); // (y ∨ w1)
    solver.add_clause_dimacs(&[7, 9]); // (y ∨ w2)

    // Subsumption pair: (p ∨ q) subsumes (p ∨ q ∨ r), so the superset must
    // be deleted by subsumption_elimination.
    solver.add_clause_dimacs(&[10, 11]); // (p ∨ q)
    solver.add_clause_dimacs(&[10, 11, 12]); // (p ∨ q ∨ r)

    // Decoy giving w1, w2, p, q, r an opposite-polarity occurrence each, so
    // none of them is independently pure (only var 7 / `y` is) – keeps the
    // (p ∨ q ∨ r) deletion attributable to subsumption alone.
    solver.add_clause_dimacs(&[-8, -9, -10, -11, -12]);

    solver
        .enable_drat_proof(&path)
        .expect("enable DRAT proof logging");

    // The instance is UNSAT purely from the PHP(3,2) core; the helper
    // clauses above are satisfiable on their own and don't affect the
    // verdict.
    assert_eq!(solver.solve(), SolverResult::Unsat);
    solver.disable_drat_proof();

    let mut contents = String::new();
    std::fs::File::open(&path)
        .expect("proof file must exist")
        .read_to_string(&mut contents)
        .expect("read proof file");
    std::fs::remove_file(&path).ok();

    // Every proof line is well-formed (addition or `d`-prefixed deletion,
    // `0`-terminated) and the proof completes with the empty clause.
    let mut saw_empty_clause = false;
    let mut deletion_lines: Vec<&str> = Vec::new();
    for line in contents.lines() {
        let line = line.trim();
        if line.is_empty() {
            continue;
        }
        assert!(
            line.ends_with('0'),
            "malformed DRAT line (missing 0 terminator): {line:?}"
        );
        if line == "0" {
            saw_empty_clause = true;
        }
        if let Some(rest) = line.strip_prefix("d ") {
            deletion_lines.push(rest.trim());
        }
    }
    assert!(
        saw_empty_clause,
        "a complete UNSAT DRAT proof must end by deriving the empty clause"
    );

    // Parse each deletion line into its sorted DIMACS literal set so the
    // check below doesn't depend on emission order.
    let parsed_deletions: Vec<Vec<i32>> = deletion_lines
        .iter()
        .map(|line| {
            let mut lits: Vec<i32> = line
                .split_whitespace()
                .map(|tok| tok.parse::<i32>().expect("DRAT literal must be an integer"))
                .filter(|&n| n != 0)
                .collect();
            lits.sort_unstable();
            lits
        })
        .collect();

    let expect_deleted = |mut lits: Vec<i32>| {
        lits.sort_unstable();
        assert!(
            parsed_deletions.contains(&lits),
            "expected a DRAT deletion line for clause {lits:?}, but none of the \
             {} deletion lines matched: {parsed_deletions:?}",
            parsed_deletions.len()
        );
    };

    // The two pure-literal clauses over `y` (var 7) must both be retired.
    expect_deleted(vec![7, 8]);
    expect_deleted(vec![7, 9]);
    // The subsumed superset clause must be retired.
    expect_deleted(vec![10, 11, 12]);
}
