//! Soundness regression: false UNSAT from over-strong learned-clause
//! minimization under chronological backtracking.
//!
//! `summle_x4044_steps7…cnf` is SATISFIABLE (CaDiCaL 1.x produces a model that
//! satisfies every clause).  The plain recursive clause minimizer used to trust
//! the analysis `seen` stamps as a "removable" shortcut: in classic CDCL a
//! resolved-away conflict-level literal sits above the UIP on the trail, out of
//! reach of the minimizer's downward reason walk, so the shortcut was harmless.
//! With chronological backtracking enabled the ordering invariant is gone and
//! the walk could resolve through conflict-level literals whose resolution
//! obligation 1-UIP analysis never discharged, producing learned clauses
//! stronger than anything resolution derives.  The cascading bogus level-0
//! units answered `unsat` after ~2.2k conflicts on this file.
//!
//! The fix ports CaDiCaL's `minimize.cpp` faithfully (flag-cached recursion,
//! `level == decision_level` rejection, depth limit) for the plain path.  The
//! test solves under a conflict budget large enough to cover the old failure
//! (2242 conflicts) and asserts the solver never claims UNSAT: the ground
//! truth `sat` takes ~150k conflicts, so within the budget the only honest
//! answers are `sat` (if the search improves) or `unknown`.

use oxiz_sat::{Lit, Solver, SolverResult, Var};

fn parse_and_solve(max_conflicts: u64) -> SolverResult {
    let path = concat!(
        env!("CARGO_MANIFEST_DIR"),
        "/tests/fixtures/summle_x4044.cnf"
    );
    let text = std::fs::read_to_string(path).expect("fixture readable");

    let mut solver = Solver::new();
    for line in text.lines() {
        let t = line.trim();
        if t.is_empty() || t.starts_with('c') {
            continue;
        }
        if t.starts_with('p') {
            let n: usize = t
                .split_whitespace()
                .nth(2)
                .and_then(|s| s.parse().ok())
                .unwrap_or(0);
            for _ in 0..n {
                solver.new_var();
            }
            continue;
        }
        // Each line in this fixture is exactly one clause.
        let clause: Vec<Lit> = t
            .split_whitespace()
            .map(|s| s.parse::<i32>().expect("int"))
            .take_while(|&x| x != 0)
            .map(|x| {
                let idx = x.unsigned_abs() - 1;
                while idx as usize >= solver.num_vars() {
                    solver.new_var();
                }
                if x > 0 {
                    Lit::pos(Var::new(idx))
                } else {
                    Lit::neg(Var::new(idx))
                }
            })
            .collect();
        solver.add_clause(clause);
    }
    solver.set_max_conflicts(Some(max_conflicts));
    solver.solve()
}

#[test]
fn summle_x4044_is_not_unsat() {
    // Budget: the old false UNSAT fired at 2242 conflicts; 20k covers it with
    // margin while finishing in a couple of seconds.
    let result = parse_and_solve(20_000);
    assert_ne!(
        result,
        SolverResult::Unsat,
        "summle_X4044 is SATISFIABLE; Unsat within the budget is the minimizer \
         soundness regression (see this file's header)"
    );
}
