//! Soundness regressions: two false-UNSAT bugs found by the CaDiCaL
//! differential sweep over `satcomp2024/bench` (both files are SATISFIABLE;
//! CaDiCaL models verified clause-by-clause against the inputs).
//!
//! # Bug 1 – learned-clause second watch not moved into the clause
//!
//! `si2-b03m-m800-03` answered `unsat` in 13,937 conflicts
//! (`SolverConfig::default()`), with the very first fabricated propagation
//! after only 92.  `learn_clause`'s multi-literal branch selected the second
//! watched literal by `watch_rank` but never swapped it into position 1 of
//! the stored clause.  The watcher scan in `propagate` requires the two
//! watched literals at positions `[0]`/`[1]`: when the falsified watch fires
//! it swaps it to position 1, reads the other watch from `lits[0]`, and
//! searches for a replacement only over the tail `j >= 2` – it never
//! examines `lits[1]`.  A watch left out in the tail therefore made the scan
//! "propagate" `lits[0]` from a clause that was not unit (e.g. one whose
//! `lits[1]` was still unassigned, or whose reason literal was already
//! TRUE).  Every conflict resolved through such a corrupted reason learned
//! an unentailed clause, and the cascade ended in a bogus root-level empty
//! clause.  The fix swaps the selected literal into position 1 of both the
//! stored clause and the local vector, exactly like `add_clause` and
//! `replace_clause_lits`.
//!
//! # Bug 2 – clause minimizer missing CaDiCaL's conflict-level guards
//!
//! `circuit_48in64out_with_700gates_4in4out_dist128_seed1` answered `unsat`
//! in 1,419,946 conflicts (`SolverConfig::default()`); the first
//! over-strengthened learned clause (`[1998, 2081, 2057, 2082, 2022]`, not
//! entailed by the input – CaDiCaL refutes its negation) appeared early in
//! the search.  The recursive minimizer rejected literals at
//! `decision_level()` instead of the genuine *conflict* level, and lacked
//! Don Knuth's `seen.count < 2` gate and the `v.trail <= l.seen.trail`
//! early abort.  Under chronological backtracking the two levels diverge, so
//! conflict-level literals were resolved out without their 1-UIP obligation
//! being discharged – clauses stronger than resolution derives.  The fix
//! ports cadical's `minimize.cpp` semantics completely (per-level seen
//! statistics maintained by `analyze`, conflict-level rejection, both
//! aborts).
//!
//! The tests solve under a conflict budget and assert the solver never
//! claims UNSAT: the ground-truth SAT takes far longer than the budget, so
//! within it the only honest answers are `sat` (if the search improves) or
//! `unknown`.  The circuit test is slow (~1.5M conflicts even for the buggy
//! verdict) and gated behind `OXIZ_SLOW_REGRESSIONS=1` so the default suite
//! stays fast; run it explicitly when touching `learn_clause` watch
//! attachment or clause minimization.

use oxiz_sat::{Lit, Solver, SolverResult, Var};

/// Parse a DIMACS CNF (one clause per line in these sanitized corpora) and
/// load it into a fresh solver with the given config, creating header
/// variables up front so the variable-creation order matches `DimacsParser`.
fn load_dimacs(text: &str) -> Solver {
    let mut solver = Solver::new();
    for line in text.lines() {
        let t = line.trim();
        if t.is_empty() || t.starts_with('c') {
            continue;
        }
        if t.starts_with('p') {
            let declared = t
                .split_whitespace()
                .nth(2)
                .and_then(|s| s.parse().ok())
                .unwrap_or(0);
            for _ in 0..declared {
                solver.new_var();
            }
            continue;
        }
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
    solver
}

fn corpus(rel: &str) -> String {
    let path = format!("{}/../satcomp2024/bench/{rel}", env!("CARGO_MANIFEST_DIR"));
    std::fs::read_to_string(path).unwrap_or_else(|e| panic!("corpus file {rel}: {e}"))
}

#[test]
fn si2_b03m_is_not_unsat() {
    // Pre-fix false UNSAT fired at 13,937 conflicts (first fabricated
    // propagation at 92); 30k covers it with margin.
    let mut solver = load_dimacs(&corpus(
        "af750c18578d52e60472315692ad83c0-si2-b03m-m800-03.cnf",
    ));
    solver.set_max_conflicts(Some(30_000));
    let result = solver.solve();
    assert_ne!(
        result,
        SolverResult::Unsat,
        "si2-b03m-m800-03 is SATISFIABLE (CaDiCaL model verified); Unsat within \
         the budget is the learned-clause watch-position regression (see this \
         file's header)"
    );
}

#[test]
fn circuit_48in64out_is_not_unsat() {
    // ~1.5M conflicts even for the buggy verdict: opt-in only.
    if std::env::var("OXIZ_SLOW_REGRESSIONS").ok().as_deref() != Some("1") {
        eprintln!("skipping (set OXIZ_SLOW_REGRESSIONS=1 to run)");
        return;
    }
    // Pre-fix false UNSAT fired at 1,419,946 conflicts; 1.5M covers it.
    let mut solver = load_dimacs(&corpus(
        "303480ca7e8322d771c94caf4ebd4e95-\
         circuit_48in64out_with_700gates_4in4out_dist128_seed1.sanitized.cnf",
    ));
    solver.set_max_conflicts(Some(1_500_000));
    let result = solver.solve();
    assert_ne!(
        result,
        SolverResult::Unsat,
        "circuit_48in64out…dist128_seed1 is SATISFIABLE (CaDiCaL model verified); \
         Unsat within the budget is the minimizer conflict-level regression (see \
         this file's header)"
    );
}
