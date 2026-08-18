//! Soundness regression: `forward_subsumption` reordered clause literals in
//! place (its normalize prologue) without rebuilding the watch lists, while
//! `propagate` requires each clause's two watched literals at stored
//! positions `[0]`/`[1]`. A normalize-only reorder with zero subsumed clauses
//! skipped the rebuild, so every clause's watchers kept pointing at stale
//! positions; BCP then "propagated" literals that were never implied and the
//! search concluded a false UNSAT within a handful of conflicts.
//!
//! Reproducer: `noL-11-14` (satcomp2024) with `enable_inprocessing` – the
//! solver answered `unsat` in ~8 ms / 6 conflicts. CaDiCaL proves the file
//! SATISFIABLE (model verified against the input). The fix rebuilds the
//! watched-literal structures unconditionally after the pass.
//!
//! The test solves under a conflict budget and asserts the solver never
//! claims UNSAT within it (the same pattern as `watch_position_soundness.rs`):
//! the ground-truth SAT takes far longer than the budget, so the only honest
//! answers are `sat` or `unknown`.

use oxiz_sat::{DimacsParser, Solver, SolverConfig, SolverResult};

#[test]
fn fs_normalize_reorder_never_yields_false_unsat() {
    let solver_cfg = SolverConfig {
        enable_inprocessing: true,
        ..SolverConfig::default()
    };
    let mut solver = Solver::with_config(solver_cfg);
    solver.set_max_conflicts(Some(5000));
    let mut parser = DimacsParser::new();
    let path = concat!(env!("CARGO_MANIFEST_DIR"), "/tests/fixtures/noL_11_14.cnf");
    parser.parse_file(path, &mut solver).expect("parse noL");
    let result = solver.solve();
    assert_ne!(
        result,
        SolverResult::Unsat,
        "noL-11-14 is SAT (CaDiCaL model verified); UNSAT within the budget \
         means a preprocessing pass corrupted the clause database"
    );
}
