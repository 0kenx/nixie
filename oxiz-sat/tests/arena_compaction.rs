//! Arena-compaction end-to-end regression: a BVE-heavy instance whose
//! elimination garbage crosses the compaction gate mid-solve must still
//! solve correctly, with the watcher-ref audit (`check_watcher_ref_consistency`,
//! wired into the standing debug invariants) verifying after every compaction
//! that no `ClauseRef` survived relocation unrewritten.
//!
//! `crn_11_99_u.cnf` is the instance that exposed the first compaction bug
//! (physical extents read off list neighbours break once tombstoned entries
//! interleave with live refs); see `ClauseArena::compact`'s pass-0 note.

use oxiz_sat::{ConfigPreset, DimacsParser, Solver, SolverResult};

#[test]
fn compaction_fires_and_solves_bve_garbage_correctly() {
    let mut solver = Solver::with_config(ConfigPreset::CaDiCaL.config());
    let mut parser = DimacsParser::new();
    let path = concat!(
        env!("CARGO_MANIFEST_DIR"),
        "/tests/fixtures/crn_11_99_u.cnf"
    );
    parser.parse_file(path, &mut solver).expect("parse crn");
    let result = solver.solve();
    assert_eq!(result, SolverResult::Unsat);
    // The gate (>= 64 KiB garbage and >= live/3) must have fired at least
    // once on this instance; 0 means compaction silently stopped running.
    assert!(
        solver.stats().arena_compactions >= 1,
        "expected at least one arena compaction, got {}",
        solver.stats().arena_compactions
    );
}
