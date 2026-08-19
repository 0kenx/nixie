//! Soundness regression: dominator hyper-binary case (B) must PROMOTE the
//! resolvent when it subsumes an original reason clause.
//!
//! The port's first version deleted the subsumed original reason and left
//! the resolvent *learned*: a later database reduction then removed the only
//! remaining (weaker) constraint, and the formula was under-constrained —
//! `Break_unsat_06_07.xml.cnf` answered `sat` in 165 ms under
//! `INPROCESS+PROBE+HBP+BVE` (CaDiCaL: `unsat`; every proper flag subset
//! unsat). cadical's `red = !contained || reason->redundant` makes the
//! resolvent irredundant exactly in the subsumes-original case; the fix
//! mirrors that via `clear_learned` before retiring the reason.

use oxiz_sat::{DimacsParser, Solver, SolverConfig, SolverResult};

#[test]
fn dominator_hbr_subsuming_original_promotes_resolvent() {
    let solver_cfg = SolverConfig {
        enable_bve: true,
        enable_inprocessing: true,
        enable_failed_literal_probing: true,
        enable_hyper_binary_probing: true,
        ..SolverConfig::default()
    };
    let mut solver = Solver::with_config(solver_cfg);
    let mut parser = DimacsParser::new();
    let path = concat!(
        env!("CARGO_MANIFEST_DIR"),
        "/tests/fixtures/break_unsat_06_07.cnf"
    );
    parser.parse_file(path, &mut solver).expect("parse");
    assert_eq!(
        solver.solve(),
        SolverResult::Unsat,
        "Break_unsat_06_07 is UNSAT (CaDiCaL); sat means the HBR resolvent \
         failed to carry the subsumed original's obligation"
    );
}
