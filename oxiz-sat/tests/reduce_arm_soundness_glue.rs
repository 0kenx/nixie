//! Soundness regression sibling: the glue-ranked cadical-reduce arm on the satisfiable
//! `constraints_17` instance must stay Sat (see
//! `reduce_arm_soundness_null.rs` for the full story and the two leaks).

use oxiz_sat::{ConfigPreset, DimacsParser, Solver, SolverResult};

fn solve_with_env() -> SolverResult {
    let mut solver = Solver::with_config(ConfigPreset::CaDiCaL.config());
    let mut parser = DimacsParser::new();
    let path = concat!(
        env!("CARGO_MANIFEST_DIR"),
        "/tests/fixtures/constraints_17_0.4_1.sanitized.cnf"
    );
    parser.parse_file(path, &mut solver).expect("parse constraints_17");
    solver.solve()
}

#[test]
fn glue_ranked_reduce_never_yields_wrong_unsat() {
    // SAFETY: single test in this binary and nextest runs each test in its
    // own process, so no other thread can observe the mutation; set before
    // the solver's OnceLock flag readers run.
    unsafe { std::env::set_var("OXIZ_CADICAL_REDUCE", "1"); }
    assert_eq!(solve_with_env(), SolverResult::Sat);
}
