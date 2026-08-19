//! Soundness regression: shrink x inprocessing combination.
//!
//! `circuit_48in64out_with_700gates_4in4out_dist128_seed1` (SATISFIABLE;
//! CaDiCaL model verified) answered `unsat` when block-UIP clause shrinking
//! ran with inprocessing enabled (`enable_inprocessing = true`): 286 of the
//! final 775 level-0 trail units were not entailed by the input, each with a
//! CaDiCaL satisfiability witness.  Root cause (fixed in
//! `shrink_block`): the per-block `MF_SHRINKABLE` reset covered only the
//! block literals, while cadical's `reset_shrinkable` /
//! `mark_shrinkable_as_removable` clear the walk-discovered literals as
//! well; a stale flag from one block's reason walk leaking into a later
//! block's backward trail scan makes that scan pop a foreign literal and
//! mis-derive the replacement – the same mis-derivation category as the
//! `uip_pos` bug (`shrink_trail_index_regression`).
//!
//! Like the other circuit regression in `watch_position_soundness`, this
//! test solves under a conflict budget and asserts the solver never claims
//! UNSAT: the ground-truth `sat` may or may not be reached within the
//! budget, but the buggy build produced its false `unsat` comfortably
//! inside it.  Gated behind `OXIZ_SLOW_REGRESSIONS=1`.
use oxiz_sat::{Lit, Solver, SolverConfig, SolverResult, Var};

/// Load a DIMACS CNF (one clause per line) into a fresh solver.
fn load_dimacs(text: &str, config: SolverConfig) -> Solver {
    let mut solver = Solver::with_config(config);
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

#[test]
fn shrink_with_inprocessing_is_not_unsat_on_satisfiable_circuit() {
    if std::env::var("OXIZ_SLOW_REGRESSIONS").ok().as_deref() != Some("1") {
        eprintln!("skipping (set OXIZ_SLOW_REGRESSIONS=1 to run)");
        return;
    }
    let path = concat!(
        env!("CARGO_MANIFEST_DIR"),
        "/../satcomp2024/bench/303480ca7e8322d771c94caf4ebd4e95-\
         circuit_48in64out_with_700gates_4in4out_dist128_seed1.sanitized.cnf"
    );
    let Ok(text) = std::fs::read_to_string(path) else {
        eprintln!("skipping (corpus file {path} not present)");
        return;
    };
    let config = SolverConfig {
        enable_inprocessing: true,
        ..SolverConfig::default()
    };
    let mut solver = load_dimacs(&text, config);
    solver.set_max_conflicts(Some(1_500_000));
    let result = solver.solve();
    assert_ne!(
        result,
        SolverResult::Unsat,
        "SATISFIABLE instance (cadical model verified) answered unsat under \
         shrink x inprocessing: the block-walk flag reset regressed"
    );
}
