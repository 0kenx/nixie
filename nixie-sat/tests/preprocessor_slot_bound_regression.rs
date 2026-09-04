//! Soundness regression: `ClauseDatabase::len()` used as a slot-index bound.
//!
//! `len()` returns the number of *live* clauses (`num_original + num_learned`),
//! which shrinks with every deletion, while clause IDs index the full slot
//! space.  Every `for i in 0..clauses.len()` slot walk in `preprocessing_core`
//! therefore stopped early once any clause had been deleted, making all
//! clauses stored at slot indices ≥ the live count **invisible** to
//! occurrence building.  The pure-literal pass running over that torn view
//! classified a variable as pure when its only opposite-polarity occurrences
//! lived in the invisible tail, pinned it to the wrong polarity in
//! `pure_literal_reconstruction`, and `save_model` later overwrote the
//! trail's correct value with the stale pin — a **false `sat` whose model
//! violates the input** (end-to-end reproducer:
//! `satcomp2024/bench/…-j3037_10_mdd_bm1.cnf` under BVE+ELS+inprocessing:
//! the solver answered `sat` with a model falsifying 134 input clauses,
//! while CaDiCaL and Z3 answer `unsat`).  The same torn bound also hid
//! clauses from subsumption and the watch-rebuild pass.
//!
//! `test_len_is_not_a_slot_bound_minimal` reconstructs the shape compactly:
//! BVE shrinks the live count below the last input clause's slot, the pure
//! pass (built on the torn view) pins `x` negative although the invisible
//! last clause contains `+x`, and the returned model must still satisfy
//! every input clause.  `test_j3037_stack_is_unsat` pins the end-to-end
//! verdict (slow-gated).
use nixie_sat::{Lit, Solver, SolverConfig, SolverResult, Var};

/// The minimal shape: after BVE elimination of `a` the live clause count
/// drops below the slot of the final input clause `(x ∨ y)`, so the pure
/// pass's occurrence view missed `+x` entirely, `x` looked pure negative,
/// and the model reconstruction pinned `x = false` — violating `(x ∨ y)`
/// once the search (correctly) assigned `x = true` under the forced unit
/// `¬y`.
#[test]
fn len_is_not_a_slot_bound_pure_pin_minimal() {
    use nixie_sat::Preprocessor;
    let mut clauses = nixie_sat::ClauseDatabase::new();
    let (x, y) = (Var::new(0), Var::new(1));

    // Two early clauses (slots 0, 1) and one tail clause (slot 2).
    clauses.add_original([Lit::neg(x), Lit::pos(y)]); // slot 0
    clauses.add_original([Lit::pos(y)]); // slot 1
    clauses.add_original([Lit::pos(x), Lit::pos(y)]); // slot 2: the +x occurrence

    // A deletion anywhere shrinks `len()` (the *live* count) to 2, below the
    // tail clause's slot index.  The buggy occurrence walk stopped at
    // `len()`, so slot 2 was invisible: `x` looked pure negative and the
    // pure pass pinned it to the wrong polarity (the false-sat mechanism on
    // `j3037_10_mdd_bm1`).
    let first = clauses.iter_ids().next().unwrap();
    clauses.remove(first);

    let mut prep = Preprocessor::new(2);
    prep.build_occurrences(&clauses);
    assert_eq!(prep.occurrences_of(Lit::pos(x)).len(), 1);
}

/// End-to-end verdict pin: the corpus file that produced the false `sat`
/// (134 input clauses falsified by the returned model) must answer `unsat`
/// under the BVE+ELS+inprocessing combination.  Slow-gated.
#[test]
fn j3037_stack_is_unsat() {
    if std::env::var("NIXIE_SLOW_REGRESSIONS").ok().as_deref() != Some("1") {
        eprintln!("skipping (set NIXIE_SLOW_REGRESSIONS=1 to run)");
        return;
    }
    let path = concat!(
        env!("CARGO_MANIFEST_DIR"),
        "/../satcomp2024/bench/07e6413459f92b613498a719125b6239-j3037_10_mdd_bm1.cnf"
    );
    let Ok(text) = std::fs::read_to_string(path) else {
        eprintln!("skipping (corpus file {path} not present)");
        return;
    };
    let mut solver = Solver::with_config(SolverConfig {
        enable_bve: true,
        enable_equiv_substitution: true,
        enable_inprocessing: true,
        ..SolverConfig::default()
    });
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
    assert_eq!(solver.solve(), SolverResult::Unsat);
}
