//! The 2026-09-21 class-crossing-unit false-sat regression (found by the
//! `gate_subsume_soundness` generator; root cause in
//! `substitute_equivalent_literals_round` — see the class-units block in
//! `equiv.rs`).
//!
//! Bug shape: an equivalence class containing a level-0-ASSIGNED literal
//! whose representative was UNASSIGNED.  The fold retired every clause
//! connecting the two (satisfied/tautology through the very same class
//! and trail values) without deriving the forced representative unit, so
//! the search branched the representative freely, answered `sat` on an
//! UNSAT formula, and the model reconstruction assigned the member from
//! the representative — clobbering the level-0 fact.  (Pinned by
//! `ce2_min` below, found by the `gate_subsume_soundness` generator.)
//!
//! `ce2_min` (16 clauses, default config, plain solve): unit ¬2 with
//! class {2 ≡ 1 ≡ 18} built from the binaries 1≡18 and the AND-gate
//! 2 ↔ 18∧13 (`(¬18∨¬13∨2)`, `(¬2∨18)`, `(¬2∨13)`); the formula is
//! UNSAT (kissat-verified) but answered `sat` with a model violating
//! the unit ¬2.

use std::io::Cursor;

use nixie_sat::{DimacsParser, LBool, Solver, SolverConfig, SolverResult};

const CE2_MIN: &str = "p cnf 18 16\n\
-3 0\n\
1 -18 0\n\
-11 0\n\
-8 10 0\n\
-18 -13 1 0\n\
-1 18 0\n\
-1 13 0\n\
-18 -13 2 0\n\
-2 18 0\n\
-2 13 0\n\
8 17 0\n\
18 -10 0\n\
-11 0\n\
-2 0\n\
6 -17 0\n\
1 -6 0\n";

fn solve_default(cnf: &str) -> (SolverResult, Vec<u8>) {
    let mut s = Solver::with_config(SolverConfig {
        enable_inprocessing: true,
        inprocessing_interval: 5,
        enable_equiv_substitution: true,
        enable_gate_congruence: true,
        ..SolverConfig::default()
    });
    let mut p = DimacsParser::new();
    p.parse_reader(Cursor::new(cnf.as_bytes()), &mut s)
        .expect("parse");
    let r = s.solve();
    let model: Vec<u8> = (0..s.num_vars())
        .map(|i| match s.model().get(i) {
            Some(LBool::True) => 1u8,
            Some(LBool::False) => 0u8,
            _ => 2u8,
        })
        .collect();
    (r, model)
}

#[test]
fn class_crossing_unit_never_false_sats() {
    let (r, m) = solve_default(CE2_MIN);
    assert_ne!(
        r,
        SolverResult::Sat,
        "UNSAT formula answered sat (the class-crossing-unit false-sat)"
    );
    if r == SolverResult::Unsat {
        return;
    }
    // Unknown is sound; still validate the model if one came back.
    let clauses: Vec<Vec<i32>> = CE2_MIN
        .lines()
        .skip(1)
        .map(|l| {
            l.split_whitespace()
                .map(|t| t.parse::<i32>().unwrap_or(0))
                .take_while(|&v| v != 0)
                .collect()
        })
        .collect();
    for c in &clauses {
        let sat = c.iter().any(|&v| {
            let vi = v.unsigned_abs() as usize - 1;
            m.get(vi).copied() == Some(if v > 0 { 1 } else { 0 })
        });
        assert!(sat, "model violates original clause {c:?}");
    }
}

#[test]
fn class_crossing_unit_survives_the_fold_knob_matrix() {
    // The same anatomy under the full study stack (SSR + pre-search +
    // gate subsumption) must stay honest too — the composition is what
    // originally exposed the base bug.
    unsafe { std::env::set_var("NIXIE_GATE_SUBSUME", "1") };
    let (r, m) = solve_default(CE2_MIN);
    unsafe { std::env::remove_var("NIXIE_GATE_SUBSUME") };
    assert_ne!(r, SolverResult::Sat);
    if r == SolverResult::Unsat {
        return;
    }
    let clauses: Vec<Vec<i32>> = CE2_MIN
        .lines()
        .skip(1)
        .map(|l| {
            l.split_whitespace()
                .map(|t| t.parse::<i32>().unwrap_or(0))
                .take_while(|&v| v != 0)
                .collect()
        })
        .collect();
    for c in &clauses {
        let sat = c.iter().any(|&v| {
            let vi = v.unsigned_abs() as usize - 1;
            m.get(vi).copied() == Some(if v > 0 { 1 } else { 0 })
        });
        assert!(sat, "model violates original clause {c:?}");
    }
}
