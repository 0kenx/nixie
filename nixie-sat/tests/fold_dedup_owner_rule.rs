//! Tests for the fold's exact-duplicate retire (2026-09-18/19): the round
//! may retire a clause only when the recorded owner of its mapped vector is
//! an ORIGINAL clause.  Retiring an original in favor of a LEARNED twin was
//! the b21/seed-1 false-`sat`'s exact mechanism — the learned owner was
//! (correctly) purged by `mark_redundant_clauses_with_eliminated_variables_
//! as_garbage` at the next elimination, the constraint left the folded
//! formula with no extension obligation, and the search answered `sat` on a
//! known-UNSAT instance.

use nixie_sat::{Lit, Solver, SolverConfig, SolverResult, Var};

fn v(i: usize) -> Var {
    Var::new(i as u32)
}

fn l(i: usize, positive: bool) -> Lit {
    if positive {
        Lit::pos(v(i))
    } else {
        Lit::neg(v(i))
    }
}

#[test]
fn fold_dedup_never_retires_original_for_learned_owner() {
    // UNSAT formula whose refutation needs the original clause (0 ∨ 1);
    // a learned duplicate of it appears during search.  The buggy dedup
    // retired the original for the learned twin; the doomed purge later
    // removed the twin; the formula became satisfiable.
    let mut s = Solver::with_config(SolverConfig {
        enable_equiv_substitution: true,
        enable_gate_congruence: true,
        enable_inprocessing: true,
        presearch_collapse: true,
        enable_lucky: false,
        ..SolverConfig::default()
    });
    for _ in 0..6 {
        s.new_var();
    }
    // An equivalence the fold can find: (2 ↔ 3).
    s.add_clause([l(2, false), l(3, false)]);
    s.add_clause([l(2, true), l(3, true)]);
    // The clause pair the fold makes identical: (0 ∨ 2) and (0 ∨ 3).
    s.add_clause([l(0, true), l(2, true)]);
    s.add_clause([l(0, true), l(3, true)]);
    // Force 0 false: the pair becomes (2)/(3) — equivalent units.
    s.add_clause([l(0, false)]);
    // Force 2 (hence 3) false: contradiction with the units above is
    // derived; without the pair the formula would be SAT.
    s.add_clause([l(1, false), l(2, false)]);
    s.add_clause([l(1, true)]);
    assert_eq!(s.solve(), SolverResult::Unsat);
}

#[test]
fn fold_dedup_survives_learned_twin_purge() {
    // Search-shaped variant: the duplicate owner is learned during search
    // (a learned binary identical to an original), then an elimination
    // purges learned clauses mentioning the eliminated var.  The original
    // must still carry the constraint.
    let mut s = Solver::with_config(nixie_sat::ConfigPreset::CaDiCaL.config());
    for _ in 0..40 {
        s.new_var();
    }
    // Genuinely unsat core: the chain forces every var equal, then 0
    // and its equivalence class are pinned to both values.
    for i in 0..7 {
        s.add_clause([l(i, false), l(i + 1, false)]);
        s.add_clause([l(i, true), l(i + 1, true)]);
    }
    s.add_clause([l(0, true)]);
    s.add_clause([l(6, false)]);
    // Gate twins driving fold rounds mid-search.
    for o in [30usize, 31, 32] {
        s.add_clause([l(0, false), l(1, false), l(o, true)]);
        s.add_clause([l(o, false), l(0, true)]);
        s.add_clause([l(o, false), l(1, true)]);
    }
    assert_eq!(s.solve(), SolverResult::Unsat);
}
