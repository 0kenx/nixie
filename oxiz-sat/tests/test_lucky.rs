//! Tests for the automatic CaDiCaL-style "lucky" pre-solving phases.
//!
//! Lucky runs by default (`enable_lucky = true`). These tests verify:
//!   * soundness — every reported model satisfies the original clauses, and
//!     UNSAT is never reported for a satisfiable formula;
//!   * coverage — the uniform / Horn / ordered-with-flip strategies actually
//!     fire (`lucky_succeeded` > 0) on appropriately-shaped instances;
//!   * the discrepancy flip path (forward/backward) finds models that need a
//!     per-variable polarity flip;
//!   * disabling lucky leaves standard search intact.

use oxiz_sat::{LBool, Lit, Solver, SolverConfig, SolverResult};

/// Build a solver with a config cloned from `base`, toggling `enable_lucky`.
fn solver_with_lucky(base: &SolverConfig, on: bool) -> Solver {
    let mut cfg = base.clone();
    cfg.enable_lucky = on;
    Solver::with_config(cfg)
}

/// Validate a model against a list of clauses (each clause as `Vec<i32>` in
/// DIMACS sign convention: `1` = x1 positive, `-1` = x1 negative, 1-based).
fn assert_model_valid(clauses: &[Vec<i32>], model: &[LBool]) {
    let lit_val = |dimacs: i32| -> bool {
        let var = dimacs.unsigned_abs() as usize - 1;
        let polarity = dimacs > 0;
        match model.get(var).copied().unwrap_or(LBool::Undef) {
            LBool::True => polarity,
            LBool::False => !polarity,
            LBool::Undef => panic!("model leaves variable x{} undefined", var + 1),
        }
    };
    for c in clauses {
        assert!(
            c.iter().any(|&l| lit_val(l)),
            "model fails to satisfy clause {:?}",
            c
        );
    }
}

/// Plain default solver (lucky on).
fn fresh() -> Solver {
    Solver::new()
}

// ---------------------------------------------------------------------------
// Soundness: lucky must not change the SAT/UNSAT verdict.
// ---------------------------------------------------------------------------

#[test]
fn lucky_unsat_stays_unsat() {
    // (a) ∧ (¬a ∨ ¬a)  ≡  a ∧ ¬a  →  UNSAT
    let clauses: Vec<Vec<i32>> = vec![vec![1], vec![-1]];
    let mut s = fresh();
    let a = s.new_var();
    s.add_clause([Lit::pos(a)]);
    s.add_clause([Lit::neg(a)]);
    assert_eq!(s.solve(), SolverResult::Unsat);
    let _ = clauses;
}

#[test]
fn lucky_trivial_sat_unaffected() {
    // (a ∨ b) ∧ (¬a ∨ c): satisfiable (e.g. a=T, c=T). Lucky must not corrupt
    // the solve nor produce an invalid model.
    let mut s = fresh();
    let a = s.new_var();
    let b = s.new_var();
    let c = s.new_var();
    s.add_clause([Lit::pos(a), Lit::pos(b)]);
    s.add_clause([Lit::neg(a), Lit::pos(c)]);
    assert_eq!(s.solve(), SolverResult::Sat);
    assert_model_valid(&[vec![1, 2], vec![-1, 3]], s.model());
}

// ---------------------------------------------------------------------------
// Coverage: each strategy fires on an appropriately-shaped instance.
// ---------------------------------------------------------------------------

/// Every clause contains a negative literal → set everything false.
#[test]
fn lucky_uniform_negative_fires() {
    // (¬a ∨ ¬b) ∧ (¬c) — all clauses have a negative literal.
    let mut s = fresh();
    let a = s.new_var();
    let b = s.new_var();
    let c = s.new_var();
    s.add_clause([Lit::neg(a), Lit::neg(b)]);
    s.add_clause([Lit::neg(c)]);
    assert_eq!(s.solve(), SolverResult::Sat);
    assert!(
        s.stats().lucky_succeeded >= 1,
        "expected lucky to satisfy without search, got lucky_tried={} succeeded={}",
        s.stats().lucky_tried,
        s.stats().lucky_succeeded,
    );
    assert_model_valid(&[vec![-1, -2], vec![-3]], s.model());
}

/// An instance no uniform/Horn guess cracks but the ordered-with-flip
/// (forward/backward) strategies do: a clause with no negative literal and a
/// clause with no positive literal.
#[test]
fn lucky_ordered_flip_fires() {
    // (a ∨ b) ∧ (¬c ∨ ¬d)
    //   - trivially(false) fails: (a ∨ b) has no negative literal.
    //   - trivially(true)  fails: (¬c ∨ ¬d) has no positive literal.
    //   - horn(false) fails on (a ∨ b); horn(true) fails on (¬c ∨ ¬d).
    // forward/backward with per-variable flip finds a model.
    let mut s = fresh();
    let a = s.new_var();
    let b = s.new_var();
    let c = s.new_var();
    let d = s.new_var();
    s.add_clause([Lit::pos(a), Lit::pos(b)]);
    s.add_clause([Lit::neg(c), Lit::neg(d)]);
    assert_eq!(s.solve(), SolverResult::Sat);
    assert!(
        s.stats().lucky_succeeded >= 1,
        "expected lucky ordered-with-flip to satisfy, got lucky_tried={} succeeded={}",
        s.stats().lucky_tried,
        s.stats().lucky_succeeded,
    );
    assert_model_valid(&[vec![1, 2], vec![-3, -4]], s.model());
}

/// A larger purely-negative-literal formula (lucky-only shape, easy to verify).
#[test]
fn lucky_uniform_negative_many_vars() {
    let mut s = fresh();
    let vars: Vec<_> = (0..20).map(|_| s.new_var()).collect();
    // Each clause is a disjunction of negatives → all-false satisfies.
    for w in vars.chunks(3) {
        let cl: Vec<Lit> = w.iter().map(|&v| Lit::neg(v)).collect();
        s.add_clause(cl);
    }
    assert_eq!(s.solve(), SolverResult::Sat);
    assert!(s.stats().lucky_succeeded >= 1);
    // every var false
    for v in &vars {
        assert_eq!(s.model()[v.index()], LBool::False);
    }
}

// ---------------------------------------------------------------------------
// Discrepancy flip: construct a model that requires flipping exactly one
// variable off the default phase, and confirm lucky still finds a valid model.
// ---------------------------------------------------------------------------

#[test]
fn lucky_flip_produces_valid_model() {
    // (a) ∧ (¬a ∨ b): a must be true (unit), which propagates b=true via the
    // second clause. A uniform all-false guess conflicts on (a) and must flip.
    let mut s = fresh();
    let a = s.new_var();
    let b = s.new_var();
    s.add_clause([Lit::pos(a)]);
    s.add_clause([Lit::neg(a), Lit::pos(b)]);
    assert_eq!(s.solve(), SolverResult::Sat);
    assert_model_valid(&[vec![1], vec![-1, 2]], s.model());
    // a=true is forced; b is propagated true.
    assert_eq!(s.model()[a.index()], LBool::True);
    assert_eq!(s.model()[b.index()], LBool::True);
}

// ---------------------------------------------------------------------------
// Disabling lucky: standard search must still solve correctly.
// ---------------------------------------------------------------------------

#[test]
fn lucky_disabled_solves_correctly() {
    let base = SolverConfig::default();
    // SAT case
    {
        let mut s = solver_with_lucky(&base, false);
        let a = s.new_var();
        let b = s.new_var();
        s.add_clause([Lit::pos(a), Lit::pos(b)]);
        s.add_clause([Lit::neg(a), Lit::pos(b)]);
        assert_eq!(s.solve(), SolverResult::Sat);
        assert_eq!(s.stats().lucky_tried, 0);
        assert_model_valid(&[vec![1, 2], vec![-1, 2]], s.model());
    }
    // UNSAT case
    {
        let mut s = solver_with_lucky(&base, false);
        let a = s.new_var();
        s.add_clause([Lit::pos(a)]);
        s.add_clause([Lit::neg(a)]);
        assert_eq!(s.solve(), SolverResult::Unsat);
        assert_eq!(s.stats().lucky_tried, 0);
    }
}

// ---------------------------------------------------------------------------
// Randomized soundness: lucky-on and lucky-off must agree, and any SAT model
// must satisfy the original clauses.
// ---------------------------------------------------------------------------

#[test]
fn lucky_random_soundness_matches_search() {
    use std::cell::RefCell;
    // Deterministic LCG so the test is reproducible without pulling in a rand
    // crate dependency.
    let rng = RefCell::new(0x1234_5678_u64);
    let next = || {
        let mut r = rng.borrow_mut();
        *r = r
            .wrapping_mul(6364136223846793005)
            .wrapping_add(1442695040888963407);
        *r
    };

    for seed_instance in 0..200 {
        let nvars = 4 + (next() % 5) as usize; // 4..8 vars
        let nclauses = 3 + (next() % 8) as usize; // 3..10 clauses

        // Build a random 2- or 3-CNF; remember it as DIMACS ints for validation.
        let mut dimacs: Vec<Vec<i32>> = Vec::new();
        let mut on = solver_with_lucky(&SolverConfig::default(), true);
        let mut off = solver_with_lucky(&SolverConfig::default(), false);
        for _ in 0..nvars {
            let _ = on.new_var();
            let _ = off.new_var();
        }
        for _ in 0..nclauses {
            let width = 2 + (next() % 2) as usize; // 2 or 3 literals
            let mut lits: Vec<i32> = Vec::new();
            let mut used = std::collections::HashSet::new();
            while lits.len() < width {
                let v = 1 + (next() as usize % nvars);
                if used.contains(&v) {
                    continue;
                }
                used.insert(v);
                let sign = if next() & 1 == 0 { 1 } else { -1 };
                lits.push(sign * v as i32);
            }
            dimacs.push(lits.clone());
            let to_lit = |d: i32| {
                let v = d.unsigned_abs() as usize - 1;
                if d > 0 {
                    Lit::pos(oxiz_sat::Var::new(v as u32))
                } else {
                    Lit::neg(oxiz_sat::Var::new(v as u32))
                }
            };
            on.add_clause(lits.iter().map(|&d| to_lit(d)));
            off.add_clause(lits.iter().map(|&d| to_lit(d)));
        }

        let r_on = on.solve();
        let r_off = off.solve();
        assert_eq!(
            r_on, r_off,
            "instance #{seed_instance}: lucky-on and lucky-off disagree (on={:?}, off={:?}, dimacs={:?})",
            r_on, r_off, dimacs
        );
        if r_on == SolverResult::Sat {
            assert_model_valid(&dimacs, on.model());
        }
        let _ = seed_instance;
    }
}

// ---------------------------------------------------------------------------
// Empty / trivial formula: lucky returns early cleanly (no panic).
// ---------------------------------------------------------------------------

#[test]
fn lucky_empty_formula_no_panic() {
    let mut s = fresh();
    let _ = s.new_var();
    // No clauses → trivially SAT. lucky should not panic.
    assert_eq!(s.solve(), SolverResult::Sat);
}
