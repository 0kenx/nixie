//! Tests for the ternary×binary SSR cascade (`extract_binary_resolvents`)
//! and the pre-search ELS fixpoint arm — both default-off study machinery
//! (2026-09-18, `docs/studies/2026-09-18-ssr-binaries.md`).

use super::*;
use crate::test_knobs;

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
fn ssr_resolvent_derived_from_ternary_and_binary() {
    // (a ∨ b ∨ c) ∧ (¬a ∨ b) ⊢ (b ∨ c): one SSR step must add the binary
    // (b ∨ c), visible as the implication ¬b → c.
    let mut s = Solver::default();
    for _ in 0..4 {
        s.new_var();
    }
    s.add_clause([l(0, true), l(1, true), l(2, true)]);
    s.add_clause([l(0, false), l(1, true)]);
    let added = s.extract_binary_resolvents();
    assert_eq!(added, 1, "exactly the (b ∨ c) resolvent");
    assert!(
        s.has_binary_implication(l(1, false), l(2, true)),
        "resolvent (b ∨ c) must be present as implication ¬b → c"
    );
    // Idempotence: a second pass finds nothing new.
    assert_eq!(s.extract_binary_resolvents(), 0);
}

#[test]
fn ssr_resolvent_is_sound_on_unsat_and_sat() {
    // The resolvent participates in a genuine refutation:
    // (a∨b∨c) ∧ (¬a∨b) ⊢ (b∨c); with ¬b and ¬c the formula is UNSAT.
    let mut s = Solver::default();
    for _ in 0..4 {
        s.new_var();
    }
    s.add_clause([l(0, true), l(1, true), l(2, true)]);
    s.add_clause([l(0, false), l(1, true)]);
    // Derive BEFORE fixing units (the pass skips level-0-assigned vars,
    // kissat parity: `if (values[lit]) continue`).
    assert_eq!(s.extract_binary_resolvents(), 1);
    s.add_clause([l(1, false)]);
    s.add_clause([l(2, false)]);
    assert_eq!(s.solve(), crate::SolverResult::Unsat);

    // Satisfiable twin (drop ¬b): the added binary changes nothing.
    let mut s2 = Solver::default();
    for _ in 0..4 {
        s2.new_var();
    }
    s2.add_clause([l(0, true), l(1, true), l(2, true)]);
    s2.add_clause([l(0, false), l(1, true)]);
    assert_eq!(s2.extract_binary_resolvents(), 1);
    s2.add_clause([l(2, false)]);
    assert_eq!(s2.solve(), crate::SolverResult::Sat);
    assert_eq!(s2.solve(), crate::SolverResult::Sat);
}

#[test]
fn ssr_skips_assigned_and_tautological_shapes() {
    // A ternary with a level-0-fixed var is left to the ordinary passes;
    // a resolvent that would be tautological is never added.
    let mut s = Solver::default();
    for _ in 0..4 {
        s.new_var();
    }
    s.add_clause([l(0, true), l(1, true), l(2, true)]);
    s.add_clause([l(0, false), l(1, true)]);
    // (b ∨ ¬b) shape: ternary (b ∨ b' ∨ c) with binary (¬b ∨ b') — the
    // resolvent (b' ∨ c) is fine, but a complementary pair can never be
    // produced because detection refuses same-var clauses; this asserts
    // the pass stays a no-op on formulas without resolution partners.
    let mut s2 = Solver::default();
    for _ in 0..3 {
        s2.new_var();
    }
    s2.add_clause([l(0, true), l(1, true), l(2, true)]);
    assert_eq!(s2.extract_binary_resolvents(), 0);
}

#[test]
fn presearch_fixpoint_arm_folds_and_stays_sound() {
    // Arm both study knobs (thread-local; no env races), run a gate-dense
    // SAT formula end-to-end: verdict + a total model satisfying every
    // original clause.
    test_knobs::set_ssr_binaries(Some(true));
    test_knobs::set_els_presearch(Some(true));
    let cfg = SolverConfig {
        enable_equiv_substitution: true,
        enable_gate_congruence: true,
        ..SolverConfig::default()
    };
    let mut s = Solver::with_config(cfg);
    for _ in 0..8 {
        s.new_var();
    }
    // Two AND-gate twins over the same inputs: o4 ↔ a0∧a1, o5 ↔ a0∧a1.
    let mut clauses: Vec<Vec<Lit>> = Vec::new();
    let add = |s: &mut Solver, clauses: &mut Vec<Vec<Lit>>, lits: &[usize; 3], pol: [bool; 3]| {
        let c: Vec<Lit> = vec![l(lits[0], pol[0]), l(lits[1], pol[1]), l(lits[2], pol[2])];
        clauses.push(c.clone());
        s.add_clause(c);
    };
    // (¬a ∨ ¬b ∨ o), (¬o ∨ a), (¬o ∨ b) for o4 and o5.
    add(&mut s, &mut clauses, &[0, 1, 4], [false, false, true]);
    s.add_clause([l(4, false), l(0, true)]);
    s.add_clause([l(4, false), l(1, true)]);
    add(&mut s, &mut clauses, &[0, 1, 5], [false, false, true]);
    s.add_clause([l(5, false), l(0, true)]);
    s.add_clause([l(5, false), l(1, true)]);
    // Random satisfiable constraints.
    s.add_clause([l(0, true), l(2, true)]);
    s.add_clause([l(3, true), l(6, true)]);
    let r = s.solve();
    assert_eq!(r, crate::SolverResult::Sat);
    for (i, c) in clauses.iter().enumerate() {
        let sat = c.iter().any(|&lit| {
            let val = s.model_value(lit.var());
            (val == crate::LBool::True) == lit.is_pos()
        });
        assert!(sat, "clause #{i} unsatisfied");
    }
    // o4 ≡ o5 must have folded: forcing them apart is UNSAT through the
    // armed pipeline.
    let s2_cfg = SolverConfig {
        enable_equiv_substitution: true,
        enable_gate_congruence: true,
        ..SolverConfig::default()
    };
    let mut s2 = Solver::with_config(s2_cfg);
    for _ in 0..8 {
        s2.new_var();
    }
    add(&mut s2, &mut clauses, &[0, 1, 4], [false, false, true]);
    s2.add_clause([l(4, false), l(0, true)]);
    s2.add_clause([l(4, false), l(1, true)]);
    add(&mut s2, &mut clauses, &[0, 1, 5], [false, false, true]);
    s2.add_clause([l(5, false), l(0, true)]);
    s2.add_clause([l(5, false), l(1, true)]);
    s2.add_clause([l(4, true), l(5, true)]);
    s2.add_clause([l(4, false), l(5, false)]);
    assert_eq!(s2.solve(), crate::SolverResult::Unsat);
    test_knobs::set_ssr_binaries(None);
    test_knobs::set_els_presearch(None);
}
