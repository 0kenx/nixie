//! Tests for the BVE-after-fold skip policy (`NIXIE_FOLD_BVE_SKIP`) —
//! the 2026-09-21 slice of the SSR-binaries study §5
//! (`docs/studies/2026-09-18-ssr-binaries.md`): when the pre-search ELS
//! fixpoint collapsed the formula beyond the threshold, the unconditional
//! phase-1 elimination is consumed without running.  Default off =
//! bit-identical.  All arms drive the policy through `test_knobs`
//! (the crate denies `unsafe`, so no env mutation here).

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

/// An eliminable pair on *unassigned* variables: `[c ∨ d] ∧ [¬c ∨ e]`
/// resolves to `[d ∨ e]`, so a real phase-1 run eliminates variable c
/// (a unit fixture would instead retire both clauses at level 0 before
/// the eliminator ever connects them).  Uses the CaDiCaL preset because
/// `Solver::default()` ships BVE off.
fn eliminable_solver() -> Solver {
    let mut s = Solver::with_config(crate::ConfigPreset::CaDiCaL.config());
    for _ in 0..4 {
        s.new_var();
    }
    s.add_clause([l(2, true), l(3, true)]);
    s.add_clause([l(2, false), l(1, true)]);
    s
}

#[test]
fn skip_consumes_phase_one_trigger_without_eliminating() {
    test_knobs::set_fold_bve_skip(Some((true, 25)));
    let mut s = eliminable_solver();
    // Fake the fold-collapse bookkeeping the ELS arm would have recorded:
    // 2 of 3 originals retired (67% ≥ 25%).
    s.fold_orig_at_entry = 3;
    s.fold_retired = 2;
    // Arm the phase-1 trigger: conflicts at/over the (lowered) limit.
    s.lim_elim = 0;
    assert!(
        s.eliminating(),
        "phase-1 trigger must be armed at lim_elim=0"
    );
    let _ = s.try_scheduled_elimination();
    assert_eq!(s.elim_phases, 1, "the skip counts the phase as consumed");
    assert_eq!(
        s.stats.bve_eliminated, 0,
        "no resolution ran: nothing was eliminated"
    );
    assert_eq!(s.last_elim_eliminated, 0);
    assert_eq!(s.elim_mark_count, 0, "pending marks were consumed");
    // The trigger must NOT re-fire: eliminating() now needs genuinely new
    // level-0 units or fresh marks (none exist).
    assert!(
        !s.eliminating(),
        "consumed trigger must stay consumed (lim_elim advanced past conflicts)"
    );
    // And the formula still solves correctly.
    assert_eq!(s.solve(), crate::SolverResult::Sat);
    test_knobs::set_fold_bve_skip(None);
}

#[test]
fn policy_off_or_below_threshold_runs_the_phase() {
    // Same solver, policy override off: the phase runs and eliminates var 0.
    test_knobs::set_fold_bve_skip(Some((false, 25)));
    let mut s = eliminable_solver();
    s.fold_orig_at_entry = 3;
    s.fold_retired = 2;
    s.lim_elim = 0;
    let _ = s.try_scheduled_elimination();
    assert_eq!(s.elim_phases, 1);
    assert!(
        s.stats.bve_eliminated >= 1,
        "the real phase-1 eliminated the resolvent variable"
    );

    // Armed but collapse below the threshold: the phase still runs.
    test_knobs::set_fold_bve_skip(Some((true, 90)));
    let mut s2 = eliminable_solver();
    s2.fold_orig_at_entry = 100;
    s2.fold_retired = 20; // 20% < 90%
    s2.lim_elim = 0;
    let _ = s2.try_scheduled_elimination();
    assert_eq!(s2.elim_phases, 1);
    assert!(
        s2.stats.bve_eliminated >= 1,
        "below threshold the phase runs as usual"
    );
    test_knobs::set_fold_bve_skip(None);
}

#[test]
fn zero_fold_recording_never_skips_even_when_armed() {
    // No ELS arm ran (the default world): fold_orig_at_entry == 0 must
    // disarm the policy, not divide by zero.
    test_knobs::set_fold_bve_skip(Some((true, 0)));
    let mut s = eliminable_solver();
    assert_eq!(s.fold_orig_at_entry, 0);
    assert_eq!(s.fold_retired, 0);
    s.lim_elim = 0;
    let _ = s.try_scheduled_elimination();
    assert_eq!(
        s.elim_phases, 1,
        "no fold bookkeeping: the phase runs (zero-denominator guard)"
    );
    assert!(s.stats.bve_eliminated >= 1, "the phase eliminated as usual");
    test_knobs::set_fold_bve_skip(None);
}

#[test]
fn fold_entry_is_recorded_by_the_els_arm() {
    test_knobs::set_els_presearch(Some(true));
    test_knobs::set_ssr_binaries(Some(true));
    // The ssr_binaries_tests gate-twin anatomy, with lucky pre-solving off
    // so the solve reaches the arm's block.  What this pins: the arm
    // records its accounting (the entry denominator); the retirements that
    // drive the ratio are formula-dependent (this toy fixture folds
    // without retiring) — the numerator is exercised end-to-end by the
    // powered experiment on the gate-dense corpus (bv_ILA), where the
    // study measured the fold retiring hundreds of thousands of clauses.
    let cfg = SolverConfig {
        enable_equiv_substitution: true,
        enable_gate_congruence: true,
        // Reach the ELS arm: this fixture is all-true satisfiable, which
        // the lucky pre-solver answers before the arm's block.
        enable_lucky: false,
        ..SolverConfig::default()
    };
    let mut s = Solver::with_config(cfg);
    for _ in 0..8 {
        s.new_var();
    }
    // (¬a ∨ ¬b ∨ o), (¬o ∨ a), (¬o ∨ b) for o4 and o5.
    s.add_clause([l(0, false), l(1, false), l(4, true)]);
    s.add_clause([l(4, false), l(0, true)]);
    s.add_clause([l(4, false), l(1, true)]);
    s.add_clause([l(0, false), l(1, false), l(5, true)]);
    s.add_clause([l(5, false), l(0, true)]);
    s.add_clause([l(5, false), l(1, true)]);
    // A clause that is a tautology once o4 folds onto o5 (o5 ∨ ¬o5 ∨ z).
    s.add_clause([l(4, true), l(5, false), l(6, true)]);
    assert_eq!(s.solve(), crate::SolverResult::Sat);
    assert!(
        s.fold_orig_at_entry >= 7,
        "the ELS arm recorded the originals at entry (got {}) — did the solve reach the arm?",
        s.fold_orig_at_entry
    );
    test_knobs::set_els_presearch(None);
    test_knobs::set_ssr_binaries(None);
}

#[test]
fn armed_policy_preserves_verdicts_on_equivalence_fold_instances() {
    // End-to-end soundness screen: the same equivalence-fold formulas solve
    // to the same verdict with the policy armed (fold + skip) and unarmed.
    let build = || {
        let mut s = Solver::default();
        for _ in 0..8 {
            s.new_var();
        }
        // Two equivalence chains whose fold collapses the formula...
        for i in 0..4 {
            s.add_clause([l(i, true), l(i + 1, false)]);
            s.add_clause([l(i, false), l(i + 1, true)]);
        }
        // ...on top of clauses that retire in the collapse.
        for i in 0..4 {
            s.add_clause([l(i, true), l(4, true), l(5, false)]);
            s.add_clause([l(i, true), l(5, true), l(6, false)]);
        }
        s
    };
    let unarmed = build().solve();
    test_knobs::set_els_presearch(Some(true));
    test_knobs::set_ssr_binaries(Some(true));
    test_knobs::set_fold_bve_skip(Some((true, 25)));
    let armed = build().solve();
    assert_eq!(unarmed, armed);
    test_knobs::set_els_presearch(None);
    test_knobs::set_ssr_binaries(None);
    test_knobs::set_fold_bve_skip(None);
}
