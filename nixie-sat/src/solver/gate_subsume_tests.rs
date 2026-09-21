//! Tests for gate-modulo forward subsumption (`gate_subsume.rs`) — the
//! kissat `forward_subsume_matching_clauses` port inside the equivalence
//! closure.  All arms drive the gate through `test_knobs`.

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
fn sorted_subset_scan_is_exact() {
    // Direct pins of the merge scan (the exhausted-`big` fall-through was
    // a real bug in the first draft — this test would have caught it).
    let s = |codes: &[u32]| -> SmallVec<[Lit; 8]> {
        let mut v: SmallVec<[Lit; 8]> = codes.iter().map(|&c| Lit::from_code(c)).collect();
        v.sort_unstable_by_key(|l| l.code());
        v
    };
    // code 0 = pos(v0), 1 = neg(v0), 2 = pos(v1), ...
    assert!(super::gate_subsume::sorted_subset(&s(&[]), &s(&[])));
    assert!(super::gate_subsume::sorted_subset(&s(&[]), &s(&[0, 2])));
    assert!(!super::gate_subsume::sorted_subset(&s(&[0]), &s(&[])));
    assert!(!super::gate_subsume::sorted_subset(&s(&[0]), &s(&[2])));
    assert!(super::gate_subsume::sorted_subset(&s(&[0]), &s(&[0, 2])));
    assert!(super::gate_subsume::sorted_subset(
        &s(&[0, 2]),
        &s(&[0, 2, 4])
    ));
    assert!(!super::gate_subsume::sorted_subset(
        &s(&[0, 4]),
        &s(&[0, 2])
    ));
    // Superset, not subset:
    assert!(!super::gate_subsume::sorted_subset(
        &s(&[0, 2, 4]),
        &s(&[0, 2])
    ));
}

#[test]
fn strictly_smaller_set_subsumes_through_the_classes() {
    // b ≡ a; d = (a ∨ x); c = (b ∨ x ∨ y) — c's canonical set is
    // {a, x, y}, d's is {a, x}: a STRICT subset, so the rewrite's
    // exact-duplicate retire leaves c behind and only the matching pass
    // retires it.  The y-fillers make y the victim's *most*-occurring
    // repr so the probe's least-occurring choice lands on the shared x
    // (the pass is deliberately incomplete: it walks one list per
    // victim, kissat parity — see the module doc).
    let build = || {
        let mut s = Solver::default();
        for _ in 0..6 {
            s.new_var();
        }
        s.add_clause([l(0, false), l(1, true)]); // ¬a ∨ b
        s.add_clause([l(0, true), l(1, false)]); // a ∨ ¬b
        s.add_clause([l(0, true), l(2, true)]); // d = (a ∨ x)
        s.add_clause([l(1, true), l(2, true), l(3, true)]); // c = (b ∨ x ∨ y)
        // y-fillers (plain satisfiable clauses making y common).
        s.add_clause([l(3, true), l(4, true)]);
        s.add_clause([l(3, true), l(4, false)]);
        s.add_clause([l(3, true), l(5, true)]);
        s.add_clause([l(3, true), l(5, false)]);
        s
    };
    test_knobs::set_gate_subsume(Some(true));
    // The volume floor guards corpus behavior; the direct fixture is far
    // below it — bypass for the unit-level semantics pin.
    test_knobs::set_gate_subsume_min(Some(0));
    let mut armed = build();
    assert_eq!(
        armed.substitute_equivalent_literals_round(),
        crate::solver::equiv::SubstOutcome::Ok
    );
    assert_eq!(
        armed.stats.gate_subsumed, 1,
        "the strict-subset victim retired through the classes"
    );
    assert_eq!(armed.solve(), crate::SolverResult::Sat);
    test_knobs::set_gate_subsume(None);
    test_knobs::set_gate_subsume_min(None);

    let mut unarmed = build();
    assert_eq!(
        unarmed.substitute_equivalent_literals_round(),
        crate::solver::equiv::SubstOutcome::Ok
    );
    assert_eq!(
        unarmed.stats.gate_subsumed, 0,
        "default off: the pass never runs"
    );
    assert_eq!(unarmed.solve(), crate::SolverResult::Sat);
}

#[test]
fn armed_pass_preserves_models_on_gate_structure() {
    // End-to-end soundness screen on gate-twin structure: same verdicts
    // with and without the pass, and the returned model satisfies every
    // ORIGINAL clause in both worlds (the wrong-model failure shape the
    // post-substitution sequence's ≈1/15k interaction is about).
    let build = || {
        let mut s = Solver::default();
        for _ in 0..8 {
            s.new_var();
        }
        // (¬a ∨ ¬b ∨ o), (¬o ∨ a), (¬o ∨ b) for o4 and o5 (o4 ≡ o5 twins).
        s.add_clause([l(0, false), l(1, false), l(4, true)]);
        s.add_clause([l(4, false), l(0, true)]);
        s.add_clause([l(4, false), l(1, true)]);
        s.add_clause([l(0, false), l(1, false), l(5, true)]);
        s.add_clause([l(5, false), l(0, true)]);
        s.add_clause([l(5, false), l(1, true)]);
        // Satisfiable constraints.
        s.add_clause([l(0, true), l(2, true)]);
        s.add_clause([l(3, true), l(6, true)]);
        s
    };
    let check_model = |s: &Solver| {
        for cid in s.clauses.iter_ids() {
            let Some(c) = s.clauses.get(cid) else {
                continue;
            };
            if c.deleted || c.learned {
                continue;
            }
            let sat = c
                .lits
                .iter()
                .any(|&lit| matches!(s.model_value(lit.var()), crate::LBool::True) == lit.is_pos());
            assert!(sat, "original clause {cid:?} unsatisfied by the model");
        }
    };
    let mut unarmed = build();
    assert_eq!(unarmed.solve(), crate::SolverResult::Sat);
    check_model(&unarmed);

    test_knobs::set_gate_subsume(Some(true));
    let mut armed = build();
    assert_eq!(armed.solve(), crate::SolverResult::Sat);
    check_model(&armed);
    test_knobs::set_gate_subsume(None);
}

#[test]
fn armed_pass_preserves_verdicts_on_equivalence_chains() {
    // The fold_bve_skip_tests chain fixture, with the pass armed on top
    // of the full study stack (SSR + pre-search + gate subsumption).
    let build = || {
        let mut s = Solver::default();
        for _ in 0..8 {
            s.new_var();
        }
        for i in 0..4 {
            s.add_clause([l(i, true), l(i + 1, false)]);
            s.add_clause([l(i, false), l(i + 1, true)]);
        }
        for i in 0..4 {
            s.add_clause([l(i, true), l(4, true), l(5, false)]);
            s.add_clause([l(i, true), l(5, true), l(6, false)]);
        }
        s
    };
    let unarmed = build().solve();
    test_knobs::set_ssr_binaries(Some(true));
    test_knobs::set_els_presearch(Some(true));
    test_knobs::set_gate_subsume(Some(true));
    let armed = build().solve();
    assert_eq!(unarmed, armed);
    test_knobs::set_ssr_binaries(None);
    test_knobs::set_els_presearch(None);
    test_knobs::set_gate_subsume(None);
}

#[test]
fn volume_floor_skips_the_pass_without_touching_state() {
    // Below the floor the pass must be a pure no-op: the round's outcome
    // then matches the fold-only arm exactly (the rewrite's own paths do
    // all the retiring).
    let build = || {
        let mut s = Solver::default();
        for _ in 0..6 {
            s.new_var();
        }
        s.add_clause([l(0, false), l(1, true)]);
        s.add_clause([l(0, true), l(1, false)]);
        s.add_clause([l(0, true), l(2, true)]);
        s.add_clause([l(1, true), l(2, true), l(3, true)]);
        s
    };
    test_knobs::set_gate_subsume(Some(true));
    // Default floor (64) >> this fixture's candidate count.  (The
    // equivalence binaries themselves are binary-graph edges, not arena
    // clauses, so `num_original` never counted them — the pass's zero is
    // the whole pin.)
    let mut guarded = build();
    assert_eq!(
        guarded.substitute_equivalent_literals_round(),
        crate::solver::equiv::SubstOutcome::Ok
    );
    assert_eq!(
        guarded.stats.gate_subsumed, 0,
        "guarded pass retires nothing"
    );
    assert_eq!(guarded.solve(), crate::SolverResult::Sat);
    test_knobs::set_gate_subsume(None);
}
