//! Fault-injection regressions for the optional minimization proof search.
//! These exercise invalid internal reasons directly; they are not evidence of
//! a wrong answer from a well-formed input or a reachable retirement bug.

use super::*;

#[derive(Clone, Copy, Debug)]
enum BadReason {
    Missing,
    Deleted,
    Compacted,
    MissingHead,
    OppositeHead,
    BothHeads,
    Cyclic,
    TrueAntecedent,
    UnassignedAntecedent,
}

const BAD_REASONS: [BadReason; 9] = [
    BadReason::Missing,
    BadReason::Deleted,
    BadReason::Compacted,
    BadReason::MissingHead,
    BadReason::OppositeHead,
    BadReason::BothHeads,
    BadReason::Cyclic,
    BadReason::TrueAntecedent,
    BadReason::UnassignedAntecedent,
];

/// a => b => c at level 1, with an unrelated UIP at level 2.
/// The candidate lemma is (!u | !a | !c); a is already kept, so c is
/// removable exactly when its entire reason path to a can be justified.
fn fixture(lrat: bool, bad: Option<(BadReason, bool)>) -> (Solver, [Var; 4]) {
    let mut solver = Solver::new();
    let a = solver.new_var();
    let b = solver.new_var();
    let c = solver.new_var();
    let u = solver.new_var();
    let unassigned = solver.new_var();
    let bc = solver.clauses.add_original([Lit::neg(a), Lit::pos(b)]);
    let cc = solver.clauses.add_original([Lit::pos(c), Lit::neg(b)]);
    solver.trail.new_decision_level();
    solver.trail.assign_decision(Lit::pos(a));
    solver.trail.assign_propagation(Lit::pos(b), bc);
    solver.trail.assign_propagation(Lit::pos(c), cc);
    solver.trail.new_decision_level();
    solver.trail.assign_decision(Lit::pos(u));
    solver.current_conflict_level = 2;
    solver.seen_level_count.resize(3, 0);
    solver.seen_level_count[1] = 2;
    solver.seen_level_trail.resize(3, 0);
    solver.seen_level_trail[1] = 0;
    solver.lrat = lrat;
    solver.mf_set(a, MF_KEEP);
    solver.learnt = [Lit::neg(u), Lit::neg(a), Lit::neg(c)]
        .into_iter()
        .collect();

    if let Some((kind, nested)) = bad {
        let (var, valid) = if nested { (b, bc) } else { (c, cc) };
        let cid = match kind {
            BadReason::Missing => {
                solver.clauses.remove(valid);
                ClauseId::new(u32::MAX - 1)
            }
            BadReason::Deleted | BadReason::Compacted => {
                // Deliberately bypass Solver's live-reason retirement guard.
                solver.clauses.remove(valid);
                if matches!(kind, BadReason::Compacted) {
                    solver.clauses.compact_arena_forced(&mut solver.watches);
                }
                valid
            }
            BadReason::MissingHead => solver.clauses.add_original([Lit::neg(a)]),
            BadReason::OppositeHead => solver.clauses.add_original([Lit::neg(a), Lit::neg(var)]),
            BadReason::BothHeads => solver.clauses.add_original([Lit::pos(var), Lit::neg(var)]),
            BadReason::Cyclic => solver.clauses.add_original([Lit::pos(var), Lit::neg(c)]),
            BadReason::TrueAntecedent => solver.clauses.add_original([Lit::pos(var), Lit::pos(a)]),
            BadReason::UnassignedAntecedent => solver
                .clauses
                .add_original([Lit::pos(var), Lit::neg(unassigned)]),
        };
        solver.trail.set_reason(var, Reason::Propagation(cid));
    }
    (solver, [a, b, c, u])
}

fn removable(solver: &mut Solver, lit: Lit) -> bool {
    if solver.lrat {
        solver.minimize_literal_lrat(lit, 0)
    } else {
        solver.minimize_literal_plain(lit, 0)
    }
}

#[test]
fn minimization_rejects_invalid_root_reasons_in_both_modes() {
    for lrat in [false, true] {
        for kind in BAD_REASONS {
            let (mut solver, [_, _, c, _]) = fixture(lrat, Some((kind, false)));
            assert!(
                !removable(&mut solver, Lit::pos(c)),
                "{kind:?}, LRAT={lrat}"
            );
            assert_eq!(solver.mf_get(c) & MF_REMOVABLE, 0);
        }
    }
}

#[test]
fn minimization_rejects_invalid_descendant_reasons_in_both_modes() {
    for lrat in [false, true] {
        for kind in BAD_REASONS {
            let (mut solver, [_, b, c, _]) = fixture(lrat, Some((kind, true)));
            assert!(
                !removable(&mut solver, Lit::pos(c)),
                "{kind:?}, LRAT={lrat}"
            );
            assert_eq!(solver.mf_get(c) & MF_REMOVABLE, 0);
            assert_eq!(solver.mf_get(b) & MF_REMOVABLE, 0);
            assert_ne!(solver.mf_get(c) & MF_POISON, 0);
        }
    }
}

#[test]
fn lrat_minimization_keeps_unjustified_literals_and_adds_no_chain() {
    for kind in BAD_REASONS {
        for nested in [false, true] {
            let (mut solver, [a, _, _, _]) = fixture(true, Some((kind, nested)));
            solver.mf_unset(a, MF_KEEP);
            let original = solver.learnt.clone();
            solver.minimize_clause_lrat();
            assert_eq!(solver.learnt, original, "{kind:?}, nested={nested}");
            assert!(solver.lrat_chain.is_empty());
            assert!(solver.mini_chain.is_empty());
            assert!(solver.lrat_flags.iter().all(|&flags| flags == 0));
        }
    }
}

#[test]
fn minimization_valid_chain_agrees_in_both_modes() {
    for lrat in [false, true] {
        let (mut solver, [a, b, c, _]) = fixture(lrat, None);
        assert!(removable(&mut solver, Lit::pos(c)));
        assert_ne!(solver.mf_get(b) & MF_REMOVABLE, 0);
        assert_ne!(solver.mf_get(c) & MF_REMOVABLE, 0);
        assert_ne!(solver.mf_get(a) & MF_KEEP, 0);
    }
}

#[test]
fn shrink_minimization_keeps_literals_with_invalid_reasons() {
    for lrat in [false, true] {
        for kind in BAD_REASONS {
            for nested in [false, true] {
                let (mut solver, [a, _, c, u]) = fixture(lrat, Some((kind, nested)));
                solver.mf_unset(a, MF_KEEP);
                let mut bumped = SmallVec::new();
                solver.shrink_and_minimize_clause(&mut bumped);
                assert_eq!(
                    solver.learnt.len(),
                    3,
                    "{kind:?}, nested={nested}, LRAT={lrat}"
                );
                assert!(solver.learnt.contains(&Lit::neg(a)));
                assert!(solver.learnt.contains(&Lit::neg(c)));
                assert_eq!(solver.learnt[0], Lit::neg(u));
                assert!(solver.lrat_chain.is_empty());
                assert!(solver.lrat_flags.iter().all(|&flags| flags == 0));
            }
        }
    }
}

#[test]
fn minimization_does_not_accept_false_or_unassigned_base_cases() {
    for lrat in [false, true] {
        let (mut solver, [a, _, _, _]) = fixture(lrat, None);
        // KEEP does not justify substituting the wrong polarity.
        assert!(!removable(&mut solver, Lit::neg(a)));
        // Unassigned variables have level 0, but are not root facts.
        let unassigned = Var::new(4);
        assert!(!removable(&mut solver, Lit::pos(unassigned)));
    }
}

#[test]
fn minimized_clause_preserves_a_countermodel_when_reason_is_unavailable() {
    for lrat in [false, true] {
        for kind in [BadReason::Missing, BadReason::Deleted, BadReason::Compacted] {
            let (mut solver, [a, b, c, u]) = fixture(lrat, Some((kind, false)));
            solver.mf_unset(a, MF_KEEP);
            // With c's reason removed, a=b=u=true, c=false satisfies every
            // live premise and (!u | !a | !c), but falsifies (!u | !a).
            // Thus dropping !c would be a strictly unjustified strengthening.
            let satisfies = |clause: &[Lit]| {
                clause.iter().any(|lit| {
                    let value = lit.var() != c;
                    value == lit.is_pos()
                })
            };
            assert!(satisfies(&solver.learnt));
            assert!(!satisfies(&[Lit::neg(u), Lit::neg(a)]));
            assert!(solver.clauses.iter_ids().all(|cid| {
                solver
                    .clauses
                    .get(cid)
                    .is_some_and(|clause| clause.deleted || satisfies(clause.lits))
            }));
            assert!(satisfies(&[Lit::neg(a), Lit::pos(b)]));
            if lrat {
                solver.minimize_clause_lrat();
            } else {
                let mut bumped = SmallVec::new();
                solver.shrink_and_minimize_clause(&mut bumped);
            }
            assert!(satisfies(&solver.learnt), "{kind:?}, LRAT={lrat}");
        }
    }
}

#[test]
fn valid_chain_depth_limit_and_flags_agree_between_minimizers() {
    for length in [1, 2, 31, 32, 33, 100, 101, 102, 150] {
        let build = |lrat| {
            let mut solver = Solver::new();
            let vars: Vec<_> = (0..length + 2).map(|_| solver.new_var()).collect();
            solver.trail.new_decision_level();
            solver.trail.assign_decision(Lit::pos(vars[0]));
            for i in 1..=length {
                let mut lits = [Lit::neg(vars[i - 1]), Lit::pos(vars[i])];
                if i % 2 == 0 {
                    lits.swap(0, 1);
                }
                let reason = solver.clauses.add_original(lits);
                solver.trail.assign_propagation(Lit::pos(vars[i]), reason);
            }
            solver.trail.new_decision_level();
            solver.trail.assign_decision(Lit::pos(vars[length + 1]));
            solver.current_conflict_level = 2;
            solver.seen_level_count[1] = 2;
            solver.seen_level_trail[1] = 0;
            solver.mf_set(vars[0], MF_KEEP);
            solver.lrat = lrat;
            (solver, Lit::pos(vars[length]))
        };
        let (mut plain, lit) = build(false);
        let (mut lrat, _) = build(true);
        let actual = removable(&mut plain, lit);
        assert_eq!(actual, removable(&mut lrat, lit), "length={length}");
        assert_eq!(actual, length <= 101, "length={length}");
        assert_eq!(plain.lrat_flags, lrat.lrat_flags, "length={length}");
        assert_eq!(plain.lrat_minimized, lrat.lrat_minimized, "length={length}");
    }
}
