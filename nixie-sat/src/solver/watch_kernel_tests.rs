use super::*;
use nixie_proof::lrat_check::check_lrat_proof;

fn raw_solver(legacy: bool, reverse: bool, hbr: bool) -> (Solver, Vec<ClauseId>) {
    let mut s = Solver::new();
    s.ensure_vars(5);
    s.propagate_legacy_oracle = legacy;
    s.config.enable_lazy_hyper_binary = hbr;
    let [t, a, b, c, d] = std::array::from_fn(|i| Lit::from_code(2 * i as u32));
    let clauses = [
        [!t, a, b],
        [!t, c, a],
        // Keep the implied literal watched so the t scan yields the whole
        // a -> c -> d chain; an undefined tail would instead move the watch.
        [!t, c, !a],
        [!t, d, !c],
        [!t, !d, b],
        [!t, b, c],
    ];
    let mut ids = Vec::new();
    for mut lits in clauses {
        if reverse {
            lits.swap(0, 1);
        }
        let id = s.clauses.add_original(lits);
        s.attach_watchers(id, lits[0], lits[1]);
        ids.push(id);
    }
    (s, ids)
}

#[test]
fn exhaustive_small_states_preserve_units_moves_conflicts_and_budgets() {
    let mut cases = 0;
    for pattern in 0..81 {
        for reverse in [false, true] {
            for hbr in [false, true] {
                for limit in [None, Some(0), Some(1), Some(4)] {
                    let (mut a, ids) = raw_solver(false, reverse, hbr);
                    let (mut b, _) = raw_solver(true, reverse, hbr);
                    for s in [&mut a, &mut b] {
                        let mut code = pattern;
                        s.trail.new_decision_level();
                        for var in 1..=4 {
                            let literal = Lit::from_code(2 * var);
                            match code % 3 {
                                0 => {}
                                1 => s.trail.assign_decision(literal),
                                2 => s.trail.assign_decision(!literal),
                                _ => unreachable!(),
                            }
                            code /= 3;
                        }
                        while s.trail.next_to_propagate().is_some() {}
                        s.trail.new_decision_level();
                        s.trail.assign_decision(Lit::from_code(0));
                        s.propagate_step_limit = limit;
                        if pattern % 5 == 0 {
                            s.clauses.mark_deleted_raw(ids[0]);
                        }
                    }
                    assert_eq!(a.propagate(), b.propagate());
                    assert_state(&a, &b);
                    for s in [&mut a, &mut b] {
                        s.trail.backtrack_to(0);
                        s.propagate_step_limit = None;
                        s.propagate_aborted = false;
                        s.trail.new_decision_level();
                        s.trail.assign_decision(Lit::from_code(0));
                    }
                    assert_eq!(a.propagate(), b.propagate());
                    assert_state(&a, &b);
                    cases += 1;
                }
            }
        }
    }
    assert_eq!(cases, 1296);
}

#[test]
fn resumption_sees_units_and_preserves_the_unvisited_conflict_tail() {
    for hbr in [false, true] {
        let (mut a, ids) = raw_solver(false, false, hbr);
        let (mut b, _) = raw_solver(true, false, hbr);
        for s in [&mut a, &mut b] {
            s.trail.assign_unit_fact(Lit::from_code(5));
            while s.trail.next_to_propagate().is_some() {}
            s.trail.new_decision_level();
            s.trail.new_decision_level();
            s.trail.assign_decision(Lit::from_code(0));
        }
        assert!(a.use_watch_kernel(false));
        assert!(!b.use_watch_kernel(false));
        let kernel_conflict = a.propagate();
        let legacy_conflict = b.propagate();
        assert_eq!(kernel_conflict, legacy_conflict);
        assert_state(&a, &b);
        assert_eq!(legacy_conflict, Some(ids[4]));
        for code in [2, 6, 8] {
            assert!(a.trail.lit_val(Lit::from_code(code)) > 0);
        }
        let list = a.watches.get(Lit::from_code(0));
        assert_eq!(list.last().map(|w| w.r), a.clauses.ref_of(ids[5]));
        // The second clause sees the first unit and parks with its new true
        // blocker. A scanner that continued with stale values would move it.
        assert_eq!(
            list.iter()
                .find(|w| Some(w.r) == a.clauses.ref_of(ids[1]))
                .map(|w| w.blocker),
            Some(Lit::from_code(2))
        );
    }
}

#[test]
fn first_hole_selects_compaction_and_units_preserve_the_phase() {
    for deleted_hole in [false, true] {
        for reverse in [false, true] {
            let mut s = Solver::new();
            s.ensure_vars(6);
            let [t, yes, no, spare, u0, u1] = std::array::from_fn(|i| Lit::from_code(2 * i as u32));
            // Hits, refreshed first/tail blockers and deleted-but-satisfied
            // watchers on both sides of the first hole; an unvisited deleted
            // watcher follows the conflict and must not be filtered away.
            let entries = [
                ([!t, yes, no], yes, false),
                ([!t, yes, no], no, false),
                ([!t, no, yes], no, false),
                ([!t, yes, no], yes, true),
                ([!t, u0, no], no, false),
                ([!t, yes, no], yes, false),
                ([!t, no, spare], no, deleted_hole),
                ([!t, yes, no], yes, false),
                ([!t, yes, no], no, false),
                ([!t, no, yes], no, false),
                ([!t, yes, no], yes, true),
                ([!t, u1, no], no, false),
                ([!t, no, !yes], no, false),
                ([!t, no, spare], no, true),
            ];
            let mut ids = Vec::new();
            for (mut lits, blocker, deleted) in entries {
                if reverse {
                    lits.swap(0, 1);
                }
                let id = s.clauses.add_original(lits);
                s.attach_watchers(id, lits[0], lits[1]);
                s.watches.get_mut(t).last_mut().expect("attached").blocker = blocker;
                if deleted {
                    s.clauses.mark_deleted_raw(id);
                }
                ids.push(id);
            }
            s.trail.assign_unit_fact(yes);
            s.trail.assign_unit_fact(!no);
            s.trail.new_decision_level();
            s.trail.assign_decision(t);
            let mut watches = core::mem::take(s.watches.get_mut(t));
            let mut cursor = Cursor::default();
            for (literal, reason, read, write) in [(u0, ids[4], 5, 5), (u1, ids[11], 12, 11)] {
                let step =
                    cursor.advance(&mut watches, !t, &s.trail, &mut s.clauses, &mut s.watches);
                assert!(matches!(step, Step::Unit { literal: l, reason: r }
                    if l == literal && r == reason));
                assert_eq!((cursor.read, cursor.write), (read, write));
                s.trail.assign_propagation(literal, reason);
            }
            assert!(matches!(
                cursor.advance(&mut watches, !t, &s.trail, &mut s.clauses, &mut s.watches),
                Step::Conflict(id) if id == ids[12]
            ));
            assert_eq!((cursor.read, cursor.write), (14, 13));
            watches.truncate(cursor.write);
            assert_eq!(
                watches.iter().map(|w| w.r).collect::<Vec<_>>(),
                ids.iter()
                    .enumerate()
                    .filter(|(i, _)| *i != 6)
                    .map(|(_, id)| s.clauses.ref_of(*id).expect("slot"))
                    .collect::<Vec<_>>()
            );
            assert_eq!(watches[12].blocker, no, "unvisited tail is untouched");
            assert_eq!(s.watches.get(!spare).len(), usize::from(!deleted_hole));
        }
    }
}

#[test]
fn prefix_can_finish_conflict_or_remove_its_last_entry() {
    for final_deleted in [false, true] {
        for conflict in [false, true] {
            let mut s = Solver::new();
            s.ensure_vars(3);
            let [t, a, b] = std::array::from_fn(|i| Lit::from_code(2 * i as u32));
            let id = s.clauses.add_original([!t, a, b]);
            s.attach_watchers(id, !t, a);
            s.trail.assign_decision(t);
            if conflict {
                s.trail.assign_decision(!a);
                s.trail.assign_decision(!b);
            } else {
                s.trail.assign_decision(b);
            }
            if final_deleted {
                s.clauses.mark_deleted_raw(id);
            }
            let mut watches = core::mem::take(s.watches.get_mut(t));
            let mut cursor = Cursor::default();
            let step = cursor.advance(&mut watches, !t, &s.trail, &mut s.clauses, &mut s.watches);
            if conflict && !final_deleted {
                assert!(matches!(step, Step::Conflict(reason) if reason == id));
            } else {
                assert!(matches!(step, Step::Done));
            }
            assert_eq!(cursor.read, 1);
            assert_eq!(cursor.write, usize::from(!final_deleted));
            if !final_deleted && !conflict {
                assert_eq!(watches[0].blocker, b);
            }
        }
    }
}

#[test]
fn active_observers_select_the_complete_legacy_loop() {
    let mut s = Solver::new();
    s.ensure_vars(5);
    assert!(s.use_watch_kernel(false));
    assert!(!s.use_watch_kernel(true));
    #[cfg(feature = "bcp-groups")]
    {
        s.enable_watch_group_stats(std::num::NonZeroU64::MIN);
        assert!(!s.use_watch_kernel(false));
        s.watch_group_stats = None;
    }
    #[cfg(feature = "bcp-regions")]
    {
        s.enable_region_stats(std::num::NonZeroU64::MIN)
            .expect("collector");
        assert!(!s.use_watch_kernel(false));
        s.region_stats = None;
    }
    #[cfg(feature = "clause-traffic")]
    {
        s.enable_clause_traffic(std::num::NonZeroU64::MIN);
        assert!(!s.use_watch_kernel(false));
        s.clause_traffic = None;
    }
    assert!(s.use_watch_kernel(false));
}

fn assert_state(a: &Solver, b: &Solver) {
    let ids: Vec<_> = a.clauses.iter_ids().collect();
    assert_eq!(ids, b.clauses.iter_ids().collect::<Vec<_>>());
    assert_eq!(a.clauses.num_slots(), b.clauses.num_slots());
    for index in 0..a.clauses.num_slots() {
        let id = ClauseId::new(index as u32);
        let ca = a.clauses.get(id);
        let cb = b.clauses.get(id);
        assert_eq!(ca.is_some(), cb.is_some());
        let (Some(ca), Some(cb)) = (ca, cb) else {
            continue;
        };
        assert_eq!(ca.lits, cb.lits);
        assert_eq!(ca.lbd, cb.lbd);
        assert_eq!(ca.usage_count, cb.usage_count);
        assert_eq!(ca.activity.to_bits(), cb.activity.to_bits());
        assert_eq!(ca.learned, cb.learned);
        assert_eq!(ca.deleted, cb.deleted);
        assert_eq!(ca.tier, cb.tier);
    }
    assert_eq!(format!("{:?}", a.stats), format!("{:?}", b.stats));
    assert_eq!(format!("{:?}", a.trail), format!("{:?}", b.trail));
    assert_eq!(format!("{:?}", a.watches), format!("{:?}", b.watches));
    assert_eq!(
        format!("{:?}", a.binary_graph),
        format!("{:?}", b.binary_graph)
    );
    assert_eq!(a.subsume_dirty, b.subsume_dirty);
    assert_eq!(a.subsume_dirty_list, b.subsume_dirty_list);
    assert_eq!(a.subsume_rounds_done, b.subsume_rounds_done);
    assert_eq!(a.elim_mark, b.elim_mark);
    assert_eq!(a.elim_mark_count, b.elim_mark_count);
    assert_eq!(a.no_conflict_until, b.no_conflict_until);
    assert_eq!(a.propagate_aborted, b.propagate_aborted);
    assert_eq!(
        (a.ticks_focused, a.ticks_stable),
        (b.ticks_focused, b.ticks_stable)
    );
    assert_eq!(a.trivially_unsat, b.trivially_unsat);
}

fn pair(
    nvars: usize,
    clauses: &[Vec<i32>],
    proof: bool,
) -> (
    Solver,
    Solver,
    Option<crate::proof::LratTranscriptHandle>,
    Option<crate::proof::LratTranscriptHandle>,
) {
    let mut a = Solver::new();
    let mut b = Solver::new();
    b.propagate_legacy_oracle = true;
    a.ensure_vars(nvars);
    b.ensure_vars(nvars);
    let pa = proof.then(|| a.enable_lrat_transcript());
    let pb = proof.then(|| b.enable_lrat_transcript());
    for clause in clauses {
        a.add_clause_dimacs(clause);
        b.add_clause_dimacs(clause);
    }
    (a, b, pa, pb)
}

#[test]
fn rounds_preserve_strengthening_connection_and_budget_exits() {
    // The first dense clause strengthens the second. Its replacement must be
    // connected after the shrink before it can subsume the last clause.
    let clauses = vec![
        vec![1, 2, 3, 4],
        vec![1, 2, 3, -4, 5],
        vec![1, 2, 3, 5, 6, 7],
        vec![-1, -2, -3, -4, -5, -6, -7, -8],
    ];
    for proof in [false, true] {
        for budget in [1, 2, 100_000] {
            let (mut a, mut b, pa, pb) = pair(8, &clauses, proof);
            a.inproc_budgets.window = 1;
            b.inproc_budgets.window = 1;
            a.inproc_budgets.subsume_checks = budget;
            b.inproc_budgets.subsume_checks = budget;
            for round in 0..3 {
                // Explicit dirty marks avoid a vacuous empty later round.
                for code in 0..16 {
                    a.mark_subsume_lit(Lit::from_code(code));
                    b.mark_subsume_lit(Lit::from_code(code));
                }
                let counts = a.subsume_round();
                assert_eq!(counts, b.subsume_round());
                if budget == 100_000 && round == 0 {
                    assert_eq!(counts, (1, 1));
                }
                assert_state(&a, &b);
            }
            assert_eq!(a.solve(), b.solve());
            assert_state(&a, &b);
            if let (Some(pa), Some(pb)) = (pa, pb) {
                a.flush_proof();
                b.flush_proof();
                assert_eq!(pa.snapshot().expect("proof"), pb.snapshot().expect("proof"));
            }
        }
    }
}

fn truth(clauses: &[Vec<i32>], assignment: usize) -> bool {
    clauses.iter().all(|clause| {
        clause.iter().any(|&lit| {
            let value = assignment & (1 << (lit.unsigned_abs() - 1)) != 0;
            value == (lit > 0)
        })
    })
}

#[test]
fn paired_solves_match_truth_models_and_independent_lrat() {
    let mut sat = 0;
    let mut unsat = 0;
    for seed in 0..24u64 {
        let mut rng = seed + 1;
        let mut clauses = Vec::new();
        for _ in 0..(40 + seed as usize * 8) {
            let mut clause: Vec<i32> = Vec::new();
            while clause.len() < 4 {
                rng ^= rng << 13;
                rng ^= rng >> 7;
                rng ^= rng << 17;
                let var = 1 + (rng % 8) as i32;
                let lit = if rng & 256 != 0 { var } else { -var };
                if !clause.iter().any(|old| old.abs() == var) {
                    clause.push(lit);
                }
            }
            clauses.push(clause);
        }
        let expected = if (0..256).any(|assignment| truth(&clauses, assignment)) {
            sat += 1;
            SolverResult::Sat
        } else {
            unsat += 1;
            SolverResult::Unsat
        };
        for proof in [false, true] {
            let (mut a, mut b, pa, pb) = pair(8, &clauses, proof);
            // Exercise actual subsumption before ordinary CDCL and
            // any further inprocessing rounds; both arms get the same budget.
            a.stats.propagations = 100_000;
            b.stats.propagations = 100_000;
            assert_eq!(a.subsume_round(), b.subsume_round());
            assert_state(&a, &b);
            assert_eq!(a.solve(), expected, "seed {seed}");
            assert_eq!(b.solve(), expected, "seed {seed}");
            assert_state(&a, &b);
            assert_eq!(a.model(), b.model());
            if expected == SolverResult::Sat {
                assert!(clauses.iter().all(|clause| clause.iter().any(|&lit| {
                    let value = a.model_value(Var::new(lit.unsigned_abs() - 1));
                    if lit > 0 {
                        value.is_true()
                    } else {
                        value.is_false()
                    }
                })));
            }
            if let (Some(pa), Some(pb)) = (pa, pb) {
                a.flush_proof();
                b.flush_proof();
                let trace = pa.snapshot().expect("complete proof");
                assert_eq!(trace, pb.snapshot().expect("complete proof"));
                assert_eq!(trace.original_clauses, clauses);
                if expected == SolverResult::Unsat {
                    let checked = check_lrat_proof(&clauses, &trace.proof);
                    assert!(checked.verified, "seed {seed}: {checked:?}");
                }
            }
        }
    }
    assert!(sat > 0 && unsat > 0, "SAT {sat}, UNSAT {unsat}");
}
