use super::super::PropagationWork;
use super::*;

#[test]
fn ledger_counts_live_and_deleted_misses_without_visiting_conflict_suffix() {
    for legacy in [false, true] {
        for deleted_hole in [false, true] {
            for reverse in [false, true] {
                let mut s = Solver::new();
                s.ensure_vars(6);
                s.propagate_legacy_oracle = legacy;
                let [t, yes, no, spare, u0, u1] =
                    std::array::from_fn(|i| Lit::from_code(2 * i as u32));
                // Five blocker hits, eight reads, two units separated by the
                // first hole, and a final conflict followed by an unvisited entry.
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
                while s.trail.next_to_propagate().is_some() {}
                s.trail.new_decision_level();
                s.trail.assign_decision(t);
                assert_eq!(s.use_watch_kernel(false), !legacy);
                assert_eq!(s.propagate(), Some(ids[12]));
                let long_lines = match core::mem::size_of::<Watcher>() {
                    8 => 1,
                    12 => 2, // Identity-bearing observers are enabled together.
                    size => panic!("unaccounted watcher size {size}"),
                };
                let expected = PropagationWork {
                    dequeued: 1,
                    started: 1,
                    long_lists: 1,
                    long_list_lines: long_lines,
                    long_visits: 13,
                    clause_reads: 8,
                    deleted: u64::from(deleted_hole),
                    first_satisfied: 2,
                    tail_probes: if deleted_hole { 5 } else { 6 },
                    tail_satisfied: 2,
                    watch_moves: u64::from(!deleted_hole),
                    long_assignments: 2,
                    long_conflicts: 1,
                    ..PropagationWork::default()
                };
                assert_eq!(s.stats.propagation_work, expected);
                assert_eq!(expected.blocker_hits(), 5);
                assert_eq!(
                    expected.estimated_ticks(),
                    u128::from(long_lines) + if deleted_hole { 11 } else { 12 }
                );
                assert_eq!(s.search_ticks(), (2, 0));
                assert_eq!(s.watches.get(t).len(), 13);
                assert_eq!(s.trail.next_to_propagate(), Some(t));
            }
        }
    }
}

#[test]
fn ledger_counts_both_binary_spans_and_early_conflict_replays() {
    for overflow_conflict in [false, true] {
        let mut s = Solver::new();
        s.ensure_vars(4);
        let [t, yes, u0, u1] = std::array::from_fn(|i| Lit::from_code(2 * i as u32));
        for implied in [yes, u0, if overflow_conflict { yes } else { !yes }] {
            let id = s.clauses.add_original([!t, implied]);
            s.attach_watchers(id, !t, implied);
        }
        let id = s.clauses.add_original([!t, u0, u1]);
        s.attach_watchers(id, !t, u0);
        s.rebuild_watches_and_binary_graph();
        for implied in [u1, !yes] {
            let id = s.clauses.add_original([!t, implied]);
            s.attach_watchers(id, !t, implied);
        }
        s.trail.assign_unit_fact(yes);
        while s.trail.next_to_propagate().is_some() {}
        s.trail.new_decision_level();
        s.trail.assign_decision(t);
        assert!(s.propagate().is_some());
        let expected = PropagationWork {
            dequeued: 1,
            started: 1,
            binary_lists: 1,
            binary_primary_visits: 3,
            binary_overflow_visits: if overflow_conflict { 2 } else { 0 },
            binary_assignments: if overflow_conflict { 2 } else { 1 },
            binary_conflicts: 1,
            binary_list_lines: 2,
            ..PropagationWork::default()
        };
        assert_eq!(s.stats.propagation_work, expected);
        assert_eq!(
            expected.estimated_ticks(),
            if overflow_conflict { 5 } else { 4 }
        );
        // The existing scheduling charge is after the binary pass. The new
        // ledger still counts work on this exit without altering that charge.
        assert_eq!(s.search_ticks(), (0, 0));
        assert!(s.propagate().is_some());
        let replayed = s.stats.propagation_work;
        assert_eq!(replayed.binary_assignments, expected.binary_assignments);
        assert_eq!(replayed.binary_primary_visits, 6);
        assert_eq!(
            replayed.binary_overflow_visits,
            expected.binary_overflow_visits * 2
        );
        assert_eq!(replayed.binary_conflicts, 2);
        assert_eq!(replayed.long_visits, 0);
        assert_eq!(replayed.estimated_ticks(), expected.estimated_ticks() + 3);
    }
}

#[test]
fn ledger_distinguishes_empty_scans_from_budget_aborts() {
    for budget in [0, 1] {
        let mut s = Solver::new();
        s.ensure_vars(1);
        s.trail.assign_decision(Lit::from_code(0));
        s.propagate_step_limit = Some(budget);
        assert_eq!(s.propagate(), None);
        assert_eq!(
            s.stats.propagation_work,
            PropagationWork {
                dequeued: 1,
                started: budget,
                ..PropagationWork::default()
            }
        );
        assert_eq!(
            s.stats.propagation_work.estimated_ticks(),
            u128::from(budget)
        );
        assert_eq!(s.search_ticks(), (budget, 0));
        s.reset();
        assert_eq!(s.stats.propagation_work, PropagationWork::default());
    }
}

#[cfg(feature = "std")]
#[test]
fn rayon_workers_own_independent_ledgers() {
    use rayon::prelude::*;
    let counts: Vec<_> = (0..8u32)
        .into_par_iter()
        .map(|n| {
            let mut s = Solver::new();
            s.ensure_vars(n as usize);
            for i in 0..n {
                s.trail.assign_unit_fact(Lit::from_code(2 * i));
            }
            assert_eq!(s.propagate(), None);
            s.stats.propagation_work
        })
        .collect();
    for (n, work) in counts.into_iter().enumerate() {
        assert_eq!(
            work,
            PropagationWork {
                dequeued: n as u64,
                started: n as u64,
                ..PropagationWork::default()
            }
        );
    }
}

#[test]
fn line_estimates_round_each_span_and_tick_sum_is_wide() {
    use super::super::propagation_work::list_lines;
    let watcher_bytes = core::mem::size_of::<Watcher>();
    assert_eq!(core::mem::size_of::<(Lit, ClauseId)>(), 8);
    for (len, lines8, lines12) in [
        (0, 0, 0),
        (1, 1, 1),
        (10, 1, 1),
        (11, 1, 2),
        (16, 1, 2),
        (17, 2, 2),
        (22, 2, 3),
    ] {
        let watch_lines = match watcher_bytes {
            8 => lines8,
            12 => lines12,
            size => panic!("unaccounted watcher size {size}"),
        };
        assert_eq!(list_lines::<Watcher>(len), watch_lines);
        assert_eq!(list_lines::<(Lit, ClauseId)>(len), lines8);
    }
    let work = PropagationWork {
        started: u64::MAX,
        clause_reads: 1,
        ..PropagationWork::default()
    };
    assert_eq!(work.estimated_ticks(), 1u128 << 64);
}

#[test]
fn failed_lucky_work_survives_the_search_counter_rollback() {
    let mut s = Solver::new();
    s.ensure_vars(2);
    let a = Lit::from_code(0);
    let b = Lit::from_code(2);
    // Every assignment is forbidden. Lucky tries both polarities, fails,
    // and restores its snapshots without proving the formula UNSAT.
    for lits in [[a, b], [a, !b], [!a, b], [!a, !b]] {
        let id = s.clauses.add_original(lits);
        s.attach_watchers(id, lits[0], lits[1]);
    }
    assert_eq!(s.lucky_phases(), None);
    assert_eq!(s.stats.lucky_tried, 1);
    assert_eq!(s.stats.propagations, 0);
    assert_eq!(s.search_ticks(), (0, 0));
    let work = s.stats.propagation_work;
    assert!(work.started > 0);
    assert_eq!(work.dequeued, work.started);
    assert!(work.binary_assignments > 0);
    assert!(work.binary_conflicts > 0);
    assert!(work.estimated_ticks() > 0);
}
