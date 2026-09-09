use super::*;

fn signed_clause(mut pattern: usize) -> Vec<Lit> {
    let mut lits = Vec::new();
    for var in 0..4 {
        match pattern % 3 {
            0 => {}
            1 => lits.push(Lit::from_code(2 * var)),
            2 => lits.push(Lit::from_code(2 * var + 1)),
            _ => unreachable!(),
        }
        pattern /= 3;
    }
    lits
}

#[test]
fn residual_membership_matches_independent_set_conditions() {
    for candidate in 0..81 {
        let candidate = signed_clause(candidate);
        let mut mark = [0; 8];
        for &lit in &candidate {
            mark[lit.index()] = 1;
            mark[lit.negate().index()] = -1;
        }
        for subsumer in 0..81 {
            let subsumer = signed_clause(subsumer);
            let absent: Vec<_> = subsumer
                .iter()
                .copied()
                .filter(|lit| !candidate.contains(lit))
                .collect();
            let expected = match absent.as_slice() {
                [] => ConnectedCheck::Subsumed,
                [lit] if candidate.contains(&lit.negate()) => {
                    ConnectedCheck::Strengthen(lit.negate())
                }
                _ => ConnectedCheck::Mismatch,
            };
            assert_eq!(
                check_connected(subsumer.iter().copied(), &mark, None),
                expected
            );
            for &key in &subsumer {
                let mut payloads = ConnectedPayloads::default();
                let connection = payloads.connect(ClauseId::new(23), &subsumer, key);
                let (id, codes) = payloads.get(connection);
                assert_eq!(id, ClauseId::new(23));
                let result = if mark[key.index()] == 0 {
                    ConnectedCheck::Mismatch
                } else {
                    check_connected(
                        codes.iter().copied().map(Lit::from_code),
                        &mark,
                        (mark[key.index()] < 0).then_some(key),
                    )
                };
                assert_eq!(
                    result, expected,
                    "candidate {candidate:?}, subsumer {subsumer:?}, key {key:?}"
                );
            }
        }
    }
}

#[test]
fn payloads_preserve_full_codes_and_survive_growth_independently() {
    let mut payloads = ConnectedPayloads::default();
    let mut records = Vec::new();
    for len in [2, 3, 8, 9, 100] {
        for omitted in 0..len {
            let mut lits: Vec<_> = (0..len).map(|i| Lit::from_code(u32::MAX - i)).collect();
            let id = ClauseId::new(u32::MAX - len);
            let connection = payloads.connect(id, &lits, lits[omitted as usize]);
            lits.remove(omitted as usize);
            records.push((connection, id, lits));
        }
    }
    for (connection, id, lits) in records {
        let (stored_id, codes) = payloads.get(connection);
        assert_eq!(stored_id, id);
        assert_eq!(codes, lits.iter().map(|lit| lit.code()).collect::<Vec<_>>());
    }
}

fn state_matches(a: &Solver, b: &Solver) {
    assert_eq!(a.clauses.num_slots(), b.clauses.num_slots());
    for index in 0..a.clauses.num_slots() {
        let id = ClauseId::new(index as u32);
        let ca = a.clauses.get(id);
        let cb = b.clauses.get(id);
        assert_eq!(ca.is_some(), cb.is_some());
        if let (Some(ca), Some(cb)) = (ca, cb) {
            assert_eq!(ca.lits, cb.lits);
            assert_eq!(
                (ca.lbd, ca.learned, ca.deleted, ca.tier, ca.usage_count),
                (cb.lbd, cb.learned, cb.deleted, cb.tier, cb.usage_count)
            );
            assert_eq!(ca.activity.to_bits(), cb.activity.to_bits());
        }
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
    assert_eq!(a.elim_mark, b.elim_mark);
    assert_eq!(a.elim_mark_count, b.elim_mark_count);
    assert_eq!(a.trivially_unsat, b.trivially_unsat);
    assert_eq!(
        (a.ticks_focused, a.ticks_stable),
        (b.ticks_focused, b.ticks_stable)
    );
}

fn round(solver: &mut Solver, budget: u64) -> (usize, usize) {
    solver.inproc_budgets.window = 1;
    solver.inproc_budgets.subsume_checks = budget;
    for code in 0..2 * solver.num_vars {
        solver.mark_subsume_lit(Lit::from_code(code as u32));
    }
    solver.subsume_round()
}

#[test]
fn empty_reusable_buffers_cover_budget_scope_and_collection_boundaries() {
    let mut a = Solver::new();
    let mut b = Solver::new();
    b.subsume_database_oracle = true;
    let pa = a.enable_lrat_transcript();
    let pb = b.enable_lrat_transcript();
    let mut clauses = Vec::new();
    for x in 1..=10 {
        for y in x + 1..=10 {
            for z in y + 1..=10 {
                clauses.push(vec![x, y, z]);
            }
        }
    }
    for s in [&mut a, &mut b] {
        for clause in &clauses {
            s.add_clause_dimacs(clause);
        }
    }
    let mut allocations = None;
    for budget in [100_000, 0, 1, 100_000] {
        assert_eq!(round(&mut a, budget), round(&mut b, budget));
        state_matches(&a, &b);
        let scratch = &a.subsume_scratch;
        assert!(scratch.schedule.is_empty());
        assert!(scratch.schedule.capacity() >= clauses.len());
        assert_eq!(scratch.occs.len(), 20);
        assert!(scratch.occs.iter().all(|list| list.is_empty()));
        assert!(scratch.occs.iter().any(|list| list.spilled()));
        assert!(scratch.mark.iter().all(|value| *value == 0));
        assert!(scratch.payloads.words.is_empty());
        assert!(scratch.payloads.words.capacity() >= 4 * clauses.len());
        let pointers = (
            scratch.schedule.as_ptr(),
            scratch.occs.as_ptr(),
            scratch.mark.as_ptr(),
            scratch.payloads.words.as_ptr(),
        );
        if let Some(previous) = allocations {
            assert_eq!(pointers, previous);
        } else {
            allocations = Some(pointers);
        }
    }
    for s in [&mut a, &mut b] {
        s.push();
        s.add_clause_dimacs(&[11, 12, 13]);
        s.add_clause_dimacs(&[11, 12, 13, 14]);
    }
    assert_eq!(round(&mut a, 100_000), round(&mut b, 100_000));
    for s in [&mut a, &mut b] {
        s.pop();
        s.clauses.compact_arena_forced(&mut s.watches);
    }
    state_matches(&a, &b);
    assert_eq!(round(&mut a, 100_000), round(&mut b, 100_000));
    assert_eq!(a.solve(), b.solve());
    state_matches(&a, &b);
    for s in [&a, &b] {
        assert!(clauses.iter().all(|clause| clause.iter().any(|lit| {
            let literal = Lit::from_dimacs(*lit);
            s.trail.lit_val(literal) > 0
        })));
    }
    a.flush_proof();
    b.flush_proof();
    assert_eq!(pa.snapshot().expect("trace"), pb.snapshot().expect("trace"));
}

#[test]
fn cached_subsumer_survives_promotion_before_later_queries() {
    let mut a = Solver::new();
    let mut b = Solver::new();
    b.subsume_database_oracle = true;
    let lits = [Lit::from_code(0), Lit::from_code(2), Lit::from_code(4)];
    for s in [&mut a, &mut b] {
        s.ensure_vars(4);
        let learned = s.clauses.add_learned(lits);
        s.clauses.set_lbd(learned, 2);
        assert_eq!(learned, ClauseId::new(0));
        s.attach_watchers(learned, lits[0], lits[1]);
        // The copied learned clause is entailed by the original duplicate.
        s.add_clause_dimacs(&[1, 2, 3]);
        s.add_clause_dimacs(&[1, 2, 3, 4]);
    }
    assert_eq!(round(&mut a, 100_000), (2, 0));
    assert_eq!(round(&mut b, 100_000), (2, 0));
    state_matches(&a, &b);
    assert!(
        !a.clauses
            .get(ClauseId::new(0))
            .expect("promoted subsumer")
            .learned
    );
}
