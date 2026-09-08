use super::*;

#[test]
fn satisfied_left_parent_clears_partial_marks() {
    for prefix_len in 0..=3 {
        for negative in [false, true] {
            let mut solver = Solver::new();
            let vars: Vec<_> = (0..6).map(|_| solver.new_var()).collect();
            let pivot = Lit::pos(vars[0]);
            let satisfied = Lit::pos(vars[4]);
            solver.trail.assign_decision(satisfied);
            let mut ctx = Eliminator::new(vars.len(), &solver.trail);
            let mut lits = vec![pivot];
            lits.extend(vars[1..=3].iter().map(
                |&v| {
                    if negative { Lit::neg(v) } else { Lit::pos(v) }
                },
            ));
            lits.insert(prefix_len + 1, satisfied);
            let left = solver.clauses.add_original(lits);
            let right = solver
                .clauses
                .add_original([pivot.negate(), Lit::pos(vars[5])]);
            assert!(matches!(
                solver.elim_resolve_clauses(&mut ctx, left, pivot, right),
                ElimResolve::Skip
            ));
            assert!(solver.clauses.get(left).is_none_or(|c| c.deleted));
            assert!(
                ctx.mark.iter().all(|&m| m == 0),
                "prefix={prefix_len}, negative={negative}: {:?}",
                ctx.mark
            );
        }
    }
}

#[test]
fn satisfied_parent_cannot_corrupt_later_resolution() {
    for complement in [false, true] {
        let mut solver = Solver::new();
        let vars: Vec<_> = (0..6).map(|_| solver.new_var()).collect();
        let [pivot, a, satisfied, next_pivot, b, c] = std::array::from_fn(|i| Lit::pos(vars[i]));
        solver.trail.assign_decision(satisfied);
        let mut ctx = Eliminator::new(vars.len(), &solver.trail);
        let left = solver.clauses.add_original([pivot, a, satisfied]);
        let right = solver.clauses.add_original([pivot.negate(), c]);
        assert!(matches!(
            solver.elim_resolve_clauses(&mut ctx, left, pivot, right),
            ElimResolve::Skip
        ));

        // A stale positive mark would drop `a`, fabricating the unit `b`.
        // A stale negative mark would call this non-tautological pair a
        // tautology and silently omit its required resolvent.
        let later_lit = if complement { a.negate() } else { a };
        let next_left = solver.clauses.add_original([next_pivot, b]);
        let next_right = solver
            .clauses
            .add_original([next_pivot.negate(), later_lit]);
        let result = solver.elim_resolve_clauses(&mut ctx, next_left, next_pivot, next_right);
        let ElimResolve::Resolvent(lits) = result else {
            panic!("expected the binary resolvent (b OR {later_lit:?})");
        };
        assert_eq!(lits.as_slice(), &[b, later_lit]);
        assert!(ctx.mark.iter().all(|&m| m == 0));
        assert!(!solver.trivially_unsat);
    }
}

#[test]
fn resolution_exits_clear_marks_and_preserve_every_parent_model() {
    // Independent truth-table oracle, including partial assignments,
    // satisfied parents, complementary literals, units, empty resolvents,
    // ordinary resolvents and both self-subsumption directions. Each of
    // three non-pivot variables is absent, positive or negative in each
    // parent, and unassigned, true or false on the root trail.
    fn tail(mut pattern: usize) -> Vec<Lit> {
        let mut lits = Vec::new();
        for index in 1..=3 {
            let var = Var::new(index);
            match pattern % 3 {
                0 => {}
                1 => lits.push(Lit::pos(var)),
                2 => lits.push(Lit::neg(var)),
                _ => unreachable!(),
            }
            pattern /= 3;
        }
        lits
    }
    fn satisfied(lit: Lit, model: u32) -> bool {
        ((model >> lit.var().index()) & 1 != 0) == lit.is_pos()
    }

    let mut cases = 0;
    for left_pattern in 0..27 {
        for right_pattern in 0..27 {
            for assignment in 0..27 {
                let mut solver = Solver::new();
                for _ in 0..4 {
                    solver.new_var();
                }
                let assigned = tail(assignment);
                for &lit in &assigned {
                    solver.trail.assign_decision(lit);
                }
                let mut ctx = Eliminator::new(4, &solver.trail);
                let pivot = Lit::pos(Var::new(0));
                let mut left_lits = tail(left_pattern);
                let mut right_lits = tail(right_pattern);
                left_lits.push(pivot);
                right_lits.push(pivot.negate());
                let left = solver.clauses.add_original(left_lits.iter().copied());
                let right = solver.clauses.add_original(right_lits.iter().copied());
                for (cid, lits) in [(left, &left_lits), (right, &right_lits)] {
                    for &lit in lits {
                        if ctx.lit_val(lit) == 0 {
                            let code = lit.code() as usize;
                            ctx.occs.push(code, cid);
                            ctx.noccs[code] += 1;
                        }
                    }
                }
                let result = solver.elim_resolve_clauses(&mut ctx, left, pivot, right);
                let derived = match result {
                    ElimResolve::Skip => None,
                    ElimResolve::Unit(lit) => Some(vec![lit]),
                    ElimResolve::Resolvent(lits) => Some(lits.into_vec()),
                };
                assert!(
                    ctx.mark.iter().all(|&m| m == 0),
                    "marks leaked: left={left_pattern} right={right_pattern} root={assignment}"
                );
                for model in 0..16 {
                    if !assigned.iter().all(|&lit| satisfied(lit, model))
                        || !left_lits.iter().any(|&lit| satisfied(lit, model))
                        || !right_lits.iter().any(|&lit| satisfied(lit, model))
                    {
                        continue;
                    }
                    assert!(!solver.trivially_unsat);
                    assert!(ctx.units.iter().all(|&lit| satisfied(lit, model)));
                    if let Some(lits) = &derived {
                        assert!(lits.iter().any(|&lit| satisfied(lit, model)));
                    }
                    for cid in solver.clauses.iter_ids() {
                        if let Some(clause) = solver.clauses.get(cid)
                            && !clause.deleted
                        {
                            assert!(clause.lits.iter().any(|&lit| satisfied(lit, model)));
                        }
                    }
                }
                cases += 1;
            }
        }
    }
    assert_eq!(cases, 19_683);
}

#[test]
fn absent_parent_exits_clear_marks() {
    for absent_left in [false, true] {
        for deleted in [false, true] {
            let mut solver = Solver::new();
            let vars: Vec<_> = (0..3).map(|_| solver.new_var()).collect();
            let pivot = Lit::pos(vars[0]);
            let mut left = solver.clauses.add_original([pivot, Lit::pos(vars[1])]);
            let mut right = solver
                .clauses
                .add_original([pivot.negate(), Lit::pos(vars[2])]);
            let absent = if absent_left { &mut left } else { &mut right };
            if deleted {
                solver.clauses.mark_deleted_raw(*absent);
            } else {
                *absent = ClauseId(u32::MAX);
            }
            let mut ctx = Eliminator::new(vars.len(), &solver.trail);
            assert!(matches!(
                solver.elim_resolve_clauses(&mut ctx, left, pivot, right),
                ElimResolve::Skip
            ));
            assert!(!solver.trivially_unsat);
            assert!(ctx.mark.iter().all(|&m| m == 0));
        }
    }
}
