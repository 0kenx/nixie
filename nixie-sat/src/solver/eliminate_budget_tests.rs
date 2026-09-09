use super::*;

fn fixture() -> (Solver, Eliminator, Lit, [ClauseId; 4]) {
    let mut solver = Solver::new();
    solver.ensure_vars(4);
    solver.elim_mark.resize(4, false);
    solver.elim_var_flag.resize(4, false);
    solver.bve_def.resize(4, Vec::new());
    let [x, y, a, b] = std::array::from_fn(|i| Lit::from_code(2 * i as u32));
    let mut ctx = Eliminator::new(4, &solver.trail);
    let ids = [[x, !y], [x, a], [!x, y], [!x, b]].map(|lits| {
        let id = solver.clauses.add_original(lits);
        for lit in lits {
            ctx.occs.push(lit.index(), id);
            ctx.noccs[lit.index()] += 1;
        }
        id
    });
    (solver, ctx, x, ids)
}

#[test]
fn both_resolution_products_stop_before_the_denied_pair() {
    for gates in [false, true] {
        let required = if gates { 3 } else { 4 };
        for budget in 0..=required + 1 {
            let (mut s, mut ctx, x, ids) = fixture();
            ctx.resolution_limit = budget;
            let mut collected = Vec::new();
            let complete = if gates {
                s.elim_definition_resolvents_bounded(
                    &mut ctx,
                    x,
                    &[ids[0]],
                    &[ids[2]],
                    4,
                    &mut collected,
                )
            } else {
                s.elim_resolvents_bounded(&mut ctx, x, 2, 2, &mut collected)
            };
            assert_eq!(
                complete,
                budget >= required,
                "gates={gates} budget={budget}"
            );
            assert_eq!(ctx.resolutions, budget.min(required));
            assert_eq!(ctx.resolution_aborted, budget < required);
            assert!(!s.var_eliminated(x.var()));
            assert!(
                ids.iter()
                    .all(|&id| s.clauses.get(id).is_some_and(|c| !c.deleted))
            );
            assert!(ctx.mark.iter().all(|&m| m == 0));
        }
    }
}

#[test]
fn interrupted_round_rearms_pivot_and_does_not_install_partial_plan() {
    for budget in [0, 1, 2, 3] {
        crate::test_knobs::set_definitions(Some(false));
        let (mut s, _, x, ids) = fixture();
        for i in 1..4 {
            s.frozen_vars.insert(Var::new(i));
        }
        s.mark_elim_one(x.var());
        // A large historical counter must not hide or consume this round's budget.
        s.elim_resolutions_total = 900_000_000;
        let (eliminated, complete, _, _) = s.elim_round_with_budget(budget, &mut 0);
        assert_eq!(eliminated, 0);
        assert!(!complete);
        assert_eq!(s.elim_resolutions_total, 900_000_000 + budget);
        assert!(s.elim_mark[x.var().index()]);
        assert_eq!(s.elim_mark_count, 1);
        assert_eq!(s.clauses.len(), 4);
        assert!(
            ids.iter()
                .all(|&id| s.clauses.get(id).is_some_and(|c| !c.deleted))
        );

        // The preserved mark alone must suffice to resume at the next round.
        let (eliminated, complete, _, _) = s.elim_round_with_budget(4, &mut 0);
        crate::test_knobs::set_definitions(None);
        assert_eq!(eliminated, 1);
        assert!(complete);
        assert!(s.var_eliminated(x.var()));
        assert_eq!(s.elim_resolutions_total, 900_000_004 + budget);
        assert!(
            ids.iter()
                .all(|&id| s.clauses.get(id).is_some_and(|c| c.deleted))
        );
    }
}

#[test]
fn zero_budget_preserves_all_pending_variables_and_nonoverflowing_charge() {
    let (mut s, _, _, _) = fixture();
    s.mark_elim_all();
    let (_, complete, _, _) = s.elim_round_with_budget(0, &mut 0);
    assert!(!complete);
    assert_eq!(s.elim_mark_count, 4);
    assert!(s.elim_mark.iter().all(|&marked| marked));
    let mut ctx = Eliminator::new(1, &s.trail);
    ctx.resolutions = u64::MAX - 1;
    assert!(ctx.charge_resolution());
    assert!(!ctx.charge_resolution());
    assert_eq!(ctx.resolutions, u64::MAX);
}

#[test]
fn semantic_extraction_budget_is_carried_into_each_round() {
    let mut ticks = DEFINITION_PHASE_TICKS + 123;
    for _ in 0..2 {
        let mut s = Solver::new();
        s.ensure_vars(3);
        s.add_clause_dimacs(&[1, 2]);
        s.add_clause_dimacs(&[-1, 3]);
        s.elim_mark.resize(3, false);
        s.elim_var_flag.resize(3, false);
        s.bve_def.resize(3, Vec::new());
        s.freeze_theory_vars([Var::new(1), Var::new(2)]);
        s.mark_elim_one(Var::new(0));
        crate::test_knobs::set_definitions(Some(true));
        let (eliminated, complete, _, _) = s.elim_round_with_budget(10, &mut ticks);
        crate::test_knobs::set_definitions(None);
        assert!(complete);
        assert_eq!(eliminated, 1);
        assert_eq!(s.stats.definitions_checked, 0);
        assert_eq!(ticks, DEFINITION_PHASE_TICKS + 123);
    }
}
