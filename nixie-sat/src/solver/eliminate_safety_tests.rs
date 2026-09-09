use super::*;
use nixie_proof::lrat_check::check_lrat_proof;

#[test]
fn freezing_after_marking_still_protects_every_scheduled_variable() {
    for armed in [false, true] {
        let mut s = Solver::new();
        s.ensure_vars(2);
        s.add_clause_dimacs(&[1, -2]);
        s.add_clause_dimacs(&[-1, 2]);
        s.elim_mark.resize(2, false);
        s.elim_var_flag.resize(2, false);
        s.bve_def.resize(2, Vec::new());
        s.mark_elim_all();
        assert_eq!(s.elim_mark_count, 2);
        s.freeze_theory_vars([Var::new(0), Var::new(1)]);
        assert_eq!(s.elim_mark_count, 0);
        s.freeze_theory_vars([Var::new(0), Var::new(1)]);
        assert_eq!(s.elim_mark_count, 0);
        crate::test_knobs::set_definitions(Some(armed));
        // Independently protect the consumer, even for an already prepared candidate.
        let mut ctx = Eliminator::new(2, &s.trail);
        for id in s.clauses.iter_ids() {
            let c = s.clauses.get(id).expect("fixture clause");
            for &lit in c.lits {
                ctx.occs.push(lit.index(), id);
                ctx.noccs[lit.index()] += 1;
            }
        }
        s.elim_try_variable(&mut ctx, Var::new(0));
        assert!(!s.var_eliminated(Var::new(0)));
        let (eliminated, complete, _, _) = s.elim_round_with_budget(100, &mut 0);
        crate::test_knobs::set_definitions(None);
        assert_eq!(eliminated, 0);
        assert!(complete);
        assert!(!s.var_eliminated(Var::new(0)));
        assert!(!s.var_eliminated(Var::new(1)));
        assert_eq!(s.stats.definitions_extracted, 0);
    }
}

#[test]
fn root_conflicts_preserve_lrat_at_phase_entry_and_after_round_units() {
    for after_round in [false, true] {
        let cnf = if after_round {
            vec![vec![1, 2], vec![-1, 2], vec![-2, 3], vec![-2, -3]]
        } else {
            vec![vec![1, 2], vec![1, -2], vec![-1]]
        };
        let mut s = Solver::new();
        s.ensure_vars(3);
        let transcript = s.enable_lrat_transcript();
        for c in &cnf {
            assert!(s.add_clause_dimacs(c));
        }
        assert!(s.pending_parse_unit_flushes.is_empty());
        if after_round {
            // Isolate the round-unit epilogue: subsumption has no budget,
            // only x may be eliminated, and resolving its parents forces y.
            s.inproc_budgets.window = 1;
            s.inproc_budgets.subsume_checks = 0;
            s.freeze_theory_vars([Var::new(1), Var::new(2)]);
        }
        assert_eq!(s.eliminate_phase(), SubstOutcome::Unsat);
        assert_eq!(s.elim_phases, u64::from(after_round));
        assert_eq!(s.elim_resolutions_total > 0, after_round);
        assert_eq!(s.solve(), SolverResult::Unsat);
        s.flush_proof();
        let trace = transcript.snapshot().expect("complete proof");
        let checked = check_lrat_proof(&cnf, &trace.proof);
        assert!(
            checked.verified,
            "after_round={after_round}: {checked:?}, {}",
            trace.proof
        );
    }
}

#[test]
fn phase_scope_assumption_and_theory_guards_precede_elimination() {
    for mode in 0..3 {
        let mut s = Solver::new();
        s.ensure_vars(4);
        for c in [vec![1, -2], vec![1, -3], vec![-1, 2, 3]] {
            s.add_clause_dimacs(&c);
        }
        match mode {
            0 => s.push(),
            1 => s.assumptions_active = true,
            2 => s.real_theory_attached = true,
            _ => unreachable!(),
        }
        crate::test_knobs::set_definitions(Some(true));
        assert!(matches!(s.eliminate_phase(), SubstOutcome::Ok));
        crate::test_knobs::set_definitions(None);
        assert_eq!(s.elim_phases, 0);
        assert_eq!(s.stats.definitions_extracted, 0);
        assert!(s.bve_order.is_empty());
    }
}
