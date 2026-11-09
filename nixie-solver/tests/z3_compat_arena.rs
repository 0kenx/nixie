//! Term ids from the facade's construction arena must never index the solver arena.
use nixie_solver::z3_compat::{Bool, Int, SatResult, Z3Config, Z3Context, Z3Solver};

#[test]
fn integer_assertions_are_transferred_instead_of_dropped() {
    let context = Z3Context::new(&Z3Config::new());
    let mut solver = Z3Solver::new(&context);
    solver.set_logic("QF_LIA");
    let x = Int::new_const(&context, "x");
    let five = Int::from_i64(&context, 5);
    solver.assert(&Int::gt(&context, &x, &five));
    assert_eq!(solver.check(), SatResult::Sat);
    assert!(solver.get_model().unwrap().to_string().contains("x"));
    solver.push();
    // Construct after solving has interned private terms in the other arena.
    let zero = Int::from_i64(&context, 0);
    solver.assert(&Int::lt(&context, &x, &zero));
    assert_eq!(solver.check(), SatResult::Unsat);
    solver.pop();
    assert_eq!(solver.check(), SatResult::Sat);
}

#[test]
fn colliding_source_and_solver_ids_keep_their_own_meanings() {
    let context = Z3Context::new(&Z3Config::new());
    let mut solver = Z3Solver::new(&context);
    let local_sort = solver.context().terms.sorts.bool_sort;
    let local = solver.context_mut().terms.mk_var("local", local_sort);
    let source = Bool::new_const(&context, "source");
    assert_eq!(local, source.id, "exercise an actual numeric id collision");
    solver.assert(&Bool::from_id(local));
    solver.assert(&Bool::not(&context, &source));
    assert_eq!(solver.check(), SatResult::Sat);
    solver.assert(&source);
    assert_eq!(solver.check(), SatResult::Unsat);
}

#[test]
fn assumptions_keep_models_and_return_source_arena_core_handles() {
    let context = Z3Context::new(&Z3Config::new());
    let mut solver = Z3Solver::new(&context);
    let p = Bool::new_const(&context, "p");
    let neg = Bool::not(&context, &p);
    assert_eq!(
        solver.check_assumptions(std::slice::from_ref(&p)),
        SatResult::Sat
    );
    assert!(solver.get_model().is_some());
    assert_eq!(solver.check_assumptions(&[p, neg]), SatResult::Unsat);
    assert!(solver.get_model().is_none());
    let core = solver.unsat_core();
    assert!(!core.is_empty());
    let mut replay = Z3Solver::new(&context);
    for term in &core {
        replay.assert(term);
    }
    assert_eq!(replay.check(), SatResult::Unsat);
    assert_eq!(solver.check(), SatResult::Sat);
    assert!(solver.unsat_core().is_empty());
}

#[test]
fn invalid_import_is_unknown_and_pop_retracts_the_error() {
    let context = Z3Context::new(&Z3Config::new());
    let foreign = Z3Context::new(&Z3Config::new());
    let mut solver = Z3Solver::new(&context);
    assert_eq!(solver.check(), SatResult::Sat);
    solver.push();
    solver.assert(&Bool::new_const(&foreign, "foreign"));
    assert_eq!(solver.check(), SatResult::Unknown);
    assert!(solver.get_model().is_none());
    solver.pop();
    assert_eq!(solver.check(), SatResult::Sat);
    assert_eq!(
        solver.check_assumptions(&[Bool::from_id(nixie_core::ast::TermId(u32::MAX))]),
        SatResult::Unknown
    );
    assert!(solver.get_model().is_none());
}
