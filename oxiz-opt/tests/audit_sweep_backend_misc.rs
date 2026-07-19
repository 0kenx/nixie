//! Regression tests for the `sweep-backend-misc` triage sweep, covering
//! `oxiz-opt/src/maxsat/algorithms.rs`:
//!
//! 1. `check_hard_satisfiable` used to unconditionally zero
//!    `lower_bound`/`upper_bound`, which -- when reached from inside a
//!    core-guided loop after every soft clause had already been relaxed --
//!    silently wiped the accumulated MaxSAT cost, making `cost()` report 0
//!    for instances with a genuinely nonzero optimum.
//! 2. OLL's cross-core group merging used to just bump the bound of the
//!    *first* intersecting group and leave every other intersecting group's
//!    bound untouched, which could keep re-deriving essentially the same
//!    conflict against the un-bumped groups and inflate `lower_bound`.
//! 3. PMRES's multi-clause-core branch built a jointly-unsatisfiable
//!    assumption set (every core member forced true *and* an `at-most-k-1`
//!    bound over that exact same set), making `solve_with_assumptions`
//!    return UNSAT by pure construction and inflating `lower_bound` on every
//!    rediscovery instead of terminating.

use oxiz_opt::smtlib::{CommandResult, OptCommand, SmtLibOptimizer};
use oxiz_opt::{MaxSatAlgorithm, MaxSatConfig, MaxSatResult, MaxSatSolver, Weight};
use oxiz_sat::{Lit, Var};

fn lit(v: u32, neg: bool) -> Lit {
    if neg {
        Lit::neg(Var(v))
    } else {
        Lit::pos(Var(v))
    }
}

/// No hard clauses; two soft unit clauses on the same variable with
/// opposite polarity (`x0` and `~x0`), each weight 1. They can never both
/// be satisfied, so the true optimal cost is exactly 1.
///
/// Fu-Malik's core-guided loop discovers this conflict in its very first
/// iteration, relaxes *both* soft clauses (bringing `assumptions` down to
/// empty), and then falls through to `check_hard_satisfiable` -- the exact
/// path that used to zero the already-accumulated `lower_bound`.
#[test]
fn check_hard_satisfiable_preserves_accumulated_cost() {
    let config = MaxSatConfig::builder()
        .algorithm(MaxSatAlgorithm::FuMalik)
        .stratified(false)
        .build();
    let mut solver = MaxSatSolver::with_config(config);
    solver.add_soft_weighted([lit(0, false)], Weight::one());
    solver.add_soft_weighted([lit(0, true)], Weight::one());

    let result = solver.solve().expect("solve should not error");
    assert_eq!(result, MaxSatResult::Optimal);
    assert_eq!(
        solver.cost(),
        Weight::one(),
        "mutually exclusive unit soft clauses must cost exactly 1, not be \
         wiped to 0 by check_hard_satisfiable's post-relaxation bound reset"
    );
    assert_eq!(
        solver.lower_bound(),
        &Weight::one(),
        "lower_bound must retain the cost accumulated before the final \
         hard-satisfiability check"
    );
}

/// Same shape as above but with no soft clauses relaxed at all: the
/// trivial (no soft clauses) `solve()` path also reaches
/// `check_hard_satisfiable` directly. Cost must stay 0 here since nothing
/// was ever violated -- confirming the fix doesn't accidentally make the
/// *legitimately* zero case report something else.
#[test]
fn check_hard_satisfiable_trivial_no_soft_clauses_is_zero_cost() {
    let mut solver = MaxSatSolver::new();
    solver.add_hard([lit(0, false), lit(1, false)]);

    let result = solver.solve().expect("solve should not error");
    assert_eq!(result, MaxSatResult::Optimal);
    assert_eq!(solver.cost(), Weight::zero());
    assert_eq!(solver.upper_bound(), &Weight::zero());
}

/// A path-shaped conflict graph over 4 soft "must be true" unit clauses:
/// `x0 - x1 - x2 - x3`, where each edge is a hard "not both" clause. The
/// independence number of a 4-node path is 2, so the true MaxSAT optimum
/// leaves exactly 2 of the 4 soft clauses violated (cost 2).
///
/// This is built to make OLL discover cores whose relaxation-blocking
/// variables straddle more than one already-established group (`x1` is
/// shared between the `x0-x1` and `x1-x2` conflicts, `x2` between
/// `x1-x2` and `x2-x3`), which is exactly the situation the old "just bump
/// the first group" code mishandled. Fu-Malik (already correct) is used
/// as the ground truth the OLL result must match.
fn build_path_conflict_instance(config: MaxSatConfig) -> MaxSatSolver {
    let mut solver = MaxSatSolver::with_config(config);
    // Hard: not both endpoints of each edge in the x0-x1-x2-x3 path.
    solver.add_hard([lit(0, true), lit(1, true)]);
    solver.add_hard([lit(1, true), lit(2, true)]);
    solver.add_hard([lit(2, true), lit(3, true)]);
    // Soft: every variable "wants" to be true, unit weight each.
    for v in 0..4u32 {
        solver.add_soft_weighted([lit(v, false)], Weight::one());
    }
    solver
}

#[test]
fn oll_path_conflict_matches_fu_malik_ground_truth() {
    let fu_malik_config = MaxSatConfig::builder()
        .algorithm(MaxSatAlgorithm::FuMalik)
        .stratified(false)
        .build();
    let mut fu_malik_solver = build_path_conflict_instance(fu_malik_config);
    let fu_malik_result = fu_malik_solver.solve().expect("Fu-Malik should not error");
    assert_eq!(fu_malik_result, MaxSatResult::Optimal);
    assert_eq!(
        fu_malik_solver.cost(),
        Weight::from(2i64),
        "sanity check: the path-conflict instance's true optimum is 2"
    );

    let oll_config = MaxSatConfig::builder()
        .algorithm(MaxSatAlgorithm::Oll)
        .stratified(false)
        .max_iterations(200)
        .build();
    let mut oll_solver = build_path_conflict_instance(oll_config);
    let oll_result = oll_solver.solve().expect("OLL should not error");
    assert_eq!(
        oll_result,
        MaxSatResult::Optimal,
        "OLL must not time out (Unknown) on a tiny 4-variable instance"
    );
    assert_eq!(
        oll_solver.cost(),
        fu_malik_solver.cost(),
        "OLL's cross-core group merge must not inflate the reported cost \
         above the true (Fu-Malik-verified) optimum"
    );
}

/// A larger version of the same path-conflict shape (7 soft clauses,
/// independence number 4, optimum cost 3) purely to increase the chance
/// that OLL's group-merge path is exercised more than once before
/// converging, while staying well within `max_iterations`.
#[test]
fn oll_larger_path_conflict_matches_fu_malik_ground_truth() {
    fn build(config: MaxSatConfig) -> MaxSatSolver {
        let mut solver = MaxSatSolver::with_config(config);
        for v in 0..6u32 {
            solver.add_hard([lit(v, true), lit(v + 1, true)]);
        }
        for v in 0..7u32 {
            solver.add_soft_weighted([lit(v, false)], Weight::one());
        }
        solver
    }

    let fu_malik_config = MaxSatConfig::builder()
        .algorithm(MaxSatAlgorithm::FuMalik)
        .stratified(false)
        .build();
    let mut fu_malik_solver = build(fu_malik_config);
    let fu_malik_result = fu_malik_solver.solve().expect("Fu-Malik should not error");
    assert_eq!(fu_malik_result, MaxSatResult::Optimal);
    assert_eq!(fu_malik_solver.cost(), Weight::from(3i64));

    let oll_config = MaxSatConfig::builder()
        .algorithm(MaxSatAlgorithm::Oll)
        .stratified(false)
        .max_iterations(500)
        .build();
    let mut oll_solver = build(oll_config);
    let oll_result = oll_solver.solve().expect("OLL should not error");
    assert_eq!(oll_result, MaxSatResult::Optimal);
    assert_eq!(oll_solver.cost(), fu_malik_solver.cost());
}

/// PMRES on a multi-clause-core instance (3 mutually exclusive-ish soft
/// clauses forced together by a single hard clause) used to build a
/// jointly-unsatisfiable assumption set in its multi-clause-core branch,
/// which meant every `solve_with_assumptions` call after the first UNSAT
/// core returned UNSAT by pure construction -- re-deriving the same core
/// forever (in practice: tens of thousands of iterations of ever-growing
/// totalizers) instead of converging. A tight `max_iterations` here proves
/// the fixed algorithm (now delegating to the already-correct Fu-Malik
/// core-guided loop) converges quickly rather than exhausting the budget.
#[test]
fn pmres_multi_clause_core_converges_without_exhausting_iterations() {
    let config = MaxSatConfig::builder()
        .algorithm(MaxSatAlgorithm::Pmres)
        .stratified(false)
        .max_iterations(50)
        .build();
    let mut solver = MaxSatSolver::with_config(config);
    solver.add_hard([lit(0, false), lit(1, false), lit(2, false)]);
    solver.add_soft([lit(0, true)]);
    solver.add_soft([lit(1, true)]);
    solver.add_soft([lit(2, true)]);

    let result = solver.solve().expect("PMRES should not error");
    assert_eq!(
        result,
        MaxSatResult::Optimal,
        "PMRES must converge well within 50 iterations on a 3-clause core, \
         not exhaust the budget chasing a self-contradictory assumption set"
    );
    assert_eq!(
        solver.cost(),
        Weight::one(),
        "exactly one of the three mutually-forced soft clauses must be \
         violated at the optimum"
    );
}

/// `oxiz-opt/src/smtlib.rs`: `(get-objectives)` used to hardcode
/// `optimal: true` on every objective value regardless of whether a
/// `(check-sat)` had ever actually run, or ever proved optimality. This
/// verifies the flag now reflects the true, most-recently-proven
/// optimization state.
#[test]
fn smtlib_get_objectives_reports_honest_optimal_flag() {
    let mut opt = SmtLibOptimizer::new();
    let (obj_term, hard_term) = {
        let ctx = opt.context_mut();
        let int_sort = ctx.terms.sorts.int_sort;
        let x = ctx.terms.mk_var("x", int_sort);
        let zero = ctx.terms.mk_int(0);
        let ten = ctx.terms.mk_int(10);
        let ge_zero = ctx.terms.mk_ge(x, zero);
        let le_ten = ctx.terms.mk_le(x, ten);
        let hard = ctx.terms.mk_and(vec![ge_zero, le_ten]);
        (x, hard)
    };
    opt.context_mut().add_hard(hard_term);

    // Before any check-sat has run at all: nothing is proven optimal.
    let before = opt
        .execute(OptCommand::GetObjectives)
        .expect("get-objectives should not error");
    match before {
        CommandResult::Objectives(objs) => assert!(
            objs.is_empty(),
            "no objectives registered yet, so none should be reported"
        ),
        other => panic!("expected Objectives, got {other:?}"),
    }

    opt.execute(OptCommand::Minimize {
        term: obj_term,
        name: Some("x".to_string()),
    })
    .expect("minimize should not error");

    // An objective now exists but check-sat has still never run.
    let unproven = opt
        .execute(OptCommand::GetObjectives)
        .expect("get-objectives should not error");
    match unproven {
        CommandResult::Objectives(objs) => {
            assert_eq!(objs.len(), 1);
            assert!(
                !objs[0].optimal,
                "optimal must be false before any check-sat has run"
            );
        }
        other => panic!("expected Objectives, got {other:?}"),
    }

    opt.execute(OptCommand::CheckSat)
        .expect("check-sat should not error");

    let proven = opt
        .execute(OptCommand::GetObjectives)
        .expect("get-objectives should not error");
    match proven {
        CommandResult::Objectives(objs) => {
            assert_eq!(objs.len(), 1);
            assert!(
                objs[0].optimal,
                "optimal must be true once check-sat has proven the optimum"
            );
        }
        other => panic!("expected Objectives, got {other:?}"),
    }

    // Adding another soft/objective command after solving invalidates the
    // previously proven optimum until the next check-sat.
    let x2 = {
        let ctx = opt.context_mut();
        let int_sort = ctx.terms.sorts.int_sort;
        ctx.terms.mk_var("y", int_sort)
    };
    opt.execute(OptCommand::Maximize {
        term: x2,
        name: Some("y".to_string()),
    })
    .expect("maximize should not error");

    let after_mutation = opt
        .execute(OptCommand::GetObjectives)
        .expect("get-objectives should not error");
    match after_mutation {
        CommandResult::Objectives(objs) => {
            assert_eq!(objs.len(), 2);
            assert!(
                objs.iter().all(|o| !o.optimal),
                "adding a new objective after solving must invalidate the \
                 stale 'optimal' claim until the next check-sat"
            );
        }
        other => panic!("expected Objectives, got {other:?}"),
    }
}

/// `MaxSatSolver::update_soft_values` had `Lit::sign()`'s polarity
/// backwards (`sign()` is `true` for *positive* literals, not negative),
/// so a soft clause built from a negative unit literal had its
/// satisfaction status reported inverted by `is_soft_satisfied`/
/// `satisfied_soft`/`unsatisfied_soft` -- even though `cost()` (tracked
/// independently via core accumulation) stayed correct.
#[test]
fn maxsat_negative_literal_soft_clause_satisfaction_is_reported_correctly() {
    let config = MaxSatConfig::builder()
        .algorithm(MaxSatAlgorithm::FuMalik)
        .stratified(false)
        .build();
    let mut solver = MaxSatSolver::with_config(config);
    // Hard: x0 must be true.
    solver.add_hard([lit(0, false)]);
    // Soft: x0 should be false (a negative unit literal) -- forced
    // violated by the hard clause.
    let soft_id = solver.add_soft_weighted([lit(0, true)], Weight::one());

    let result = solver.solve().expect("solve should not error");
    assert_eq!(result, MaxSatResult::Optimal);
    assert_eq!(solver.cost(), Weight::one());
    assert!(
        !solver.is_soft_satisfied(soft_id),
        "the negative-literal soft clause ~x0 is genuinely violated (x0 \
         is forced true), so is_soft_satisfied must report false, not \
         the sign-inverted true"
    );
    assert!(
        solver.unsatisfied_soft().any(|id| id == soft_id),
        "the violated soft clause must appear in unsatisfied_soft()"
    );
    assert!(
        solver.satisfied_soft().next().is_none(),
        "no soft clause is actually satisfied here"
    );
}
