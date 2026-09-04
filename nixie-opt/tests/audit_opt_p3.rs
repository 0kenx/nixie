//! Regression tests for the opt-p3 audit findings.
//!
//! 1. `maxsat/core.rs`: `Weight` must order/compare by numeric value, not by
//!    enum variant, across `Int`/`Rational`.
//! 2. `hybrid.rs`: `HybridSolver` must support hard clauses (partial MaxSAT)
//!    and must propagate the exact solver's real result.
//! 3. `maxsmt.rs`: `MaxSmtSolver` must actually solve (via `solve_with`), and
//!    the manager-less `solve()` must fail honestly instead of returning a
//!    fabricated `Unknown`.
//! 4. `omt.rs`: binary search must not claim `Optimal` when it exits via the
//!    iteration budget without proving optimality.
//! 5. `context.rs`: `is_soft_satisfied` must evaluate compound soft terms
//!    (e.g. `(not p)`) recursively so `cost()` is not over-reported.
//! 6. `preprocess.rs`: bounded variable elimination must be off by default and
//!    must never resolve finite-weight soft clauses as if they were hard.

use std::collections::hash_map::RandomState;
use std::hash::{BuildHasher, Hash};

use nixie_core::ast::TermManager;
use nixie_opt::{
    ArithConstraint, HybridConfig, HybridSolver, HybridStrategy, LinearObjective, MaxSmtError,
    MaxSmtResult, MaxSmtSolver, ObjectiveId, ObjectiveResult, OmtConfig, OmtSolver, OmtStrategy,
    OptContext, PreprocessConfig, Preprocessor, SoftClause, SoftId, Weight,
};
use nixie_sat::{Lit, Var};
use num_bigint::BigInt;
use num_rational::BigRational;
use rustc_hash::FxHashMap;

fn lit(v: u32, neg: bool) -> Lit {
    if neg {
        Lit::neg(Var(v))
    } else {
        Lit::pos(Var(v))
    }
}

fn hash_with<T: Hash>(rs: &RandomState, t: &T) -> u64 {
    rs.hash_one(t)
}

// ========  ========
// Finding 2: Weight numeric ordering / equality / hashing.
// ========  ========

#[test]
fn weight_big_int_greater_than_small_rational() {
    // Historically `Int(_) < Rational(_)` by variant order, so this was FALSE.
    assert!(Weight::from(1_000_000) > Weight::Rational(BigRational::new(1.into(), 2.into())));
    assert!(Weight::Rational(BigRational::new(1.into(), 2.into())) < Weight::from(1_000_000));
}

#[test]
fn weight_int_and_rational_compare_equal_by_value() {
    let int_five = Weight::from(5);
    let rat_five = Weight::Rational(BigRational::from(BigInt::from(5)));
    assert_eq!(int_five, rat_five);
    // `Hash` must stay consistent with the value-based `PartialEq`: equal
    // values hash equal under the same build-hasher.
    let rs = RandomState::new();
    assert_eq!(hash_with(&rs, &int_five), hash_with(&rs, &rat_five));
}

#[test]
fn weight_infinite_is_greatest_and_min_weight_correct() {
    assert!(Weight::Infinite > Weight::from(10_000));
    // Core min-weight extraction relies on this: min(Int 1000000, Rational 1/2)
    // must be the rational, not the integer.
    let a = Weight::from(1_000_000);
    let b = Weight::Rational(BigRational::new(1.into(), 2.into()));
    assert_eq!(a.min_weight(&b), b);
}

// ========  ========
// Finding 1: HybridSolver hard-clause support + real result propagation.
// ========  ========

#[test]
fn hybrid_hard_clause_forces_soft_violation() {
    // hard: x0 ; soft: ~x0 (w1) ; soft: x1 (w1).
    // ~x0 is unsatisfiable given the hard fact x0, so the exact optimum has
    // cost exactly 1. Without hard-clause support this could not be expressed.
    let mut solver = HybridSolver::with_config(HybridConfig {
        strategy: HybridStrategy::Parallel,
        ..Default::default()
    });
    solver.add_hard([lit(0, false)]);
    solver.add_soft(SoftClause::new(SoftId(0), [lit(0, true)], Weight::from(1)));
    solver.add_soft(SoftClause::new(SoftId(1), [lit(1, false)], Weight::from(1)));

    let result = solver.solve();
    assert!(result.is_ok());
    // The exact phase proves the optimum; cost is driven by the hard clause.
    assert_eq!(*solver.best_cost(), Weight::from(1));
}

// ========  ========
// Finding 3: MaxSmtSolver is no longer a hollow stub.
// ========  ========

#[test]
fn maxsmt_solve_without_manager_fails_honestly() {
    let mut solver = MaxSmtSolver::new();
    let mut tm = TermManager::new();
    let bs = tm.sorts.bool_sort;
    let p = tm.mk_var("p", bs);
    solver.add_soft(p);
    // The manager-less entry point must not fabricate an `Unknown` verdict.
    assert!(matches!(
        solver.solve(),
        Err(MaxSmtError::RequiresTermManager)
    ));
}

#[test]
fn maxsmt_solve_with_all_soft_satisfiable_has_zero_cost() {
    let mut tm = TermManager::new();
    let bs = tm.sorts.bool_sort;
    let p = tm.mk_var("p", bs);
    let q = tm.mk_var("q", bs);

    let mut solver = MaxSmtSolver::new();
    let id_p = solver.add_soft(p);
    let id_q = solver.add_soft(q);

    let res = solver.solve_with(&mut tm);
    assert_eq!(res.ok(), Some(MaxSmtResult::Optimal));
    assert_eq!(solver.cost(), Weight::zero());
    assert!(solver.is_satisfied(id_p));
    assert!(solver.is_satisfied(id_q));
}

#[test]
fn maxsmt_solve_with_hard_conflict_reports_weighted_cost() {
    let mut tm = TermManager::new();
    let bs = tm.sorts.bool_sort;
    let p = tm.mk_var("hp", bs);
    let not_p = tm.mk_not(p);

    let mut solver = MaxSmtSolver::new();
    // hard: ¬p ; soft: p (weight 3). p can never hold, so cost = 3.
    solver.add_hard(not_p);
    let id = solver.add_soft_weighted(p, Weight::from(3));

    let res = solver.solve_with(&mut tm);
    assert_eq!(res.ok(), Some(MaxSmtResult::Optimal));
    assert_eq!(solver.cost(), Weight::from(3));
    assert!(!solver.is_satisfied(id));
}

// ========  ========
// Finding 4: OMT binary search must not over-claim Optimal.
// ========  ========

#[test]
fn omt_binary_search_reports_satisfiable_on_iteration_budget() {
    // A single iteration cannot close the [0, 100] gap, so the result is a
    // feasible-but-unproven value: it must be `Satisfiable`, never `Optimal`.
    let mut solver = OmtSolver::with_config(OmtConfig {
        strategy: OmtStrategy::BinarySearch,
        max_iterations: 1,
        ..Default::default()
    });
    solver.minimize(LinearObjective::var(0));
    solver.set_bounds(
        ObjectiveId::new(0),
        Some(Weight::from(0)),
        Some(Weight::from(100)),
    );

    // Checker: any point with var0 = 2 satisfies "var0 >= 2".
    let checker = |c: &ArithConstraint| -> Option<FxHashMap<u32, BigRational>> {
        let point: FxHashMap<u32, BigRational> = [(0u32, BigRational::from(BigInt::from(2)))]
            .into_iter()
            .collect();
        if c.is_satisfied(&point) {
            Some(point)
        } else {
            None
        }
    };

    let result = solver.optimize_binary_search(0, checker);
    assert!(
        matches!(result, ObjectiveResult::Satisfiable(_)),
        "expected Satisfiable on exhausted budget, got {result:?}"
    );
}

// ========  ========
// Finding: context.rs is_soft_satisfied recursive evaluation.
// ========  ========

#[test]
fn soft_compound_not_term_is_evaluated_recursively() {
    // soft: (not p), no hard constraints. The optimum sets p = false so
    // (not p) holds and cost is 0. A direct-lookup implementation would never
    // find `(not p)` as a model key and would over-report the cost as 1.
    let mut ctx = OptContext::new();
    let bs = ctx.terms.sorts.bool_sort;
    let p = ctx.terms.mk_var("cp", bs);
    let not_p = ctx.terms.mk_not(p);
    let id = ctx.add_soft(not_p);

    let res = ctx.optimize();
    assert!(res.is_ok());
    assert_eq!(ctx.cost(), Weight::zero());
    assert!(ctx.is_soft_satisfied(id));
}

#[test]
fn soft_compound_not_term_unsatisfied_when_forced() {
    // hard: p ; soft: (not p) weight 1. (not p) is false under the model, so
    // it must be reported unsatisfied and cost must be 1.
    let mut ctx = OptContext::new();
    let bs = ctx.terms.sorts.bool_sort;
    let p = ctx.terms.mk_var("fp", bs);
    let true_term = ctx.terms.mk_true();
    let p_true = ctx.terms.mk_eq(p, true_term);
    ctx.add_hard(p_true);
    let not_p = ctx.terms.mk_not(p);
    let id = ctx.add_soft_weighted(not_p, Weight::from(1));

    let res = ctx.optimize();
    assert!(res.is_ok());
    assert!(!ctx.is_soft_satisfied(id));
    assert_eq!(ctx.cost(), Weight::from(1));
}

// ========  ========
// Finding: preprocess BVE default off + no unsound soft resolution.
// ========  ========

#[test]
fn preprocess_bve_is_disabled_by_default() {
    assert!(!PreprocessConfig::default().bounded_variable_elimination);
}

#[test]
fn preprocess_bve_never_resolves_finite_weight_soft_clauses() {
    // The audit counterexample: soft (x0)w1, (~x0)w1, (~x0)w1. Resolving x0 as
    // if hard produces empty clauses and inflates the optimum from 1 to 2. The
    // soundness guard must refuse to eliminate x0 (all occurrences finite).
    let config = PreprocessConfig {
        merge_duplicates: false,
        harden_high_weight: false,
        harden_threshold: None,
        subsumption: false,
        simplify: false,
        unit_propagation: false,
        failed_literal_detection: false,
        bounded_variable_elimination: true,
        bve_clause_limit: 100,
        bve_occurrence_limit: 10,
    };
    let mut prep = Preprocessor::with_config(config);
    let soft = vec![
        SoftClause::new(SoftId(0), [lit(0, false)], Weight::from(1)),
        SoftClause::new(SoftId(1), [lit(0, true)], Weight::from(1)),
        SoftClause::new(SoftId(2), [lit(0, true)], Weight::from(1)),
    ];

    let (result, _hard) = prep.preprocess(&soft);

    assert_eq!(prep.stats().variables_eliminated, 0);
    // No clause was resolved away into an empty (always-violated) clause.
    assert!(result.iter().all(|c| !c.lits.is_empty()));
}
