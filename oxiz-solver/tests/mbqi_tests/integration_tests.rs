//! Integration tests for MBQI
//!
//! Audit fix (sweep-solver): this file was dead code -- it existed on disk
//! but was never referenced by any `mod` declaration reachable from a
//! top-level `tests/*.rs` file, so `cargo test`/`cargo nextest run` never
//! compiled or ran any of it (see `tests/audit_sweep_solver.rs`, which now
//! wires it in). Bringing it back into the build surfaced two real compile
//! errors against the current API (`TermManager::intern` is
//! `pub(crate)`, and an unused `FxHashMap::default()` had no inferable
//! type), both fixed below. `test_mbqi_model_completion` was also vacuous
//! (it built a partial model and quantifier list but never actually called
//! `complete()`); it now exercises the real completion path. A genuine
//! end-to-end solving test that depends on MBQI actually instantiating a
//! quantifier has been added at the bottom of this file, closing the "no
//! end-to-end solving test" gap the audit flagged.

use oxiz_core::ast::{TermId, TermManager};
use oxiz_solver::mbqi::*;
use rustc_hash::FxHashMap;

#[test]
fn test_mbqi_basic_quantifier() {
    let mut manager = TermManager::new();
    let x = manager.mk_var("x", manager.sorts.int_sort);
    let zero = manager.mk_int(num_bigint::BigInt::from(0));
    let body = manager.mk_ge(x, zero);

    // Create quantifier: ∀x. x >= 0
    // This should be unsatisfiable
    let mut quant = QuantifiedFormula::new(body, smallvec::SmallVec::new(), body, true);
    quant
        .bound_vars
        .push((manager.intern_str("x"), manager.sorts.int_sort));

    assert!(quant.is_universal);
    assert_eq!(quant.num_vars(), 1);
}

#[test]
fn test_mbqi_model_completion() {
    let mut manager = TermManager::new();
    let mut completer = model_completion::ModelCompleter::new();

    let partial_model: FxHashMap<TermId, TermId> = FxHashMap::default();
    let quantifiers: Vec<QuantifiedFormula> = vec![];

    // Actually drive the completion path (previously this test built
    // `partial_model`/`quantifiers` and then never used them at all).
    let completed = completer
        .complete(&partial_model, &quantifiers, &mut manager)
        .expect("completing an empty partial model with no quantifiers must succeed");
    assert!(
        completed.assignments.is_empty(),
        "completing an empty partial model should not fabricate assignments"
    );

    let result = completer.stats();
    assert_eq!(result.num_completions, 1);
}

#[test]
fn test_mbqi_counterexample_generation() {
    let generator = counterexample::CounterExampleGenerator::new();
    let stats = generator.stats();

    assert_eq!(stats.num_searches, 0);
    assert_eq!(stats.num_counterexamples_found, 0);
}

#[test]
fn test_mbqi_instantiation_engine() {
    let engine = instantiation::InstantiationEngine::new();
    let stats = engine.stats();

    assert_eq!(stats.num_instantiations, 0);
}

#[test]
fn test_mbqi_finite_model_finder() {
    let finder = finite_model::FiniteModelFinder::new();
    let stats = finder.stats();

    assert_eq!(stats.num_searches, 0);
}

#[test]
fn test_mbqi_lazy_instantiator() {
    let mut inst = lazy_instantiation::LazyInstantiator::new();
    assert_eq!(inst.stats().num_process_calls, 0);

    inst.clear();
    assert_eq!(inst.stats().num_process_calls, 0);
}

#[test]
fn test_mbqi_integration() {
    let mut integration = integration::MBQIIntegration::new();
    integration.set_max_rounds(50);
    integration.clear();

    assert_eq!(integration.stats().num_quantifiers, 0);
}

#[test]
fn test_mbqi_heuristics() {
    let heuristics = heuristics::MBQIHeuristics::new();
    assert!(heuristics.enable_conflict_analysis);

    let conservative = heuristics::MBQIHeuristics::conservative();
    assert!(conservative.enable_model_bounds);
}

#[test]
fn test_mbqi_stats_display() {
    let stats = MBQIStats::new();
    let display = format!("{}", stats);
    assert!(display.contains("MBQI Statistics"));
}

#[test]
fn test_mbqi_result_predicates() {
    let sat = MBQIResult::Satisfied;
    assert!(sat.is_sat());
    assert!(!sat.is_unsat());

    let conflict = MBQIResult::Conflict {
        quantifier: oxiz_core::ast::TermId::new(1),
        reason: vec![],
    };
    assert!(!conflict.is_sat());
    assert!(conflict.is_unsat());
}

#[test]
fn test_instantiation_reason_display() {
    assert_eq!(
        format!("{}", InstantiationReason::ModelBased),
        "model-based"
    );
    assert_eq!(format!("{}", InstantiationReason::EMatching), "e-matching");
    assert_eq!(format!("{}", InstantiationReason::Conflict), "conflict");
}

#[test]
fn test_quantified_formula_priority() {
    let manager = TermManager::new();
    let body = manager.mk_true();
    let mut qf = QuantifiedFormula::new(body, smallvec::SmallVec::new(), body, true);

    let initial = qf.priority_score();
    qf.record_instantiation();
    let after = qf.priority_score();

    assert!(after < initial);
}

/// End-to-end regression: MBQI must actually *instantiate* the quantifier
/// for the solver to detect this contradiction.
///
/// `forall x. f(x) >= 0` together with the ground fact `f(a) < 0` (for a
/// fresh declared constant `a`) is UNSAT, but only if the axiom gets
/// instantiated at `x = a` so the arithmetic theory sees the resulting
/// ground inequality `f(a) >= 0` clash with `f(a) < 0` -- neither
/// assertion is individually contradictory, and nothing here is a
/// syntactic tautology/contradiction that a quantifier-free preprocessing
/// pass could short-circuit. Every other test in this file only exercised
/// freshly-constructed MBQI substructures in isolation (e.g.
/// `ModelCompleter::new().stats()`); this is the missing full-solve path.
#[test]
fn test_mbqi_end_to_end_instantiation_detects_unsat() {
    let mut solver = oxiz_solver::Solver::new();
    let mut manager = TermManager::new();
    let int_sort = manager.sorts.int_sort;

    let x = manager.mk_var("x", int_sort);
    let f_x = manager.mk_apply("f", [x], int_sort);
    let zero = manager.mk_int(0);
    let f_x_ge_0 = manager.mk_ge(f_x, zero);
    let forall = manager.mk_forall([("x", int_sort)], f_x_ge_0);
    solver.assert(forall, &mut manager);

    // `a` is a free constant: same `TermKind::Var` representation as a
    // bound variable, but with no enclosing binder it denotes an
    // uninterpreted 0-ary symbol.
    let a = manager.mk_var("a", int_sort);
    let f_a = manager.mk_apply("f", [a], int_sort);
    let f_a_lt_0 = manager.mk_lt(f_a, zero);
    solver.assert(f_a_lt_0, &mut manager);

    let result = solver.check(&mut manager);
    assert_eq!(
        result,
        oxiz_solver::SolverResult::Unsat,
        "forall x. f(x) >= 0  AND  f(a) < 0  should be UNSAT via MBQI instantiation at x=a, got {:?}",
        result
    );
}
