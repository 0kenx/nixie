//! Regression tests for the spacer-p3 audit findings.
//!
//! Covers:
//!  * `bmc_unroll`: renaming must reach *every* term kind (Div/Mod/Neg/...),
//!    so no variable can escape step-indexing and mix time frames.
//!  * `existential`: `WitnessExtractor::extract_witnesses` must map witness
//!    values to the variable they actually belong to (by name), never an
//!    arbitrary model entry.
//!  * `distributed`: `DistributedCoordinator::solve` / `Worker::run` must
//!    return the real (sound) verdict, not a fabricated sleep-based result.

use nixie_core::tactic::{Goal, TacticResult};
use nixie_core::{TermId, TermKind, TermManager};
use nixie_spacer::chc::{ChcSystem, PredicateApp};
use nixie_spacer::{
    BmcUnrollTactic, DistributedConfig, DistributedCoordinator, SharedState, SpacerResult,
    WitnessExtractor, Worker,
};
use std::collections::HashMap;
use std::sync::Arc;

/// Collect every variable name occurring in `term` (via the manager's free-var
/// walk, which visits all term kinds).
fn collect_var_names(manager: &TermManager, term: TermId, out: &mut Vec<String>) {
    for var in manager.free_vars(term) {
        if let Some(node) = manager.get(var)
            && let TermKind::Var(sym) = &node.kind
        {
            out.push(manager.resolve_str(*sym).to_string());
        }
    }
}

/// A transition using `div`/`mod` (previously in the `_ => term` fallthrough)
/// must still get its variables step-renamed: after unrolling, *no* variable
/// may retain its bare (un-`@`-stepped) name.
#[test]
fn bmc_unroll_renames_div_mod_subterms() {
    let mut manager = TermManager::new();
    let int_sort = manager.sorts.int_sort;

    let x = manager.mk_var("x", int_sort);
    let x_next = manager.mk_var("x_next", int_sort);
    let zero = manager.mk_int(0);
    let two = manager.mk_int(2);

    // init: x = 0
    let init = manager.mk_eq(x, zero);
    // trans: x_next = (x div 2) + (x mod 2)   -- uses Div and Mod (Neg too)
    let x_div_2 = manager.mk_div(x, two);
    let x_mod_2 = manager.mk_mod(x, two);
    let neg = manager.mk_neg(x_mod_2);
    let rhs = manager.mk_add([x_div_2, neg]);
    let trans = manager.mk_eq(x_next, rhs);
    // property: x >= 0
    let property = manager.mk_ge(x, zero);

    let goal = Goal::new(vec![init, trans, property]);

    let mut tactic = BmcUnrollTactic::with_depth(&mut manager, 2);
    let result = tactic
        .apply_mut(&goal)
        .expect("tactic should apply to a 3-assertion goal");

    let TacticResult::SubGoals(goals) = result else {
        panic!("expected SubGoals from BMC unroll");
    };
    assert_eq!(goals.len(), 1);

    let mut names = Vec::new();
    for &assertion in &goals[0].assertions {
        collect_var_names(&manager, assertion, &mut names);
    }
    assert!(!names.is_empty(), "unrolled goal should contain variables");

    // Every variable must be step-indexed. With the old partial walk, the `x`
    // inside `x div 2` / `x mod 2` escaped renaming and stayed bare `x`.
    for name in &names {
        assert!(
            name.contains('@'),
            "variable `{name}` escaped step-renaming (Div/Mod subterm not renamed)"
        );
    }
    // And specifically the divisor operand's `x` became `x@0`.
    assert!(
        names.iter().any(|n| n == "x@0"),
        "expected the `x` inside `x div 2` to be renamed to `x@0`, got names: {names:?}"
    );
}

/// `extract_witnesses` must bind each existential variable to the model value
/// of the term that carries *its* name – not an arbitrary hash-ordered entry.
#[test]
fn witness_extraction_matches_variable_names() {
    let mut manager = TermManager::new();
    let int_sort = manager.sorts.int_sort;

    let y1 = manager.mk_var("y1", int_sort);
    let y2 = manager.mk_var("y2", int_sort);
    let v1 = manager.mk_int(11);
    let v2 = manager.mk_int(22);

    // Model: y1 -> 11, y2 -> 22 (keyed by the variable terms).
    let mut model: HashMap<TermId, TermId> = HashMap::new();
    model.insert(y1, v1);
    model.insert(y2, v2);

    let existentials = vec![("y1".to_string(), int_sort), ("y2".to_string(), int_sort)];

    let witnesses = WitnessExtractor::extract_witnesses(&manager, &model, &existentials);

    assert_eq!(
        witnesses.get("y1"),
        Some(&v1),
        "y1 must map to its own model value (11), not an arbitrary entry"
    );
    assert_eq!(
        witnesses.get("y2"),
        Some(&v2),
        "y2 must map to its own model value (22), not an arbitrary entry"
    );
}

/// Build the classic "incrementing counter is non-negative" safe system used by
/// the distributed solver tests.
fn build_safe_counter(terms: &mut TermManager) -> ChcSystem {
    let mut system = ChcSystem::new();
    let inv = system.declare_predicate("Inv", [terms.sorts.int_sort]);

    let x = terms.mk_var("x", terms.sorts.int_sort);
    let x_prime = terms.mk_var("x'", terms.sorts.int_sort);
    let zero = terms.mk_int(0);
    let one = terms.mk_int(1);

    let init_constraint = terms.mk_eq(x, zero);
    system.add_init_rule(
        [("x".to_string(), terms.sorts.int_sort)],
        init_constraint,
        inv,
        [x],
    );

    let x_plus_one = terms.mk_add(vec![x, one]);
    let transition_constraint = terms.mk_eq(x_prime, x_plus_one);
    system.add_transition_rule(
        [
            ("x".to_string(), terms.sorts.int_sort),
            ("x'".to_string(), terms.sorts.int_sort),
        ],
        [PredicateApp::new(inv, [x])],
        transition_constraint,
        inv,
        [x_prime],
    );

    let query_constraint = terms.mk_lt(x, zero);
    system.add_query(
        [("x".to_string(), terms.sorts.int_sort)],
        [PredicateApp::new(inv, [x])],
        query_constraint,
    );

    system
}

/// The distributed coordinator must return the *real* verdict from the sound
/// sequential engine (Safe here), not a fabricated `Unknown` from sleep-based
/// simulated work.
#[test]
fn distributed_solve_returns_real_safe_verdict() {
    let mut terms = TermManager::new();
    let system = build_safe_counter(&mut terms);

    let config = DistributedConfig::default();
    let mut coordinator = DistributedCoordinator::new(&mut terms, &system, config);
    let result = coordinator
        .solve()
        .expect("distributed solve should succeed");

    assert_eq!(
        result,
        SpacerResult::Safe,
        "distributed solve must return the real Safe verdict, not fabricated Unknown"
    );
}

/// A `Worker::run` must publish the real verdict into the shared state, not a
/// parity-based fake block result.
#[test]
fn distributed_worker_publishes_real_result() {
    let mut terms = TermManager::new();
    let system = build_safe_counter(&mut terms);
    let config = nixie_spacer::SpacerConfig::default();

    let shared = Arc::new(SharedState::new());
    let mut worker = Worker::new(0, Arc::clone(&shared));
    worker
        .run(&mut terms, &system, &config)
        .expect("worker run should succeed");

    assert_eq!(
        shared.get_result(),
        Some(SpacerResult::Safe),
        "worker must publish the real Safe verdict to shared state"
    );
}
