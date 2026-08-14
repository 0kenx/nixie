//! Wave-2 integration tests for oxiz-spacer.
//!
//! Covers:
//! * SP-01 – inductive (MIC) generalization is wired into the PDR engine: a
//!   safe instance still verifies with generalization enabled.
//! * The unsafe path still surfaces a concrete counterexample.
//! * spacer-distributed – the real `std::thread` parallel portfolio returns the
//!   same verdict as the sequential engine, actually spawns worker threads
//!   (asserted via the coordinator's spawn counter), and terminates.

use oxiz_core::TermManager;
use oxiz_spacer::chc::{ChcSystem, PredicateApp};
use oxiz_spacer::distributed::{DistributedConfig, DistributedCoordinator};
use oxiz_spacer::pdr::{Spacer, SpacerConfig, SpacerResult};

/// Build a safe single-predicate linear system:
/// `x = 0 => Inv(x)`, `Inv(x) ∧ x' = x + 1 ∧ x' < 10 => Inv(x')`,
/// query `Inv(x) ∧ x < 0 => false`. The invariant `x >= 0` proves safety.
fn build_safe_system(terms: &mut TermManager) -> ChcSystem {
    let mut system = ChcSystem::new();
    let inv = system.declare_predicate("Inv", [terms.sorts.int_sort]);

    let x = terms.mk_var("x", terms.sorts.int_sort);
    let zero = terms.mk_int(0);
    let init = terms.mk_eq(x, zero);
    system.add_init_rule([("x".to_string(), terms.sorts.int_sort)], init, inv, [x]);

    let xp = terms.mk_var("x'", terms.sorts.int_sort);
    let one = terms.mk_int(1);
    let ten = terms.mk_int(10);
    let x_plus_one = terms.mk_add([x, one]);
    let step = terms.mk_eq(xp, x_plus_one);
    let bound = terms.mk_lt(xp, ten);
    let trans = terms.mk_and([step, bound]);
    system.add_transition_rule(
        [
            ("x".to_string(), terms.sorts.int_sort),
            ("x'".to_string(), terms.sorts.int_sort),
        ],
        [PredicateApp::new(inv, [x])],
        trans,
        inv,
        [xp],
    );

    let neg = terms.mk_lt(x, zero);
    system.add_query(
        [("x".to_string(), terms.sorts.int_sort)],
        [PredicateApp::new(inv, [x])],
        neg,
    );
    system
}

/// Build an unsafe system: `x = 0 => Inv(x)`, `Inv(x) ∧ x' = x + 1 => Inv(x')`,
/// query `Inv(x) ∧ x = 2 => false`. `x = 2` is reachable in two steps.
fn build_unsafe_system(terms: &mut TermManager) -> ChcSystem {
    let mut system = ChcSystem::new();
    let inv = system.declare_predicate("Inv", [terms.sorts.int_sort]);

    let x = terms.mk_var("x", terms.sorts.int_sort);
    let zero = terms.mk_int(0);
    let init = terms.mk_eq(x, zero);
    system.add_init_rule([("x".to_string(), terms.sorts.int_sort)], init, inv, [x]);

    let xp = terms.mk_var("x'", terms.sorts.int_sort);
    let one = terms.mk_int(1);
    let x_plus_one = terms.mk_add([x, one]);
    let trans = terms.mk_eq(xp, x_plus_one);
    system.add_transition_rule(
        [
            ("x".to_string(), terms.sorts.int_sort),
            ("x'".to_string(), terms.sorts.int_sort),
        ],
        [PredicateApp::new(inv, [x])],
        trans,
        inv,
        [xp],
    );

    let two = terms.mk_int(2);
    let bad = terms.mk_eq(x, two);
    system.add_query(
        [("x".to_string(), terms.sorts.int_sort)],
        [PredicateApp::new(inv, [x])],
        bad,
    );
    system
}

#[test]
fn safe_instance_verifies_with_generalization_enabled() {
    let mut terms = TermManager::new();
    let system = build_safe_system(&mut terms);

    let config = SpacerConfig {
        use_inductive_gen: true,
        ..SpacerConfig::default()
    };
    let mut spacer = Spacer::with_config(&mut terms, &system, config);
    let result = spacer.solve();
    assert_eq!(
        result.ok(),
        Some(SpacerResult::Safe),
        "safe instance must verify with inductive generalization on"
    );
}

#[test]
fn unsafe_instance_yields_counterexample() {
    let mut terms = TermManager::new();
    let system = build_unsafe_system(&mut terms);

    let mut spacer = Spacer::new(&mut terms, &system);
    let result = spacer.solve();
    assert_eq!(
        result.ok(),
        Some(SpacerResult::Unsafe),
        "x = 2 is reachable, so the system is unsafe"
    );
    assert!(
        spacer.counterexample().is_some(),
        "an Unsafe verdict must carry a concrete counterexample trace"
    );
}

#[test]
fn distributed_matches_sequential_safe_and_spawns_threads() {
    let mut terms = TermManager::new();
    let system = build_safe_system(&mut terms);

    // Sequential baseline.
    let sequential = {
        let mut spacer = Spacer::new(&mut terms, &system);
        spacer.solve()
    };
    assert_eq!(sequential.ok(), Some(SpacerResult::Safe));

    // Parallel portfolio over 3 real worker threads.
    let config = DistributedConfig {
        num_workers: 3,
        ..DistributedConfig::default()
    };
    let mut coordinator = DistributedCoordinator::new(&mut terms, &system, config);
    let distributed = coordinator.solve();

    assert_eq!(
        distributed.ok(),
        Some(SpacerResult::Safe),
        "distributed verdict must match the sequential engine"
    );
    assert_eq!(
        coordinator.spawned_threads(),
        3,
        "the portfolio must actually spawn one thread per worker"
    );
}

#[test]
fn distributed_matches_sequential_unsafe() {
    let mut terms = TermManager::new();
    let system = build_unsafe_system(&mut terms);

    let sequential = {
        let mut spacer = Spacer::new(&mut terms, &system);
        spacer.solve()
    };
    assert_eq!(sequential.ok(), Some(SpacerResult::Unsafe));

    let config = DistributedConfig {
        num_workers: 4,
        ..DistributedConfig::default()
    };
    let mut coordinator = DistributedCoordinator::new(&mut terms, &system, config);
    let distributed = coordinator.solve();

    assert_eq!(
        distributed.ok(),
        Some(SpacerResult::Unsafe),
        "distributed verdict must match the sequential engine on an unsafe instance"
    );
    assert!(
        coordinator.spawned_threads() >= 2,
        "multiple worker threads must have run"
    );
}
