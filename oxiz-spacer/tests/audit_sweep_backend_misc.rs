//! Regression tests for the `sweep-backend-misc` triage sweep, covering
//! `oxiz-spacer/src/bmc.rs`:
//!
//! `run_kinduction` used to fall through to `Ok(BmcResult::Safe(max_depth))`
//! whenever every attempted `k` returned `Unknown`, silently fabricating a
//! bounded-safety claim even though no depth range was ever conclusively
//! verified free of a counterexample.

use oxiz_core::TermManager;
use oxiz_spacer::{Bmc, BmcConfig, BmcResult, ChcSystem, PredicateApp};

/// Trivially safe single-transition system (`x=0` initially, never
/// changes, bad state `x<0`), but with a *second*, entirely unused
/// predicate also declared on the system. `check_kinduction`'s inductive
/// step bails out to `Unknown` whenever `system.predicates().count() > 1`
/// (it's only sound for single-predicate linear CHC), so every `k` in
/// `1..=max_depth` comes back `Unknown` -- `run_kinduction` must report
/// that honestly as `Unknown`, not fabricate `Safe(max_depth)`.
#[test]
fn kinduction_all_unknown_reports_unknown_not_fabricated_safe() {
    let mut terms = TermManager::new();
    let mut system = ChcSystem::new();

    let inv = system.declare_predicate("SweepInv", [terms.sorts.int_sort]);
    // A second, unrelated predicate purely to push `predicates().count()`
    // above 1 and force the inductive-step's multi-predicate bailout.
    let _unused = system.declare_predicate("SweepUnused", [terms.sorts.int_sort]);

    let x = terms.mk_var("sweep_x", terms.sorts.int_sort);
    let zero = terms.mk_int(0);
    let init_c = terms.mk_eq(x, zero);
    system.add_init_rule(
        [("sweep_x".to_string(), terms.sorts.int_sort)],
        init_c,
        inv,
        [x],
    );

    let bad_c = terms.mk_lt(x, zero);
    system.add_query(
        [("sweep_x".to_string(), terms.sorts.int_sort)],
        [PredicateApp::new(inv, [x])],
        bad_c,
    );

    let config = BmcConfig {
        max_depth: 3,
        use_kinduction: true,
        verbosity: 0,
    };
    let mut bmc = Bmc::with_config(&mut terms, &system, config);
    let result = bmc.check().expect("BMC should not error");

    assert_eq!(
        result,
        BmcResult::Unknown,
        "k-induction that never got past the multi-predicate bailout must \
         report Unknown, not a fabricated Safe(max_depth)"
    );
}
