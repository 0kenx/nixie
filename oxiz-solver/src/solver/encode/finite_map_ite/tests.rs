//! White-box coverage for spine detection and the state
//! `flatten_lookup_spines` leaves behind — `lookup_index_terms` is
//! `pub(super)` and unreachable from an external integration test, so the
//! state assertions below have to live here. End-to-end
//! sat/unsat/get-value behaviour lives in `tests/pr32_pr33_soundness.rs`.

use super::*;
use crate::SolverResult;

/// A chain of exactly [`MIN_LOOKUP_ARMS`] keys must be recognised: the index
/// is registered as a lookup index, and each of its keys selects that arm's
/// value — which is what "the spine's keys were read correctly" means where
/// it counts, in the answers rather than in the bookkeeping.
#[test]
fn test_pr32_spine_at_minimum_length_is_recognised() {
    let mut manager = TermManager::new();
    let mut solver = Solver::new();
    let int = manager.sorts.int_sort;
    let idx = manager.mk_var("idx", int);

    let default = manager.mk_int(99);
    let mut chain = default;
    for (key, value) in [(3i64, 30i64), (2, 20), (1, 10)] {
        let k = manager.mk_int(key);
        let v = manager.mk_int(value);
        let eq = manager.mk_eq(idx, k);
        chain = manager.mk_ite(eq, v, chain);
    }
    let r = manager.mk_var("r", int);
    let top = manager.mk_eq(r, chain);
    solver.assert(top, &mut manager);

    assert!(
        solver.lookup_index_terms.contains(&idx),
        "a 3-arm equality-ite spine must be flattened and its index tracked"
    );

    // Each key must resolve to its own arm. Checking all three at once (each
    // on its own solver, so the pins do not interfere) is what pins down that
    // every key of the spine was read, and read at the right arm.
    for (key, value) in [(1i64, 10i64), (2, 20), (3, 30)] {
        let mut probe = Solver::new();
        probe.assert(top, &mut manager);
        let k = manager.mk_int(key);
        let pin = manager.mk_eq(idx, k);
        probe.assert(pin, &mut manager);
        assert_eq!(probe.check(&mut manager), SolverResult::Sat);
        let model = probe.model().expect("sat must produce a model");
        assert_eq!(
            model.get(r),
            Some(manager.mk_int(value)),
            "idx = {key} must select the arm holding {value}"
        );
    }
}

/// One arm short of [`MIN_LOOKUP_ARMS`] must be left alone: the generic
/// `eliminate_nonbool_ite` muxer handles it, and nothing is registered here.
#[test]
fn test_pr32_short_chain_is_not_flattened() {
    let mut manager = TermManager::new();
    let mut solver = Solver::new();
    let int = manager.sorts.int_sort;
    let idx = manager.mk_var("idx", int);

    let default = manager.mk_int(99);
    let mut chain = default;
    for (key, value) in [(2i64, 20i64), (1, 10)] {
        let k = manager.mk_int(key);
        let v = manager.mk_int(value);
        let eq = manager.mk_eq(idx, k);
        chain = manager.mk_ite(eq, v, chain);
    }
    let r = manager.mk_var("r", int);
    let top = manager.mk_eq(r, chain);
    solver.assert(top, &mut manager);

    assert!(
        !solver.lookup_index_terms.contains(&idx),
        "a 2-arm chain is below MIN_LOOKUP_ARMS and must not be flattened"
    );
    assert!(
        solver.lookup_index_terms.is_empty(),
        "no index at all may be registered by a chain that was not flattened"
    );
}

/// A guard whose comparison constant repeats further down the chain is
/// unreachable (the first match wins) and must not appear twice in the
/// tracked domain — nor may it silently force the two arms' values equal.
#[test]
fn test_pr32_duplicate_key_is_deduplicated_keeping_the_first_arm() {
    let mut manager = TermManager::new();
    let mut solver = Solver::new();
    let int = manager.sorts.int_sort;
    let idx = manager.mk_var("idx", int);
    let r = manager.mk_var("r", int);

    // (ite (= idx 1) 10 (ite (= idx 2) 20 (ite (= idx 1) 999 (ite (= idx 3) 30 0))))
    // Key `1` repeats; the *first* arm (value 10) is the reachable one.
    let default = manager.mk_int(0);
    let three = manager.mk_int(3);
    let k3 = manager.mk_eq(idx, three);
    let v3 = manager.mk_int(30);
    let inner3 = manager.mk_ite(k3, v3, default);

    let one_dup = manager.mk_int(1);
    let k1_dup = manager.mk_eq(idx, one_dup);
    let v1_dup = manager.mk_int(999);
    let inner_dup = manager.mk_ite(k1_dup, v1_dup, inner3);

    let two = manager.mk_int(2);
    let k2 = manager.mk_eq(idx, two);
    let v2 = manager.mk_int(20);
    let inner2 = manager.mk_ite(k2, v2, inner_dup);

    let one = manager.mk_int(1);
    let k1 = manager.mk_eq(idx, one);
    let v1 = manager.mk_int(10);
    let spine = manager.mk_ite(k1, v1, inner2);

    let top = manager.mk_eq(r, spine);
    solver.assert(top, &mut manager);

    assert!(
        solver.lookup_index_terms.contains(&idx),
        "a spine with a repeated key is still a spine and must be flattened"
    );

    // Semantic check, not just bookkeeping: with idx pinned to 1, the model
    // must land on the *first* arm's value (10), never the dead arm's (999).
    let one = manager.mk_int(1);
    let pin = manager.mk_eq(idx, one);
    solver.assert(pin, &mut manager);
    assert_eq!(solver.check(&mut manager), SolverResult::Sat);
    let model = solver.model().expect("sat must produce a model");
    let r_value = model.get(r).expect("r must be valued");
    assert_eq!(
        r_value,
        manager.mk_int(10),
        "idx = 1 must select the first (reachable) arm, not the dead duplicate"
    );
}

/// Two distinct keys of the same flattened index can never both hold: the
/// pairwise at-most-one clauses `flatten_lookup_spines` adds must make that
/// combination UNSAT outright, without needing arithmetic reasoning at all.
#[test]
fn test_pr32_at_most_one_key_holds_at_once() {
    let mut manager = TermManager::new();
    let mut solver = Solver::new();
    let int = manager.sorts.int_sort;
    let idx = manager.mk_var("idx", int);
    let r = manager.mk_var("r", int);

    let default = manager.mk_int(0);
    let mut chain = default;
    for (key, value) in [(3i64, 30i64), (2, 20), (1, 10)] {
        let k = manager.mk_int(key);
        let v = manager.mk_int(value);
        let eq = manager.mk_eq(idx, k);
        chain = manager.mk_ite(eq, v, chain);
    }
    let top = manager.mk_eq(r, chain);
    solver.assert(top, &mut manager);
    assert!(solver.lookup_index_terms.contains(&idx));

    let one = manager.mk_int(1);
    let two = manager.mk_int(2);
    let eq1 = manager.mk_eq(idx, one);
    let eq2 = manager.mk_eq(idx, two);
    let both = manager.mk_and([eq1, eq2]);
    solver.assert(both, &mut manager);

    assert_eq!(
        solver.check(&mut manager),
        SolverResult::Unsat,
        "idx cannot equal two distinct keys of the same flattened table at once"
    );
}
