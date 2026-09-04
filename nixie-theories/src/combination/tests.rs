//! Unit tests for [`super`]'s Nelson-Oppen theory combination.
//!
//! Moved out of `combination.rs` verbatim (no test was changed) so that file
//! stays under the workspace's 2000-line limit.

use super::*;

impl TheoryCombiner {
    /// Check if a lemma is cached (exact match) – test helper only
    fn is_lemma_cached(&self, lemma: &TheoryLemma) -> bool {
        self.lemma_cache.contains_key(lemma)
    }
}

#[test]
fn test_theory_combiner_basic() {
    let mut combiner = TheoryCombiner::new();

    // Create some shared variables
    let x = TermId::new(1);
    let y = TermId::new(2);

    combiner.add_shared_var(x);
    combiner.add_shared_var(y);

    assert!(combiner.shared_vars().contains(&x));
    assert!(combiner.shared_vars().contains(&y));

    // Check should succeed with no constraints
    assert!(matches!(combiner.check(), Ok(TheoryResult::Sat)));
}

#[test]
fn test_nelson_oppen_terminates_with_equal_shared_pair() {
    // Regression (audit theories-p3): once two shared variables are EUF-equal,
    // extract_euf_equalities re-reports the pair every round. Without
    // deduplication check() spins forever. This test must simply RETURN.
    let mut combiner = TheoryCombiner::new();

    let a = TermId::new(1);
    let b = TermId::new(2);
    combiner.add_shared_var(a);
    combiner.add_shared_var(b);

    // Make a and b equal inside EUF.
    let na = combiner.euf_mut().intern(a);
    let nb = combiner.euf_mut().intern(b);
    combiner
        .euf_mut()
        .merge(na, nb, TermId::new(0))
        .expect("merge must not error");

    // Must terminate (previously looped forever) and report Sat.
    let result = combiner.check().expect("check must not error");
    assert!(matches!(result, TheoryResult::Sat));
}

#[test]
fn test_theory_combiner_push_pop() {
    let mut combiner = TheoryCombiner::new();

    let x = TermId::new(1);
    combiner.add_shared_var(x);

    combiner.push();

    let y = TermId::new(2);
    combiner.add_shared_var(y);

    assert!(combiner.shared_vars().contains(&y));

    combiner.pop();

    // x should still be there (we can't easily remove from HashSet)
    assert!(combiner.shared_vars().contains(&x));
}

#[test]
fn test_purifier() {
    let mut purifier = Purifier::new();

    let original = TermId::new(100);
    let fresh = purifier.fresh_var();

    purifier.add_purification(original, fresh, TheoryId::LRA);

    assert_eq!(purifier.get_purified(original), Some(fresh));
    assert_eq!(purifier.constraints().len(), 1);
    assert_eq!(purifier.constraints()[0].theory, TheoryId::LRA);
}

#[test]
fn test_equality_propagation() {
    let mut combiner = TheoryCombiner::new();

    let x = TermId::new(1);
    let y = TermId::new(2);

    combiner.add_shared_var(x);
    combiner.add_shared_var(y);

    // Propagate x = y from EUF
    combiner.propagate_equality(x, y, TheoryId::EUF);

    // Process the propagation
    let result = combiner.propagate();
    assert!(matches!(result, Ok(TheoryResult::Sat)));
}

#[test]
fn test_relevancy_tracking() {
    let mut combiner = TheoryCombiner::new();

    let x = TermId::new(1);
    let y = TermId::new(2);
    let z = TermId::new(3);

    // Initially, with empty relevant set, all terms are considered relevant
    assert!(combiner.is_relevant(x));
    assert!(combiner.is_relevant(y));

    // Mark x as relevant
    combiner.mark_relevant(x);
    assert!(combiner.is_relevant(x));
    assert!(!combiner.is_relevant(y)); // y is not relevant now
    assert!(!combiner.is_relevant(z)); // z is not relevant

    // Check statistics
    assert_eq!(combiner.stats().relevancy_propagations, 1);

    // Marking same term again shouldn't increment counter
    combiner.mark_relevant(x);
    assert_eq!(combiner.stats().relevancy_propagations, 1);

    // Mark another term
    combiner.mark_relevant(y);
    assert_eq!(combiner.stats().relevancy_propagations, 2);
}

#[test]
fn test_theory_combination_statistics() {
    let mut combiner = TheoryCombiner::new();

    // Initially stats are zero
    assert_eq!(combiner.stats().theory_checks, 0);
    assert_eq!(combiner.stats().equalities_propagated, 0);

    // Run a check
    let _ = combiner.check();
    assert_eq!(combiner.stats().theory_checks, 1);

    // Reset statistics
    combiner.reset_stats();
    assert_eq!(combiner.stats().theory_checks, 0);
}

#[test]
fn test_minimize_conflict_empty() {
    let mut combiner = TheoryCombiner::new();

    let result = combiner
        .minimize_conflict(&[])
        .expect("test operation should succeed");
    assert!(result.is_empty());
}

#[test]
fn test_minimize_by_theory() {
    let mut combiner = TheoryCombiner::new();

    let x = TermId::new(1);
    let y = TermId::new(2);
    let z = TermId::new(3);

    // Register terms with theories
    combiner.register_term(x, TheoryId::EUF);
    combiner.register_term(y, TheoryId::LRA);
    combiner.register_term(z, TheoryId::EUF);

    let assumptions = vec![x, y, z];
    let result = combiner
        .minimize_by_theory(&assumptions)
        .expect("test operation should succeed");

    // Result should contain all assumptions (grouped by theory)
    assert_eq!(result.len(), 3);
    assert!(result.contains(&x));
    assert!(result.contains(&y));
    assert!(result.contains(&z));
}

#[test]
fn test_presolve() {
    let mut combiner = TheoryCombiner::new();

    // Presolve returns stats
    let stats = combiner.presolve().expect("test operation should succeed");

    // With no constraints, no simplifications are performed
    assert_eq!(stats.vars_eliminated, 0);
    assert_eq!(stats.singleton_propagations, 0);
    assert_eq!(stats.constraints_removed, 0);
    assert_eq!(stats.equality_substitutions, 0);
}

#[test]
fn test_combination_modes() {
    let combiner_no = TheoryCombiner::with_mode(CombinationMode::NelsonOppen);
    assert_eq!(combiner_no.mode(), CombinationMode::NelsonOppen);

    let combiner_mb = TheoryCombiner::with_mode(CombinationMode::ModelBased);
    assert_eq!(combiner_mb.mode(), CombinationMode::ModelBased);

    let combiner_delayed = TheoryCombiner::with_mode(CombinationMode::Delayed);
    assert_eq!(combiner_delayed.mode(), CombinationMode::Delayed);
}

#[test]
fn test_lemma_cache() {
    let mut combiner = TheoryCombiner::new();

    assert_eq!(combiner.lemma_cache_size(), 0);

    // Cache a lemma
    let lemma = TheoryLemma {
        assumptions: vec![TermId::new(1)],
        conclusion: vec![TermId::new(2)],
        theory: TheoryId::EUF,
    };
    combiner.cache_lemma(lemma.clone());

    assert_eq!(combiner.lemma_cache_size(), 1);
    assert_eq!(combiner.stats().lemmas_cached, 1);

    // Caching same lemma again shouldn't increase size
    combiner.cache_lemma(lemma);
    assert_eq!(combiner.lemma_cache_size(), 1);
    assert_eq!(combiner.stats().lemmas_cached, 1);

    // Clear cache
    combiner.clear_cache();
    assert_eq!(combiner.lemma_cache_size(), 0);
}

#[test]
fn test_lemma_subsumption() {
    // Test subsumption logic
    let weak_lemma = TheoryLemma {
        assumptions: vec![TermId::new(1), TermId::new(2)],
        conclusion: vec![TermId::new(3)],
        theory: TheoryId::EUF,
    };

    let strong_lemma = TheoryLemma {
        assumptions: vec![TermId::new(1)],
        conclusion: vec![TermId::new(3)],
        theory: TheoryId::EUF,
    };

    // strong_lemma is stronger (proves same conclusion with fewer assumptions)
    assert!(strong_lemma.is_stronger_than(&weak_lemma));
    assert!(strong_lemma.subsumes(&weak_lemma));
    assert!(!weak_lemma.subsumes(&strong_lemma));
}

#[test]
fn test_lemma_subsumption_caching() {
    let mut combiner = TheoryCombiner::new();

    // Cache a weaker lemma first
    let weak_lemma = TheoryLemma {
        assumptions: vec![TermId::new(1), TermId::new(2)],
        conclusion: vec![TermId::new(3)],
        theory: TheoryId::EUF,
    };
    combiner.cache_lemma(weak_lemma);
    assert_eq!(combiner.lemma_cache_size(), 1);

    // Cache a stronger lemma - should replace the weaker one
    let strong_lemma = TheoryLemma {
        assumptions: vec![TermId::new(1)],
        conclusion: vec![TermId::new(3)],
        theory: TheoryId::EUF,
    };
    combiner.cache_lemma(strong_lemma.clone());

    // Only the stronger lemma should be cached
    assert_eq!(combiner.lemma_cache_size(), 1);

    // The stronger lemma should be in the cache
    assert!(combiner.is_lemma_cached(&strong_lemma));
}

#[test]
fn test_is_lemma_subsumed() {
    let mut combiner = TheoryCombiner::new();

    // Cache a strong lemma
    let strong_lemma = TheoryLemma {
        assumptions: vec![TermId::new(1)],
        conclusion: vec![TermId::new(3)],
        theory: TheoryId::EUF,
    };
    combiner.cache_lemma(strong_lemma);

    // Test if a weaker lemma is subsumed
    assert!(combiner.is_lemma_subsumed(
        &[TermId::new(1), TermId::new(2)],
        &[TermId::new(3)],
        TheoryId::EUF
    ));

    // Test if a non-subsumed lemma is not detected
    assert!(!combiner.is_lemma_subsumed(&[TermId::new(5)], &[TermId::new(6)], TheoryId::EUF));
}

// ======== New LRU-cache integration tests ========

#[test]
fn test_lru_cache_evicts_at_capacity() {
    use crate::lru_cache::LruCache;
    let mut cache: LruCache<i32, ()> = LruCache::new(3);
    cache.insert(1, ());
    cache.insert(2, ());
    cache.insert(3, ());
    cache.insert(4, ()); // should evict 1 (LRU)
    assert!(!cache.contains_key(&1), "entry 1 should have been evicted");
    assert!(cache.contains_key(&4), "entry 4 should be present");
    assert_eq!(cache.len(), 3);
}

#[test]
fn test_lru_cache_truncate_to() {
    use crate::lru_cache::LruCache;
    let mut cache: LruCache<i32, ()> = LruCache::new(100);
    for i in 0..5 {
        cache.insert(i, ());
    }
    cache.truncate_to(2);
    assert_eq!(cache.len(), 2);
}

#[test]
fn test_lru_cache_iter_yields_all() {
    use crate::lru_cache::LruCache;
    let mut cache: LruCache<i32, ()> = LruCache::new(10);
    for i in 0..3 {
        cache.insert(i, ());
    }
    assert_eq!(cache.iter().count(), 3);
}

#[test]
fn test_lemma_cache_enforces_max_size() {
    // Create a combiner with a tiny cache and push many lemmas
    let mut combiner = TheoryCombiner::with_max_lemma_cache_size(5);

    for i in 0..10_u32 {
        let lemma = TheoryLemma {
            assumptions: vec![TermId::new(100 + i)],
            conclusion: vec![TermId::new(200 + i)],
            theory: TheoryId::EUF,
        };
        combiner.cache_lemma(lemma);
    }

    // The LRU cache must enforce the capacity
    assert!(
        combiner.lemma_cache_size() <= 5,
        "lemma cache exceeded max size: {}",
        combiner.lemma_cache_size()
    );
}

#[test]
fn test_lemma_cache_stats_exposed() {
    use crate::lru_cache::LruCache;
    let mut cache: LruCache<i32, i32> = LruCache::new(3);
    cache.insert(1, 10);
    let _ = cache.get(&1); // hit
    let _ = cache.get(&99); // miss
    let (hits, misses, _evictions) = cache.stats();
    assert!(
        hits > 0 || misses > 0,
        "at least one stat should be nonzero"
    );
}

// Audit regression (theories-combination): `extract_arrangement_from_arith`
// used to unconditionally assert a disequality for EVERY pair of shared
// variables ("for now, assume they're different"), regardless of their
// actual arithmetic values. It must instead partition shared variables
// by their real arithmetic-model value: same value -> equality,
// different value -> disequality.
#[test]
fn audit_extract_arrangement_reflects_arithmetic_values() {
    let mut combiner = TheoryCombiner::new();
    let x = TermId::new(1);
    let y = TermId::new(2);
    let z = TermId::new(3);
    combiner.add_shared_var(x);
    combiner.add_shared_var(y);
    combiner.add_shared_var(z);

    combiner.arith_mut().assert_eq(
        &[(x, Rational64::from_integer(1))],
        Rational64::from_integer(5),
        TermId::new(10),
    );
    combiner.arith_mut().assert_eq(
        &[(y, Rational64::from_integer(1))],
        Rational64::from_integer(5),
        TermId::new(11),
    );
    combiner.arith_mut().assert_eq(
        &[(z, Rational64::from_integer(1))],
        Rational64::from_integer(7),
        TermId::new(12),
    );
    combiner
        .arith_mut()
        .check()
        .expect("arithmetic check should succeed");

    let arrangement = combiner.extract_arrangement_from_arith();

    let has_pair = |pairs: &[(TermId, TermId)], p: TermId, q: TermId| {
        pairs
            .iter()
            .any(|&(a, b)| (a == p && b == q) || (a == q && b == p))
    };

    assert!(
        has_pair(&arrangement.equalities, x, y),
        "x and y share the same arithmetic value (5) and must be arranged equal"
    );
    assert!(
        !has_pair(&arrangement.disequalities, x, y),
        "x and y must NOT be arranged disequal when they share a value \
         (the old bug asserted every pair disequal unconditionally)"
    );
    assert!(
        has_pair(&arrangement.disequalities, x, z) || has_pair(&arrangement.disequalities, y, z),
        "the value-7 group (z) must be arranged disequal from the value-5 group (x, y)"
    );
}

// Audit regression (theories-combination): `propagate()` never actually
// forwarded an equality into arithmetic when it originated elsewhere
// ("Arithmetic propagation would be implemented here" -- a no-op). If
// arithmetic already has conflicting information about the two
// propagated terms, forwarding the equality must now surface that
// conflict instead of silently doing nothing.
#[test]
fn audit_propagate_forwards_equality_to_arithmetic() {
    let mut combiner = TheoryCombiner::new();
    let x = TermId::new(1);
    let y = TermId::new(2);
    combiner.add_shared_var(x);
    combiner.add_shared_var(y);

    // Both already known to arithmetic, with DIFFERENT values.
    combiner.arith_mut().assert_eq(
        &[(x, Rational64::from_integer(1))],
        Rational64::from_integer(3),
        TermId::new(10),
    );
    combiner.arith_mut().assert_eq(
        &[(y, Rational64::from_integer(1))],
        Rational64::from_integer(9),
        TermId::new(11),
    );

    combiner.propagate_equality(x, y, TheoryId::EUF);
    let result = combiner.propagate().expect("propagate must not error");
    // `notify_equality` itself only ADDS the `x = y` constraint to the
    // simplex (it does not re-run `check()`), so `propagate()` succeeding
    // is expected here; the real assertion is that arithmetic actually
    // received the constraint at all.
    assert!(matches!(result, TheoryResult::Sat));

    // Now that arithmetic actually has `x = y` (alongside the
    // previously-asserted `x = 3` and `y = 9`), its own `check()` must
    // find the resulting inconsistency. Before this fix, `propagate()`
    // never forwarded the equality at all, so arithmetic would never
    // have learned about it and this `check()` would incorrectly stay
    // `Sat`.
    let arith_result = combiner
        .arith_mut()
        .check()
        .expect("arithmetic check must not error");
    assert!(
        matches!(arith_result, TheoryResult::Unsat(_)),
        "arithmetic must detect x=3 & y=9 & x=y as inconsistent once the \
         equality actually reaches the simplex; got {arith_result:?}"
    );
}

// Audit regression (theories-combination): `propagate()`'s arithmetic
// forwarding must not treat "arithmetic doesn't know these terms" as a
// conflict (that would break the ordinary case of propagating a
// pure-EUF equality between terms arithmetic never interned).
#[test]
fn audit_propagate_ignores_terms_arithmetic_does_not_know() {
    let mut combiner = TheoryCombiner::new();
    let x = TermId::new(1);
    let y = TermId::new(2);
    combiner.add_shared_var(x);
    combiner.add_shared_var(y);

    combiner.propagate_equality(x, y, TheoryId::EUF);
    let result = combiner.propagate().expect("propagate must not error");
    assert!(
        matches!(result, TheoryResult::Sat),
        "propagating an equality between terms arithmetic never interned \
         must not be treated as a conflict; got {result:?}"
    );
}

// Audit regression (theories-combination): `extract_assignments` used
// to map every term trivially to itself, ignoring the equalities in
// `model` entirely. It must compute real union-find equivalence
// classes (including transitive equalities).
#[test]
fn audit_extract_assignments_uses_real_union_find() {
    let combiner = TheoryCombiner::new();
    let a = TermId::new(1);
    let b = TermId::new(2);
    let c = TermId::new(3);

    // a = b, b = c (transitively a = b = c).
    let model = vec![(a, b), (b, c)];
    let assignments = combiner.extract_assignments(&model);

    assert_eq!(
        assignments.get(&a),
        assignments.get(&c),
        "a and c must share a representative (transitively equal via b)"
    );
    assert_eq!(assignments.get(&a), assignments.get(&b));
}

// Audit regression (theories-combination): `verify_model` used to
// unconditionally return `true`. It must now actually check the
// model's claimed equalities against a component theory that knows
// about both terms.
#[test]
fn audit_verify_model_detects_euf_inconsistency() {
    let mut combiner = TheoryCombiner::new();
    let a = TermId::new(1);
    let b = TermId::new(2);

    // EUF knows about both `a` and `b` but does NOT consider them
    // equal (no merge performed).
    let _ = combiner.euf_mut().intern(a);
    let _ = combiner.euf_mut().intern(b);

    let model = vec![(a, b)];
    assert!(
        !combiner.verify_model(&model),
        "verify_model must reject a claimed equality EUF (which knows both terms) disagrees with"
    );
}

#[test]
fn audit_verify_model_accepts_euf_confirmed_equality() {
    let mut combiner = TheoryCombiner::new();
    let a = TermId::new(1);
    let b = TermId::new(2);

    let na = combiner.euf_mut().intern(a);
    let nb = combiner.euf_mut().intern(b);
    combiner
        .euf_mut()
        .merge(na, nb, TermId::new(99))
        .expect("merge must not error");

    let model = vec![(a, b)];
    assert!(
        combiner.verify_model(&model),
        "verify_model must accept an equality EUF actually confirms"
    );
}
