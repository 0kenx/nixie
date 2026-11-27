//! Tests for the explicit-stack backtracking E-matcher.
//!
//! These pin the three properties the conversion away from
//! `match_recursive` had to preserve or fix: both `Eq` orientations are
//! still explored, bindings made along a failed alternative are undone, and
//! neither depth nor nested equalities can blow up the native stack or the
//! search time.
//!
//! `Eq` nodes are built with [`TermManager::intern_term`] rather than
//! `mk_eq` on purpose: `mk_eq` canonicalises its operand order by `TermId`,
//! which would leave the stored orientation at the mercy of allocation
//! order and make "this only matches after swapping" untestable.

use super::*;
use crate::ast::TermManager;

/// Build `Eq(lhs, rhs)` with the operand order exactly as given.
fn eq_ordered(manager: &mut TermManager, lhs: TermId, rhs: TermId) -> TermId {
    let bool_sort = manager.sorts.bool_sort;
    manager.intern_term(TermKind::Eq(lhs, rhs), bool_sort)
}

/// The bound-variable list a `Pattern` would carry for `names`, all of
/// integer sort.
fn bound_int_vars(manager: &mut TermManager, names: &[&str]) -> SmallVec<[(Spur, SortId); 2]> {
    let int_sort = manager.sorts.int_sort;
    names
        .iter()
        .map(|name| (manager.intern_str(name), int_sort))
        .collect()
}

/// Resolve a substitution to a `(name, term)` list for readable assertions.
fn resolved(manager: &TermManager, subst: &FxHashMap<Spur, TermId>) -> Vec<(String, TermId)> {
    let mut out: Vec<(String, TermId)> = subst
        .iter()
        .map(|(&name, &term)| (manager.resolve_str(name).to_string(), term))
        .collect();
    out.sort_by(|a, b| a.0.cmp(&b.0));
    out
}

// ======== Eq orientations ========

/// `Eq(x, k)` matches `Eq(k, m)` only in the swapped orientation, and the
/// `x := k` binding made while the first orientation failed must not survive
/// to block it.
///
/// The retired recursion threaded one `&mut` binding map through
/// `(a && b) || (c && d)` with no undo, so it reported *no match* here.
#[test]
fn eq_orientation_swap_after_undoing_a_failed_binding() {
    let mut manager = TermManager::new();
    let int_sort = manager.sorts.int_sort;

    let x = manager.mk_var("x", int_sort);
    let k = manager.mk_var("k", int_sort);
    let m = manager.mk_var("m", int_sort);

    let pattern = eq_ordered(&mut manager, x, k);
    let ground = eq_ordered(&mut manager, k, m);

    let bound = bound_int_vars(&mut manager, &["x"]);
    let matcher = PatternMatcher::new();
    let subst = matcher
        .try_match_term(pattern, ground, &bound, &manager)
        .expect("Eq(x, k) matches Eq(k, m) with x := m after swapping");

    assert_eq!(resolved(&manager, &subst), vec![("x".to_string(), m)]);
}

/// A variable bound only while exploring a failed alternative must not
/// appear in the successful match's substitution.
///
/// `PatternMatcher::match_against` gates instantiation on "every bound
/// variable is assigned", so a leaked binding is not cosmetic: it lets the
/// quantifier be instantiated with a term the trigger never matched.
#[test]
fn failed_alternative_leaves_no_binding_behind() {
    let mut manager = TermManager::new();
    let int_sort = manager.sorts.int_sort;

    let y = manager.mk_var("y", int_sort);
    let k = manager.mk_var("k", int_sort);
    let k2 = manager.mk_var("k2", int_sort);

    // h(Eq(y, k), g(k)) against h(Eq(k, k2), g(k)): the equality's first
    // orientation binds y := k and then fails on (k, k2).
    let pattern_eq = eq_ordered(&mut manager, y, k);
    let ground_eq = eq_ordered(&mut manager, k, k2);
    let pattern_g = manager.mk_apply("g", vec![k], int_sort);
    let pattern = manager.mk_apply("h", vec![pattern_eq, pattern_g], int_sort);
    let ground = manager.mk_apply("h", vec![ground_eq, pattern_g], int_sort);

    let bound = bound_int_vars(&mut manager, &["y"]);
    let matcher = PatternMatcher::new();
    let subst = matcher
        .try_match_term(pattern, ground, &bound, &manager)
        .expect("second orientation matches with y := k2");

    // y := k came from the failed orientation and must be gone.
    assert_eq!(resolved(&manager, &subst), vec![("y".to_string(), k2)]);
}

/// Backtracking must reach across *sibling arguments*: the first argument
/// admits two orientations, and only the one the second argument agrees
/// with is a match.
#[test]
fn backtracks_across_sibling_arguments() {
    let mut manager = TermManager::new();
    let int_sort = manager.sorts.int_sort;

    let x = manager.mk_var("x", int_sort);
    let y = manager.mk_var("y", int_sort);
    let p = manager.mk_var("p", int_sort);
    let q = manager.mk_var("q", int_sort);

    // h(Eq(x, y), g(x)) vs h(Eq(p, q), g(q)).
    // Sibling 1 matches either way: {x:=p, y:=q} or {x:=q, y:=p}.
    // Sibling 2 forces x := q, so the first orientation must be retracted.
    let pattern_eq = eq_ordered(&mut manager, x, y);
    let ground_eq = eq_ordered(&mut manager, p, q);
    let pattern_g = manager.mk_apply("g", vec![x], int_sort);
    let ground_g = manager.mk_apply("g", vec![q], int_sort);
    let pattern = manager.mk_apply("h", vec![pattern_eq, pattern_g], int_sort);
    let ground = manager.mk_apply("h", vec![ground_eq, ground_g], int_sort);

    let bound = bound_int_vars(&mut manager, &["x", "y"]);
    let matcher = PatternMatcher::new();
    let subst = matcher
        .try_match_term(pattern, ground, &bound, &manager)
        .expect("the swapped orientation of sibling 1 agrees with sibling 2");

    assert_eq!(
        resolved(&manager, &subst),
        vec![("x".to_string(), q), ("y".to_string(), p)]
    );
}

/// Build a `depth`-level nested equality pair whose every level matches only
/// after swapping: `p_k = Eq(p_{k-1}, c_k)` against `g_k = Eq(c_k, g_{k-1})`.
///
/// Returns `(pattern, ground, expected binding for x)`.
fn nested_swapped_eq_chain(manager: &mut TermManager, depth: usize) -> (TermId, TermId, TermId) {
    let int_sort = manager.sorts.int_sort;
    let x = manager.mk_var("x", int_sort);
    let base = manager.mk_var("c0", int_sort);

    let mut pattern = x;
    let mut ground = base;
    for level in 1..=depth {
        let anchor = manager.mk_var(&format!("c{level}"), int_sort);
        pattern = eq_ordered(manager, pattern, anchor);
        ground = eq_ordered(manager, anchor, ground);
    }
    (pattern, ground, base)
}

/// Four levels of nested equalities, each needing the swapped orientation.
#[test]
fn four_level_nested_eq_matches_through_every_swap() {
    let mut manager = TermManager::new();
    let (pattern, ground, expected) = nested_swapped_eq_chain(&mut manager, 4);

    let bound = bound_int_vars(&mut manager, &["x"]);
    let matcher = PatternMatcher::new();
    let subst = matcher
        .try_match_term(pattern, ground, &bound, &manager)
        .expect("every level matches after swapping");

    assert_eq!(
        resolved(&manager, &subst),
        vec![("x".to_string(), expected)]
    );
}

/// The same shape at a depth where the retired `4^depth` `Eq` arm would not
/// finish: 16 levels is ~4.3e9 recursive calls there, and one backtracking
/// step per level here.
#[test]
fn nested_eq_does_not_blow_up_exponentially() {
    let mut manager = TermManager::new();
    let (pattern, ground, expected) = nested_swapped_eq_chain(&mut manager, 16);

    let bound = bound_int_vars(&mut manager, &["x"]);
    let matcher = PatternMatcher::new();

    let started = nixie_time::Instant::now();
    let subst = matcher
        .try_match_term(pattern, ground, &bound, &manager)
        .expect("every level matches after swapping");
    let elapsed = started.elapsed();

    assert_eq!(
        resolved(&manager, &subst),
        vec![("x".to_string(), expected)]
    );
    assert!(
        elapsed < nixie_time::Duration::from_secs(10),
        "16 nested equalities took {elapsed:?}; the search is no longer linear"
    );
}

// ======== Non-matches still fail (and fail fast) ========

#[test]
fn arity_and_head_mismatches_reject() {
    let mut manager = TermManager::new();
    let int_sort = manager.sorts.int_sort;

    let x = manager.mk_var("x", int_sort);
    let a = manager.mk_var("a", int_sort);
    let b = manager.mk_var("b", int_sort);

    let pattern = manager.mk_apply("f", vec![x, x], int_sort);
    let wrong_arity = manager.mk_apply("f", vec![a], int_sort);
    let wrong_head = manager.mk_apply("g", vec![a, b], int_sort);
    let inconsistent = manager.mk_apply("f", vec![a, b], int_sort);

    let bound = bound_int_vars(&mut manager, &["x"]);
    let matcher = PatternMatcher::new();

    assert!(
        matcher
            .try_match_term(pattern, wrong_arity, &bound, &manager)
            .is_none()
    );
    assert!(
        matcher
            .try_match_term(pattern, wrong_head, &bound, &manager)
            .is_none()
    );
    // f(x, x) vs f(a, b): the repeated variable cannot be both.
    assert!(
        matcher
            .try_match_term(pattern, inconsistent, &bound, &manager)
            .is_none()
    );
}

// ======== Deep regression: no native stack involved ========

/// A 50 000-level pattern and ground term matched on a 1 MiB stack.
///
/// The retired `match_recursive` needed one native frame per level in both
/// the `Apply` chain and the `Eq` chain, so either half of this overflowed
/// and aborted the process. Both halves are now heap-stack walks.
#[test]
fn deep_pattern_and_term_match_on_a_small_stack() {
    const DEPTH: usize = 50_000;
    const STACK_SIZE: usize = 1 << 20;

    let worker = std::thread::Builder::new()
        .stack_size(STACK_SIZE)
        .spawn(|| {
            let mut manager = TermManager::new();
            let int_sort = manager.sorts.int_sort;

            // Half 1: f(f(...f(x)...)) against f(f(...f(a)...)).
            let x = manager.mk_var("x", int_sort);
            let a = manager.mk_var("a", int_sort);
            let mut pattern = x;
            let mut ground = a;
            for _ in 0..DEPTH {
                pattern = manager.mk_apply("f", vec![pattern], int_sort);
                ground = manager.mk_apply("f", vec![ground], int_sort);
            }

            let bound = bound_int_vars(&mut manager, &["x"]);
            let matcher = PatternMatcher::new();
            let subst = matcher
                .try_match_term(pattern, ground, &bound, &manager)
                .expect("a deep unary chain matches");
            assert_eq!(subst.len(), 1);

            // Half 2: the same depth of nested equalities, every level
            // requiring the swapped orientation (so every level also
            // creates and consumes a choice point).
            let (deep_pattern, deep_ground, expected) =
                nested_swapped_eq_chain(&mut manager, DEPTH);
            let deep_subst = matcher
                .try_match_term(deep_pattern, deep_ground, &bound, &manager)
                .expect("a deep equality chain matches after swapping at every level");
            assert_eq!(
                resolved(&manager, &deep_subst),
                vec![("x".to_string(), expected)]
            );
        })
        .expect("spawning the 1 MiB worker thread");

    worker.join().expect("the deep match must not overflow");
}

// ======== Multi-trigger join ========

/// The retired multi-trigger merge, kept as the oracle over the matcher's
/// own partial substitutions: the pairwise cross product of one trigger's
/// matches with the next's, a consistency test per pair, a binding per
/// complete merge in the order the product visited them.
fn cross_product_bindings(
    matcher: &PatternMatcher,
    triggers: &[TermId],
    bound: &[(Spur, SortId)],
    ground: &GroundTermCollector,
    manager: &TermManager,
) -> Vec<Binding> {
    let mut levels: Vec<Vec<FxHashMap<Spur, TermId>>> = Vec::new();
    for &trigger in triggers {
        let mut partial = Vec::new();
        for &term in ground.all_terms() {
            partial.extend(matcher.try_match_term(trigger, term, bound, manager));
        }
        levels.push(partial);
    }
    let mut combined = levels.remove(0);
    for next in levels {
        let mut merged = Vec::new();
        for one in &combined {
            for two in &next {
                let consistent = two
                    .iter()
                    .all(|(&var, &term)| one.get(&var).is_none_or(|bound| *bound == term));
                if consistent {
                    let mut subst = one.clone();
                    subst.extend(two.iter().map(|(&var, &term)| (var, term)));
                    merged.push(subst);
                }
            }
        }
        combined = merged;
    }
    combined
        .into_iter()
        .filter(|subst| bound.iter().all(|(name, _)| subst.contains_key(name)))
        .map(|substitution| Binding {
            pattern_idx: 0,
            substitution,
        })
        .collect()
}

/// `forall x. (or (f x) (g x))` under the two-trigger pattern `((f x) (g x))`
/// over `n` values on each side, with `p` and `q` thrown in as non-matching
/// ground terms; the matcher and the collector are built once per call.
fn two_trigger_problem(
    manager: &mut TermManager,
    n: u32,
    second_trigger: &str,
) -> (PatternMatcher, GroundTermCollector, Vec<TermId>) {
    let int_sort = manager.sorts.int_sort;
    let bool_sort = manager.sorts.bool_sort;
    let x = manager.mk_var("x", int_sort);
    let y = manager.mk_var("y", int_sort);
    let f_x = manager.mk_apply("f", [x], bool_sort);
    let second = manager.mk_apply(
        second_trigger,
        [if second_trigger == "h" { y } else { x }],
        bool_sort,
    );
    let body = manager.mk_or([f_x, second]);
    let vars: Vec<(&str, crate::sort::SortId)> = if second_trigger == "h" {
        vec![("x", int_sort), ("y", int_sort)]
    } else {
        vec![("x", int_sort)]
    };
    let forall = manager.mk_forall_with_patterns(vars, body, [[f_x, second]]);

    let mut ground = Vec::new();
    for i in 0..n {
        let k = manager.mk_int(i as i64);
        ground.push(manager.mk_apply("f", [k], bool_sort));
        ground.push(manager.mk_apply(second_trigger, [k], bool_sort));
    }
    let p = manager.mk_var("p", bool_sort);
    let q = manager.mk_var("q", bool_sort);
    ground.push(p);
    ground.push(q);
    let goal = crate::tactic::Goal::new(ground);

    let mut matcher = PatternMatcher::new();
    matcher.add_pattern(forall, manager);
    let mut collector = GroundTermCollector::new();
    collector.collect_from_goal(&goal, manager);
    (matcher, collector, vec![f_x, second])
}

/// The indexed join produces the bindings the pairwise cross product did,
/// binding for binding in order, for triggers sharing their variable (n
/// bindings from n matches a side) and for triggers over disjoint
/// variables (n² bindings).
#[test]
fn multi_trigger_join_is_the_cross_product_in_order() {
    let mut manager = TermManager::new();
    for (second, per_side, expected) in [("g", 40u32, 40usize), ("h", 12u32, 144usize)] {
        let (mut matcher, collector, triggers) =
            two_trigger_problem(&mut manager, per_side, second);
        let names: Vec<&str> = if second == "h" {
            vec!["x", "y"]
        } else {
            vec!["x"]
        };
        let bound = bound_int_vars(&mut manager, &names);
        let oracle = cross_product_bindings(&matcher, &triggers, &bound, &collector, &manager);
        assert_eq!(oracle.len(), expected, "oracle for {second}");
        let joined = matcher.match_against(&collector, &manager);
        assert_eq!(joined.len(), expected, "join for {second}");
        for (joined, oracle) in joined.iter().zip(&oracle) {
            assert_eq!(joined.pattern_idx, oracle.pattern_idx);
            assert_eq!(
                resolved(&manager, &joined.substitution),
                resolved(&manager, &oracle.substitution)
            );
        }
    }
}

/// `match_against_within` yields the first `limit` bindings of the
/// unlimited list, in its order – for a single trigger and for a
/// multi-trigger whose product is far larger than the limit.
#[test]
fn limited_matching_yields_a_prefix_of_the_unlimited_bindings() {
    let mut manager = TermManager::new();
    for (second, per_side) in [("g", 64u32), ("h", 64u32)] {
        let (mut matcher, collector, _) = two_trigger_problem(&mut manager, per_side, second);
        let all = matcher.match_against(&collector, &manager);
        assert!(all.len() > 7);
        for limit in [0usize, 1, 7, all.len() - 1, all.len(), all.len() + 5] {
            // A fresh matcher per limit: its deduplication remembers the
            // bindings an earlier call produced.
            let (mut fresh, _, _) = two_trigger_problem(&mut manager, per_side, second);
            let limited = fresh.match_against_within(&collector, &manager, limit);
            let take = limit.min(all.len());
            assert_eq!(limited.len(), take, "{second} at limit {limit}");
            for (limited, unlimited) in limited.iter().zip(&all[..take]) {
                assert_eq!(
                    resolved(&manager, &limited.substitution),
                    resolved(&manager, &unlimited.substitution)
                );
            }
        }
    }
}
