//! Unit tests for [`super::MBQIIntegration`].
//!
//! Split out into its own file (rather than an inline `mod tests` at the bottom
//! of `integration/mod.rs`) purely to keep that file under the workspace's
//! 2000-line-per-file ceiling.  As a child of the module that defines
//! `MBQIIntegration`, this file still sees its private fields, so every access
//! below (e.g. `integration.extra_candidates`) resolves exactly as an inline
//! `mod tests` would.
use super::*;

#[test]
fn test_mbqi_integration_creation() {
    let integration = MBQIIntegration::new();
    assert_eq!(integration.quantifiers.len(), 0);
    assert_eq!(integration.current_round, 0);
}

#[test]
fn test_default_callback() {
    let mut callback = DefaultCallback::new();
    assert!(!callback.should_stop());
    callback.request_stop();
    assert!(callback.should_stop());
}

#[test]
fn test_integration_clear() {
    let mut integration = MBQIIntegration::new();
    integration.current_round = 5;
    integration.clear();
    assert_eq!(integration.current_round, 0);
    assert_eq!(integration.quantifiers.len(), 0);
}

#[test]
fn test_set_max_rounds() {
    let mut integration = MBQIIntegration::new();
    integration.set_max_rounds(50);
    assert_eq!(integration.max_rounds, 50);
}

/// Regression test for the audit finding that `set_max_rounds` was
/// ineffective: `run()` used to reset `current_round` to `0` on every
/// call, so `current_round >= max_rounds` could never fire (barring
/// `max_rounds == 0`). `run()` is invoked once per outer solver
/// iteration (see `check_with_model`, called from `solver::mod::solve`),
/// so `current_round` must accumulate *across* calls for the limit to
/// bound the total number of MBQI rounds for a single solve.
#[test]
fn test_audit_max_rounds_accumulates_and_is_enforced() {
    let mut manager = TermManager::new();
    let int_sort = manager.sorts.int_sort;
    let x = manager.mk_var("x", int_sort);
    let zero = manager.mk_int(0);
    // `forall x. f(x) > 0` over the infinite Int domain: neither
    // trivially valid nor finitely exhaustible, so successive `run()`
    // calls never resolve to `Satisfied` and keep consuming rounds.
    let f_x = manager.mk_apply("f", [x], int_sort);
    let body = manager.mk_gt(f_x, zero);
    let forall = manager.mk_forall([("x", int_sort)], body);

    let mut integration = MBQIIntegration::new();
    integration.add_quantifier(forall, &manager);
    integration.set_max_rounds(2);

    let model = FxHashMap::default();
    for _ in 0..2 {
        let _ = integration.check_with_model(&model, &mut manager);
    }
    assert_eq!(
        integration.current_round, 2,
        "current_round must persist/accumulate across calls, not reset to 0 each run()"
    );

    // A further call must now be refused purely on the round limit,
    // without incrementing current_round any further.
    let result = integration.check_with_model(&model, &mut manager);
    assert!(
        matches!(result, MBQIResult::Unknown),
        "expected Unknown once max_rounds is exhausted, got {result:?}"
    );
    assert_eq!(
        integration.current_round, 2,
        "run() must return before incrementing once the round limit is hit"
    );
}

#[test]
fn test_set_time_limit() {
    let mut integration = MBQIIntegration::new();
    let limit = Duration::from_secs(30);
    integration.set_time_limit(limit);
    assert_eq!(integration.time_limit, Some(limit));
}

/// Regression test for the audit finding that `collect_ground_terms`
/// was an empty stub: trigger patterns never seeded candidates.
/// A trigger `g(0)` (fully ground: no `Var` anywhere in its subtree)
/// must now register both `g(0)` itself and the literal `0` as
/// candidates for their respective sorts, while a trigger containing a
/// bound variable (`f(x)`) must register nothing, since `f(x)` is not
/// ground under any binder-free interpretation.
#[test]
fn test_audit_collect_ground_terms_seeds_candidates() {
    let mut manager = TermManager::new();
    let int_sort = manager.sorts.int_sort;

    let zero = manager.mk_int(0);
    let g_zero = manager.mk_apply("g", [zero], int_sort);

    let mut integration = MBQIIntegration::new();
    integration.collect_ground_terms(g_zero, &manager);

    let candidates = integration
        .extra_candidates
        .get(&int_sort)
        .cloned()
        .unwrap_or_default();
    assert!(
        candidates.contains(&g_zero),
        "the fully ground trigger term itself must be seeded as a candidate"
    );
    assert!(
        candidates.contains(&zero),
        "ground subterms of the trigger must also be seeded as candidates"
    );

    // A trigger containing a `Var` occurrence anywhere (e.g. the bound
    // variable `x` of the enclosing quantifier) must not add any new
    // candidates: it isn't ground.
    let mut integration2 = MBQIIntegration::new();
    let x = manager.mk_var("x", int_sort);
    let f_x = manager.mk_apply("f", [x], int_sort);
    integration2.collect_ground_terms(f_x, &manager);
    assert!(
        integration2.extra_candidates.is_empty(),
        "a trigger containing a Var occurrence must not be treated as ground"
    );
}

// ---------------------------------------------------------------------
// Audit regression tests (solver-mbqi)
// ---------------------------------------------------------------------

use num_bigint::BigInt;

/// Finding #1 (integration.rs:296): a universal quantifier over the
/// *infinite* Int domain must NEVER be reported `Satisfied` (sat) merely
/// because a finite sample of candidate values did not falsify it.
///
/// `(forall ((x Int)) (>= x (- 10)))` is false at `x = -11`, yet the finite
/// candidate sampler only tries roughly `-2..=5`, all of which satisfy the
/// body.  The result must be non-sat (Unknown / instantiations), never
/// Satisfied.
#[test]
fn test_audit_infinite_int_domain_not_satisfied() {
    let mut manager = TermManager::new();
    let int_sort = manager.sorts.int_sort;
    let x = manager.mk_var("x", int_sort);
    let neg_ten = manager.mk_int(BigInt::from(-10));
    let body = manager.mk_ge(x, neg_ten);
    let forall = manager.mk_forall([("x", int_sort)], body);

    let mut integration = MBQIIntegration::new();
    integration.add_quantifier(forall, &manager);

    let model = FxHashMap::default();
    let result = integration.check_with_model(&model, &mut manager);
    assert!(
        !result.is_sat(),
        "forall x:Int. x >= -10 is false at x=-11 and must NOT be reported \
         Satisfied from a finite candidate sample, got {result:?}"
    );
}

/// Finding #1: classification of which sorts the counterexample generator
/// can enumerate exhaustively.  Bool is exhaustible; Int/Real/String are
/// not (infinite); BitVec is not (only sampled).
#[test]
fn test_audit_sort_finitely_exhausted_classification() {
    let mut manager = TermManager::new();
    let integration = MBQIIntegration::new();
    let model = CompletedModel::new();

    let bool_sort = manager.sorts.bool_sort;
    let int_sort = manager.sorts.int_sort;
    let real_sort = manager.sorts.real_sort;
    let bv_sort = manager.sorts.bitvec(8);

    assert!(
        integration.sort_finitely_exhausted(bool_sort, &model, &manager),
        "Bool is a genuinely finite, fully-enumerated domain"
    );
    assert!(
        !integration.sort_finitely_exhausted(int_sort, &model, &manager),
        "Int is infinite and must not be treated as exhausted"
    );
    assert!(
        !integration.sort_finitely_exhausted(real_sort, &model, &manager),
        "Real is infinite and must not be treated as exhausted"
    );
    assert!(
        !integration.sort_finitely_exhausted(bv_sort, &model, &manager),
        "BitVec is only sampled, never fully enumerated by the candidate sampler"
    );
}

/// Finding #1: an uninterpreted sort is exhaustible only when the completed
/// model pins a small finite universe for it.  A universe larger than the
/// candidate limit is NOT fully enumerated.
#[test]
fn test_audit_uninterpreted_universe_exhaustion() {
    let mut manager = TermManager::new();
    let integration = MBQIIntegration::new();

    let spur = manager.intern_str("U");
    let u_sort = manager.sorts.intern(SortKind::Uninterpreted(spur));

    // No universe at all -> not exhausted.
    let empty_model = CompletedModel::new();
    assert!(!integration.sort_finitely_exhausted(u_sort, &empty_model, &manager));

    // Small universe (<= FINITE_ENUM_LIMIT) -> exhausted.
    let mut small_model = CompletedModel::new();
    for i in 0..3i64 {
        let v = manager.mk_int(BigInt::from(i));
        small_model.add_to_universe(u_sort, v);
    }
    assert!(
        integration.sort_finitely_exhausted(u_sort, &small_model, &manager),
        "a 3-element universe fits within FINITE_ENUM_LIMIT and is exhausted"
    );

    // Oversized universe (> FINITE_ENUM_LIMIT) -> not exhausted, because the
    // sampler truncates the candidate list and would miss elements.
    let mut big_model = CompletedModel::new();
    for i in 0..(FINITE_ENUM_LIMIT as i64 + 5) {
        let v = manager.mk_int(BigInt::from(i));
        big_model.add_to_universe(u_sort, v);
    }
    assert!(
        !integration.sort_finitely_exhausted(u_sort, &big_model, &manager),
        "a universe larger than FINITE_ENUM_LIMIT is not fully enumerated"
    );
}

/// Finding #1 (reviewer follow-up): the finite-domain gate must account for
/// the counterexample generator's *cartesian-product* enumeration cap, not
/// just per-variable finiteness.  `forall x,y,z : U. P` with a completed
/// model pinning |U| = 5 has 125 candidate tuples, but the generator
/// enumerates only the first `COMBINATION_ENUM_CAP` (= 100) and does not
/// flag the truncation.  Because P could be false only at an un-enumerated
/// tuple, the absence of a counterexample must NOT be reported `Satisfied`.
#[test]
fn test_audit_multivar_product_exceeds_combination_cap_not_exhausted() {
    let mut manager = TermManager::new();
    let spur = manager.intern_str("U");
    let u_sort = manager.sorts.intern(SortKind::Uninterpreted(spur));

    // Completed model with a 5-element universe for U.
    let mut model = CompletedModel::new();
    for i in 0..5i64 {
        let v = manager.mk_int(BigInt::from(i));
        model.add_to_universe(u_sort, v);
    }

    let build = |manager: &mut TermManager, n: usize| {
        let vars: Vec<(&str, SortId)> = ["x", "y", "z"][..n]
            .iter()
            .map(|&nm| (nm, u_sort))
            .collect();
        let body = manager.mk_true();
        let forall = manager.mk_forall(vars, body);
        let mut integration = MBQIIntegration::new();
        integration.add_quantifier(forall, manager);
        integration.quantifiers.clone()
    };

    let integration = MBQIIntegration::new();

    // 2 variables -> 5*5 = 25 <= 100: fully enumerated, may conclude sat.
    let q2 = build(&mut manager, 2);
    assert!(
        integration.all_domains_finitely_exhausted(&q2, &model, &manager),
        "2 vars over |U|=5 has 25 combinations (<= cap) and IS fully enumerated"
    );

    // 3 variables -> 5*5*5 = 125 > 100: truncated, must NOT conclude sat.
    let q3 = build(&mut manager, 3);
    assert!(
        !integration.all_domains_finitely_exhausted(&q3, &model, &manager),
        "3 vars over |U|=5 has 125 combinations (> cap); enumeration is \
         truncated so the domain is NOT exhaustively covered and MBQI must \
         not report Satisfied"
    );
}

/// Finding #1 (reviewer follow-up): a large number of Bool-quantified
/// variables also blows past the combination cap (2^n grows quickly), so
/// such a quantifier must not be treated as exhaustively enumerated even
/// though each individual Bool domain is trivially finite.
#[test]
fn test_audit_many_bool_vars_exceed_combination_cap() {
    let mut manager = TermManager::new();
    let bool_sort = manager.sorts.bool_sort;
    let model = CompletedModel::new();

    let build = |manager: &mut TermManager, n: usize| {
        let names = ["a", "b", "c", "d", "e", "f", "g", "h"];
        let vars: Vec<(&str, SortId)> = names[..n].iter().map(|&nm| (nm, bool_sort)).collect();
        let body = manager.mk_true();
        let forall = manager.mk_forall(vars, body);
        let mut integration = MBQIIntegration::new();
        integration.add_quantifier(forall, manager);
        integration.quantifiers.clone()
    };

    let integration = MBQIIntegration::new();

    // 6 Bool vars -> 2^6 = 64 <= 100: fully enumerated.
    let q6 = build(&mut manager, 6);
    assert!(
        integration.all_domains_finitely_exhausted(&q6, &model, &manager),
        "2^6 = 64 combinations fit within the cap"
    );

    // 7 Bool vars -> 2^7 = 128 > 100: truncated, not exhausted.
    let q7 = build(&mut manager, 7);
    assert!(
        !integration.all_domains_finitely_exhausted(&q7, &model, &manager),
        "2^7 = 128 combinations exceed the cap and are not fully enumerated"
    );
}

/// Finding #2 (integration.rs:509): substitution must descend into EVERY
/// term kind, including `Xor`.  Previously the catch-all `_ => term` arm
/// skipped `Xor`, leaving the bound variable `x` inside `(xor x false)`
/// even after instantiating `x := true` -- producing a lemma that
/// constrains a stray free variable.
#[test]
fn test_audit_substitution_covers_xor_no_leftover_bound_var() {
    let mut manager = TermManager::new();
    let bool_sort = manager.sorts.bool_sort;
    let x = manager.mk_var("x", bool_sort);
    let f = manager.mk_false();
    let xor = manager.mk_xor(x, f);
    let body = manager.mk_eq(x, xor); // (= x (xor x false))
    let forall = manager.mk_forall([("x", bool_sort)], body);

    let mut integration = MBQIIntegration::new();
    integration.add_quantifier(forall, &manager);
    let quantifier = integration.quantifiers[0].clone();

    let true_val = manager.mk_true();
    let x_spur = quantifier.bound_vars[0].0;
    let mut subst: FxHashMap<Spur, TermId> = FxHashMap::default();
    subst.insert(x_spur, true_val);

    let result = integration
        .apply_substitution(&quantifier, &subst, &mut manager)
        .expect("substitution of x:=true must fully ground the Xor body");

    let free = collect_free_vars_including_patterns(result, &manager);
    assert!(
        !free.contains(&x),
        "instantiation lemma still contains free bound variable x -- Xor was \
         not substituted (found free vars: {free:?})"
    );
}

/// Finding #2: substitution must descend into `Distinct` (also previously
/// skipped by the catch-all arm).
#[test]
fn test_audit_substitution_covers_distinct() {
    let mut manager = TermManager::new();
    let int_sort = manager.sorts.int_sort;
    let x = manager.mk_var("x", int_sort);
    let c0 = manager.mk_int(BigInt::from(0));
    let c1 = manager.mk_int(BigInt::from(1));
    let distinct = manager.mk_distinct([x, c0, c1]); // (distinct x 0 1)
    let forall = manager.mk_forall([("x", int_sort)], distinct);

    let mut integration = MBQIIntegration::new();
    integration.add_quantifier(forall, &manager);
    let quantifier = integration.quantifiers[0].clone();

    let seven = manager.mk_int(BigInt::from(7));
    let x_spur = quantifier.bound_vars[0].0;
    let mut subst: FxHashMap<Spur, TermId> = FxHashMap::default();
    subst.insert(x_spur, seven);

    let result = integration
        .apply_substitution(&quantifier, &subst, &mut manager)
        .expect("substitution of x:=7 must fully ground the Distinct body");

    let free = collect_free_vars_including_patterns(result, &manager);
    assert!(
        !free.contains(&x),
        "Distinct body still contains free bound variable x after substitution"
    );
}

/// Finding #2: a nested quantifier that re-binds the same variable name
/// must be left intact by capture-avoiding substitution and must NOT be
/// mis-flagged as a leftover free variable.
#[test]
fn test_audit_substitution_respects_inner_shadowing() {
    let mut manager = TermManager::new();
    let int_sort = manager.sorts.int_sort;
    let bool_sort = manager.sorts.bool_sort;

    // Inner: (exists ((x Int)) (>= x 0)) -- rebinds x.
    let x_inner = manager.mk_var("x", int_sort);
    let zero = manager.mk_int(BigInt::from(0));
    let inner_body = manager.mk_ge(x_inner, zero);
    let inner = manager.mk_exists([("x", int_sort)], inner_body);

    // Outer body: (and P inner) where P mentions the outer x.
    let x_outer = manager.mk_var("x", int_sort);
    let p = manager.mk_gt(x_outer, zero);
    let outer_body = manager.mk_and(vec![p, inner]);
    let forall = manager.mk_forall([("x", int_sort)], outer_body);

    let mut integration = MBQIIntegration::new();
    integration.add_quantifier(forall, &manager);
    let quantifier = integration.quantifiers[0].clone();

    let five = manager.mk_int(BigInt::from(5));
    let x_spur = quantifier.bound_vars[0].0;
    let mut subst: FxHashMap<Spur, TermId> = FxHashMap::default();
    subst.insert(x_spur, five);

    // Should succeed: the inner exists legitimately keeps its own x; only
    // the outer occurrence is replaced.
    let result = integration.apply_substitution(&quantifier, &subst, &mut manager);
    assert!(
        result.is_some(),
        "capture-avoiding substitution with inner shadowing must not be \
         rejected as a leftover-bound-variable internal error"
    );

    // Sanity: the bool sort remains distinct from the int sort (guards
    // against accidental sort collapse in this fixture).
    assert_ne!(int_sort, bool_sort);
}

/// Finding (solver-p3b #3): a universal quantifier whose body simplifies to
/// `true` regardless of its bound variable (e.g. `forall x. f(x) = f(x)`)
/// must be reported `Satisfied` even over the infinite Int domain, so simple
/// UFLIA tautological quantifiers return sat rather than Unknown.
#[test]
fn test_audit_trivially_valid_quantifier_is_satisfied() {
    let mut manager = TermManager::new();
    let int_sort = manager.sorts.int_sort;
    let x = manager.mk_var("x", int_sort);
    let f_x = manager.mk_apply("f", [x], int_sort);
    let body = manager.mk_eq(f_x, f_x); // f(x) = f(x)  ≡ true
    let forall = manager.mk_forall([("x", int_sort)], body);

    let mut integration = MBQIIntegration::new();
    integration.add_quantifier(forall, &manager);

    let model = FxHashMap::default();
    let result = integration.check_with_model(&model, &mut manager);
    assert!(
        result.is_sat(),
        "forall x:Int. f(x) = f(x) is a tautology and must be Satisfied, \
         got {result:?}"
    );
}

/// Guard: the trivially-valid recognition must NOT grant sat for a
/// non-tautological body.  `forall x. x >= -10` does not simplify to true
/// and is in fact false at x = -11, so it must not be reported sat.
#[test]
fn test_audit_trivially_valid_does_not_overreach() {
    use num_bigint::BigInt;
    let mut manager = TermManager::new();
    let int_sort = manager.sorts.int_sort;
    let x = manager.mk_var("x", int_sort);
    let neg_ten = manager.mk_int(BigInt::from(-10));
    let body = manager.mk_ge(x, neg_ten);
    let forall = manager.mk_forall([("x", int_sort)], body);

    let mut integration = MBQIIntegration::new();
    integration.add_quantifier(forall, &manager);

    let model = FxHashMap::default();
    let result = integration.check_with_model(&model, &mut manager);
    assert!(
        !result.is_sat(),
        "forall x:Int. x >= -10 is not a tautology and must not be granted \
         sat by trivial-validity recognition, got {result:?}"
    );
}

/// New MBQI-candidate accessor test: `extra_candidates_snapshot` (added for
/// `solver::encode`'s Skolem-candidate regression tests, which live in a
/// different module and so cannot reach the private `extra_candidates`
/// field directly) must agree with the field it wraps.
#[test]
fn test_extra_candidates_snapshot_matches_add_candidate() {
    let mut manager = TermManager::new();
    let int_sort = manager.sorts.int_sort;
    let mut integration = MBQIIntegration::new();

    assert!(integration.extra_candidates_snapshot(int_sort).is_empty());

    let five = manager.mk_int(5);
    integration.add_candidate(five, int_sort);
    assert_eq!(integration.extra_candidates_snapshot(int_sort), vec![five]);

    let bool_sort = manager.sorts.bool_sort;
    assert!(
        integration.extra_candidates_snapshot(bool_sort).is_empty(),
        "snapshot must be scoped to the requested sort only"
    );
}

/// Regression: the grounding guard used the *non*-pattern-aware
/// `collect_free_vars`, which ignores a quantifier's `patterns` field. A
/// nested quantifier whose trigger still mentioned the variable being
/// eliminated therefore looked fully grounded, and the guard passed a lemma
/// that is not.
///
/// Here the outer `forall x` body is a nested `forall y` whose *only*
/// reference to `x` is its trigger `(f x y)`. `TermManager::substitute`
/// rewrites trigger terms, so the substituted result is in fact fully
/// grounded -- the point of this test is that the guard now *inspects* the
/// trigger rather than being blind to it, which is what makes the guard's
/// "passed" verdict meaningful.
#[test]
fn test_grounding_guard_inspects_trigger_patterns() {
    let mut manager = TermManager::new();
    let int_sort = manager.sorts.int_sort;
    let x = manager.mk_var("x", int_sort);
    let y = manager.mk_var("y", int_sort);
    let trigger = manager.mk_apply("f", [x, y], int_sort);
    let inner_body = manager.mk_true();
    let inner = manager.mk_forall_with_patterns([("y", int_sort)], inner_body, [vec![trigger]]);
    let forall = manager.mk_forall([("x", int_sort)], inner);

    // Before the fix this set was empty, so the guard could not see `x` at
    // all; it must now report the trigger-only occurrence.
    assert!(
        collect_free_vars_including_patterns(inner, &manager).contains(&x),
        "the trigger-only occurrence of x must be visible to the guard"
    );

    let mut integration = MBQIIntegration::new();
    integration.add_quantifier(forall, &manager);
    let quantifier = integration.quantifiers[0].clone();

    let seven = manager.mk_int(BigInt::from(7));
    let x_spur = quantifier.bound_vars[0].0;
    let mut subst: FxHashMap<Spur, TermId> = FxHashMap::default();
    subst.insert(x_spur, seven);

    let result = integration
        .apply_substitution(&quantifier, &subst, &mut manager)
        .expect("x:=7 must ground the body, triggers included");

    assert!(
        !collect_free_vars_including_patterns(result, &manager).contains(&x),
        "x must not survive anywhere in the lemma, trigger patterns included"
    );
}

// ===== deep_simplify iterative-machine regression tests =====
//
// `deep_simplify_cached` used to recurse natively once per nesting level;
// it now runs as an explicit-stack frame machine. These tests pin exact
// simplification results (behavior preservation), deep-input survival on a
// deliberately small thread stack (an overflow would abort the process, so
// returning is the proof), and memoized shared-DAG traversal.

#[test]
fn deep_simplify_semantic_pins() {
    let integration = MBQIIntegration::new();
    let mut m = TermManager::new();
    let int_sort = m.sorts.int_sort;
    let bool_sort = m.sorts.bool_sort;

    let zero = m.mk_int(0);
    let one = m.mk_int(1);
    let ten = m.mk_int(10);
    let three = m.mk_int(3);
    let five = m.mk_int(5);
    let p = m.mk_var("p", bool_sort);
    let a = m.mk_var("a", int_sort);
    let b = m.mk_var("b", int_sort);
    let tt = m.mk_true();
    let ff = m.mk_false();

    // Constant comparisons fold exactly as before (`mk_ge`/`mk_lt`/... do
    // not fold at construction, so the machine does the folding).
    let ge_53 = m.mk_ge(five, three);
    assert_eq!(integration.deep_simplify(ge_53, &mut m), tt);
    let lt_53 = m.mk_lt(five, three);
    assert_eq!(integration.deep_simplify(lt_53, &mut m), ff);
    let le_35 = m.mk_le(three, five);
    assert_eq!(integration.deep_simplify(le_35, &mut m), tt);
    let gt_35 = m.mk_gt(three, five);
    assert_eq!(integration.deep_simplify(gt_35, &mut m), ff);

    // Eq folds once its children simplified to the same term.
    let eq_fold = m.mk_eq(ge_53, tt);
    assert_eq!(integration.deep_simplify(eq_fold, &mut m), tt);

    // Ge/Gt normalize to Le/Lt with swapped operands — pigeonhole.rs
    // pattern-matches on exactly this shape.
    let ge_ab = m.mk_ge(a, b);
    let le_ba = m.mk_le(b, a);
    assert_eq!(integration.deep_simplify(ge_ab, &mut m), le_ba);
    let gt_ab = m.mk_gt(a, b);
    let lt_ba = m.mk_lt(b, a);
    assert_eq!(integration.deep_simplify(gt_ab, &mut m), lt_ba);

    // Guard collapse: (0>=0 /\ 1<=10) => C simplifies to C.
    let g1 = m.mk_ge(zero, zero);
    let g2 = m.mk_le(one, ten);
    let guard = m.mk_and([g1, g2]);
    let f_a = m.mk_apply("f", [a], int_sort);
    let f_b = m.mk_apply("f", [b], int_sort);
    let conseq = m.mk_eq(f_a, f_b);
    let lemma = m.mk_implies(guard, conseq);
    assert_eq!(integration.deep_simplify(lemma, &mut m), conseq);

    // A False conjunct short-circuits the conjunction; a True disjunct the
    // disjunction (the operands are non-constant *terms* at construction,
    // so the machine performs the collapse).
    let bad = m.mk_lt(ten, one);
    let and_sc = m.mk_and([bad, p]);
    assert_eq!(integration.deep_simplify(and_sc, &mut m), ff);
    let or_sc = m.mk_or([g2, p]);
    assert_eq!(integration.deep_simplify(or_sc, &mut m), tt);

    // Not folds through its simplified child.
    let not_bad = m.mk_not(bad);
    assert_eq!(integration.deep_simplify(not_bad, &mut m), tt);

    // Apply rebuilds with simplified arguments.
    let g_bad = m.mk_apply("g", [bad], bool_sort);
    let g_false = m.mk_apply("g", [ff], bool_sort);
    assert_eq!(integration.deep_simplify(g_bad, &mut m), g_false);
}

/// Deep-nesting regression: 12 500 implication levels on a 128 KiB stack.
/// The old implementation recursed once per level and would overflow here;
/// the frame machine must return (returning at all is the proof).
#[test]
fn deep_simplify_deep_implies_chain_returns_on_small_stack() {
    // Stack and depth scale together (1 MiB/100k -> 128 KiB/12.5k): the
    // ~10 B-per-frame threshold is the pin, so never raise one alone.
    const DEPTH: usize = 12_500;

    std::thread::Builder::new()
        .stack_size(1 << 17)
        .spawn(|| {
            let integration = MBQIIntegration::new();
            let mut m = TermManager::new();
            let bool_sort = m.sorts.bool_sort;
            let p = m.mk_var("p", bool_sort);
            let q = m.mk_var("q", bool_sort);
            let mut chain = q;
            for _ in 0..DEPTH {
                chain = m.mk_implies(p, chain);
            }
            // Nothing folds (all operands symbolic): the rebuilt chain is
            // id-identical, pinning the conversion as behavior-preserving.
            assert_eq!(integration.deep_simplify(chain, &mut m), chain);
        })
        .expect("spawn deep-simplify thread")
        .join()
        .expect("deep implies chain must simplify without overflowing");
}

/// Shared-DAG regression: 60 doubling levels reference each child twice
/// (2^60 paths); the memo cache must bound the machine to one visit per
/// distinct term.
#[test]
fn deep_simplify_shared_dag_apply_doubling_is_memoized() {
    let integration = MBQIIntegration::new();
    let mut m = TermManager::new();
    let int_sort = m.sorts.int_sort;
    let x = m.mk_var("x", int_sort);
    let mut t = x;
    for _ in 0..60 {
        let prev = t;
        t = m.mk_apply("g", [prev, prev], int_sort);
        assert_ne!(t, prev, "doubling must build a fresh application");
    }
    assert_eq!(integration.deep_simplify(t, &mut m), t);
}
