//! Regression tests for audited soundness defects in
//! `oxiz-core/src/ast/normal_forms.rs::skolemize`.
//!
//! This is the Wave-1-deferred twin of the fixes already applied to
//! `SkolemizationTactic` in `oxiz-core/src/tactic/quantifier.rs` (see
//! `oxiz-core/tests/audit_tactic_quant.rs`). The standalone `skolemize`
//! function had the same three defects:
//!
//!   1. **No polarity tracking.** `Forall` was always treated as
//!      effectively universal and `Exists` always as effectively
//!      existential, regardless of how many `Not`s enclosed them. This
//!      unsoundly Skolemizes negated existentials/universals:
//!      `¬(∃x.P(x))` became `¬P(sk_0)`, flipping UNSAT into SAT.
//!   2. **Hard-coded `Bool` sort for Skolem-function arguments.** The
//!      governing universal variables were re-materialized with
//!      `manager.sorts.bool_sort` instead of their real sort, producing a
//!      sort-mismatched (and effectively bogus) Skolem application.
//!   3. **Per-call counter reset.** Each top-level `skolemize()` call started
//!      its counter at 0, so Skolemizing several assertions of one goal by
//!      calling `skolemize` once per assertion let distinct existentials
//!      collide on the same Skolem symbol: `{∃x.P(x), ∃x.¬P(x)}` (SAT)
//!      collapsed to `{P(sk_0), ¬P(sk_0)}` (UNSAT).
//!
//! Fix: `skolemize` now threads polarity through the recursion (mirroring
//! `SkolemizationTactic::skolemize_polar`), uses the real sorts of governing
//! universal variables, and a new `skolemize_with_counter` entry point lets
//! callers share one fresh-name counter across multiple assertions.

use oxiz_core::TermKind;
use oxiz_core::ast::{TermManager, skolemize, skolemize_with_counter};

fn setup_manager() -> TermManager {
    TermManager::new()
}

/// Baseline: `∃x. x > 0` Skolemizes to a ground fact with no quantifier left.
#[test]
fn test_skolemize_basic_existential() {
    let mut manager = setup_manager();
    let int_sort = manager.sorts.int_sort;

    let x = manager.mk_var("x", int_sort);
    let zero = manager.mk_int(0);
    let body = manager.mk_gt(x, zero);
    let exists = manager.mk_exists([("x", int_sort)], body);

    let result = skolemize(exists, &mut manager);
    assert!(
        !contains_quantifier(&manager, result),
        "positive-polarity existential should be fully Skolemized"
    );
}

/// Finding 1a: a negated existential must NOT be Skolemized as if positive.
/// `¬(∃x.P(x)) ≡ ∀x.¬P(x)`; rewriting it to `¬P(sk_0)` flips UNSAT→SAT.
#[test]
fn test_skolemize_negated_existential_not_skolemized() {
    let mut manager = setup_manager();
    let int_sort = manager.sorts.int_sort;
    let bool_sort = manager.sorts.bool_sort;

    let x = manager.mk_var("x", int_sort);
    let p_x = manager.mk_apply("P", [x], bool_sort);
    let exists = manager.mk_exists([("x", int_sort)], p_x);
    let not_exists = manager.mk_not(exists);

    let result = skolemize(not_exists, &mut manager);

    // The existential is at negative polarity (effectively universal), so
    // the binder must be preserved, not eliminated in favor of a bare
    // negated Skolem application.
    assert!(
        contains_quantifier(&manager, result),
        "negated existential was unsoundly Skolemized away"
    );
}

/// Finding 1b: a negated universal (`¬∀x.P(x) ≡ ∃x.¬P(x)`) IS effectively
/// existential and must be Skolemized.
#[test]
fn test_skolemize_negated_universal_is_skolemized() {
    let mut manager = setup_manager();
    let int_sort = manager.sorts.int_sort;
    let bool_sort = manager.sorts.bool_sort;

    let x = manager.mk_var("x", int_sort);
    let p_x = manager.mk_apply("P", [x], bool_sort);
    let forall = manager.mk_forall([("x", int_sort)], p_x);
    let not_forall = manager.mk_not(forall);

    let result = skolemize(not_forall, &mut manager);

    assert!(
        !contains_quantifier(&manager, result),
        "negated universal (effectively existential) should be Skolemized away"
    );
}

/// Finding 2: Skolem-function arguments must use the real universal-variable
/// sort, not a hard-coded `Bool`.
#[test]
fn test_skolemize_function_arg_uses_real_sort() {
    let mut manager = setup_manager();
    let int_sort = manager.sorts.int_sort;
    let bool_sort = manager.sorts.bool_sort;

    // forall y:Int. exists x:Int. P(x, y)
    let x = manager.mk_var("x", int_sort);
    let y = manager.mk_var("y", int_sort);
    let p_xy = manager.mk_apply("P", [x, y], bool_sort);
    let exists = manager.mk_exists([("x", int_sort)], p_xy);
    let forall = manager.mk_forall([("y", int_sort)], exists);

    let result = skolemize(forall, &mut manager);

    // Result: forall y. P(sk(y), y). The Skolem function's argument must be
    // an Int-sorted term (the governing y), not Bool.
    let body = match manager.get(result).map(|t| t.kind.clone()) {
        Some(TermKind::Forall { body, .. }) => body,
        other => panic!("expected Forall, got {other:?}"),
    };
    let sk_arg = match manager.get(body).map(|t| t.kind.clone()) {
        Some(TermKind::Apply { args, .. }) => args[0],
        other => panic!("expected P(.., ..) application, got {other:?}"),
    };
    let sk_fun_arg = match manager.get(sk_arg).map(|t| t.kind.clone()) {
        Some(TermKind::Apply { args, .. }) => args[0],
        other => panic!("expected Skolem function application, got {other:?}"),
    };
    let sort = manager.get(sk_fun_arg).map(|t| t.sort);
    assert_eq!(
        sort,
        Some(int_sort),
        "Skolem-function argument should have the governing variable's real (Int) sort"
    );
    assert_ne!(sort, Some(bool_sort));
}

/// Finding 3: `skolemize` called once per assertion (starting a fresh
/// counter each time) lets distinct existentials collide on the same
/// Skolem symbol. `skolemize_with_counter` sharing one counter must not.
#[test]
fn test_skolemize_plain_collides_but_shared_counter_does_not() {
    let int_sort_of = |m: &TermManager| m.sorts.int_sort;

    // ======== Buggy usage pattern: fresh counter per call ========
    let mut manager = setup_manager();
    let int_sort = int_sort_of(&manager);
    let bool_sort = manager.sorts.bool_sort;

    let x1 = manager.mk_var("x", int_sort);
    let p_x1 = manager.mk_apply("P", [x1], bool_sort);
    let exists1 = manager.mk_exists([("x", int_sort)], p_x1);

    let x2 = manager.mk_var("x", int_sort);
    let p_x2 = manager.mk_apply("P", [x2], bool_sort);
    let not_p_x2 = manager.mk_not(p_x2);
    let exists2 = manager.mk_exists([("x", int_sort)], not_p_x2);

    let sk1 = skolemize(exists1, &mut manager);
    let sk2 = skolemize(exists2, &mut manager);

    let arg1 = p_apply_arg(&manager, sk1);
    let arg2 = p_apply_arg(&manager, sk2);
    assert_eq!(
        arg1, arg2,
        "documenting the known collision when each assertion resets the counter: \
         callers wanting distinct Skolem symbols across assertions must use \
         skolemize_with_counter, not repeated skolemize() calls"
    );

    // ======== Correct usage pattern: shared counter ========
    let mut manager2 = setup_manager();
    let int_sort2 = int_sort_of(&manager2);
    let bool_sort2 = manager2.sorts.bool_sort;

    let x1b = manager2.mk_var("x", int_sort2);
    let p_x1b = manager2.mk_apply("P", [x1b], bool_sort2);
    let exists1b = manager2.mk_exists([("x", int_sort2)], p_x1b);

    let x2b = manager2.mk_var("x", int_sort2);
    let p_x2b = manager2.mk_apply("P", [x2b], bool_sort2);
    let not_p_x2b = manager2.mk_not(p_x2b);
    let exists2b = manager2.mk_exists([("x", int_sort2)], not_p_x2b);

    let mut counter = 0usize;
    let sk1b = skolemize_with_counter(exists1b, &mut manager2, &mut counter);
    let sk2b = skolemize_with_counter(exists2b, &mut manager2, &mut counter);

    let arg1b = p_apply_arg(&manager2, sk1b);
    let arg2b = p_apply_arg(&manager2, sk2b);
    assert_ne!(
        arg1b, arg2b,
        "skolemize_with_counter must give distinct existentials distinct Skolem \
         constants when threaded across assertions (SAT must not become UNSAT)"
    );
}

/// `Ite` conditions occur at mixed polarity and must be left untouched by
/// Skolemization, while both branches still get Skolemized at the ambient
/// polarity.
#[test]
fn test_skolemize_ite_condition_untouched() {
    let mut manager = setup_manager();
    let int_sort = manager.sorts.int_sort;
    let bool_sort = manager.sorts.bool_sort;

    let cx = manager.mk_var("cx", int_sort);
    let zero = manager.mk_int(0);
    let cond_body = manager.mk_gt(cx, zero);
    let cond_exists = manager.mk_exists([("cx", int_sort)], cond_body);

    let tx = manager.mk_var("tx", int_sort);
    let p_tx = manager.mk_apply("P", [tx], bool_sort);
    let then_exists = manager.mk_exists([("tx", int_sort)], p_tx);

    let ex = manager.mk_var("ex", int_sort);
    let q_ex = manager.mk_apply("Q", [ex], bool_sort);
    let else_exists = manager.mk_exists([("ex", int_sort)], q_ex);

    let ite = manager.mk_ite(cond_exists, then_exists, else_exists);
    let result = skolemize(ite, &mut manager);

    let (cond, then_br, else_br) = match manager.get(result).map(|t| t.kind.clone()) {
        Some(TermKind::Ite(c, t, e)) => (c, t, e),
        other => panic!("expected Ite, got {other:?}"),
    };
    // Condition must still contain its quantifier (untouched, mixed
    // polarity); both branches must have been Skolemized away.
    assert!(
        contains_quantifier(&manager, cond),
        "Ite condition must not be Skolemized (mixed polarity)"
    );
    assert!(
        !contains_quantifier(&manager, then_br),
        "Ite then-branch should be Skolemized at the ambient (positive) polarity"
    );
    assert!(
        !contains_quantifier(&manager, else_br),
        "Ite else-branch should be Skolemized at the ambient (positive) polarity"
    );
}

fn p_apply_arg(manager: &TermManager, term: oxiz_core::TermId) -> oxiz_core::TermId {
    let inner = match manager.get(term).map(|t| t.kind.clone()) {
        Some(TermKind::Not(a)) => a,
        _ => term,
    };
    match manager.get(inner).map(|t| t.kind.clone()) {
        Some(TermKind::Apply { args, .. }) => args[0],
        other => panic!("expected application, got {other:?}"),
    }
}

fn contains_quantifier(manager: &TermManager, term_id: oxiz_core::TermId) -> bool {
    match manager.get(term_id).map(|t| t.kind.clone()) {
        None => false,
        Some(TermKind::Forall { .. } | TermKind::Exists { .. }) => true,
        Some(TermKind::Not(a)) => contains_quantifier(manager, a),
        Some(TermKind::And(args) | TermKind::Or(args)) => {
            args.iter().any(|&a| contains_quantifier(manager, a))
        }
        Some(TermKind::Implies(l, r)) => {
            contains_quantifier(manager, l) || contains_quantifier(manager, r)
        }
        Some(TermKind::Ite(c, t, e)) => {
            contains_quantifier(manager, c)
                || contains_quantifier(manager, t)
                || contains_quantifier(manager, e)
        }
        _ => false,
    }
}
