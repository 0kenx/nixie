//! Regression tests for audited soundness defects in the quantifier tactics
//! (`oxiz-core/src/tactic/quantifier.rs`).
//!
//! Findings fixed:
//!   1. DER's ∀ rule was inverted — it resolved a *positive* equality
//!      (∀x.(x=t ∨ ψ) → ψ[t/x]) instead of a *disequality*
//!      (∀x.(x≠t ∨ ψ) ≡ ψ[t/x]).  {∀x.(x=5 ∨ P(x)), ¬P(6)} is UNSAT but the old
//!      rule produced {P(5), ¬P(6)} = SAT.
//!   2. `SkolemizationTactic` reset its fresh-name counter per assertion (so
//!      distinct existentials collided on one Skolem symbol), ignored polarity
//!      (negated existentials were unsoundly Skolemized), and hard-coded a
//!      `Bool` sort for Skolem-function arguments.
//!   3. `QuantifierInstantiationTactic` gathered `Forall` subterms at *any*
//!      polarity and asserted φ(t) as a top-level fact, flipping SAT→UNSAT for
//!      goals like ¬(∀x.P(x)) ∧ ¬P(c).
//!
//! These tests use only the public API and mirror the structural transforms;
//! the two remaining tests that need private access stay in the source module.

use oxiz_core::TermKind;
use oxiz_core::ast::TermManager;
use oxiz_core::tactic::{
    DerConfig, DerTactic, Goal, QuantifierInstantiationTactic, SkolemizationTactic,
    StatelessDerTactic, TacticResult, contains_quantifier, goal_has_quantifiers,
};

fn setup_manager() -> TermManager {
    TermManager::new()
}

// ---------------------------------------------------------------------------
// Skolemization
// ---------------------------------------------------------------------------

#[test]
fn test_skolemization_tactic() {
    let mut manager = setup_manager();
    let int_sort = manager.sorts.int_sort;

    // exists x. x > 0  ->  sk > 0 (no quantifier remains)
    let x = manager.mk_var("x", int_sort);
    let zero = manager.mk_int(0);
    let body = manager.mk_gt(x, zero);
    let exists = manager.mk_exists([("x", int_sort)], body);

    let goal = Goal::new(vec![exists]);
    let mut tactic = SkolemizationTactic::new(&mut manager);
    let result = tactic.apply_mut(&goal).expect("tactic should succeed");

    match result {
        TacticResult::SubGoals(goals) => {
            assert_eq!(goals.len(), 1);
            assert!(!goal_has_quantifiers(&goals[0], &manager));
        }
        _ => panic!("Expected SubGoals result"),
    }
}

/// Finding 2a: distinct existentials in different assertions must receive
/// distinct Skolem constants.  {∃x.P(x), ∃x.¬P(x)} is SAT; a shared sk_0 makes
/// {P(sk_0), ¬P(sk_0)} UNSAT.
#[test]
fn test_skolem_distinct_names_across_assertions() {
    let mut manager = setup_manager();
    let int_sort = manager.sorts.int_sort;
    let bool_sort = manager.sorts.bool_sort;

    let x1 = manager.mk_var("x", int_sort);
    let p_x1 = manager.mk_apply("P", [x1], bool_sort);
    let exists1 = manager.mk_exists([("x", int_sort)], p_x1);

    let x2 = manager.mk_var("x", int_sort);
    let p_x2 = manager.mk_apply("P", [x2], bool_sort);
    let not_p_x2 = manager.mk_not(p_x2);
    let exists2 = manager.mk_exists([("x", int_sort)], not_p_x2);

    let goal = Goal::new(vec![exists1, exists2]);
    let mut tactic = SkolemizationTactic::new(&mut manager);
    let result = tactic.apply_mut(&goal).expect("tactic should succeed");

    let goals = match result {
        TacticResult::SubGoals(g) => g,
        _ => panic!("Expected SubGoals"),
    };
    assert_eq!(goals[0].assertions.len(), 2);

    // Extract the Skolem argument of P from each assertion.
    let arg0 = p_apply_arg(&manager, goals[0].assertions[0]);
    let arg1 = p_apply_arg(&manager, goals[0].assertions[1]);
    assert!(
        arg0 != arg1,
        "distinct existentials reused the same Skolem constant (SAT would become UNSAT)"
    );
}

/// Finding 2b: a negated existential must NOT be Skolemized as if positive.
/// ¬(∃x.P(x)) ≡ ∀x.¬P(x); rewriting it to ¬P(sk_0) flips UNSAT→SAT.
#[test]
fn test_skolem_negated_existential_not_skolemized() {
    let mut manager = setup_manager();
    let int_sort = manager.sorts.int_sort;
    let bool_sort = manager.sorts.bool_sort;

    let x = manager.mk_var("x", int_sort);
    let p_x = manager.mk_apply("P", [x], bool_sort);
    let exists = manager.mk_exists([("x", int_sort)], p_x);
    let not_exists = manager.mk_not(exists);

    let goal = Goal::new(vec![not_exists]);
    let mut tactic = SkolemizationTactic::new(&mut manager);
    let result = tactic.apply_mut(&goal).expect("tactic should succeed");

    // The existential is at negative polarity: nothing may be Skolemized.
    match result {
        TacticResult::NotApplicable => {}
        TacticResult::SubGoals(goals) => {
            // If (re)built, it must still contain the quantifier — never a bare
            // ¬P(sk).
            assert!(
                goal_has_quantifiers(&goals[0], &manager),
                "negated existential was unsoundly Skolemized"
            );
        }
        other => panic!("Unexpected result: {other:?}"),
    }
}

/// Finding 2c: Skolem-function arguments must use the real universal-variable
/// sorts, not a hard-coded `Bool`.
#[test]
fn test_skolem_function_arg_uses_real_sort() {
    let mut manager = setup_manager();
    let int_sort = manager.sorts.int_sort;
    let bool_sort = manager.sorts.bool_sort;

    // forall y:Int. exists x:Int. P(x, y)
    let x = manager.mk_var("x", int_sort);
    let y = manager.mk_var("y", int_sort);
    let p_xy = manager.mk_apply("P", [x, y], bool_sort);
    let exists = manager.mk_exists([("x", int_sort)], p_xy);
    let forall = manager.mk_forall([("y", int_sort)], exists);

    let goal = Goal::new(vec![forall]);
    let mut tactic = SkolemizationTactic::new(&mut manager);
    let result = tactic.apply_mut(&goal).expect("tactic should succeed");

    let goals = match result {
        TacticResult::SubGoals(g) => g,
        _ => panic!("Expected SubGoals"),
    };

    // Result: forall y. P(sk(y), y).  The Skolem function's argument must be an
    // Int-sorted term (the governing y), not a Bool.
    let assertion = goals[0].assertions[0];
    let body = match manager.get(assertion).map(|t| t.kind.clone()) {
        Some(TermKind::Forall { body, .. }) => body,
        other => panic!("expected Forall, got {other:?}"),
    };
    let sk_arg = match manager.get(body).map(|t| t.kind.clone()) {
        Some(TermKind::Apply { args, .. }) => args[0],
        other => panic!("expected P(.., ..) application, got {other:?}"),
    };
    // sk_arg should itself be a Skolem application sk(y).
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

fn p_apply_arg(manager: &TermManager, term: oxiz_core::TermId) -> oxiz_core::TermId {
    // Unwrap an optional leading Not, then take the first argument of the
    // application.
    let inner = match manager.get(term).map(|t| t.kind.clone()) {
        Some(TermKind::Not(a)) => a,
        _ => term,
    };
    match manager.get(inner).map(|t| t.kind.clone()) {
        Some(TermKind::Apply { args, .. }) => args[0],
        other => panic!("expected application, got {other:?}"),
    }
}

// ---------------------------------------------------------------------------
// Quantifier instantiation
// ---------------------------------------------------------------------------

/// Finding 3: a universal under a negation must NOT be instantiated as a fact.
/// {¬(∀x.P(x)), ¬P(5)} is SAT; adding P(5) would make it UNSAT.
#[test]
fn test_qi_negative_forall_not_instantiated() {
    let mut manager = setup_manager();
    let int_sort = manager.sorts.int_sort;
    let bool_sort = manager.sorts.bool_sort;

    let x = manager.mk_var("x", int_sort);
    let p_x = manager.mk_apply("P", [x], bool_sort);
    let forall = manager.mk_forall_with_patterns([("x", int_sort)], p_x, [[p_x]]);
    let not_forall = manager.mk_not(forall);

    let five = manager.mk_int(5);
    let p_five = manager.mk_apply("P", [five], bool_sort);
    let not_p_five = manager.mk_not(p_five);

    let goal = Goal::new(vec![not_forall, not_p_five]);
    let mut tactic = QuantifierInstantiationTactic::new(&mut manager);
    let result = tactic.apply_mut(&goal).expect("tactic should succeed");

    assert!(
        matches!(result, TacticResult::NotApplicable),
        "negative-polarity forall must not be instantiated as a fact"
    );
}

/// Positive control: a genuinely asserted universal is still instantiated.
#[test]
fn test_qi_positive_forall_instantiated() {
    let mut manager = setup_manager();
    let int_sort = manager.sorts.int_sort;
    let bool_sort = manager.sorts.bool_sort;

    let x = manager.mk_var("x", int_sort);
    let q_x = manager.mk_apply("Q", [x], bool_sort);
    let forall = manager.mk_forall_with_patterns([("x", int_sort)], q_x, [[q_x]]);

    let five = manager.mk_int(5);
    let q_five = manager.mk_apply("Q", [five], bool_sort);

    let goal = Goal::new(vec![forall, q_five]);
    let mut tactic = QuantifierInstantiationTactic::new(&mut manager);
    let result = tactic.apply_mut(&goal).expect("tactic should succeed");

    match result {
        TacticResult::SubGoals(goals) => {
            // The instance Q(5) is entailed and added.
            assert!(goals[0].assertions.contains(&q_five));
        }
        other => panic!("Expected SubGoals for a positive universal, got {other:?}"),
    }
}

// ---------------------------------------------------------------------------
// DER (Destructive Equality Resolution)
// ---------------------------------------------------------------------------

#[test]
fn test_contains_quantifier() {
    let mut manager = setup_manager();
    let bool_sort = manager.sorts.bool_sort;
    let int_sort = manager.sorts.int_sort;

    let x = manager.mk_var("x", int_sort);
    let p_x = manager.mk_apply("P", [x], bool_sort);
    let forall = manager.mk_forall([("x", int_sort)], p_x);

    assert!(contains_quantifier(forall, &manager));
    assert!(!contains_quantifier(p_x, &manager));
}

#[test]
fn test_der_config_default() {
    let config = DerConfig::default();
    assert_eq!(config.max_depth, 10);
    assert!(config.recursive);
    assert!(config.handle_diseq);
}

/// Finding 1 (corrected rule): ∀x.(x ≠ 5 ∨ P(x)) ≡ P(5).
#[test]
fn test_der_forall_with_disequality_in_or() {
    let mut manager = setup_manager();
    let int_sort = manager.sorts.int_sort;
    let bool_sort = manager.sorts.bool_sort;

    let x = manager.mk_var("x", int_sort);
    let five = manager.mk_int(5);
    let x_eq_5 = manager.mk_eq(x, five);
    let x_ne_5 = manager.mk_not(x_eq_5);
    let p_x = manager.mk_apply("P", [x], bool_sort);
    let body = manager.mk_or([x_ne_5, p_x]);
    let forall = manager.mk_forall([("x", int_sort)], body);

    let goal = Goal::new(vec![forall]);
    let mut tactic = DerTactic::new(&mut manager);
    let result = tactic.apply_mut(&goal).expect("DER should succeed");

    match result {
        TacticResult::SubGoals(goals) => {
            assert_eq!(goals.len(), 1);
            assert!(!goal_has_quantifiers(&goals[0], &manager));
            let five2 = manager.mk_int(5);
            let p_5 = manager.mk_apply("P", [five2], bool_sort);
            assert_eq!(goals[0].assertions, vec![p_5]);
        }
        other => panic!("Expected SubGoals result, got {other:?}"),
    }
}

/// Finding 1 (regression): ∀x.(x = 5 ∨ P(x)) must NOT be rewritten to P(5).
/// {∀x.(x=5 ∨ P(x)), ¬P(6)} is UNSAT; {P(5), ¬P(6)} is SAT.
#[test]
fn test_der_forall_positive_equality_not_eliminated() {
    let mut manager = setup_manager();
    let int_sort = manager.sorts.int_sort;
    let bool_sort = manager.sorts.bool_sort;

    let x = manager.mk_var("x", int_sort);
    let five = manager.mk_int(5);
    let x_eq_5 = manager.mk_eq(x, five);
    let p_x = manager.mk_apply("P", [x], bool_sort);
    let body = manager.mk_or([x_eq_5, p_x]);
    let forall = manager.mk_forall([("x", int_sort)], body);

    let goal = Goal::new(vec![forall]);
    let mut tactic = DerTactic::new(&mut manager);
    let result = tactic.apply_mut(&goal).expect("DER should succeed");

    assert!(
        matches!(result, TacticResult::NotApplicable),
        "positive equality disjunct must not be DER-eliminated"
    );
}

/// Finding 1 (regression): ∀x.(x = 5) must NOT collapse to `true`.
#[test]
fn test_der_forall_bare_equality_not_true() {
    let mut manager = setup_manager();
    let int_sort = manager.sorts.int_sort;

    let x = manager.mk_var("x", int_sort);
    let five = manager.mk_int(5);
    let x_eq_5 = manager.mk_eq(x, five);
    let forall = manager.mk_forall([("x", int_sort)], x_eq_5);

    let goal = Goal::new(vec![forall]);
    let mut tactic = DerTactic::new(&mut manager);
    let result = tactic.apply_mut(&goal).expect("DER should succeed");

    match result {
        TacticResult::NotApplicable => {}
        TacticResult::SubGoals(goals) => {
            let truth = manager.mk_true();
            assert_ne!(
                goals[0].assertions,
                vec![truth],
                "∀x.(x=5) was unsoundly rewritten to true"
            );
        }
        other => panic!("Unexpected result: {other:?}"),
    }
}

#[test]
fn test_der_exists_with_equality_in_and() {
    let mut manager = setup_manager();
    let int_sort = manager.sorts.int_sort;
    let bool_sort = manager.sorts.bool_sort;

    // exists x. (x = 5 ∧ P(x))  ->  P(5)
    let x = manager.mk_var("x", int_sort);
    let five = manager.mk_int(5);
    let x_eq_5 = manager.mk_eq(x, five);
    let p_x = manager.mk_apply("P", [x], bool_sort);
    let body = manager.mk_and([x_eq_5, p_x]);
    let exists = manager.mk_exists([("x", int_sort)], body);

    let goal = Goal::new(vec![exists]);
    let mut tactic = DerTactic::new(&mut manager);
    let result = tactic.apply_mut(&goal).expect("DER should succeed");

    match result {
        TacticResult::SubGoals(goals) => {
            assert_eq!(goals.len(), 1);
            assert!(!goal_has_quantifiers(&goals[0], &manager));
        }
        _ => panic!("Expected SubGoals result"),
    }
}

#[test]
fn test_der_not_applicable_no_equality() {
    let mut manager = setup_manager();
    let int_sort = manager.sorts.int_sort;
    let bool_sort = manager.sorts.bool_sort;

    let x = manager.mk_var("x", int_sort);
    let p_x = manager.mk_apply("P", [x], bool_sort);
    let forall = manager.mk_forall([("x", int_sort)], p_x);

    let goal = Goal::new(vec![forall]);
    let mut tactic = DerTactic::new(&mut manager);
    let result = tactic.apply_mut(&goal).expect("DER should succeed");

    assert!(matches!(result, TacticResult::NotApplicable));
}

#[test]
fn test_der_symmetric_equality() {
    let mut manager = setup_manager();
    let int_sort = manager.sorts.int_sort;
    let bool_sort = manager.sorts.bool_sort;

    // exists x. (5 = x ∧ P(x))  ->  P(5)  (equality is symmetric)
    let x = manager.mk_var("x", int_sort);
    let five = manager.mk_int(5);
    let five_eq_x = manager.mk_eq(five, x);
    let p_x = manager.mk_apply("P", [x], bool_sort);
    let body = manager.mk_and([five_eq_x, p_x]);
    let exists = manager.mk_exists([("x", int_sort)], body);

    let goal = Goal::new(vec![exists]);
    let mut tactic = DerTactic::new(&mut manager);
    let result = tactic.apply_mut(&goal).expect("DER should succeed");

    match result {
        TacticResult::SubGoals(goals) => {
            assert_eq!(goals.len(), 1);
            assert!(!goal_has_quantifiers(&goals[0], &manager));
        }
        _ => panic!("Expected SubGoals result"),
    }
}

#[test]
fn test_der_multiple_bound_vars() {
    let mut manager = setup_manager();
    let int_sort = manager.sorts.int_sort;
    let bool_sort = manager.sorts.bool_sort;

    // exists x y. (x = 5 ∧ P(x, y))  ->  exists y. P(5, y)
    let x = manager.mk_var("x", int_sort);
    let y = manager.mk_var("y", int_sort);
    let five = manager.mk_int(5);
    let x_eq_5 = manager.mk_eq(x, five);
    let p_xy = manager.mk_apply("P", [x, y], bool_sort);
    let body = manager.mk_and([x_eq_5, p_xy]);
    let exists = manager.mk_exists([("x", int_sort), ("y", int_sort)], body);

    let goal = Goal::new(vec![exists]);
    let mut tactic = DerTactic::new(&mut manager);
    let result = tactic.apply_mut(&goal).expect("DER should succeed");

    match result {
        TacticResult::SubGoals(goals) => {
            assert_eq!(goals.len(), 1);
            let assertion = goals[0].assertions[0];
            match manager.get(assertion).map(|t| t.kind.clone()) {
                Some(TermKind::Exists { vars, .. }) => assert_eq!(vars.len(), 1),
                other => panic!("Expected Exists term, got {other:?}"),
            }
        }
        _ => panic!("Expected SubGoals result"),
    }
}

#[test]
fn test_der_var_occurs_in_substitute_fails() {
    let mut manager = setup_manager();
    let int_sort = manager.sorts.int_sort;
    let bool_sort = manager.sorts.bool_sort;

    // exists x. (x = f(x) ∧ P(x))  -- DER must NOT apply (x occurs in f(x))
    let x = manager.mk_var("x", int_sort);
    let f_x = manager.mk_apply("f", [x], int_sort);
    let x_eq_fx = manager.mk_eq(x, f_x);
    let p_x = manager.mk_apply("P", [x], bool_sort);
    let body = manager.mk_and([x_eq_fx, p_x]);
    let exists = manager.mk_exists([("x", int_sort)], body);

    let goal = Goal::new(vec![exists]);
    let mut tactic = DerTactic::new(&mut manager);
    let result = tactic.apply_mut(&goal).expect("DER should succeed");

    assert!(matches!(result, TacticResult::NotApplicable));
}

#[test]
fn test_stateless_der_tactic() {
    let mut manager = setup_manager();
    let int_sort = manager.sorts.int_sort;
    let bool_sort = manager.sorts.bool_sort;

    let x = manager.mk_var("x", int_sort);
    let five = manager.mk_int(5);
    let x_eq_5 = manager.mk_eq(x, five);
    let p_x = manager.mk_apply("P", [x], bool_sort);
    let body = manager.mk_and([x_eq_5, p_x]);
    let exists = manager.mk_exists([("x", int_sort)], body);

    let goal = Goal::new(vec![exists]);
    let tactic = StatelessDerTactic::new();
    let result = tactic
        .apply(&goal, &mut manager)
        .expect("DER should succeed");

    match result {
        TacticResult::SubGoals(goals) => {
            assert_eq!(goals.len(), 1);
            assert!(!goal_has_quantifiers(&goals[0], &manager));
        }
        _ => panic!("Expected SubGoals result"),
    }
}
