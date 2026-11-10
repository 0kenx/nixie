//! Validation-only regressions: exact array values, quantifier polarity and
//! shared certificate budgets. Optional completion search is withheld.

use super::*;
use nixie_core::ast::TermManager;

#[test]
fn an_array_value_is_a_literal_store_chain_over_a_literal_constant() {
    let mut tm = TermManager::new();
    let index = tm.sorts.bitvec(7);
    let element = tm.sorts.bitvec(1);
    let array_sort = tm.sorts.array(index, element);
    let one = tm.mk_bitvec(1u8, 1);
    let zero = tm.mk_bitvec(0u8, 1);
    let k = tm.mk_bitvec(5u8, 7);
    let constant = const_array(array_sort, one, &mut tm);
    let chain = tm.mk_store(constant, k, zero);
    assert!(is_array_value(constant, &tm));
    assert!(is_array_value(chain, &tm));
    let x = tm.mk_var("x", element);
    let symbolic_default = const_array(array_sort, x, &mut tm);
    let symbolic_value = tm.mk_store(constant, k, x);
    let a = tm.mk_var("a", array_sort);
    let over_a_variable = tm.mk_store(a, k, zero);
    assert!(
        !is_array_value(symbolic_default, &tm)
            && !is_array_value(symbolic_value, &tm)
            && !is_array_value(over_a_variable, &tm)
            && !is_array_value(a, &tm),
        "only a closed, literal interpretation is an installed array value"
    );
}

/// Decision (54)(ii), `polarity`: a negated `exists` is certified false
/// through its dual universal, an implication's antecedent is negative, and
/// an `exists` in an `ite` condition keeps both polarities (certified true
/// as before).
#[test]
fn quantifiers_are_classified_by_polarity_with_duals_for_the_negative_ones() {
    let mut tm = TermManager::new();
    let index = tm.sorts.bitvec(7);
    let element = tm.sorts.bitvec(1);
    let array_sort = tm.sorts.array(index, element);
    let a = tm.mk_var("a", array_sort);
    let j = tm.mk_var("j", index);
    let read = tm.mk_select(a, j);
    let zero = tm.mk_bitvec(num_bigint::BigInt::from(0u8), 1);
    let body = tm.mk_eq(read, zero);
    let exists = tm.mk_exists([("j", index)], body);
    let negated = tm.mk_not(exists);
    let false_term = tm.mk_false();
    let implication = tm.mk_implies(exists, false_term);
    for assertion in [negated, implication] {
        let found = polarity::collect_quantifiers(&[assertion], &mut tm)
            .unwrap_or_else(|| panic!("the walk reads every term"));
        assert!(
            found.existentials.is_empty(),
            "no positive `exists` is left"
        );
        assert_eq!(found.universals.len(), 1, "one dual universal");
        assert_eq!(
            found.negations,
            vec![(exists, found.universals[0])],
            "the original `exists` is certified false through its dual"
        );
        let dual_is_universal = matches!(
            tm.get(found.universals[0]).map(|d| &d.kind),
            Some(TermKind::Forall { .. })
        );
        assert!(
            dual_is_universal,
            "the dual of a negated `exists` is `∀j. ¬φ`"
        );
    }
    let p = tm.mk_var("p", tm.sorts.bool_sort);
    let q = tm.mk_var("q", tm.sorts.bool_sort);
    let under_ite = tm.mk_ite(exists, p, q);
    let found = polarity::collect_quantifiers(&[under_ite], &mut tm)
        .unwrap_or_else(|| panic!("the walk reads every term"));
    assert_eq!(
        found.existentials,
        vec![exists],
        "two-sided: certified true"
    );
    assert!(found.negations.is_empty());
}

#[test]
fn certificate_query_budget_is_shared_and_refuses_quantified_queries() {
    let mut tm = TermManager::new();
    let solver = Solver::new();
    let mut budget = QueryBudget::for_solver(&solver);
    let p = tm.mk_var("p", tm.sorts.bool_sort);
    let q = tm.mk_forall([("x", tm.sorts.int_sort)], p);
    assert!(budget.start(q, &tm, None).is_none());
    assert_eq!(budget.used, 0);
    let goal = tm.mk_false();
    for _ in 0..MAX_CERTIFICATE_QUERIES {
        assert!(budget.start(goal, &tm, None).is_some());
    }
    assert!(budget.start(goal, &tm, None).is_none());
    let mut budget = QueryBudget::for_solver(&solver);
    budget.conflicts = Some(0);
    assert!(budget.start(goal, &tm, None).is_none());
    budget.conflicts = None;
    budget.deadline = Some(nixie_time::Instant::now());
    assert!(budget.start(goal, &tm, None).is_none());
}

#[test]
fn publication_attempts_share_the_query_cap_and_cached_checks_get_a_new_budget() {
    let manager = TermManager::new();
    let solver = Solver::new();
    let truth = manager.mk_true();
    let mut first = QueryBudget::for_solver(&solver);
    for _ in 0..MAX_CERTIFICATE_QUERIES {
        assert!(first.start(truth, &manager, None).is_some());
    }
    let mut second = QueryBudget::for_solver(&solver);
    assert!(second.start(truth, &manager, None).is_none());
    let mut solver = solver;
    solver.completion_work = std::sync::Arc::new(CompletionWork::cached_query());
    assert!(
        QueryBudget::for_solver(&solver)
            .start(truth, &manager, None)
            .is_some()
    );
}
