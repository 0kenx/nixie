use crate::{Context, SolverResult};

#[test]
fn repeated_printed_reading_is_idempotent_but_model_changes_are_not_cached() {
    let mut context = Context::new();
    let output = context
        .execute_script(
            "(declare-sort U 0)
             (declare-const a U)(declare-const b U)(declare-fun f (U) U)
             (declare-const x Int)
             (assert (distinct a b))(assert (= (f a) b))(assert (= x 1))
             (check-sat)",
        )
        .expect("script");
    assert_eq!(output, ["sat"]);
    assert_eq!(context.printed_model_falsifies(), None);
    let terms = context.terms.len();
    let domains = context.published.witness_domains.clone();
    let model = context.get_model();
    for _ in 0..3 {
        assert_eq!(context.printed_model_falsifies(), None);
        assert_eq!(context.terms.len(), terms);
        assert_eq!(context.published.witness_domains, domains);
        assert_eq!(context.get_model(), model);
    }

    let x = context.terms.mk_var("x", context.terms.sorts.int_sort);
    let two = context.terms.mk_int(2);
    let original = context.published_model().expect("model").clone();
    let mut wrong = original.clone();
    wrong.set(x, two);
    context.published.model = Some(wrong);
    assert!(context.printed_model_falsifies().is_some());
    context.published.model = Some(original);
    assert_eq!(context.printed_model_falsifies(), None);

    context.push();
    let contradiction = context.terms.mk_eq(x, two);
    context.assert(contradiction);
    assert_eq!(context.check_sat(), SolverResult::Unsat);
    context.pop();
    assert_eq!(context.check_sat(), SolverResult::Sat);
    assert_eq!(context.printed_model_falsifies(), None);
}
