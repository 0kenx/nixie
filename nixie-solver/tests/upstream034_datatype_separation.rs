use nixie_solver::Context;

#[test]
fn unconstrained_enum_fields_publish_valid_values_across_scopes() {
    let mut context = Context::new();
    let output = context
        .execute_script(
            "(set-logic ALL)
        (declare-datatype C ((red) (green) (blue)))
        (declare-datatype B ((empty) (full (item C))))
        (declare-const b B)
        (assert (not ((_ is empty) b)))
        (assert (distinct b (full red)))
        (check-sat) (get-value ((distinct b (full red))))
        (push 1) (assert (distinct b (full green)))
        (check-sat) (get-value ((= b (full blue))))
        (assert (= b (full red))) (check-sat)
        (pop 1) (check-sat)",
        )
        .expect("valid script");
    assert_eq!(
        output
            .iter()
            .filter(|s| matches!(s.as_str(), "sat" | "unsat" | "unknown"))
            .map(String::as_str)
            .collect::<Vec<_>>(),
        ["sat", "sat", "unsat", "sat"]
    );
    assert!(output[1].ends_with("true))"), "{output:?}");
    assert!(output[3].ends_with("true))"), "{output:?}");
}
