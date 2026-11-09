use nixie_solver::Context;

#[test]
fn nested_array_enum_witnesses_have_datatype_semantics_across_scopes() {
    let mut context = Context::new();
    let output = context
        .execute_script(
            "(set-logic ALL)
         (declare-datatype E ((ea) (eb) (ec)))
         (declare-const x Int) (declare-const y Int)
         (assert (<= 0 x 4)) (assert (<= 0 y 4))
         (declare-fun h ((Array Int E)) Int)
         (declare-const a (Array Int (Array Int E)))
         (assert (distinct (h (select a x)) (h (select a y))))
         (assert (= (select (select a x) 0) ea))
         (check-sat)
         (get-value ((distinct (h (select a x)) (h (select a y)))))
         (push 1) (assert (= x y)) (check-sat) (pop 1) (check-sat)",
        )
        .expect("script");
    assert_eq!(output[0], "sat", "{output:?}");
    assert!(output[1].ends_with("true))"), "{output:?}");
    assert_eq!(output[2], "unsat", "{output:?}");
    assert_eq!(output[3], "sat", "{output:?}");
}
