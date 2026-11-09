use nixie_solver::Context;

#[test]
fn compound_record_fields_use_the_function_interpretation() {
    for extra in ["", "(assert (= (q 3) 4))"] {
        let mut context = Context::new();
        let output = context
            .execute_script(&format!(
                "(set-logic ALL)
            (declare-datatype P ((mk (px Int) (py Int))))
            (declare-fun q (Int) Int) (declare-const p P)
            (assert (= p (mk (+ (q 3) 1) 5))) {extra}
            (check-sat) (get-value ((= p (mk (+ (q 3) 1) 5))))
            (push 1) (assert (= (px p) (+ (q 3) 2))) (check-sat)
            (pop 1) (check-sat)"
            ))
            .expect("script");
        assert_eq!(output[0], "sat", "{output:?}");
        assert!(output[1].ends_with("true))"), "{output:?}");
        assert_eq!(output[2], "unsat", "{output:?}");
        assert_eq!(output[3], "sat", "{output:?}");
    }
}
