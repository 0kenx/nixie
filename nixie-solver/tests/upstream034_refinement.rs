use nixie_solver::Context;

#[test]
fn fractional_nira_witness_survives_publication_and_scopes() {
    let mut context = Context::new();
    let output = context
        .execute_script(
            "(set-logic QF_NIRA)
        (declare-const x Int)(declare-const y Real)
        (assert (= (* x x) 4))(assert (> y 1.0))(assert (< y 2.0))
        (check-sat)(get-value ((> y 1.0) (< y 2.0)))
        (push)(assert (= y 1.5))(check-sat)(get-value (y))
        (pop)(check-sat)(get-value ((> y 1.0) (< y 2.0)))",
        )
        .expect("script");
    assert_eq!(output[0], "sat", "{output:?}");
    assert_eq!(output[2], "sat", "{output:?}");
    assert_eq!(output[4], "sat", "{output:?}");
    assert_eq!(output[1].matches("true").count(), 2, "{output:?}");
    assert_eq!(output[5].matches("true").count(), 2, "{output:?}");
}

#[test]
fn datatype_alias_contradiction_reaches_unsat_in_public_api() {
    let mut context = Context::new();
    let output = context
        .execute_script(
            "(declare-datatype L ((nil)(cons (hd Int)(tl L))))
        (declare-const l L)
        (assert (= l (cons 1 nil)))
        (assert (= l (cons 1 (cons 2 nil))))
        (check-sat)",
        )
        .expect("script");
    assert_eq!(output, ["unsat"]);
}
