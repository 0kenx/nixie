use nixie_solver::Context;

#[test]
fn division_by_zero_is_an_explicit_consistent_model_choice() {
    let mut ctx = Context::new();
    let out = ctx
        .execute_script(
            "(set-logic UFLIA)(declare-fun f (Int) Int)(declare-const y Int)
        (assert (forall ((z Int)) (>= (f z) 0)))
        (assert (= y 1))(assert (distinct (f y) (f (div 1 0))))
        (check-sat)(get-model)(get-value ((div 1 0) (div 7 0) (distinct (f y) (f (div 1 0)))))",
        )
        .expect("script");
    assert_eq!(out[0], "sat", "{out:?}");
    assert!(out[1].contains("define-fun div0"), "{out:?}");
    assert!(
        out[2].contains("((div 1 0) 0)") && out[2].contains("((div 7 0) 0)"),
        "{out:?}"
    );
    assert!(
        out[2].contains("(distinct (f y) (f (div 1 0))) true"),
        "{out:?}"
    );
}

