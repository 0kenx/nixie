use nixie_solver::Context;

#[test]
fn unsupported_guard_search_never_fabricates_a_satisfying_model() {
    for body in [
        "(assert (forall ((x Int)) (=> (distinct x 3) false)))",
        "(declare-const m Int)
         (assert (forall ((x Int)) (=> (>= x 10) (= m 1))))(assert (= m 2))",
        "(declare-const m Int)
         (assert (forall ((x Int)) (or (<= x 7) (= m 1))))(assert (= m 2))",
        "(declare-fun f (Int) Int)
         (assert (forall ((i Int)) (=> (< i 5) (= (f i) 0))))(assert (= (f 4) 1))",
    ] {
        let mut context = Context::new();
        let output = context
            .execute_script(&format!("(set-logic ALL){body}(check-sat)"))
            .expect("script");
        assert!(
            matches!(output.as_slice(), [answer] if answer == "unsat" || answer == "unknown"),
            "{body}: {output:?}"
        );
    }
}

#[test]
fn guard_point_instances_remain_scope_consistent() {
    let mut context = Context::new();
    let output = context
        .execute_script(
            "(set-logic ALL)(declare-const m Int)
         (assert (forall ((x Int)) (or (<= x 7) (= m 1))))
         (push)(assert (= m 2))(check-sat)(pop)
         (assert (= m 1))(check-sat)
         (push)(assert (= m 2))(check-sat)(pop)(check-sat)",
        )
        .expect("script");
    assert_eq!(output.len(), 4);
    assert!(matches!(output[0].as_str(), "unsat" | "unknown"));
    assert_eq!(output[1], "sat");
    assert!(matches!(output[2].as_str(), "unsat" | "unknown"));
    assert_eq!(output[3], "sat");
}
