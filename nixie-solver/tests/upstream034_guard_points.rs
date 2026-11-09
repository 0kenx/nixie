use nixie_solver::Context;

#[test]
fn upstream_guard_boundaries_refute_universals() {
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
        assert_eq!(output, ["unsat"], "{body}");
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
    assert_eq!(output, ["unsat", "sat", "unsat", "sat"]);
}
