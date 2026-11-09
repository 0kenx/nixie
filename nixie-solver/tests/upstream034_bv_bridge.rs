use nixie_solver::Context;

#[test]
fn selectors_are_pinned_even_without_bv_variables() {
    for mode in ["eager", "lazy"] {
        let mut ctx = Context::new();
        let output = ctx
            .execute_script(&format!(
                "(set-logic QF_ABV)
             (set-option :theory-mode {mode})
             (declare-const p Bool)
             (declare-const a (Array (_ BitVec 8) (_ BitVec 8)))
             (assert (= (select a #x00) #x00))
             (assert (= (ite p (select a #x00) (select a #x01)) #x01))
             (check-sat)
             (push 1)(assert p)(check-sat)(pop 1)
             (assert (not p))(check-sat)"
            ))
            .unwrap();
        assert_eq!(output, ["sat", "unsat", "sat"], "{mode}");
    }
}

#[test]
fn published_uf_arguments_extend_to_the_checked_bv_model() {
    let mut ctx = Context::new();
    let output = ctx
        .execute_script(
            "(set-logic QF_UFBV)
         (declare-const x (_ BitVec 1))
         (declare-const y (_ BitVec 1))
         (declare-fun f ((_ BitVec 1)) (_ BitVec 1))
         (assert (distinct (f x) (f y)))
         (check-sat)(get-value (x y))",
        )
        .unwrap();
    assert_eq!(output[0], "sat");
    // There are only two possible values: a valid witness must publish both.
    assert!(
        output[1].contains("#b0") && output[1].contains("#b1"),
        "{output:?}"
    );
}

#[test]
fn constant_array_reads_keep_their_value_under_bv_arithmetic() {
    let mut ctx = Context::new();
    assert_eq!(ctx.execute_script(
        "(set-logic QF_ABV)
         (declare-const i (_ BitVec 8))
         (assert (= (bvadd (select ((as const (Array (_ BitVec 8) (_ BitVec 8))) #x02) i) #x01) #x06))
         (check-sat)"
    ).unwrap(), ["unsat"]);
}

#[test]
fn arithmetic_and_bv_agree_on_uf_arguments_and_results() {
    for body in [
        "(declare-fun f ((_ BitVec 2)) Int)
         (assert (= (bvadd x #b01) (bvadd y #b01)))
         (assert (< (f x) (f y)))",
        "(declare-const a Int)(declare-const b Int)
         (declare-fun f (Int) (_ BitVec 2))
         (assert (<= a b))(assert (>= a b))
         (assert (distinct (bvadd (f a) #b01) (bvadd (f b) #b01)))",
    ] {
        let mut ctx = Context::new();
        let script = format!(
            "(set-logic ALL)(declare-const x (_ BitVec 2))(declare-const y (_ BitVec 2))
             {body}(check-sat)"
        );
        assert_eq!(ctx.execute_script(&script).unwrap(), ["unsat"], "{script}");
    }
}

#[test]
fn compatible_arithmetic_partition_survives_a_conflicting_scope() {
    let mut ctx = Context::new();
    let output = ctx
        .execute_script(
            "(set-logic ALL)
         (declare-const x (_ BitVec 2))(declare-const y (_ BitVec 2))
         (declare-fun f ((_ BitVec 2)) Int)
         (assert (= (bvadd x #b01) (bvadd y #b01)))
         (assert (>= (f x) 2))(assert (>= (f y) 3))
         (check-sat)
         (push 1)(assert (< (f x) (f y)))(check-sat)(pop 1)
         (check-sat)",
        )
        .unwrap();
    assert_eq!(output, ["sat", "unsat", "sat"]);
}
