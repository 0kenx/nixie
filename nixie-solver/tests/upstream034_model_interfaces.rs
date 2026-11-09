use nixie_solver::Context;

#[test]
fn arrays_used_only_as_function_arguments_get_separating_reads() {
    let mut context = Context::new();
    let output = context
        .execute_script(
            "(set-logic QF_AUFBV)
        (declare-fun fa ((Array (_ BitVec 1) (_ BitVec 2))) (_ BitVec 2))
        (declare-const a (Array (_ BitVec 1) (_ BitVec 2)))
        (declare-const b (Array (_ BitVec 1) (_ BitVec 2)))
        (assert (distinct (fa a) (fa b)))
        (check-sat) (get-value ((distinct a b) (distinct (fa a) (fa b))))
        (push 1) (assert (= a b)) (check-sat) (pop 1) (check-sat)",
        )
        .expect("script");
    assert_eq!(output[0], "sat", "{output:?}");
    assert_eq!(output[1].matches("true").count(), 2, "{output:?}");
    assert_eq!(output[2], "unsat", "{output:?}");
    assert_eq!(output[3], "sat", "{output:?}");
}

#[test]
fn repeated_array_distinct_selector_remains_decidable_incrementally() {
    let mut context = Context::new();
    let output = context
        .execute_script(
            "(set-logic QF_AUFBV)
        (declare-const i (_ BitVec 1))
        (declare-const a (Array (_ BitVec 1) (_ BitVec 1)))
        (assert (= a ((as const (Array (_ BitVec 1) (_ BitVec 1))) #b0)))
        (check-sat)
        (push 1)
        (assert (=> (= ((as const (Array (_ BitVec 1) (_ BitVec 1))) #b1) a)
                    (bvule (ite (distinct a a) #b1 i) i)))
        (assert (distinct (store a i #b1) a))
        (check-sat) (pop 1) (check-sat)",
        )
        .expect("script");
    assert_eq!(output, ["sat", "sat", "sat"]);
}

#[test]
fn preprocessed_false_core_names_original_assertions_and_obeys_scopes() {
    let mut context = Context::new();
    let output = context
        .execute_script(
            "(set-logic ALL)
        (set-option :produce-unsat-cores true)
        (declare-sort U 0) (declare-fun f (U) U)
        (assert (! true :named harmless)) (push 1)
        (assert (! (not (forall ((x U)) (= (f x) (f x)))) :named A1))
        (check-sat) (get-unsat-core) (pop 1) (get-unsat-core)
        (check-sat) (push 1) (assert (! false :named A2))
        (check-sat) (get-unsat-core)",
        )
        .expect("script");
    assert_eq!(output[0], "unsat");
    assert_eq!(output[1], "(A1)", "{output:?}");
    assert!(output[2].starts_with("(error"));
    assert_eq!(output[3], "sat");
    assert_eq!(output[4], "unsat");
    assert_eq!(output[5], "(A2)");
}

#[test]
fn published_real_function_definition_round_trips() {
    let mut context = Context::new();
    let output = context
        .execute_script(
            "(set-logic ALL)
        (define-fun f ((x Real)) Real
          (ite (= x (to_real 3)) (to_real 1) (+ (* (to_real 0) x) (to_real 0))))
        (assert (not (and (= (f 1.5) 0.0) (= (f 1.9) 0.0) (= (f 3.0) 1.0))))
        (check-sat)",
        )
        .expect("a printed model must parse");
    assert_eq!(output, ["unsat"]);
}

#[test]
fn finite_field_function_model_replays_with_in_range_separate_arguments() {
    let mut context = Context::new();
    let output = context
        .execute_script(
            "(set-logic QF_UFFF)
         (declare-fun f ((_ FiniteField 2)) (_ FiniteField 2))
         (declare-const x (_ FiniteField 2))
         (declare-const y (_ FiniteField 2))
         (assert (distinct (f x) (f y)))
         (check-sat) (get-model)",
        )
        .expect("script");
    assert_eq!(output[0], "sat", "{output:?}");
    let definitions = output[1]
        .trim()
        .strip_prefix("(model")
        .expect("model")
        .strip_suffix(')')
        .expect("close");
    let mut replay = Context::new();
    let result = replay
        .execute_script(&format!(
            "(set-logic QF_FF) {definitions}
         (assert (not (and (distinct x y) (distinct (f x) (f y))))) (check-sat)"
        ))
        .expect("model parses");
    assert_eq!(result, ["unsat"]);
}

#[test]
fn rejected_set_synthesis_cannot_publish_identical_choices() {
    let mut context = Context::new();
    let output = context
        .execute_script(
            "(set-logic ALL) (declare-const A (Set Int)) (declare-const B (Set Int))
         (declare-const c Bool) (assert (not c)) (assert (>= (set.card A) 1))
         (assert (distinct (set.choose (ite c A B)) (set.choose A)))
         (check-sat) (get-model) (get-info :reason-unknown)",
        )
        .expect("script");
    assert_eq!(output[0], "unknown");
    assert!(output[1].contains("model not certified"), "{output:?}");
    assert!(output[2].contains("assertion 3 is false"), "{output:?}");
}
