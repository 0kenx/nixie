//! Array completion must publish the same interpretation its certificate checked.
use nixie_solver::Context;

#[test]
fn two_arrays_under_one_binder_publish_a_model_of_all_128_points() {
    let declarations = "(set-logic ALL)
      (declare-const a (Array (_ BitVec 7) (_ BitVec 1)))
      (declare-const b (Array (_ BitVec 7) (_ BitVec 1)))";
    let mut context = Context::new();
    let answers = context
        .execute_script(&format!(
            "{declarations}
      (assert (forall ((i (_ BitVec 7))) (= (select a i) (bvnot (select b i)))))
      (assert (= (select a (_ bv0 7)) #b1)) (check-sat)"
        ))
        .expect("valid script");
    assert_eq!(answers.last().map(String::as_str), Some("sat"));
    let model = context.get_model().expect("published model");
    let mut replay = declarations.to_string();
    for (name, _, value) in model {
        assert!(!value.contains('?'), "{name}: {value}");
        replay.push_str(&format!("\n(assert (= {name} {value}))"));
    }
    for i in 0..128 {
        replay.push_str(&format!(
            "\n(assert (= (select a (_ bv{i} 7)) (bvnot (select b (_ bv{i} 7)))))"
        ));
    }
    replay.push_str("\n(assert (= (select a (_ bv0 7)) #b1)) (check-sat)");
    let answers = Context::new()
        .execute_script(&replay)
        .expect("model replay parses");
    assert_eq!(answers.last().map(String::as_str), Some("sat"));
}

#[test]
fn completed_array_defaults_answer_get_value_and_survive_scope_changes() {
    let mut context = Context::new();
    let answers = context
        .execute_script(
            "(set-logic ALL)
      (declare-const a (Array (_ BitVec 7) Bool))
      (assert (forall ((i (_ BitVec 7))) (select a i)))
      (check-sat) (get-value ((select a (_ bv85 7))))
      (push 1) (assert (not (select a (_ bv2 7)))) (check-sat)
      (pop 1) (check-sat) (get-value ((select a (_ bv2 7))))",
        )
        .expect("valid script");
    let verdicts: Vec<_> = answers
        .iter()
        .map(String::as_str)
        .filter(|s| matches!(*s, "sat" | "unsat" | "unknown"))
        .collect();
    assert_eq!(verdicts, ["sat", "unsat", "sat"]);
    let reads: Vec<_> = answers
        .iter()
        .filter(|s| s.starts_with("(((select"))
        .collect();
    assert_eq!(reads.len(), 2);
    assert!(reads.iter().all(|s| s.ends_with(" true))")), "{answers:?}");
}

#[test]
fn incomplete_bound_index_completion_is_honestly_unknown() {
    let answers = Context::new()
        .execute_script(
            "(set-logic ALL)
      (declare-const a (Array (_ BitVec 7) (_ BitVec 7)))
      (declare-const k (_ BitVec 7))
      (assert (and (forall ((k (_ BitVec 7))) (forall ((k (_ BitVec 7))) (= k k)))
        (forall ((i (_ BitVec 7))) (= (select (store a i k) (_ bv1 7)) k))))
      (check-sat)",
        )
        .expect("valid script");
    assert_eq!(answers.last().map(String::as_str), Some("unknown"));
}
