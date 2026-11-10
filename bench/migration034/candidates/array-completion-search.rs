use nixie_solver::Context;

#[test]
fn repeated_bound_index_names_do_not_capture_the_free_scalar() {
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
    assert_eq!(answers.last().map(String::as_str), Some("sat"));
}
