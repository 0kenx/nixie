//! Tuple shape must not erase nominal datatype identity during set reduction.
use nixie_solver::Context;

#[test]
fn custom_tuple_cardinality_preserves_its_constructor_and_sort() {
    for (restriction, expected) in [
        ("(not (= (set.card s) 3))", "sat"),
        ("(= (set.card s) 2)", "sat"),
        ("(= (set.card s) 3)", "unsat"),
    ] {
        let script = format!(
            "(set-logic ALL)\n\
             (declare-datatype Pair ((pair (@t1 Int) (@t2 Int))))\n\
             (declare-const s (Set Pair))\n\
             (assert (= s (set.union (set.singleton (pair 1 2))\n\
                                      (set.singleton (pair 3 4)))))\n\
             (assert {restriction})\n(check-sat)"
        );
        let answers = Context::new().execute_script(&script);
        assert_eq!(answers.ok(), Some(vec![expected.to_string()]), "{script}");
    }
}
