use nixie_core::ast::{TermId, TermKind, TermManager};
use nixie_core::smtlib::parse_script;
use num_rational::Rational64;

#[test]
fn repeated_distinct_operands_cannot_hide_an_invalid_suffix() {
    let mut tm = TermManager::new();
    let sort = tm.sorts.array(tm.sorts.int_sort, tm.sorts.int_sort);
    let a = tm.mk_var("a", sort);
    let b = tm.mk_var("b", sort);
    assert!(tm.distinct_has_repeated_operand(&[a, b, a]));
    assert_eq!(tm.mk_distinct([a, b, a]), tm.false_id);
    assert!(!tm.distinct_has_repeated_operand(&[a, a, tm.true_id]));
    assert!(!tm.distinct_has_repeated_operand(&[a, a, TermId::new(u32::MAX)]));
    assert_ne!(tm.mk_distinct([a, a, tm.true_id]), tm.false_id);
}

#[test]
fn real_injection_zero_survives_raw_product_simplification() {
    let mut tm = TermManager::new();
    let zero = tm.mk_int(0);
    let one = tm.mk_real(Rational64::from_integer(1));
    let product = tm.intern_term(TermKind::Mul(vec![zero, one].into()), tm.sorts.real_sort);
    let simplified = tm.simplify(product);
    assert_eq!(tm.get(simplified).expect("value").sort, tm.sorts.real_sort);
    assert!(
        matches!(tm.get(simplified).expect("value").kind, TermKind::RealConst(value) if value == Rational64::from_integer(0))
    );
}

#[test]
fn to_real_has_real_sort_for_literals_wide_values_and_integer_variables() {
    for value in [
        "0",
        "3",
        "1461501637330902918203684832716283019655932542979",
        "n",
    ] {
        let mut tm = TermManager::new();
        parse_script(
            &format!(
                "(declare-const n Int) (declare-const p Bool)
            (assert (= (ite p (to_real {value}) 0.0) 1.0))"
            ),
            &mut tm,
        )
        .expect("both ite branches have Real sort");
    }
    for value in ["true", "1.5"] {
        let mut tm = TermManager::new();
        assert!(parse_script(&format!("(assert (= (to_real {value}) 0.0))"), &mut tm).is_err());
    }
}
