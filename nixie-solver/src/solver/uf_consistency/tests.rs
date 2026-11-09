use super::*;
use crate::Context;

#[test]
fn exact_real_arguments_share_a_function_point() {
    let mut tm = TermManager::new();
    let real = tm.sorts.real_sort;
    let boolean = tm.sorts.bool_sort;
    let x = tm.mk_var("x", real);
    let y = tm.mk_var("y", real);
    let fx = tm.mk_apply("f", [x], boolean);
    let fy = tm.mk_apply("f", [y], boolean);
    let a = tm.mk_real(num_rational::Rational64::from_integer(1));
    let one = tm.mk_int(1);
    let b = tm.mk_rdiv(one, one);
    let mut solver = Solver::new();
    for term in [x, y, fx, fy] {
        solver.euf.intern(term);
    }
    let mut model = Model::new();
    model.set(x, a);
    model.set(y, b);
    model.set(fx, tm.true_id);
    model.set(fy, tm.false_id);
    solver.model = Some(model.clone());
    assert_eq!(solver.functional_collision_lemmas(&mut tm, true).len(), 1);
    solver.push();
    solver.model = Some(model.clone());
    assert!(solver.assert_functional_consistency(&mut tm, true));
    solver.model = Some(model);
    assert!(!solver.assert_functional_consistency(&mut tm, true));
    solver.pop();
    assert!(solver.dt_axiom_instances.is_empty());
}

#[test]
fn closed_constructor_keys_normalize_scalar_fields_and_shared_dags() {
    let mut context = Context::new();
    context
        .execute_script("(declare-datatype T ((leaf (value Real)) (node (left T) (right T))))")
        .expect("declaration");
    let mut tm = context.terms;
    let sort = tm.sorts.mk_datatype_sort("T");
    let one = tm.mk_int(1);
    let real = tm.mk_real(num_rational::Rational64::from_integer(1));
    let quotient = tm.mk_rdiv(one, one);
    let mut a = tm.mk_dt_constructor("leaf", [real], sort);
    let mut b = tm.mk_dt_constructor("leaf", [quotient], sort);
    for _ in 0..70 {
        a = tm.mk_dt_constructor("node", [a, a], sort);
        b = tm.mk_dt_constructor("node", [b, b], sort);
    }
    let solver = Solver::new();
    let mut values = Values::new(&solver).expect("budget");
    assert_eq!(
        values.closed_value(&solver, a, &mut tm),
        values.closed_value(&solver, b, &mut tm)
    );
    assert!(values.work > MAX_WORK - 1000);
}

#[test]
fn defaults_do_not_supply_function_collision_evidence() {
    let mut tm = TermManager::new();
    let integer = tm.sorts.int_sort;
    let boolean = tm.sorts.bool_sort;
    let x = tm.mk_var("x", integer);
    let y = tm.mk_var("y", integer);
    let fx = tm.mk_apply("f", [x], boolean);
    let fy = tm.mk_apply("f", [y], boolean);
    let mut solver = Solver::new();
    for term in [x, y, fx, fy] {
        solver.euf.intern(term);
    }
    let zero = tm.mk_int(0);
    let mut model = Model::new();
    model.set_default(x, zero);
    model.set_default(y, zero);
    model.set(fx, tm.true_id);
    model.set(fy, tm.false_id);
    solver.model = Some(model);
    assert!(solver.functional_collision_lemmas(&mut tm, true).is_empty());
}

#[test]
fn datatype_and_uninterpreted_results_emit_only_guarded_congruence() {
    for opaque in [false, true] {
        let mut context = Context::new();
        context
            .execute_script("(declare-datatype C ((red) (blue))) (declare-sort U 0)")
            .expect("sorts");
        let mut tm = context.terms;
        let sort = if opaque {
            {
                let name = tm.intern_str("U");
                tm.sorts.intern(SortKind::Uninterpreted(name))
            }
        } else {
            tm.sorts.mk_datatype_sort("C")
        };
        let int = tm.sorts.int_sort;
        let x = tm.mk_var("x", int);
        let y = tm.mk_var("y", int);
        let fx = tm.mk_apply("f", [x], sort);
        let fy = tm.mk_apply("f", [y], sort);
        let mut solver = Solver::new();
        for term in [x, y, fx, fy] {
            solver.euf.intern(term);
        }
        let mut model = Model::new();
        let zero = tm.mk_int(0);
        model.set(x, zero);
        model.set(y, zero);
        if !opaque {
            let red = tm.mk_dt_constructor("red", [], sort);
            let blue = tm.mk_dt_constructor("blue", [], sort);
            model.set(fx, red);
            model.set(fy, blue);
        }
        solver.model = Some(model);
        let lemmas = solver.functional_collision_lemmas(&mut tm, true);
        assert_eq!(lemmas.len(), 1);
        let argument_eq = tm.mk_eq(x, y);
        let result_eq = tm.mk_eq(fx, fy);
        let expected = tm.mk_implies(argument_eq, result_eq);
        assert_eq!(lemmas[0], expected);
    }
}
