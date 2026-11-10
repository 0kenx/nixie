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

#[test]
fn unpinned_literal_function_collision_is_not_a_certificate() {
    let mut tm = TermManager::new();
    let int = tm.sorts.int_sort;
    let four = tm.mk_int(4);
    let x = tm.mk_var("x", int);
    let f4 = tm.mk_apply("f", [four], int);
    let fx = tm.mk_apply("f", [x], int);
    let mut solver = Solver::new();
    for term in [four, x, f4, fx] {
        solver.euf.intern(term);
    }
    let root = tm.mk_eq(f4, fx);
    solver.encode(root, &mut tm);
    let mut model = Model::new();
    model.set(x, four);
    model.set(f4, tm.mk_int(0));
    model.set(fx, tm.mk_int(1));
    // A stale assignment to the literal cannot make 4 denote 7.
    model.set(four, tm.mk_int(7));
    solver.model = Some(model);
    assert!(!solver.unpinned_function_model_is_consistent(&mut tm));
    solver.model.as_mut().unwrap().set(fx, tm.mk_int(0));
    assert!(solver.unpinned_function_model_is_consistent(&mut tm));
}

#[test]
fn function_certificate_declines_missing_and_defaulted_values() {
    let mut tm = TermManager::new();
    let int = tm.sorts.int_sort;
    let four = tm.mk_int(4);
    let x = tm.mk_var("x", int);
    let f4 = tm.mk_apply("f", [four], int);
    let fx = tm.mk_apply("f", [x], int);
    let mut solver = Solver::new();
    for term in [four, x, f4, fx] {
        solver.euf.intern(term);
    }
    let root = tm.mk_eq(f4, fx);
    solver.encode(root, &mut tm);
    let mut model = Model::new();
    model.set(f4, tm.mk_int(0));
    model.set(fx, tm.mk_int(0));
    solver.model = Some(model);
    assert!(!solver.unpinned_function_model_is_consistent(&mut tm));
    solver.model.as_mut().unwrap().set_default(x, four);
    assert!(!solver.unpinned_function_model_is_consistent(&mut tm));
    solver.model.as_mut().unwrap().set(x, four);
    assert!(solver.unpinned_function_model_is_consistent(&mut tm));
}

#[test]
fn function_certificate_budget_exhaustion_is_not_success() {
    let mut tm = TermManager::new();
    let solver = Solver::new();
    let model = Model::new();
    let four = tm.mk_int(4);
    let mut values = Values::new(&solver).unwrap();
    values.work = 0;
    assert!(
        values
            .certificate_key(&solver, four, &model, &mut tm)
            .is_none()
    );
}

#[test]
fn interface_constant_recognition_does_not_overflow_on_signed_remainder() {
    let mut tm = TermManager::new();
    let int = tm.sorts.int_sort;
    let min = tm.mk_int(i64::MIN);
    let minus_one = tm.mk_int(-1);
    let solver = Solver::new();
    for kind in [TermKind::Div(min, minus_one), TermKind::Mod(min, minus_one)] {
        let term = tm.intern_term(kind, int);
        assert!(solver.interface_constant_value(term, &tm).is_none());
    }
}

#[test]
fn popped_numeric_function_obligations_do_not_poison_the_outer_scope() {
    let mut tm = TermManager::new();
    let mut solver = Solver::new();
    solver.push();
    let four = tm.mk_int(4);
    let app = tm.mk_apply("f", [four], tm.sorts.int_sort);
    solver.euf.intern(four);
    solver.euf.intern(app);
    let zero = tm.mk_int(0);
    let root = tm.mk_eq(app, zero);
    solver.encode(root, &mut tm);
    assert!(solver.unpinned_uf_apps.contains(&app));
    solver.model = Some(Model::new());
    assert!(!solver.unpinned_function_model_is_consistent(&mut tm));
    solver.pop();
    assert!(solver.unpinned_uf_apps.is_empty());
    solver.model = Some(Model::new());
    assert!(solver.unpinned_function_model_is_consistent(&mut tm));
}

#[test]
fn coefficient_argument_is_checked_without_an_eager_uf_pin() {
    let mut ctx = Context::new();
    ctx.execute_script(
        "(set-logic QF_UFLIA)
        (declare-fun f (Int) Int)(declare-const x Int)
        (assert (= (* 4 x) 8))(assert (= (f 4) 0))",
    )
    .unwrap();
    let four = ctx.terms.mk_int(4);
    assert!(!ctx.solver().interface_const_pins.contains_key(&four));
    let result = ctx
        .execute_script(
            "(check-sat)(check-sat)
        (push 1)(assert false)(check-sat)(pop 1)(check-sat)",
        )
        .unwrap();
    assert_eq!(result, ["sat", "sat", "unsat", "sat"]);
}
