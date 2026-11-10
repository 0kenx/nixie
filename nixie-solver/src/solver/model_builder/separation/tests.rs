use super::*;
use crate::Context;
use nixie_sat::{Lit, SolverResult};

fn manager() -> (TermManager, SortId, SortId) {
    let mut context = Context::new();
    context
        .execute_script(
            "(declare-datatype C ((red) (green) (blue))) (declare-datatype B ((full (item C))))",
        )
        .expect("declarations");
    let color = context.terms.sorts.mk_datatype_sort("C");
    let box_sort = context.terms.sorts.mk_datatype_sort("B");
    (context.terms, color, box_sort)
}

#[test]
fn default_repair_does_not_search_enum_alternatives_or_the_left_side() {
    let (mut manager, color, box_sort) = manager();
    let red = manager.mk_dt_constructor("red", [], color);
    let full_red = manager.mk_dt_constructor("full", [red], box_sort);
    let p = manager.mk_var("p", box_sort);
    let q = manager.mk_var("q", box_sort);
    let mut solver = Solver::new();
    let q_node = solver.euf.intern(q);
    let literal_node = solver.euf.intern(full_red);
    solver
        .euf
        .merge(q_node, literal_node, manager.true_id)
        .expect("merge");
    // Check the pin primitive independently: disabling enum proposals must
    // not make literal-constructor protection pass only by avoiding repair.
    let mut work = MAX_REPAIR_WORK;
    let class = solver
        .separation_class(q, &FxHashMap::default(), &manager, &mut work)
        .expect("class within budget");
    assert!(class.contains(&full_red));
    assert!(field_is_pinned(
        &class,
        "full",
        0,
        "item",
        color,
        &FxHashSet::default(),
        &mut manager,
    ));
    let mut model = Model::new();
    model.set(p, full_red);
    model.set(q, full_red);
    model.set(full_red, full_red);
    let decls = FxHashMap::from_iter([(box_sort, resolve_decl(box_sort, &manager).expect("box"))]);
    solver.separate_datatype_models(
        &decls,
        &FxHashMap::default(),
        &[(p, q)],
        &mut model,
        &mut manager,
    );
    assert_eq!(model.get(p), model.get(q));
    assert_eq!(model.get(q), Some(full_red));
    assert_eq!(model.get(full_red), Some(full_red));
    let accessor = manager.mk_dt_selector("item", p, color);
    assert_eq!(model.get(accessor), None);
}

#[test]
fn encoded_ground_roots_pin_fields_not_visible_in_source_assertions() {
    let mut context = Context::new();
    context
        .execute_script("(declare-datatype B ((full (item Int))))")
        .expect("declaration");
    let mut manager = context.terms;
    let color = manager.sorts.int_sort;
    let box_sort = manager.sorts.mk_datatype_sort("B");
    let zero = manager.mk_int(0);
    let value = manager.mk_dt_constructor("full", [zero], box_sort);
    let p = manager.mk_var("p", box_sort);
    let q = manager.mk_var("q", box_sort);
    let mut solver = Solver::new();
    for term in [p, q] {
        let accessor = manager.mk_dt_selector("item", term, color);
        solver.ground_instance_roots.insert(accessor);
    }
    let mut model = Model::new();
    model.set(p, value);
    model.set(q, value);
    let decls = FxHashMap::from_iter([(box_sort, resolve_decl(box_sort, &manager).expect("box"))]);
    solver.separate_datatype_models(
        &decls,
        &FxHashMap::default(),
        &[(p, q)],
        &mut model,
        &mut manager,
    );
    assert_eq!(model.get(p), Some(value));
    assert_eq!(model.get(q), Some(value));
}

fn wide_single_offset_trial(forbid_increment: bool) {
    let mut context = Context::new();
    context
        .execute_script("(declare-datatype R ((mk (field Real))))")
        .expect("declaration");
    let mut manager = context.terms;
    let sort = manager.sorts.mk_datatype_sort("R");
    let real = manager.sorts.real_sort;
    let p = manager.mk_var("p", sort);
    let q = manager.mk_var("q", sort);
    let current = manager.mk_real(num_rational::Rational64::from_integer(i64::MAX));
    let literal = manager.mk_dt_constructor("mk", [current], sort);
    let accessor = manager.mk_dt_selector("field", q, real);
    let mut solver = Solver::new();
    let p_node = solver.euf.intern(p);
    let literal_node = solver.euf.intern(literal);
    solver
        .euf
        .merge(p_node, literal_node, manager.true_id)
        .expect("merge");
    let one = manager.mk_int(1);
    let huge = manager.mk_int(num_bigint::BigInt::from(i64::MAX) + 1);
    let forbidden = manager.mk_rdiv(huge, one);
    if forbid_increment {
        let equality = solver.sat.new_var();
        solver
            .var_to_constraint
            .insert(equality, Constraint::Eq(accessor, forbidden));
        solver.sat.add_clause([Lit::neg(equality)]);
        assert_eq!(solver.sat.solve(), SolverResult::Sat);
    }
    let mut model = Model::new();
    model.set(p, literal);
    model.set(q, literal);
    model.set(literal, literal);
    let decls = FxHashMap::from_iter([(sort, resolve_decl(sort, &manager).expect("record"))]);
    solver.separate_datatype_models(
        &decls,
        &FxHashMap::default(),
        &[(p, q)],
        &mut model,
        &mut manager,
    );
    if forbid_increment {
        // Do not search +2..+8 when the old +1 proposal is inadmissible.
        assert_eq!(model.get(accessor), None);
        assert_eq!(model.get(q), Some(literal));
    } else {
        let proposed = model.get(accessor).expect("separated field");
        let value = crate::solver::array_completion_certify::evaluate_closed_value_pure(
            &solver, proposed, &manager,
        )
        .expect("exact value")
        .to_big()
        .expect("number");
        assert_eq!(
            value,
            BigRational::from_integer(num_bigint::BigInt::from(i64::MAX) + 1)
        );
    }
    assert_eq!(model.get(literal), Some(literal));
}

#[test]
fn retained_single_numeric_offset_is_exact_above_i64_max() {
    wide_single_offset_trial(false);
}

#[test]
fn rejected_single_offset_does_not_enable_a_wider_search() {
    wide_single_offset_trial(true);
}

#[test]
fn collision_validation_cannot_trade_one_violation_for_another() {
    let a = TermId::new(10);
    let b = TermId::new(11);
    let c = TermId::new(12);
    let before = Violations {
        datatype: FxHashSet::from_iter([(a, b)]),
        ..Default::default()
    };
    let after = Violations {
        datatype: FxHashSet::from_iter([(a, c)]),
        ..Default::default()
    };
    assert!(!after.improves(&before));
    assert!(Violations::default().improves(&before));
}
