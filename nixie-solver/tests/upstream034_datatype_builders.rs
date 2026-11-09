//! Datatype builder and theory-integration regressions from OxiZ 0.3.4.
use nixie_core::{TermManager, ast::TermKind, sort::DataTypeConstructor};
use nixie_solver::{Context, Solver, SolverResult};
use smallvec::smallvec;

#[test]
fn constructor_ite_cannot_equal_a_third_color() {
    let output = Context::new()
        .execute_script(
            r#"
(set-logic ALL)
(declare-datatypes ((C 0) (R 0)) (((red) (green) (blue)) ((mk (px Int) (pc C)))))
(declare-const c Bool)
(declare-const x Int)
(assert (= (ite c (mk 1 red) (mk x green)) (mk 1 blue)))
(check-sat)
"#,
        )
        .expect("valid SMT-LIB");
    assert_eq!(output, ["unsat"]);
}

#[test]
fn constructor_ite_proxy_is_sound_without_builder_folding() {
    let mut m = TermManager::new();
    let color = m.sorts.mk_datatype_sort("C");
    let colors = ["red", "green", "blue"].map(|name| DataTypeConstructor {
        name: m.intern_str(name),
        selectors: smallvec![],
    });
    m.declare_datatype("C", colors.to_vec());
    let record = m.sorts.mk_datatype_sort("R");
    let mk = DataTypeConstructor {
        name: m.intern_str("mk"),
        selectors: smallvec![
            (m.intern_str("px"), m.sorts.int_sort),
            (m.intern_str("pc"), color)
        ],
    };
    m.declare_datatype("R", vec![mk]);
    let [red, green, blue] =
        ["red", "green", "blue"].map(|name| m.mk_dt_constructor(name, [], color));
    let c = m.mk_var("c", m.sorts.bool_sort);
    let x = m.mk_var("x", m.sorts.int_sort);
    let one = m.mk_int(1);
    let a = m.mk_dt_constructor("mk", [one, red], record);
    let b = m.mk_dt_constructor("mk", [x, green], record);
    let target = m.mk_dt_constructor("mk", [one, blue], record);
    let choice = m.intern_term(TermKind::Ite(c, a, b), record);
    let equality = m.mk_eq_atom(choice, target);
    let mut solver = Solver::new();
    solver.assert(equality, &mut m);
    assert_eq!(solver.check(&mut m), SolverResult::Unsat);
}

#[test]
fn selector_under_uf_and_substituted_tester_keep_their_meaning() {
    let output = Context::new()
        .execute_script(
            r#"
(set-logic ALL)
(declare-datatype L ((nil) (cons (hd Int) (tl L))))
(declare-fun f (Int) Int)
(declare-const l L)
(assert (distinct (f (hd (cons 1 l))) (f 1)))
(check-sat)
"#,
        )
        .expect("valid SMT-LIB");
    assert_eq!(output, ["unsat"]);
    let output = Context::new()
        .execute_script(
            r#"
(set-logic ALL)
(declare-datatype L ((nil) (cons (hd Int) (tl L))))
(declare-const l L)
(assert (forall ((x L)) ((_ is cons) x)))
(assert (= l nil))
(check-sat)
"#,
        )
        .expect("valid SMT-LIB");
    assert_eq!(output, ["unsat"]);
}

#[test]
fn wrong_constructor_selector_is_underspecified_and_scopes_restore() {
    let output = Context::new()
        .execute_script(
            r#"
(set-logic ALL)
(declare-datatype L ((nil) (cons (hd Int) (tl L))))
(assert (= (hd nil) 42))
(check-sat)
(push 1)
(assert (= (hd nil) 43))
(check-sat)
(pop 1)
(check-sat)
"#,
        )
        .expect("valid SMT-LIB");
    assert_eq!(output, ["sat", "unsat", "sat"]);
}

#[test]
fn cyclic_array_model_reads_stop_and_preserve_known_writes() {
    use nixie_solver::Model;
    let mut m = TermManager::new();
    let int = m.sorts.int_sort;
    let sort = m.sorts.array(int, int);
    let a = m.mk_var("a", sort);
    let b = m.mk_var("b", sort);
    let one = m.mk_int(1);
    let two = m.mk_int(2);
    let nine = m.mk_int(9);
    let first = m.mk_store(a, one, nine);
    let three = m.mk_int(3);
    let store = m.mk_store(first, three, nine);
    for through_alias in [false, true] {
        let mut model = Model::new();
        model.set(a, if through_alias { b } else { store });
        if through_alias {
            model.set(b, store);
        }
        let known = m.mk_select(a, one);
        assert_eq!(model.eval(known, &mut m), nine);
        let unknown = m.mk_select(a, two);
        let result = model.eval(unknown, &mut m);
        assert!(
            matches!(m.get(result).map(|n| &n.kind), Some(TermKind::Select(_, i)) if *i == two)
        );
    }
}

#[test]
fn an_equality_intermediate_does_not_invent_a_set_member() {
    let output = Context::new()
        .execute_script(
            r#"
(set-logic ALL)
(declare-const f (Array Int Int))
(declare-const d (Set Int))
(declare-const base (Array Int Int))
(assert (and (= f (store (store base 1 10) 2 20))
             (= d (set.union (set.singleton 1) (set.singleton 2)))))
(assert (not (= (select f 2) 1)))
(check-sat)
(get-value (d (set.member (select f 2) d)))
"#,
        )
        .expect("valid SMT-LIB");
    assert_eq!(output[0], "sat");
    assert!(output[1].contains("(set.singleton 1)"), "{output:?}");
    assert!(output[1].contains("(set.singleton 2)"), "{output:?}");
    assert!(
        output[1].contains("((set.member (select f 2) d) false)"),
        "{output:?}"
    );
}

#[test]
fn cyclic_array_model_ites_do_not_expand_unresolved_branches() {
    use nixie_solver::Model;
    let mut m = TermManager::new();
    let int = m.sorts.int_sort;
    let sort = m.sorts.array(int, int);
    let a = m.mk_var("a", sort);
    let c = m.mk_var("c", m.sorts.bool_sort);
    let one = m.mk_int(1);
    let two = m.mk_int(2);
    let nine = m.mk_int(9);
    let write = m.mk_store(a, one, nine);
    let choice = m.mk_ite(c, write, a);
    let read = m.mk_select(a, one);
    let absent = m.mk_select(a, two);
    let mut model = Model::new();
    model.set(a, choice);
    let before = m.len();
    let unresolved = model.eval(read, &mut m);
    assert!(matches!(
        m.get(unresolved).map(|n| &n.kind),
        Some(TermKind::Select(..))
    ));
    assert!(m.len() <= before + 1, "must not unfold the cyclic ITE");
    model.set(c, m.true_id);
    assert_eq!(model.eval(read, &mut m), nine);
    let unresolved = model.eval(absent, &mut m);
    assert!(matches!(
        m.get(unresolved).map(|n| &n.kind),
        Some(TermKind::Select(..))
    ));
    model.set(c, m.false_id);
    let unresolved = model.eval(read, &mut m);
    assert!(matches!(
        m.get(unresolved).map(|n| &n.kind),
        Some(TermKind::Select(..))
    ));
}
