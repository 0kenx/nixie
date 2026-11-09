use super::*;
use crate::{Context, SolverResult};

fn list_manager() -> (TermManager, nixie_core::sort::SortId) {
    let mut context = Context::new();
    context
        .execute_script("(declare-datatype L ((nil) (cons (hd Int) (tl L))))")
        .expect("declaration");
    let sort = context.terms.sorts.mk_datatype_sort("L");
    (context.terms, sort)
}

#[test]
fn constructor_refinement_has_explicit_guards_even_for_unexplained_merges() {
    let (mut m, sort) = list_manager();
    let nil = m.mk_dt_constructor("nil", [], sort);
    let one = m.mk_int(1);
    let cons = m.mk_dt_constructor("cons", [one, nil], sort);
    let mut solver = Solver::new();
    let a = solver.euf.intern(nil);
    let b = solver.euf.intern(cons);
    // Deliberately not a SAT atom or registered explanation. The theorem must
    // still be conditional; this merge cannot justify an unconditional false.
    solver.euf.merge(a, b, one).expect("merge");
    let lemmas = solver
        .constructor_class_lemmas(&mut m)
        .expect("valid constructors");
    assert_eq!(lemmas.len(), 1);
    let TermKind::Not(eq) = m.get(lemmas[0]).expect("lemma").kind else {
        panic!("guard missing")
    };
    assert!(matches!(
        m.get(eq).expect("equality").kind,
        TermKind::Eq(_, _)
    ));
    assert_ne!(lemmas[0], m.false_id);
    assert_eq!(m.mk_eq(nil, cons), m.false_id);
}

#[test]
fn raw_solver_refutes_nested_constructor_aliases_and_restores_scopes() {
    let (mut m, sort) = list_manager();
    let nil = m.mk_dt_constructor("nil", [], sort);
    let one = m.mk_int(1);
    let two = m.mk_int(2);
    let tail = m.mk_dt_constructor("cons", [two, nil], sort);
    let short = m.mk_dt_constructor("cons", [one, nil], sort);
    let long = m.mk_dt_constructor("cons", [one, tail], sort);
    let alias = m.mk_var("l", sort);
    let first = m.mk_eq(alias, short);
    let second = m.mk_eq(alias, long);
    let mut solver = Solver::new();
    solver.assert(first, &mut m);
    assert_eq!(solver.check(&mut m), SolverResult::Sat);
    let base = solver.dt_axiom_instances.clone();
    for _ in 0..2 {
        solver.push();
        solver.assert(second, &mut m);
        assert_eq!(solver.check(&mut m), SolverResult::Unsat);
        solver.pop();
        assert_eq!(solver.dt_axiom_instances, base);
        assert_eq!(solver.check(&mut m), SolverResult::Sat);
    }
}

#[test]
fn purified_datatype_cycles_are_refuted_beyond_one_constructor() {
    for depth in [2, 3, 5] {
        let (mut m, sort) = list_manager();
        let one = m.mk_int(1);
        let opaque = m.mk_apply("h", [one], sort);
        let mut chain = opaque;
        for _ in 0..depth {
            chain = m.mk_dt_constructor("cons", [one, chain], sort);
        }
        let cycle = m.mk_eq(opaque, chain);
        let mut solver = Solver::new();
        solver.assert(cycle, &mut m);
        assert_eq!(solver.check(&mut m), SolverResult::Unsat, "depth {depth}");
    }
}

#[test]
fn constructor_validation_does_not_treat_bad_arity_as_distinctness() {
    let (mut m, sort) = list_manager();
    let nil = m.mk_dt_constructor("nil", [], sort);
    let invalid = m.mk_dt_constructor("cons", [nil], sort);
    let mut solver = Solver::new();
    let a = solver.euf.intern(nil);
    let b = solver.euf.intern(invalid);
    solver.euf.merge(a, b, m.true_id).expect("merge");
    assert!(solver.constructor_class_lemmas(&mut m).is_none());
}

#[test]
fn constructor_cycle_scan_is_iterative_and_guarded() {
    std::thread::Builder::new()
        .stack_size(1024 * 1024)
        .spawn(|| {
            let (mut m, sort) = list_manager();
            let one = m.mk_int(1);
            let leaf = m.mk_var("l", sort);
            let mut solver = Solver::new();
            let leaf_node = solver.euf.intern(leaf);
            let mut root = leaf;
            for _ in 0..20_000 {
                root = m.mk_dt_constructor("cons", [one, root], sort);
                solver.euf.intern(root);
            }
            let root_node = solver.euf.term_to_node(root).expect("root");
            solver.euf.merge(leaf_node, root_node, one).expect("merge");
            let lemmas = solver.constructor_cycle_lemmas(&mut m).expect("cycle scan");
            assert_eq!(lemmas.len(), 1);
            assert_ne!(lemmas[0], m.false_id);
            assert!(matches!(
                m.get(lemmas[0]).expect("lemma").kind,
                TermKind::Not(_)
            ));
        })
        .expect("thread")
        .join()
        .expect("bounded native stack");
}

#[test]
fn datatype_cycle_scan_descends_through_unregistered_constructors() {
    let (mut m, sort) = list_manager();
    let one = m.mk_int(1);
    let leaf = m.mk_var("l", sort);
    let inner = m.mk_dt_constructor("cons", [one, leaf], sort);
    let outer = m.mk_dt_constructor("cons", [one, inner], sort);
    let mut solver = Solver::new();
    let a = solver.euf.intern(leaf);
    let b = solver.euf.intern(outer);
    assert!(solver.euf.term_to_node(inner).is_none());
    solver.euf.merge(a, b, one).expect("merge");
    let lemmas = solver.constructor_cycle_lemmas(&mut m).expect("cycle");
    assert_eq!(lemmas.len(), 1);
    assert_ne!(lemmas[0], m.false_id);
}

#[test]
fn datatype_refinement_accepts_fields_decided_by_their_owning_theory() {
    let (mut m, sort) = list_manager();
    let one = m.mk_int(1);
    let x = m.mk_var("x", m.sorts.int_sort);
    let nil = m.mk_dt_constructor("nil", [], sort);
    let left = m.mk_dt_constructor("cons", [one, nil], sort);
    let right = m.mk_dt_constructor("cons", [x, nil], sort);
    let field_eq = m.mk_eq(x, one);
    let mut solver = Solver::new();
    let a = solver.euf.intern(left);
    let b = solver.euf.intern(right);
    solver.euf.merge(a, b, m.true_id).expect("merge");
    assert_eq!(
        solver
            .constructor_class_lemmas(&mut m)
            .expect("lemmas")
            .len(),
        1
    );
    let literal = solver.encode(field_eq, &mut m);
    solver.sat.add_clause([literal]);
    assert_eq!(solver.sat.solve(), nixie_sat::SolverResult::Sat);
    assert!(!solver.euf_merged(x, one));
    assert!(
        solver
            .constructor_class_lemmas(&mut m)
            .expect("satisfied injection")
            .is_empty()
    );
    solver
        .encoded_terms
        .insert(field_eq, (literal, super::super::types::Polarity::Negative));
    assert!(!solver.datatype_conclusion_holds(field_eq, &m));
}

#[test]
fn boolean_theory_nodes_are_typed_terms_readable_by_refinement() {
    let mut context = Context::new();
    let result = context
        .execute_script(
            "(declare-datatype E ((ea)(eb)))
        (declare-fun p (Int) Bool)(assert (p 0))(check-sat)",
        )
        .expect("script");
    assert_eq!(result, ["sat"]);
    let euf = &context.solver().euf;
    assert!(euf.term_to_node(context.terms.true_id).is_some());
    assert!(euf.term_to_node(context.terms.false_id).is_some());
    for node in euf.all_node_indices() {
        let term = euf.node_term(node).expect("node");
        assert!(context.terms.get(term).is_some(), "untyped node {term:?}");
    }
}
