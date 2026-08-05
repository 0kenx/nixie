//! White-box coverage for the parts of the pure-equality fast path an
//! external SMT-LIB2 script cannot reach directly: the purity walk's own
//! edge cases, and the post-solve re-verification actually catching a
//! deliberately broken graph. End-to-end sat/unsat behaviour (the normal way
//! to exercise this module) lives in `tests/pr32_pr33_soundness.rs`.

use super::*;
use oxiz_core::sort::SortKind;

/// Build a fresh `TermManager` with one uninterpreted sort `"U"` interned,
/// for tests that need `declare-const`-equivalent terms without going
/// through `Context`/the SMT-LIB2 parser.
fn manager_with_uninterpreted_sort() -> (TermManager, oxiz_core::sort::SortId) {
    let mut manager = TermManager::new();
    let spur = manager.sorts.intern_str("U");
    let sort = manager.sorts.intern(SortKind::Uninterpreted(spur));
    (manager, sort)
}

// ---------------------------------------------------------------------
// Purity detection
// ---------------------------------------------------------------------

/// A conjunction of equalities and disequalities over uninterpreted-sort
/// constants, with `and`/`or`/`not` connectives — squarely inside the
/// grammar — must be accepted.
#[test]
fn test_pr33_pure_equality_conjunction_is_accepted() {
    let (mut manager, sort) = manager_with_uninterpreted_sort();
    let mut solver = Solver::new();
    let a = manager.mk_var("a", sort);
    let b = manager.mk_var("b", sort);
    let c = manager.mk_var("c", sort);
    let ab = manager.mk_eq(a, b);
    let bc = manager.mk_eq(b, c);
    let conj = manager.mk_and([ab, bc]);
    solver.assert(conj, &mut manager);

    assert!(
        solver.collect_equality_skeleton(&manager).is_some(),
        "a plain and/eq formula over one uninterpreted sort must be accepted"
    );
}

/// A single `distinct`/function application anywhere in the assertion set
/// disqualifies the *entire* formula, even though every other assertion is
/// pure — the gate has to look at the whole assertion set, not just the
/// first assertion.
#[test]
fn test_pr33_function_application_disqualifies_whole_formula() {
    let (mut manager, sort) = manager_with_uninterpreted_sort();
    let mut solver = Solver::new();
    let a = manager.mk_var("a", sort);
    let b = manager.mk_var("b", sort);
    let ab = manager.mk_eq(a, b);
    solver.assert(ab, &mut manager);

    // A second, otherwise-independent assertion drags in a function
    // application (`f(a) = a`), which is EUF, not equality logic.
    let fa = manager.mk_apply("f", [a], sort);
    let eq_fa = manager.mk_eq(fa, a);
    solver.assert(eq_fa, &mut manager);

    assert!(
        solver.collect_equality_skeleton(&manager).is_none(),
        "a function application anywhere in the assertion set must disqualify the fast path"
    );
}

/// An arithmetic atom over `Int` constants must disqualify the formula too:
/// `Int` has its own equality-adjacent semantics (ordering) this module does
/// not model, so even a `(= x y)` between two `Int` vars is declined — the
/// gate's `Eq` arm requires *both* operands to be `Uninterpreted`-sorted.
#[test]
fn test_pr33_arithmetic_comparison_disqualifies() {
    let mut manager = TermManager::new();
    let mut solver = Solver::new();
    let int = manager.sorts.int_sort;
    let x = manager.mk_var("x", int);
    let y = manager.mk_var("y", int);
    let gt = manager.mk_gt(x, y);
    solver.assert(gt, &mut manager);

    assert!(
        solver.collect_equality_skeleton(&manager).is_none(),
        "an Int comparison must never be accepted as an equality-logic edge"
    );
}

/// `ite` and `=>` are Boolean connectives this module does not walk through
/// (only `not`/`and`/`or`/`eq` are); either one anywhere must decline.
#[test]
fn test_pr33_ite_and_implies_disqualify() {
    let (mut manager, sort) = manager_with_uninterpreted_sort();
    let bool_sort = manager.sorts.bool_sort;

    let mut solver_ite = Solver::new();
    let a = manager.mk_var("a", sort);
    let b = manager.mk_var("b", sort);
    let c = manager.mk_var("c", sort);
    let p = manager.mk_var("p", bool_sort);
    let eq1 = manager.mk_eq(a, b);
    let eq2 = manager.mk_eq(a, c);
    let ite = manager.mk_ite(p, eq1, eq2);
    solver_ite.assert(ite, &mut manager);
    assert!(solver_ite.collect_equality_skeleton(&manager).is_none());

    let mut solver_implies = Solver::new();
    let implies = manager.mk_implies(eq1, eq2);
    solver_implies.assert(implies, &mut manager);
    assert!(solver_implies.collect_equality_skeleton(&manager).is_none());
}

/// A formula with no equality atom at all (Booleans only) has nothing for
/// this module to contribute; it must decline rather than run a pointless
/// (empty) chordalization.
#[test]
fn test_pr33_no_equality_atoms_declines() {
    let mut manager = TermManager::new();
    let mut solver = Solver::new();
    let bool_sort = manager.sorts.bool_sort;
    let p = manager.mk_var("p", bool_sort);
    solver.assert(p, &mut manager);
    assert!(solver.collect_equality_skeleton(&manager).is_none());
}

// ---------------------------------------------------------------------
// Post-solve re-verification: the actual backstop
// ---------------------------------------------------------------------

/// Force a SAT-decided assignment onto three equality-atom variables that is
/// *not* transitively consistent (`a=b` and `b=c` true, `a=c` false) without
/// ever adding the transitivity clauses that would normally rule this out —
/// simulating exactly the bug class the re-verification exists to catch (a
/// triangle `install_transitivity` never saw). The check must refuse to
/// confirm this as a valid model.
#[test]
fn test_pr33_backstop_refutes_a_transitively_inconsistent_assignment() {
    let (mut manager, sort) = manager_with_uninterpreted_sort();
    let mut solver = Solver::new();
    let a = manager.mk_var("a", sort);
    let b = manager.mk_var("b", sort);
    let c = manager.mk_var("c", sort);

    let ab_term = manager.mk_eq(a, b);
    let bc_term = manager.mk_eq(b, c);
    let ac_term = manager.mk_eq(a, c);
    let ab = solver.get_or_create_var(ab_term);
    let bc = solver.get_or_create_var(bc_term);
    let ac = solver.get_or_create_var(ac_term);

    // Force exactly the inconsistent assignment; deliberately no
    // transitivity clause is added, so plain SAT accepts it.
    solver.sat.add_clause([Lit::pos(ab)]);
    solver.sat.add_clause([Lit::pos(bc)]);
    solver.sat.add_clause([Lit::neg(ac)]);
    assert_eq!(solver.sat.solve(), oxiz_sat::SolverResult::Sat);

    let graph = EqualityGraph {
        vertices: vec![a, b, c],
        adjacency: vec![
            FxHashSet::from_iter([1, 2]),
            FxHashSet::from_iter([0, 2]),
            FxHashSet::from_iter([0, 1]),
        ],
        edge_var: FxHashMap::from_iter([((0, 1), ab), ((1, 2), bc), ((0, 2), ac)]),
        direct_edges: vec![(0, 1), (1, 2), (0, 2)],
    };

    assert!(
        solver.verify_and_build_classes(&graph).is_none(),
        "a=b, b=c, a!=c must be refused: it is not a valid equivalence relation"
    );
}

/// The positive control for the test above: the same three variables, same
/// graph shape, but *with* the triangle clauses this module would actually
/// add. The union-find re-derivation must now agree with every direct edge's
/// decided value.
#[test]
fn test_pr33_backstop_confirms_a_consistent_assignment() {
    let (mut manager, sort) = manager_with_uninterpreted_sort();
    let mut solver = Solver::new();
    let a = manager.mk_var("a", sort);
    let b = manager.mk_var("b", sort);
    let c = manager.mk_var("c", sort);

    let ab_term = manager.mk_eq(a, b);
    let bc_term = manager.mk_eq(b, c);
    let ac_term = manager.mk_eq(a, c);
    let ab = solver.get_or_create_var(ab_term);
    let bc = solver.get_or_create_var(bc_term);
    let ac = solver.get_or_create_var(ac_term);

    solver.sat.add_clause([Lit::pos(ab)]);
    solver.sat.add_clause([Lit::pos(bc)]);
    // The actual transitivity clause: ab /\ bc => ac.
    solver
        .sat
        .add_clause([Lit::neg(ab), Lit::neg(bc), Lit::pos(ac)]);
    assert_eq!(solver.sat.solve(), oxiz_sat::SolverResult::Sat);

    let graph = EqualityGraph {
        vertices: vec![a, b, c],
        adjacency: vec![
            FxHashSet::from_iter([1, 2]),
            FxHashSet::from_iter([0, 2]),
            FxHashSet::from_iter([0, 1]),
        ],
        edge_var: FxHashMap::from_iter([((0, 1), ab), ((1, 2), bc), ((0, 2), ac)]),
        direct_edges: vec![(0, 1), (1, 2), (0, 2)],
    };

    let classes = solver.verify_and_build_classes(&graph);
    assert!(
        classes.is_some(),
        "a consistent assignment must be confirmed"
    );
    let classes = classes.expect("checked Some above");
    assert_eq!(
        classes[0], classes[1],
        "a and b are asserted equal and must land in the same class"
    );
    assert_eq!(
        classes[1], classes[2],
        "b and c are asserted equal and must land in the same class"
    );
}

// ---------------------------------------------------------------------
// Chordalization and triangle enumeration
// ---------------------------------------------------------------------

/// Build an adjacency structure from an undirected edge list.
fn adjacency_of(vertex_count: usize, edges: &[(usize, usize)]) -> Vec<FxHashSet<usize>> {
    let mut adjacency: Vec<FxHashSet<usize>> = vec![FxHashSet::default(); vertex_count];
    for &(a, b) in edges {
        adjacency[a].insert(b);
        adjacency[b].insert(a);
    }
    adjacency
}

/// The elimination order must be a genuine *perfect* elimination ordering of
/// the completed graph: for every vertex, the neighbours that outlive it form
/// a clique. Everything downstream (the triangle enumeration in particular)
/// reads triangles straight off that property instead of searching for them,
/// so it has to actually hold.
#[test]
fn test_pr33_chordal_completion_yields_a_perfect_elimination_ordering() {
    // A 5-cycle: not chordal, and its completion needs two chords.
    let mut adjacency = adjacency_of(5, &[(0, 1), (1, 2), (2, 3), (3, 4), (4, 0)]);
    let order = chordal_completion(&mut adjacency);
    assert_eq!(
        order.len(),
        5,
        "every vertex must be eliminated exactly once"
    );

    let mut position = [usize::MAX; 5];
    for (slot, &vertex) in order.iter().enumerate() {
        position[vertex] = slot;
    }
    for &vertex in &order {
        let later: Vec<usize> = adjacency[vertex]
            .iter()
            .copied()
            .filter(|&other| position[other] > position[vertex])
            .collect();
        for (offset, &left) in later.iter().enumerate() {
            for &right in &later[offset + 1..] {
                assert!(
                    adjacency[left].contains(&right),
                    "vertex {vertex}'s later neighbourhood must be a clique, \
                     but {left} and {right} are not adjacent"
                );
            }
        }
    }
}

/// A graph that is already a triangle needs no fill edges, and yields exactly
/// that one triangle -- once, not once per vertex.
#[test]
fn test_pr33_triangle_enumeration_reports_each_triangle_once() {
    let mut adjacency = adjacency_of(3, &[(0, 1), (1, 2), (0, 2)]);
    let order = chordal_completion(&mut adjacency);
    let triangles = triangles_from_elimination_order(&adjacency, &order);
    assert_eq!(triangles.len(), 1);
    let mut vertices = triangles[0];
    vertices.sort_unstable();
    assert_eq!(vertices, [0, 1, 2]);
}

/// A tree has no cycle at all, so its completion adds nothing and there is no
/// transitivity clause to emit.
#[test]
fn test_pr33_acyclic_graph_yields_no_triangles() {
    let mut adjacency = adjacency_of(4, &[(0, 1), (1, 2), (1, 3)]);
    let order = chordal_completion(&mut adjacency);
    assert!(triangles_from_elimination_order(&adjacency, &order).is_empty());
}

/// The clause set the enumeration drives has to cover the 4-cycle case the
/// whole construction exists for: `a=b, b=c, c=d, d=a` with `a != c` forced is
/// only refutable once a chord makes the cycle chordal.
#[test]
fn test_pr33_four_cycle_gains_a_chord_and_two_triangles() {
    let mut adjacency = adjacency_of(4, &[(0, 1), (1, 2), (2, 3), (3, 0)]);
    let before: usize = adjacency.iter().map(FxHashSet::len).sum::<usize>() / 2;
    let order = chordal_completion(&mut adjacency);
    let after: usize = adjacency.iter().map(FxHashSet::len).sum::<usize>() / 2;
    assert_eq!(before, 4);
    assert_eq!(after, 5, "a 4-cycle needs exactly one chord");
    assert_eq!(
        triangles_from_elimination_order(&adjacency, &order).len(),
        2,
        "one chord cuts the square into two triangles"
    );
}

// ---------------------------------------------------------------------
// Repeated solving must not re-assert the same clauses
// ---------------------------------------------------------------------

/// A second `check` on an unchanged goal must add no transitivity clause at
/// all: the ones from the first attempt are still in the database, and
/// re-asserting them would grow it without bound across repeated `check-sat`.
#[test]
fn test_pr33_repeated_fast_path_adds_no_duplicate_clauses() {
    let (mut manager, sort) = manager_with_uninterpreted_sort();
    let mut solver = Solver::new();
    let a = manager.mk_var("a", sort);
    let b = manager.mk_var("b", sort);
    let c = manager.mk_var("c", sort);
    for (x, y) in [(a, b), (b, c), (a, c)] {
        let eq = manager.mk_eq(x, y);
        solver.assert(eq, &mut manager);
    }

    assert_eq!(
        solver.try_pure_equality_fast_path(&mut manager),
        Some(SolverResult::Sat)
    );
    let after_first = solver.sat.num_original_clauses();
    assert!(
        !solver.eq_transitivity_triangles.is_empty(),
        "the triangle must have been recorded"
    );

    assert_eq!(
        solver.try_pure_equality_fast_path(&mut manager),
        Some(SolverResult::Sat)
    );
    assert_eq!(
        solver.sat.num_original_clauses(),
        after_first,
        "a repeated fast path on an unchanged goal must assert nothing new"
    );
}

/// The `Sat` path must record the partition rather than a value: an
/// uninterpreted sort has no literals, so anything concrete written into the
/// model here would print at the wrong sort.
#[test]
fn test_pr33_sat_records_classes_not_model_values() {
    let (mut manager, sort) = manager_with_uninterpreted_sort();
    let mut solver = Solver::new();
    let a = manager.mk_var("a", sort);
    let b = manager.mk_var("b", sort);
    let c = manager.mk_var("c", sort);
    let ab = manager.mk_eq(a, b);
    let ac = manager.mk_eq(a, c);
    solver.assert(ab, &mut manager);
    let not_ac = manager.mk_not(ac);
    solver.assert(not_ac, &mut manager);

    assert_eq!(
        solver.try_pure_equality_fast_path(&mut manager),
        Some(SolverResult::Sat)
    );
    for constant in [a, b, c] {
        assert!(
            solver
                .model
                .as_ref()
                .and_then(|m| m.get(constant))
                .is_none(),
            "an uninterpreted-sort constant must get no concrete model value here"
        );
    }
    let class_of = |t| {
        solver
            .euf_class_representative(t)
            .expect("the fast path must publish a class for every vertex")
    };
    assert_eq!(class_of(a), class_of(b), "a = b is asserted");
    assert_ne!(class_of(a), class_of(c), "a != c is asserted");
}

// ---------------------------------------------------------------------
// Size guards
// ---------------------------------------------------------------------

/// A graph past [`MAX_EQUALITY_VERTICES`] must be declined, and declined
/// *cleanly*: nothing asserted, nothing recorded, so the caller's fall-through
/// to the ordinary search starts from exactly the state it would have had if
/// this module had never looked.
#[test]
fn test_pr33_oversized_graph_is_declined_without_side_effects() {
    let (mut manager, sort) = manager_with_uninterpreted_sort();
    let mut solver = Solver::new();

    // A chain of equalities over one more constant than the cap allows.
    let constants: Vec<TermId> = (0..=MAX_EQUALITY_VERTICES + 1)
        .map(|i| manager.mk_var(&format!("v{i}"), sort))
        .collect();
    for pair in constants.windows(2) {
        let eq = manager.mk_eq(pair[0], pair[1]);
        solver.assert(eq, &mut manager);
    }

    let clauses_before = solver.sat.num_original_clauses();
    assert!(
        solver.collect_equality_skeleton(&manager).is_none(),
        "a graph past the vertex cap must be declined"
    );
    assert!(solver.try_pure_equality_fast_path(&mut manager).is_none());
    assert_eq!(
        solver.sat.num_original_clauses(),
        clauses_before,
        "declining must not leave a transitivity clause behind"
    );
    assert!(
        solver.eq_transitivity_triangles.is_empty(),
        "declining must not record a triangle either"
    );
}
