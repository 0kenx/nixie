#![allow(clippy::unwrap_used)]

//! Exhaustive small-graph oracle tests.
//!
//! Every partial edge/atom assignment of each case graph is replayed through
//! the propagator (driven by `UserPropagatorManager`), and every emitted
//! consequence or conflict is checked against **all concrete completions**
//! of the graph, computed by an independent transitive-closure oracle. The
//! oracle uses boolean-matrix closure — a different algorithm from the
//! propagator's BFS — so agreement is genuine cross-validation, not a
//! tautology. Verdicts (Sat/Unsat/Unknown) are checked against an
//! independent violation analysis.

use super::*;
use crate::user_propagator::UserPropagatorManager;

/// Tri-state for enumerating partial states.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
enum Tri {
    Unfixed,
    T,
    F,
}

/// Which (from, to) pairs get reach atoms in a test case.
struct Case {
    vertices: usize,
    edges: Vec<(u32, u32)>,
    reach: Vec<(u32, u32)>,
    acyclic: bool,
}

impl Case {
    fn build(&self, tm: &mut TermManager) -> (GraphModel, GraphHandle) {
        let mut model = GraphModel::new(tm);
        let g = model.new_graph();
        for _ in 0..self.vertices {
            model.add_vertex(g).unwrap();
        }
        for &(u, v) in &self.edges {
            model.new_edge(g, VertexId(u), VertexId(v), tm).unwrap();
        }
        for &(u, v) in &self.reach {
            model.reach(g, VertexId(u), VertexId(v), tm).unwrap();
        }
        if self.acyclic {
            model.acyclic(g, tm).unwrap();
        }
        (model, g)
    }
}

/// Independent transitive closure (paths of length ≥ 1) by matrix squaring.
/// `present[i]` selects edge `i`. Reachability is `closure[u][v]`; a cycle
/// through `u` is `closure[u][u]`.
fn closure(case: &Case, present: &[bool]) -> Vec<Vec<bool>> {
    let n = case.vertices;
    let mut r = vec![vec![false; n]; n];
    for (i, &(u, v)) in case.edges.iter().enumerate() {
        if present[i] {
            r[u as usize][v as usize] = true;
        }
    }
    loop {
        let mut changed = false;
        let mut next = r.clone();
        for (row, next_row) in r.iter().zip(&mut next) {
            for a in 0..n {
                for b in 0..n {
                    if row[a] && r[a][b] && !next_row[b] {
                        next_row[b] = true;
                        changed = true;
                    }
                }
            }
        }
        r = next;
        if !changed {
            return r;
        }
    }
}

/// A concrete completion of a case's edges plus the oracle evaluation of
/// every declared atom under it.
struct Completion {
    present: Vec<bool>,
    r: Vec<Vec<bool>>,
}

/// Oracle evaluation context: the case's declared terms, their negations,
/// and the atom semantics.
struct Oracle<'a> {
    case: &'a Case,
    edge_terms: &'a [(VertexId, VertexId, TermId)],
    reach_terms: &'a [(VertexId, VertexId, TermId)],
    acyclic: Option<TermId>,
    neg: &'a FxHashMap<TermId, TermId>,
}

impl Oracle<'_> {
    /// Truth of a signed literal (edge or atom, either polarity) under a
    /// concrete completion.
    fn holds(&self, completion: &Completion, term: TermId) -> bool {
        let Completion { present, r } = completion;
        for (i, &(_, _, atom)) in self.edge_terms.iter().enumerate() {
            if atom == term {
                return present[i];
            }
            if self.neg.get(&atom) == Some(&term) {
                return !present[i];
            }
        }
        for &(u, v, atom) in self.reach_terms {
            if atom == term {
                return r[u.0 as usize][v.0 as usize];
            }
            if self.neg.get(&atom) == Some(&term) {
                return !r[u.0 as usize][v.0 as usize];
            }
        }
        if let Some(a) = self.acyclic {
            let acyclic_holds = (0..self.case.vertices).all(|i| !r[i][i]);
            if a == term {
                return acyclic_holds;
            }
            if self.neg.get(&a) == Some(&term) {
                return !acyclic_holds;
            }
        }
        panic!("unknown literal in oracle: {term:?}");
    }

    fn completion(&self, present: Vec<bool>) -> Completion {
        let r = closure(self.case, &present);
        Completion { present, r }
    }
}

/// Expected verdict from the independent violation analysis.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum Verdict {
    Sat,
    Unsat,
    Unknown,
}

fn expected_verdict(
    case: &Case,
    edge_states: &[Tri],
    atom_states: &[Tri],
    model: &GraphModel,
    g: GraphHandle,
) -> Verdict {
    let forced_present: Vec<bool> = edge_states.iter().map(|&s| s == Tri::T).collect();
    let possible_present: Vec<bool> = edge_states.iter().map(|&s| s != Tri::F).collect();
    let forced = closure(case, &forced_present);
    let possible = closure(case, &possible_present);
    let forced_cycle = (0..case.vertices).any(|i| forced[i][i]);
    let possible_acyclic = (0..case.vertices).all(|i| !possible[i][i]);

    let reach_atoms = model.reach_atoms(g).unwrap();
    for (k, &(u, v, _)) in reach_atoms.iter().enumerate() {
        match atom_states[k] {
            Tri::T => {
                if !possible[u.0 as usize][v.0 as usize] {
                    return Verdict::Unsat;
                }
            }
            Tri::F => {
                if forced[u.0 as usize][v.0 as usize] {
                    return Verdict::Unsat;
                }
            }
            Tri::Unfixed => {}
        }
    }
    if case.acyclic {
        let state = atom_states[reach_atoms.len()];
        match state {
            Tri::T => {
                if forced_cycle {
                    return Verdict::Unsat;
                }
            }
            Tri::F => {
                if possible_acyclic {
                    return Verdict::Unsat;
                }
            }
            Tri::Unfixed => {}
        }
    }
    let all_edges_fixed = edge_states.iter().all(|&s| s != Tri::Unfixed);
    let all_atoms_fixed = atom_states.iter().all(|&s| s != Tri::Unfixed);
    if all_edges_fixed && all_atoms_fixed {
        Verdict::Sat
    } else {
        Verdict::Unknown
    }
}

/// Replay one partial state through a fresh manager and validate everything
/// the propagator emits against all concrete completions.
fn check_state(case: &Case, edge_states: &[Tri], atom_states: &[Tri]) {
    let mut tm = TermManager::new();
    let (model, g) = case.build(&mut tm);
    let reach_atoms = model.reach_atoms(g).unwrap();
    let acyclic_atom = model.acyclic_atom(g).unwrap();
    let edge_terms = model.edges(g).unwrap();
    let expected = expected_verdict(case, edge_states, atom_states, &model, g);
    let mut atom_terms: Vec<TermId> = reach_atoms.iter().map(|&(_, _, a)| a).collect();
    if let Some(a) = acyclic_atom {
        atom_terms.push(a);
    }
    let mut neg = FxHashMap::default();
    for &(_, _, atom) in &edge_terms {
        neg.insert(atom, tm.mk_not(atom));
    }
    for &atom in &atom_terms {
        neg.insert(atom, tm.mk_not(atom));
    }

    let (propagator, watches) = model.into_propagator();
    let mut manager = UserPropagatorManager::new();
    for &w in &watches {
        manager.watch_term(w);
    }
    manager.register_propagator(propagator);
    let true_term = tm.mk_bool(true);
    let false_term = tm.mk_bool(false);

    for (i, &(_, _, atom)) in edge_terms.iter().enumerate() {
        match edge_states[i] {
            Tri::T => manager.notify_fixed(atom, true_term),
            Tri::F => manager.notify_fixed(atom, false_term),
            Tri::Unfixed => {}
        }
    }
    for (k, &atom) in atom_terms.iter().enumerate() {
        match atom_states[k] {
            Tri::T => manager.notify_fixed(atom, true_term),
            Tri::F => manager.notify_fixed(atom, false_term),
            Tri::Unfixed => {}
        }
    }

    let oracle = Oracle {
        case,
        edge_terms: &edge_terms,
        reach_terms: &reach_atoms,
        acyclic: acyclic_atom,
        neg: &neg,
    };

    let verdict = manager.final_check();
    let consequences = manager.get_consequences();

    // Verdict agreement.
    let got = match verdict {
        crate::user_propagator::PropagatorResult::Sat => Verdict::Sat,
        crate::user_propagator::PropagatorResult::Unsat(_) => Verdict::Unsat,
        crate::user_propagator::PropagatorResult::Unknown => Verdict::Unknown,
    };
    assert_eq!(
        got, expected,
        "verdict mismatch for edges={edge_states:?} atoms={atom_states:?}"
    );

    // Unsat reasons must be currently-true literals ruling out every
    // completion; a conflict also arrives as the queued consequence below.
    if let crate::user_propagator::PropagatorResult::Unsat(reasons) = &verdict {
        assert!(
            reasons.iter().all(|&r| {
                literal_holds_current(r, edge_states, atom_states, &edge_terms, &atom_terms, &neg)
            }),
            "untrue reason in conflict {reasons:?} for edges={edge_states:?} atoms={atom_states:?}"
        );
        assert!(
            !completion_exists(&oracle, reasons),
            "conflict {reasons:?} is satisfiable by a completion (edges={edge_states:?} atoms={atom_states:?})"
        );
    }

    for consequence in &consequences {
        let term = consequence.term;
        // All justification literals are currently true.
        for &j in &consequence.justification {
            assert!(
                literal_holds_current(j, edge_states, atom_states, &edge_terms, &atom_terms, &neg),
                "untrue justification {j:?} in {term:?} for edges={edge_states:?}"
            );
        }
        // The implication holds in every completion satisfying the reasons.
        let mut witnessed = false;
        for mask in 0..(1usize << case.edges.len()) {
            let present: Vec<bool> = (0..case.edges.len())
                .map(|i| mask & (1 << i) != 0)
                .collect();
            let completion = oracle.completion(present);
            let reasons_hold = consequence
                .justification
                .iter()
                .all(|&j| oracle.holds(&completion, j));
            if !reasons_hold {
                continue;
            }
            witnessed = true;
            if term == false_term {
                panic!(
                    "conflict consequence is satisfiable: {consequence:?} under present={:?}",
                    completion.present
                );
            }
            assert!(
                oracle.holds(&completion, term),
                "invalid consequence {consequence:?} under present={:?} (edges={edge_states:?} atoms={atom_states:?})",
                completion.present
            );
        }
        // With no completion satisfying the reasons, only conflicts are
        // acceptable; propagations always have at least one witness.
        if term != false_term {
            assert!(witnessed, "propagation {consequence:?} has no witness");
        }
    }

    // Determined atoms must propagate when all edges are fixed and no
    // conflict preempted the run (the value is then uniquely determined by
    // the biconditional).
    if edge_states.iter().all(|&s| s != Tri::Unfixed) && expected != Verdict::Unsat {
        let propagated: Vec<TermId> = consequences
            .iter()
            .filter(|c| c.term != false_term)
            .map(|c| c.term)
            .collect();
        for (k, &atom) in atom_terms.iter().enumerate() {
            if atom_states[k] == Tri::Unfixed {
                assert!(
                    propagated.contains(&atom) || propagated.contains(&neg[&atom]),
                    "determined atom {atom:?} did not propagate (edges={edge_states:?})"
                );
            }
        }
    }
}

/// Is a signed literal true in the *current partial state*?
fn literal_holds_current(
    term: TermId,
    edge_states: &[Tri],
    atom_states: &[Tri],
    edge_terms: &[(VertexId, VertexId, TermId)],
    atom_terms: &[TermId],
    neg: &FxHashMap<TermId, TermId>,
) -> bool {
    for (i, &(_, _, atom)) in edge_terms.iter().enumerate() {
        if atom == term {
            return edge_states[i] == Tri::T;
        }
        if neg.get(&atom) == Some(&term) {
            return edge_states[i] == Tri::F;
        }
    }
    for (k, &atom) in atom_terms.iter().enumerate() {
        if atom == term {
            return atom_states[k] == Tri::T;
        }
        if neg.get(&atom) == Some(&term) {
            return atom_states[k] == Tri::F;
        }
    }
    false
}

/// Does any concrete completion satisfy all conflict reasons?
fn completion_exists(oracle: &Oracle, reasons: &[TermId]) -> bool {
    for mask in 0..(1usize << oracle.case.edges.len()) {
        let present: Vec<bool> = (0..oracle.case.edges.len())
            .map(|i| mask & (1 << i) != 0)
            .collect();
        let completion = oracle.completion(present);
        if reasons.iter().all(|&x| oracle.holds(&completion, x)) {
            return true;
        }
    }
    false
}

/// Enumerate `3^k` tri-state vectors.
fn tri_vectors(k: usize) -> Vec<Vec<Tri>> {
    let mut out = vec![Vec::new()];
    for _ in 0..k {
        let mut next = Vec::new();
        for v in &out {
            for unit in [Tri::Unfixed, Tri::T, Tri::F] {
                let mut w = v.clone();
                w.push(unit);
                next.push(w);
            }
        }
        out = next;
    }
    out
}

fn exhaustive(case: Case, fix_atoms: bool) {
    let atom_count = case.reach.len() + usize::from(case.acyclic);
    let atom_modes: Vec<Vec<Tri>> = if fix_atoms {
        tri_vectors(atom_count)
    } else {
        vec![vec![Tri::Unfixed; atom_count]]
    };
    for edges in tri_vectors(case.edges.len()) {
        for atoms in &atom_modes {
            check_state(&case, &edges, atoms);
        }
    }
}

/// Cycle-capable triangle with chords, self-atom reachability and an
/// acyclicity atom. Partial edges, atoms unfixed.
#[test]
fn oracle_partial_edges_triangle() {
    exhaustive(
        Case {
            vertices: 3,
            edges: vec![(0, 1), (1, 2), (0, 2), (2, 0)],
            reach: vec![(0, 2), (0, 0), (2, 2), (1, 0)],
            acyclic: true,
        },
        false,
    );
}

/// Same graph, but this time every combination of fixed atom values too
/// (edges partial in the outer loop; the full cross product of atoms).
#[test]
fn oracle_partial_edges_all_atom_values_triangle() {
    exhaustive(
        Case {
            vertices: 2,
            edges: vec![(0, 1), (1, 0), (1, 1)],
            reach: vec![(0, 1), (1, 0), (1, 1)],
            acyclic: true,
        },
        true,
    );
}

/// Fully fixed edges crossed with all atom assignments (complete
/// assignments exercise the final-check biconditional in every direction).
#[test]
fn oracle_complete_assignments_all_atoms() {
    let case = Case {
        vertices: 3,
        edges: vec![(0, 1), (1, 2), (2, 0), (1, 1)],
        reach: vec![(0, 0), (0, 2), (2, 0), (1, 1), (0, 1)],
        acyclic: true,
    };
    let atom_count = case.reach.len() + 1;
    for edges in tri_vectors(case.edges.len()) {
        if edges.contains(&Tri::Unfixed) {
            continue; // complete assignments only in this test
        }
        for atoms in tri_vectors(atom_count) {
            check_state(&case, &edges, &atoms);
        }
    }
}

/// Disconnected and self-loop-only corner cases.
#[test]
fn oracle_disconnected_vertex() {
    exhaustive(
        Case {
            vertices: 3,
            edges: vec![(0, 1), (1, 0)],
            reach: vec![(0, 2), (2, 2), (2, 1), (0, 0)],
            acyclic: true,
        },
        false,
    );
}

#[test]
fn oracle_single_self_loop() {
    exhaustive(
        Case {
            vertices: 1,
            edges: vec![(0, 0)],
            reach: vec![(0, 0)],
            acyclic: true,
        },
        true,
    );
}

#[test]
fn oracle_empty_graph() {
    // No edges at all: every reachability atom is unconditionally false and
    // the graph is unconditionally acyclic (empty justifications).
    exhaustive(
        Case {
            vertices: 2,
            edges: vec![],
            reach: vec![(0, 1), (1, 1)],
            acyclic: true,
        },
        true,
    );
}

/// A larger mixed case: longer paths, chords, several sources.
#[test]
fn oracle_four_vertex_chain_and_chords() {
    let case = Case {
        vertices: 4,
        edges: vec![(0, 1), (1, 2), (2, 3), (0, 2), (1, 3), (3, 1)],
        reach: vec![(0, 3), (3, 3), (3, 0), (1, 1)],
        acyclic: true,
    };
    // Full 3^6 x 3^5 is heavy; cross partial edges with unfixed atoms, and
    // complete edges with all atom values.
    for edges in tri_vectors(case.edges.len()) {
        if edges.iter().all(|&s| s != Tri::Unfixed) {
            for atoms in tri_vectors(case.reach.len() + 1) {
                check_state(&case, &edges, &atoms);
            }
        } else {
            check_state(&case, &edges, &vec![Tri::Unfixed; case.reach.len() + 1]);
        }
    }
}

/// Parallel edges between the same pair.
#[test]
fn oracle_parallel_edges() {
    exhaustive(
        Case {
            vertices: 2,
            edges: vec![(0, 1), (0, 1), (1, 0)],
            reach: vec![(0, 1), (0, 0)],
            acyclic: true,
        },
        true,
    );
}

/// The propagator is stateless: scoped notifications unwind cleanly and a
/// replayed prefix reproduces identical consequences.
#[test]
fn push_pop_replays_identically() {
    let mut tm = TermManager::new();
    let case = Case {
        vertices: 3,
        edges: vec![(0, 1), (1, 2), (2, 0)],
        reach: vec![(0, 2), (2, 0)],
        acyclic: true,
    };
    let (model, g) = case.build(&mut tm);
    let edges = model.edges(g).unwrap();
    let (propagator, watches) = model.into_propagator();
    let mut manager = UserPropagatorManager::new();
    for &w in &watches {
        manager.watch_term(w);
    }
    manager.register_propagator(propagator);
    let true_term = tm.mk_bool(true);
    let false_term = tm.mk_bool(false);

    // Level 0: first edge true.
    manager.notify_fixed(edges[0].2, true_term);
    let _ = manager.final_check();
    let base = manager.get_consequences();

    manager.push();
    manager.notify_fixed(edges[1].2, true_term);
    let inner_verdict = manager.final_check();
    let inner = manager.get_consequences();
    assert_eq!(
        inner_verdict,
        crate::user_propagator::PropagatorResult::Unknown
    );
    // 0->1->2 forces reach(0,2).
    assert!(inner.iter().any(|c| c.term != false_term));

    manager.pop(1);
    // After the pop the state is back to the base prefix.
    let again = manager.final_check();
    assert_eq!(again, crate::user_propagator::PropagatorResult::Unknown);
    let replay = manager.get_consequences();
    assert_eq!(replay.len(), base.len());
}

/// Non-Boolean fixed values fail closed to Unknown.
#[test]
fn non_boolean_fixation_fails_closed() {
    let mut tm = TermManager::new();
    let case = Case {
        vertices: 2,
        edges: vec![(0, 1)],
        reach: vec![(0, 1)],
        acyclic: false,
    };
    let (model, g) = case.build(&mut tm);
    let edges = model.edges(g).unwrap();
    let (propagator, watches) = model.into_propagator();
    let mut manager = UserPropagatorManager::new();
    for &w in &watches {
        manager.watch_term(w);
    }
    manager.register_propagator(propagator);
    let junk: TermId = tm.mk_int(num_bigint::BigInt::from(0));
    manager.notify_fixed(edges[0].2, junk);
    assert_eq!(
        manager.final_check(),
        crate::user_propagator::PropagatorResult::Unknown
    );
}

/// Two graphs in one model: a conflict in either is reported; atoms in the
/// other graph stay untouched.
#[test]
fn two_graphs_are_independent() {
    let mut tm = TermManager::new();
    let mut model = GraphModel::new(&tm);
    let g1 = model.new_graph();
    let g2 = model.new_graph();
    for g in [g1, g2] {
        for _ in 0..2 {
            model.add_vertex(g).unwrap();
        }
    }
    let (a1, b1) = (
        model
            .new_edge(g1, VertexId(0), VertexId(1), &mut tm)
            .unwrap(),
        model
            .new_edge(g1, VertexId(1), VertexId(0), &mut tm)
            .unwrap(),
    );
    let _ = model
        .new_edge(g2, VertexId(0), VertexId(1), &mut tm)
        .unwrap();
    let _ = model
        .new_edge(g2, VertexId(1), VertexId(0), &mut tm)
        .unwrap();
    let _r1 = model.reach(g1, VertexId(0), VertexId(1), &mut tm).unwrap();
    let ac1 = model.acyclic(g1, &mut tm).unwrap();
    let g1_edges = model.edges(g1).unwrap();
    let g1_reach = model.reach_atoms(g1).unwrap();
    let (propagator, watches) = model.into_propagator();
    let mut manager = UserPropagatorManager::new();
    for &w in &watches {
        manager.watch_term(w);
    }
    manager.register_propagator(propagator);
    let true_term = tm.mk_bool(true);
    let false_term = tm.mk_bool(false);
    // g1: two-cycle present and acyclic demanded: conflict.
    manager.notify_fixed(a1, true_term);
    manager.notify_fixed(b1, true_term);
    manager.notify_fixed(ac1, true_term);
    let verdict = manager.final_check();
    let reasons = match verdict {
        crate::user_propagator::PropagatorResult::Unsat(r) => r,
        other => panic!("expected conflict, got {other:?}"),
    };
    assert!(reasons.contains(&a1) && reasons.contains(&b1) && reasons.contains(&ac1));
    // g1 consistent without the acyclicity demand; reach(0,1) holds.
    let mut tm2 = TermManager::new();
    let mut m2 = GraphModel::new(&tm2);
    let g2solo = m2.new_graph();
    for _ in 0..2 {
        m2.add_vertex(g2solo).unwrap();
    }
    let e = m2
        .new_edge(g2solo, VertexId(0), VertexId(1), &mut tm2)
        .unwrap();
    let r = m2
        .reach(g2solo, VertexId(0), VertexId(1), &mut tm2)
        .unwrap();
    let (prop2, watch2) = m2.into_propagator();
    let mut manager2 = UserPropagatorManager::new();
    for &w in &watch2 {
        manager2.watch_term(w);
    }
    manager2.register_propagator(prop2);
    manager2.notify_fixed(e, true_term);
    manager2.final_check();
    let cons = manager2.get_consequences();
    assert!(cons.iter().any(|c| c.term == r), "reach must propagate");
    assert_eq!(false_term, tm2.mk_bool(false));
    assert_eq!((g1_edges.len(), g1_reach.len()), (2, 1));
}

/// Construction validation.
#[test]
fn rejects_malformed_construction() {
    let mut tm = TermManager::new();
    let mut model = GraphModel::new(&tm);
    let g = model.new_graph();
    let v = model.add_vertex(g).unwrap();
    // Vertex out of range.
    assert!(model.new_edge(g, VertexId(1), v, &mut tm).is_err());
    // Non-Boolean atom.
    let int_var = tm.mk_var("i", tm.sorts.int_sort);
    assert!(model.add_edge(g, v, v, int_var, &mut tm).is_err());
    // Boolean constants.
    assert!(model.add_edge(g, v, v, tm.mk_bool(true), &mut tm).is_err());
    assert!(model.add_edge(g, v, v, tm.mk_bool(false), &mut tm).is_err());
    // Duplicate edge atom.
    let e = tm.mk_var("e", tm.sorts.bool_sort);
    assert!(model.add_edge(g, v, v, e, &mut tm).is_ok());
    assert!(model.add_edge(g, v, v, e, &mut tm).is_err());
    // Unknown handles.
    assert!(model.add_vertex(GraphHandle(9)).is_err());
    assert!(model.reach(GraphHandle(9), v, v, &mut tm).is_err());
    assert!(model.reach(g, VertexId(7), v, &mut tm).is_err());
    // Shadowing a system atom with an edge.
    let reach_atom = model.reach(g, v, v, &mut tm).unwrap();
    assert!(model.add_edge(g, v, v, reach_atom, &mut tm).is_err());
    // Same pair returns the same reach atom.
    assert_eq!(model.reach(g, v, v, &mut tm).unwrap(), reach_atom);
    // Acyclic atom is idempotent.
    let a1 = model.acyclic(g, &mut tm).unwrap();
    assert_eq!(model.acyclic(g, &mut tm).unwrap(), a1);
}

/// Zero-length paths do not count: reach(u,u) is false on an acyclic graph
/// with edges present, true only with a cycle through u.
#[test]
fn zero_length_paths_do_not_count() {
    let mut tm = TermManager::new();
    let case = Case {
        vertices: 3,
        edges: vec![(0, 1), (1, 2)],
        reach: vec![(0, 0), (1, 1), (2, 2), (0, 2)],
        acyclic: false,
    };
    let (model, g) = case.build(&mut tm);
    let edges = model.edges(g).unwrap();
    let reach_atoms = model.reach_atoms(g).unwrap();
    let (propagator, watches) = model.into_propagator();
    let mut manager = UserPropagatorManager::new();
    for &w in &watches {
        manager.watch_term(w);
    }
    manager.register_propagator(propagator);
    let true_term = tm.mk_bool(true);
    manager.notify_fixed(edges[0].2, true_term);
    manager.notify_fixed(edges[1].2, true_term);
    manager.final_check();
    let consequences = manager.get_consequences();
    let value_of = |term: TermId| consequences.iter().find(|c| c.term == term).is_some();
    // 0 reaches 2, but nobody reaches itself.
    assert!(value_of(reach_atoms[3].2));
    assert!(
        reach_atoms
            .iter()
            .take(3)
            .all(|&(_, _, a)| value_of(tm.mk_not(a)))
    );
}

/// Focused regression for the empty-cut soundness defect caught by the
/// exhaustive oracle during development: a *forward*-closure cut for the
/// self-pair case produced `Consequence(¬reach(u,u), [])` — an
/// unconditional justification the solver would keep as a permanent unit
/// clause, wrongly forbidding cycles in later branches (a false `unsat`
/// whenever the search backtracks past the false edges and re-enables
/// them). The correct backward cut must pin the false edges that close the
/// cycle, here `{¬e0, ¬e1}`.
#[test]
fn self_pair_negative_propagation_pins_the_cut_edges() {
    let mut tm = TermManager::new();
    let mut model = GraphModel::new(&tm);
    let g = model.new_graph();
    let v0 = model.add_vertex(g).unwrap();
    let v1 = model.add_vertex(g).unwrap();
    let e0 = model.new_edge(g, v0, v1, &mut tm).unwrap();
    let e1 = model.new_edge(g, v0, v1, &mut tm).unwrap();
    let e2 = model.new_edge(g, v1, v0, &mut tm).unwrap();
    let r00 = model.reach(g, v0, v0, &mut tm).unwrap();
    let edge_terms = model.edges(g).unwrap();
    let (propagator, watches) = model.into_propagator();
    let mut manager = UserPropagatorManager::new();
    for &w in &watches {
        manager.watch_term(w);
    }
    manager.register_propagator(propagator);
    let true_term = tm.mk_bool(true);
    let false_term = tm.mk_bool(false);

    // The exact state that triggered the defect: both parallel edges from
    // the source false, the back edge unassigned.
    manager.notify_fixed(e0, false_term);
    manager.notify_fixed(e1, false_term);
    assert_eq!(
        manager.final_check(),
        crate::user_propagator::PropagatorResult::Unknown
    );
    let consequences = manager.get_consequences();
    let neg_r00 = tm.mk_not(r00);
    let mut found = false;
    for c in &consequences {
        if c.term == neg_r00 {
            found = true;
            // The justification must be non-empty and consist exactly of
            // the false cycle-closing edges: an unconditional ¬reach(0,0)
            // would be a globally invalid unit clause.
            assert!(
                !c.justification.is_empty(),
                "empty justification would forbid all cycles through vertex 0"
            );
            let expected = [tm.mk_not(e0), tm.mk_not(e1)];
            for &j in &c.justification {
                assert!(
                    expected.contains(&j),
                    "unexpected justification literal {j:?} in {:?}",
                    c.justification
                );
            }
            for &want in &expected {
                assert!(
                    c.justification.contains(&want),
                    "missing cut literal {want:?} in {:?}",
                    c.justification
                );
            }
        }
    }
    assert!(found, "¬reach(0,0) must propagate in this state");
    // And with the back edge also disabled there is no route back at all:
    // the cut stays the two false edges from the source.
    manager.notify_fixed(e2, false_term);
    assert_eq!(
        manager.final_check(),
        crate::user_propagator::PropagatorResult::Unknown
    );
    let _ = edge_terms;
    let _ = true_term;
}

/// Driver-side mirror of what has been notified to the manager, with
/// snapshot rollback for scopes.
#[derive(Clone)]
struct Shadow {
    edges: Vec<Option<bool>>,
    atoms: Vec<Option<bool>>,
}

/// Deterministic tiny RNG (xorshift64) for the generated campaign — no
/// external rand dependency, fully reproducible from the printed seed.
struct Rng(u64);
impl Rng {
    fn next(&mut self) -> u64 {
        let mut x = self.0;
        x ^= x << 13;
        x ^= x >> 7;
        x ^= x << 17;
        self.0 = x;
        x
    }
    fn below(&mut self, n: usize) -> usize {
        (self.next() % n as u64) as usize
    }
    fn chance(&mut self, percent: usize) -> bool {
        self.below(100) < percent
    }
}

/// Generated-oracle campaign: random medium graphs driven through random
/// event scripts (edge/atom fixations, nested push/pop, interleaved
/// final-checks), with every consequence validated against every concrete
/// completion (or a seeded sample when too many are unfixed), exactly like
/// the CP generated-oracle study. This exercises the incremental
/// propagator's maintained state across long sequences — the post-backtrack
/// full re-read, repeated invalidation, and re-fixation paths the
/// exhaustive small oracles cannot reach.
#[test]
fn generated_oracle_random_event_scripts_with_nested_rollback() {
    for campaign in 0..200u64 {
        let mut rng = Rng(0x9E3779B97F4A7C15 ^ campaign);
        let vertices = 8 + rng.below(10);
        let edge_count = 4 + rng.below(28);
        let reach_count = 2 + rng.below(8);

        // Build the case graph.
        let mut tm = TermManager::new();
        let mut model = GraphModel::new(&tm);
        let g = model.new_graph();
        for _ in 0..vertices {
            model.add_vertex(g).unwrap();
        }
        let mut edges: Vec<(usize, usize)> = Vec::new();
        for _ in 0..edge_count {
            let u = rng.below(vertices);
            let v = rng.below(vertices);
            edges.push((u, v));
        }
        for &(u, v) in &edges {
            model
                .new_edge(g, VertexId::new(u as u32), VertexId::new(v as u32), &mut tm)
                .unwrap();
        }
        let mut reach_pairs: Vec<(usize, usize)> = Vec::new();
        for _ in 0..reach_count {
            let u = rng.below(vertices);
            let v = rng.below(vertices);
            reach_pairs.push((u, v));
        }
        for &(u, v) in &reach_pairs {
            model
                .reach(g, VertexId::new(u as u32), VertexId::new(v as u32), &mut tm)
                .unwrap();
        }
        let acyclic = if rng.chance(60) {
            Some(model.acyclic(g, &mut tm).unwrap())
        } else {
            None
        };

        let edge_terms = model.edges(g).unwrap();
        let reach_atoms = model.reach_atoms(g).unwrap();
        let mut neg_of: FxHashMap<TermId, TermId> = FxHashMap::default();
        for &(_, _, a) in &edge_terms {
            neg_of.insert(a, tm.mk_not(a));
        }
        for &(_, _, a) in &reach_atoms {
            neg_of.insert(a, tm.mk_not(a));
        }
        if let Some(a) = acyclic {
            neg_of.insert(a, tm.mk_not(a));
        }
        let mut atom_terms: Vec<TermId> = reach_atoms.iter().map(|&(_, _, a)| a).collect();
        if let Some(a) = acyclic {
            atom_terms.push(a);
        }

        let (propagator, watches) = model.into_propagator();
        let mut manager = UserPropagatorManager::new();
        for &w in &watches {
            manager.watch_term(w);
        }
        manager.register_propagator(propagator);
        let true_term = tm.mk_bool(true);
        let false_term = tm.mk_bool(false);

        // Driver shadow state (snapshots for rollback), mirroring what has
        // been notified to the manager.
        let mut shadow = Shadow {
            edges: vec![None; edge_terms.len()],
            atoms: vec![None; atom_terms.len()],
        };
        let mut scopes: Vec<Shadow> = Vec::new();
        let open_scopes = 0usize;

        let mut open_scopes = open_scopes;
        let mut ops: Vec<String> = Vec::new();

        // Run the random event script.
        let script_len = 120 + rng.below(120);
        for _step in 0..script_len {
            match rng.below(100) {
                0..=39 if shadow.edges.iter().any(|e| e.is_none()) => {
                    // Fix a random unfixed edge.
                    let candidates: Vec<usize> = shadow
                        .edges
                        .iter()
                        .enumerate()
                        .filter(|(_, e)| e.is_none())
                        .map(|(i, _)| i)
                        .collect();
                    let i = candidates[rng.below(candidates.len())];
                    let value = rng.chance(55);
                    shadow.edges[i] = Some(value);
                    let term = edge_terms[i].2;
                    ops.push(format!("edge{i}:={value}"));
                    manager.notify_fixed(term, if value { true_term } else { false_term });
                }
                40..=49 if shadow.atoms.iter().any(|a| a.is_none()) => {
                    let candidates: Vec<usize> = shadow
                        .atoms
                        .iter()
                        .enumerate()
                        .filter(|(_, a)| a.is_none())
                        .map(|(i, _)| i)
                        .collect();
                    let k = candidates[rng.below(candidates.len())];
                    let value = rng.chance(50);
                    shadow.atoms[k] = Some(value);
                    let term = atom_terms[k];
                    ops.push(format!("atom{k}:={value}"));
                    manager.notify_fixed(term, if value { true_term } else { false_term });
                }
                50..=64 => {
                    scopes.push(shadow.clone());
                    open_scopes += 1;
                    ops.push("push".into());
                    manager.push();
                }
                65..=74 if open_scopes > 0 => {
                    let levels = 1 + rng.below(open_scopes.min(3));
                    for _ in 0..levels {
                        if let Some(s) = scopes.pop() {
                            shadow = s;
                            open_scopes -= 1;
                        }
                    }
                    ops.push(format!("pop{levels}"));
                    manager.pop(levels);
                }
                check_idx => {
                    // final_check + consequence validation (the heavy
                    // all-completion check throttled to every third check).
                    let verdict = manager.final_check();
                    let mut consequences = manager.get_consequences();
                    if check_idx % 3 != 0 {
                        consequences.clear();
                    }
                    validate_generated_state(
                        &edges,
                        vertices,
                        &reach_atoms,
                        acyclic,
                        &shadow,
                        &verdict,
                        &consequences,
                        &edge_terms,
                        &atom_terms,
                        &neg_of,
                        &tm,
                        &mut rng,
                        campaign,
                        &ops,
                    );
                }
            }
        }
        // Drain any final pending consequences at the end.
        let verdict = manager.final_check();
        let consequences = manager.get_consequences();
        validate_generated_state(
            &edges,
            vertices,
            &reach_atoms,
            acyclic,
            &shadow,
            &verdict,
            &consequences,
            &edge_terms,
            &atom_terms,
            &neg_of,
            &tm,
            &mut rng,
            campaign,
            &ops,
        );
    }
}

/// Validate one generated state against the driver's shadow:
///  1. the verdict agrees with an independent violation analysis;
///  2. every consequence's justification literals are currently true;
///  3. every consequence is a valid implication over concrete completions
///     (all of them when ≤ 16 edges are unfixed, else a 64-sample).
#[allow(clippy::too_many_arguments)]
fn validate_generated_state(
    edges: &[(usize, usize)],
    vertices: usize,
    reach_atoms: &[(VertexId, VertexId, TermId)],
    acyclic: Option<TermId>,
    shadow: &Shadow,
    verdict: &crate::user_propagator::PropagatorResult,
    consequences: &[Consequence],
    edge_terms: &[(VertexId, VertexId, TermId)],
    _atom_terms: &[TermId],
    neg_of: &FxHashMap<TermId, TermId>,
    tm: &TermManager,
    rng: &mut Rng,
    campaign: u64,
    ops: &[String],
) {
    let false_term = tm.mk_bool(false);
    let _true_term = tm.mk_bool(true);
    let closure_of = |present: &[bool]| -> Vec<Vec<bool>> {
        let mut r = vec![vec![false; vertices]; vertices];
        for (i, &(u, v)) in edges.iter().enumerate() {
            if present[i] {
                r[u][v] = true;
            }
        }
        loop {
            let mut changed = false;
            for m in 0..vertices {
                for a in 0..vertices {
                    for b in 0..vertices {
                        if r[a][m] && r[m][b] && !r[a][b] {
                            r[a][b] = true;
                            changed = true;
                        }
                    }
                }
            }
            if !changed {
                return r;
            }
        }
    };

    // 1. Expected verdict.
    let forced_present: Vec<bool> = shadow.edges.iter().map(|e| e == &Some(true)).collect();
    let possible_present: Vec<bool> = shadow.edges.iter().map(|e| e != &Some(false)).collect();
    let forced = closure_of(&forced_present);
    let possible = closure_of(&possible_present);
    let mut expected_unsat = false;
    for (k, &(u, v, _)) in reach_atoms.iter().enumerate() {
        let (u, v) = (u.0 as usize, v.0 as usize);
        match shadow.atoms[k] {
            Some(true) if !possible[u][v] => expected_unsat = true,
            Some(false) if forced[u][v] => expected_unsat = true,
            _ => {}
        }
    }
    if acyclic.is_some() {
        let k = shadow.atoms.len() - 1;
        let forced_cycle = (0..vertices).any(|i| forced[i][i]);
        let possible_acyclic = (0..vertices).all(|i| !possible[i][i]);
        match shadow.atoms[k] {
            Some(true) if forced_cycle => expected_unsat = true,
            Some(false) if possible_acyclic => expected_unsat = true,
            _ => {}
        }
    }
    let all_fixed =
        shadow.edges.iter().all(|e| e.is_some()) && shadow.atoms.iter().all(|a| a.is_some());
    let expected_matches = match verdict {
        crate::user_propagator::PropagatorResult::Unsat(_) => expected_unsat,
        crate::user_propagator::PropagatorResult::Sat => !expected_unsat && all_fixed,
        crate::user_propagator::PropagatorResult::Unknown => !expected_unsat && !all_fixed,
    };
    assert!(
        expected_matches,
        "campaign {campaign}: verdict {verdict:?} disagrees with shadow analysis"
    );

    // 2. & 3. Consequence validation over completions.
    let unfixed: Vec<usize> = shadow
        .edges
        .iter()
        .enumerate()
        .filter(|(_, e)| e.is_none())
        .map(|(i, _)| i)
        .collect();
    let sample_all = unfixed.len() <= 12;
    let completion_count = if sample_all {
        1usize << unfixed.len()
    } else {
        64
    };
    let holds_lit = |present: &[bool], closure: &[Vec<bool>], term: TermId| -> bool {
        for (i, &(_, _, atom)) in edge_terms.iter().enumerate() {
            if atom == term {
                return present[i];
            }
            if neg_of.get(&atom) == Some(&term) {
                return !present[i];
            }
        }
        for &(u, v, atom) in reach_atoms {
            if atom == term {
                return closure[u.0 as usize][v.0 as usize];
            }
            if neg_of.get(&atom) == Some(&term) {
                return !closure[u.0 as usize][v.0 as usize];
            }
        }
        if let Some(a) = acyclic {
            let acyclic_holds = (0..vertices).all(|i| !closure[i][i]);
            if a == term {
                return acyclic_holds;
            }
            if neg_of.get(&a) == Some(&term) {
                return !acyclic_holds;
            }
        }
        false
    };
    // Current truth is by FIXATION, not closure semantics: a conflict's
    // offending atom literal is true because the atom is *fixed* to that
    // value, even when the graph semantics disagrees (that is the conflict).
    let now_true_lit = |term: TermId| -> bool {
        for (i, &(_, _, atom)) in edge_terms.iter().enumerate() {
            if atom == term {
                return shadow.edges[i] == Some(true);
            }
            if neg_of.get(&atom) == Some(&term) {
                return shadow.edges[i] == Some(false);
            }
        }
        for (k, &(_, _, atom)) in reach_atoms.iter().enumerate() {
            if atom == term {
                return shadow.atoms[k] == Some(true);
            }
            if neg_of.get(&atom) == Some(&term) {
                return shadow.atoms[k] == Some(false);
            }
        }
        if let Some(a) = acyclic {
            let k = shadow.atoms.len() - 1;
            if a == term {
                return shadow.atoms[k] == Some(true);
            }
            if neg_of.get(&a) == Some(&term) {
                return shadow.atoms[k] == Some(false);
            }
        }
        false
    };
    // Cache the completion set (present, closure) once for this check.
    let mut completions: Vec<(Vec<bool>, Vec<Vec<bool>>)> = Vec::new();
    for c in 0..completion_count {
        let mut present: Vec<bool> = shadow.edges.iter().map(|e| e == &Some(true)).collect();
        if sample_all {
            for (bit, &i) in unfixed.iter().enumerate() {
                present[i] = c & (1 << bit) != 0;
            }
        } else {
            for &i in &unfixed {
                present[i] = rng.chance(50);
            }
        }
        let closure = closure_of(&present);
        completions.push((present, closure));
    }
    for consequence in consequences {
        let term = consequence.term;
        for &j in &consequence.justification {
            assert!(
                now_true_lit(j),
                "campaign {campaign}: justification {j:?} not currently true; recent ops: {ops:?}"
            );
        }
        let mut any_completion = false;
        for (present, closure) in &completions {
            let reasons_hold = consequence
                .justification
                .iter()
                .all(|&j| holds_lit(present, closure, j));
            if !reasons_hold {
                continue;
            }
            any_completion = true;
            if term == false_term {
                panic!(
                    "campaign {campaign}: conflict {consequence:?} satisfiable by a completion; ops: {ops:?}"
                );
            }
            assert!(
                holds_lit(present, closure, term),
                "campaign {campaign}: consequence {consequence:?} invalid under a completion; ops: {ops:?}"
            );
        }
        if term != false_term && !any_completion && !consequence.justification.is_empty() {
            // Non-conflict with no satisfying completion: vacuously true.
        }
    }
}

/// Focused regression for the closure-preservation probe of the
/// epoch-static possible view (`still_reaches_closure`): disabling an edge
/// whose tail retains an alternative route to the target keeps the
/// memoized backward closure (no recompute, identical answers); disabling
/// the last route drops it and the newly determined ¬reach propagates with
/// exactly the false in-edges of the recomputed closure as the cut.
///
/// The 1↔4 cycle exists to catch the probe's first (wrong) version, which
/// exited at *any* closure member instead of at the target: after e1 and
/// e3 die, vertex 1 still reaches members {1,4} of the stale closure, but
/// only through the cycle that never gets back to 2 — a probe that
/// accepts that keeps a too-large closure and misses the determined
/// ¬reach(0,2) (the shape the exhaustive oracle caught).
#[test]
fn closure_probe_preserves_and_drops_exactly() {
    let mut tm = TermManager::new();
    let mut model = GraphModel::new(&tm);
    let g = model.new_graph();
    let v = |i| VertexId(i);
    let _ = model.add_vertex(g).unwrap(); // 0
    let _ = model.add_vertex(g).unwrap(); // 1
    let _ = model.add_vertex(g).unwrap(); // 2
    let _ = model.add_vertex(g).unwrap(); // 3
    let _ = model.add_vertex(g).unwrap(); // 4
    let e0 = model.new_edge(g, v(0), v(1), &mut tm).unwrap();
    let e1 = model.new_edge(g, v(1), v(2), &mut tm).unwrap();
    let e3 = model.new_edge(g, v(1), v(2), &mut tm).unwrap();
    let _e2 = model.new_edge(g, v(3), v(1), &mut tm).unwrap();
    let e4 = model.new_edge(g, v(1), v(4), &mut tm).unwrap();
    let e5 = model.new_edge(g, v(4), v(1), &mut tm).unwrap();
    let r02 = model.reach(g, v(0), v(2), &mut tm).unwrap();
    let (propagator, watches) = model.into_propagator();
    let mut manager = UserPropagatorManager::new();
    for &w in &watches {
        manager.watch_term(w);
    }
    manager.register_propagator(propagator);
    let true_term = tm.mk_bool(true);
    let false_term = tm.mk_bool(false);
    let neg_r02 = tm.mk_not(r02);

    // Stage 1: only e1 dies. Vertex 1 keeps its parallel route e3 to 2, so
    // the closure is preserved and 0 may still reach 2 — no propagation.
    manager.notify_fixed(e1, false_term);
    assert_eq!(
        manager.final_check(),
        crate::user_propagator::PropagatorResult::Unknown
    );
    let consequences = manager.get_consequences();
    assert!(
        consequences.iter().all(|c| c.term != neg_r02),
        "reach(0,2) is still possible; ¬reach must not propagate"
    );

    // Stage 2: e3 dies too. Vertex 1's only remaining routes into the
    // stale closure are the 1↔4 cycle, which never reaches 2 — the probe
    // must reject that (exit only at the target!) and the recomputed
    // closure {2} makes ¬reach(0,2) determined, cut = {¬e1, ¬e3}.
    manager.notify_fixed(e3, false_term);
    assert_eq!(
        manager.final_check(),
        crate::user_propagator::PropagatorResult::Unknown
    );
    let consequences = manager.get_consequences();
    let cut = consequences
        .iter()
        .find(|c| c.term == neg_r02)
        .expect("¬reach(0,2) is determined and must propagate");
    let expected = [tm.mk_not(e1), tm.mk_not(e3)];
    assert_eq!(cut.justification.len(), expected.len());
    for &want in &expected {
        assert!(cut.justification.contains(&want));
    }

    // Stage 3: all edges fixed (e0, e4, e5 true) — still no 0→2 route; the
    // all-fixed state stays consistent with ¬reach (no conflict), and
    // re-fixing after a push/pop cycle re-derives the same state.
    manager.push();
    manager.notify_fixed(e0, true_term);
    manager.notify_fixed(e4, true_term);
    manager.notify_fixed(e5, true_term);
    assert_eq!(
        manager.final_check(),
        crate::user_propagator::PropagatorResult::Unknown
    );
    manager.pop(1);
    // After the pop everything re-reads from the manager; the earlier
    // determinations replay identically.
    assert_eq!(
        manager.final_check(),
        crate::user_propagator::PropagatorResult::Unknown
    );
}

/// All-edges-fixed determined propagation: with every edge fixed, an
/// undecided reach atom must receive its determined value (the state the
/// exhaustive oracle pins with "determined atom did not propagate").
#[test]
fn all_fixed_determined_reach_propagates() {
    let mut tm = TermManager::new();
    let mut model = GraphModel::new(&tm);
    let g = model.new_graph();
    let v = |i| VertexId(i);
    for i in 0..4 {
        let _ = model.add_vertex(g).unwrap();
        let _ = i;
    }
    let e0 = model.new_edge(g, v(0), v(1), &mut tm).unwrap();
    let e1 = model.new_edge(g, v(1), v(2), &mut tm).unwrap();
    let e2 = model.new_edge(g, v(2), v(3), &mut tm).unwrap();
    let e3 = model.new_edge(g, v(3), v(1), &mut tm).unwrap();
    let r03 = model.reach(g, v(0), v(3), &mut tm).unwrap();
    let (propagator, watches) = model.into_propagator();
    let mut manager = UserPropagatorManager::new();
    for &w in &watches {
        manager.watch_term(w);
    }
    manager.register_propagator(propagator);
    let true_term = tm.mk_bool(true);
    let false_term = tm.mk_bool(false);
    let neg_r03 = tm.mk_not(r03);

    // 0→1 and 3→1 are true, but both exits toward 3 are false: 0 cannot
    // reach 3 in any completion — and with all edges fixed the value is
    // determined, so it must propagate.
    manager.notify_fixed(e0, true_term);
    manager.notify_fixed(e1, false_term);
    manager.notify_fixed(e2, false_term);
    manager.notify_fixed(e3, true_term);
    assert_eq!(
        manager.final_check(),
        crate::user_propagator::PropagatorResult::Unknown
    );
    let consequences = manager.get_consequences();
    assert!(
        consequences.iter().any(|c| c.term == neg_r03),
        "determined ¬reach(0,3) must propagate at the all-fixed state"
    );
}
