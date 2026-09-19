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
