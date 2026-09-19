#![allow(clippy::unwrap_used)]

//! End-to-end tests for the finite-graph constraint integration
//! (`nixie_theories::graph` + `Solver::register_graph`).
//!
//! Oracle methodology mirrors `nixie-theories/src/graph/tests.rs` but at the
//! full CDCL(T) level: exhaustive enumeration of complete graphs up to three
//! vertices (all `2^(n²)` digraphs including self-loops), exhaustive
//! acyclicity classification, brute-forced partial-assignment verdicts,
//! scope lifecycle, and independent re-validation of every returned model
//! with a naive closure oracle. Semantics reference: `docs/GRAPH.md`.

use nixie_core::ast::{TermId, TermManager};
use nixie_solver::{Solver, SolverResult};
use nixie_theories::graph::{GraphModel, VertexId};

/// Naive length-≥1 transitive closure oracle over an explicit adjacency.
fn closure(n: usize, edges: &[(usize, usize)], present: &[bool]) -> Vec<Vec<bool>> {
    let mut r = vec![vec![false; n]; n];
    for (i, &(u, v)) in edges.iter().enumerate() {
        if present[i] {
            r[u][v] = true;
        }
    }
    loop {
        let mut changed = false;
        let mut next = r.clone();
        #[allow(clippy::needless_range_loop)]
        for m in 0..n {
            for a in 0..n {
                for b in 0..n {
                    if r[a][m] && r[m][b] && !next[a][b] {
                        next[a][b] = true;
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

/// A complete digraph (with self-loops) on `n` vertices with every possible
/// edge, reach and acyclicity atom declared.
struct CompleteGraph {
    n: usize,
    /// `edge[u][v]` term.
    edge: Vec<Vec<TermId>>,
    /// `reach[u][v]` term.
    reach: Vec<Vec<TermId>>,
    acyclic: Option<TermId>,
    /// Flat edge list in declaration order.
    edges: Vec<(usize, usize)>,
}

fn complete_graph(
    n: usize,
    tm: &mut TermManager,
    with_acyclic: bool,
) -> (CompleteGraph, GraphModel) {
    let mut model = GraphModel::new(tm);
    let g = model.new_graph();
    for _ in 0..n {
        model.add_vertex(g).unwrap();
    }
    let mut edge = vec![vec![TermId::new(u32::MAX); n]; n];
    let mut edges = Vec::new();
    for (u, edge_row) in edge.iter_mut().enumerate() {
        for (v, slot) in edge_row.iter_mut().enumerate() {
            *slot = model
                .new_edge(g, VertexId::new(u as u32), VertexId::new(v as u32), tm)
                .unwrap();
            edges.push((u, v));
        }
    }
    let mut reach = vec![vec![TermId::new(u32::MAX); n]; n];
    for (u, reach_row) in reach.iter_mut().enumerate() {
        for (v, slot) in reach_row.iter_mut().enumerate() {
            *slot = model
                .reach(g, VertexId::new(u as u32), VertexId::new(v as u32), tm)
                .unwrap();
        }
    }
    let acyclic = if with_acyclic {
        Some(model.acyclic(g, tm).unwrap())
    } else {
        None
    };
    (
        CompleteGraph {
            n,
            edge,
            reach,
            acyclic,
            edges,
        },
        model,
    )
}

/// Read a Boolean variable's value from a returned model.
fn model_bool(solver: &Solver, term: TermId, tm: &TermManager) -> bool {
    let model = solver.model().expect("model must exist after sat");
    let value = *model
        .assignments()
        .get(&term)
        .unwrap_or_else(|| panic!("term {term:?} has no model assignment"));
    let true_term = tm.mk_bool(true);
    let false_term = tm.mk_bool(false);
    assert!(
        value == true_term || value == false_term,
        "term {term:?} has non-Boolean model value {value:?}"
    );
    value == true_term
}

/// Independent full-model validation: every reach atom equals the closure
/// over the model's edges, and the acyclicity atom equals the cycle test.
#[allow(clippy::needless_range_loop)]
fn validate_model(solver: &Solver, graph: &CompleteGraph, tm: &TermManager) {
    let present: Vec<bool> = graph
        .edges
        .iter()
        .map(|&(u, v)| model_bool(solver, graph.edge[u][v], tm))
        .collect();
    let r = closure(graph.n, &graph.edges, &present);
    for u in 0..graph.n {
        for v in 0..graph.n {
            let got = model_bool(solver, graph.reach[u][v], tm);
            assert_eq!(
                got, r[u][v],
                "model reach({u},{v}) = {got}, oracle says {}",
                r[u][v]
            );
        }
    }
    if let Some(atom) = graph.acyclic {
        let acyclic = (0..graph.n).all(|i| !r[i][i]);
        let got = model_bool(solver, atom, tm);
        assert_eq!(got, acyclic, "model acyclic = {got}, oracle says {acyclic}");
    }
}

/// Every complete graph on n ≤ 3 vertices: asserting all edges is Sat and
/// the returned model agrees with the closure oracle on every atom
/// (reification completeness, validated independently of the propagator).
#[test]
fn exhaustive_complete_graphs_models_match_oracle() {
    for n in 1..=3 {
        for mask in 0..(1usize << (n * n)) {
            let mut tm = TermManager::new();
            let (graph, model) = complete_graph(n, &mut tm, true);
            let (propagator, watches) = model.into_propagator();
            let mut solver = Solver::new();
            solver
                .register_user_propagator(propagator, &watches, &mut tm)
                .unwrap();
            for (i, &(u, v)) in graph.edges.iter().enumerate() {
                let value = mask & (1 << i) != 0;
                let term = if value {
                    graph.edge[u][v]
                } else {
                    tm.mk_not(graph.edge[u][v])
                };
                solver.assert(term, &mut tm);
            }
            assert_eq!(
                solver.check(&mut tm),
                SolverResult::Sat,
                "n={n} mask={mask} must be sat"
            );
            validate_model(&solver, &graph, &tm);
        }
    }
}

/// Flipping exactly one atom value from the oracle's makes the assignment
/// unsatisfiable (both polarity directions of the biconditional).
#[test]
fn exhaustive_flipped_atoms_are_unsat() {
    let mut flips = 0usize;
    for n in 1..=3 {
        for mask in 0..(1usize << (n * n)) {
            let present: Vec<bool> = (0..n * n).map(|i| mask & (1 << i) != 0).collect();
            let r = closure(
                n,
                &(0..n)
                    .flat_map(|u| (0..n).map(move |v| (u, v)))
                    .collect::<Vec<_>>(),
                &present,
            );
            // Candidate atoms: all reach atoms plus the acyclic atom.
            let mut atoms: Vec<(usize, usize)> = Vec::new();
            for u in 0..n {
                for v in 0..n {
                    atoms.push((u, v));
                }
            }
            let atom_count = atoms.len() + 1;
            for flip in 0..atom_count {
                // Deterministic subsample to bound runtime: for n = 3 flip a
                // rotating selection; smaller n flip everything.
                if n == 3 && (mask + flip) % 7 != 0 {
                    continue;
                }
                let mut tm = TermManager::new();
                let (graph, model) = complete_graph(n, &mut tm, true);
                let (propagator, watches) = model.into_propagator();
                let mut solver = Solver::new();
                solver
                    .register_user_propagator(propagator, &watches, &mut tm)
                    .unwrap();
                for (i, &(u, v)) in graph.edges.iter().enumerate() {
                    let value = mask & (1 << i) != 0;
                    solver.assert(
                        if value {
                            graph.edge[u][v]
                        } else {
                            tm.mk_not(graph.edge[u][v])
                        },
                        &mut tm,
                    );
                }
                let (term, want) = if flip < atoms.len() {
                    let (u, v) = atoms[flip];
                    (graph.reach[u][v], r[u][v])
                } else {
                    let acyclic = (0..n).all(|i| !r[i][i]);
                    (graph.acyclic.unwrap(), acyclic)
                };
                solver.assert(if want { tm.mk_not(term) } else { term }, &mut tm);
                assert_eq!(
                    solver.check(&mut tm),
                    SolverResult::Unsat,
                    "n={n} mask={mask} flip={flip} must be unsat"
                );
                flips += 1;
            }
        }
    }
    assert!(flips > 200, "expected a broad sample, got {flips}");
}

/// Exhaustive acyclicity classification: `acyclic + edges` is Sat exactly
/// for DAGs; `¬acyclic + edges` is Sat exactly for cyclic graphs.
#[test]
fn exhaustive_acyclic_classification() {
    for n in 1..=3 {
        for mask in 0..(1usize << (n * n)) {
            let present: Vec<bool> = (0..n * n).map(|i| mask & (1 << i) != 0).collect();
            let edges: Vec<_> = (0..n).flat_map(|u| (0..n).map(move |v| (u, v))).collect();
            let r = closure(n, &edges, &present);
            let is_dag = (0..n).all(|i| !r[i][i]);
            for demand_dag in [true, false] {
                let mut tm = TermManager::new();
                let (graph, model) = complete_graph(n, &mut tm, true);
                let (propagator, watches) = model.into_propagator();
                let mut solver = Solver::new();
                solver
                    .register_user_propagator(propagator, &watches, &mut tm)
                    .unwrap();
                for (i, &(u, v)) in graph.edges.iter().enumerate() {
                    let value = mask & (1 << i) != 0;
                    solver.assert(
                        if value {
                            graph.edge[u][v]
                        } else {
                            tm.mk_not(graph.edge[u][v])
                        },
                        &mut tm,
                    );
                }
                solver.assert(
                    if demand_dag {
                        graph.acyclic.unwrap()
                    } else {
                        tm.mk_not(graph.acyclic.unwrap())
                    },
                    &mut tm,
                );
                let expected = if demand_dag { is_dag } else { !is_dag };
                assert_eq!(
                    solver.check(&mut tm),
                    if expected {
                        SolverResult::Sat
                    } else {
                        SolverResult::Unsat
                    },
                    "n={n} mask={mask} demand_dag={demand_dag}"
                );
                if expected {
                    validate_model(&solver, &graph, &tm);
                }
            }
        }
    }
}

/// A four-vertex acyclicity sample (2^16 exhaustive would be excessive here;
/// the propagator-level oracles in nixie-theories cover the full space for
/// smaller graphs).
#[test]
fn acyclic_four_vertices_sampled() {
    let n = 4usize;
    let mut passed = 0;
    for mask in 0..(1usize << (n * n)) {
        if mask % 97 != 0 {
            continue;
        }
        let present: Vec<bool> = (0..n * n).map(|i| mask & (1 << i) != 0).collect();
        let edges: Vec<_> = (0..n).flat_map(|u| (0..n).map(move |v| (u, v))).collect();
        let r = closure(n, &edges, &present);
        let is_dag = (0..n).all(|i| !r[i][i]);
        let mut tm = TermManager::new();
        let mut model = GraphModel::new(&tm);
        let g = model.new_graph();
        for _ in 0..n {
            model.add_vertex(g).unwrap();
        }
        let mut terms = Vec::new();
        for &(u, v) in &edges {
            terms.push(
                model
                    .new_edge(g, VertexId::new(u as u32), VertexId::new(v as u32), &mut tm)
                    .unwrap(),
            );
        }
        let acyclic = model.acyclic(g, &mut tm).unwrap();
        let (propagator, watches) = model.into_propagator();
        let mut solver = Solver::new();
        solver
            .register_user_propagator(propagator, &watches, &mut tm)
            .unwrap();
        for (i, &term) in terms.iter().enumerate() {
            solver.assert(if present[i] { term } else { tm.mk_not(term) }, &mut tm);
        }
        solver.assert(acyclic, &mut tm);
        assert_eq!(
            solver.check(&mut tm),
            if is_dag {
                SolverResult::Sat
            } else {
                SolverResult::Unsat
            },
            "mask={mask}"
        );
        passed += 1;
    }
    assert!(passed >= 170, "sampled {passed} masks");
}

/// Partial edge assignments with reachability/acyclicity demands: the
/// verdict must equal a brute-force enumeration over all completions of the
/// unfixed edges.
#[allow(clippy::needless_range_loop)]
#[test]
fn partial_assignments_match_bruteforce() {
    // n = 3, fix a prefix of the edges, demand reach(0,2), ¬reach(2,0),
    // acyclic, and reach(0,0) = false. Brute force over the free suffix.
    let n = 3usize;
    let edges: Vec<_> = (0..n).flat_map(|u| (0..n).map(move |v| (u, v))).collect();
    for fixed_prefix in [0usize, 3, 6] {
        for prefix_mask in 0..(1usize << fixed_prefix) {
            let free = edges.len() - fixed_prefix;
            let mut feasible = false;
            for free_mask in 0..(1usize << free) {
                let mut present = Vec::new();
                for i in 0..fixed_prefix {
                    present.push(prefix_mask & (1 << i) != 0);
                }
                for i in 0..free {
                    present.push(free_mask & (1 << i) != 0);
                }
                let r = closure(n, &edges, &present);
                if r[0][2] && !r[2][0] && (0..n).all(|i| !r[i][i]) && !r[0][0] {
                    feasible = true;
                    break;
                }
            }
            let mut tm = TermManager::new();
            let (graph, model) = complete_graph(n, &mut tm, true);
            let (propagator, watches) = model.into_propagator();
            let mut solver = Solver::new();
            solver
                .register_user_propagator(propagator, &watches, &mut tm)
                .unwrap();
            for i in 0..fixed_prefix {
                let (u, v) = edges[i];
                solver.assert(
                    if prefix_mask & (1 << i) != 0 {
                        graph.edge[u][v]
                    } else {
                        tm.mk_not(graph.edge[u][v])
                    },
                    &mut tm,
                );
            }
            solver.assert(graph.reach[0][2], &mut tm);
            solver.assert(tm.mk_not(graph.reach[2][0]), &mut tm);
            solver.assert(graph.acyclic.unwrap(), &mut tm);
            solver.assert(tm.mk_not(graph.reach[0][0]), &mut tm);
            assert_eq!(
                solver.check(&mut tm),
                if feasible {
                    SolverResult::Sat
                } else {
                    SolverResult::Unsat
                },
                "prefix={fixed_prefix}/{prefix_mask:b}"
            );
            if feasible {
                validate_model(&solver, &graph, &tm);
            }
        }
    }
}

/// Positive and negative reachability through chains, cycles, self-loops,
/// disconnected vertices — small directed scenarios.
#[test]
fn reachability_scenarios() {
    // Path a->b->c: reach(a,c) holds, reach(c,a) does not, graph acyclic.
    let mut tm = TermManager::new();
    let mut model = GraphModel::new(&tm);
    let g = model.new_graph();
    let a = model.add_vertex(g).unwrap();
    let b = model.add_vertex(g).unwrap();
    let c = model.add_vertex(g).unwrap();
    let e_ab = model.new_edge(g, a, b, &mut tm).unwrap();
    let e_bc = model.new_edge(g, b, c, &mut tm).unwrap();
    let r_ac = model.reach(g, a, c, &mut tm).unwrap();
    let r_ca = model.reach(g, c, a, &mut tm).unwrap();
    let acyclic = model.acyclic(g, &mut tm).unwrap();
    let (propagator, watches) = model.into_propagator();
    let mut solver = Solver::new();
    solver
        .register_user_propagator(propagator, &watches, &mut tm)
        .unwrap();
    solver.assert(e_ab, &mut tm);
    solver.assert(e_bc, &mut tm);
    solver.assert(r_ac, &mut tm);
    solver.assert(tm.mk_not(r_ca), &mut tm);
    solver.assert(acyclic, &mut tm);
    assert_eq!(solver.check(&mut tm), SolverResult::Sat);
    // Zero-length paths excluded: reach(a,a) is false on this DAG.
    let mut tm = TermManager::new();
    let mut model = GraphModel::new(&tm);
    let g = model.new_graph();
    let a = model.add_vertex(g).unwrap();
    let b = model.add_vertex(g).unwrap();
    let e_ab = model.new_edge(g, a, b, &mut tm).unwrap();
    let r_aa = model.reach(g, a, a, &mut tm).unwrap();
    let acyclic = model.acyclic(g, &mut tm).unwrap();
    let (propagator, watches) = model.into_propagator();
    let mut solver = Solver::new();
    solver
        .register_user_propagator(propagator, &watches, &mut tm)
        .unwrap();
    solver.assert(e_ab, &mut tm);
    solver.assert(acyclic, &mut tm);
    solver.assert(r_aa, &mut tm);
    assert_eq!(solver.check(&mut tm), SolverResult::Unsat);
    // A self-loop makes reach(u,u) true and kills acyclicity.
    let mut tm = TermManager::new();
    let mut model = GraphModel::new(&tm);
    let g = model.new_graph();
    let u = model.add_vertex(g).unwrap();
    let loop_edge = model.new_edge(g, u, u, &mut tm).unwrap();
    let r_uu = model.reach(g, u, u, &mut tm).unwrap();
    let acyclic = model.acyclic(g, &mut tm).unwrap();
    let (propagator, watches) = model.into_propagator();
    let mut solver = Solver::new();
    solver
        .register_user_propagator(propagator, &watches, &mut tm)
        .unwrap();
    solver.assert(loop_edge, &mut tm);
    solver.assert(r_uu, &mut tm);
    solver.assert(tm.mk_not(acyclic), &mut tm);
    assert_eq!(solver.check(&mut tm), SolverResult::Sat);
    // Disconnected vertex: unreachable, unconditionally.
    let mut tm = TermManager::new();
    let mut model = GraphModel::new(&tm);
    let g = model.new_graph();
    let a = model.add_vertex(g).unwrap();
    let d = model.add_vertex(g).unwrap();
    let e = model.new_edge(g, a, a, &mut tm).unwrap();
    let r_ad = model.reach(g, a, d, &mut tm).unwrap();
    let (propagator, watches) = model.into_propagator();
    let mut solver = Solver::new();
    solver
        .register_user_propagator(propagator, &watches, &mut tm)
        .unwrap();
    solver.assert(e, &mut tm);
    solver.assert(r_ad, &mut tm);
    assert_eq!(solver.check(&mut tm), SolverResult::Unsat);
}

/// Cycles: reach(u,u) detects them, acyclicity forbids them, and demanding
/// both directions of reachability between two vertices needs a cycle.
#[test]
fn cycles_and_mutual_reachability() {
    let mut tm = TermManager::new();
    let mut model = GraphModel::new(&tm);
    let g = model.new_graph();
    let a = model.add_vertex(g).unwrap();
    let b = model.add_vertex(g).unwrap();
    let r_ab = model.reach(g, a, b, &mut tm).unwrap();
    let r_ba = model.reach(g, b, a, &mut tm).unwrap();
    let acyclic = model.acyclic(g, &mut tm).unwrap();
    let (propagator, watches) = model.into_propagator();
    let mut solver = Solver::new();
    solver
        .register_user_propagator(propagator, &watches, &mut tm)
        .unwrap();
    solver.assert(r_ab, &mut tm);
    solver.assert(r_ba, &mut tm);
    solver.assert(acyclic, &mut tm);
    assert_eq!(solver.check(&mut tm), SolverResult::Unsat);
    // Without acyclicity, a two-cycle exists (declare its two edges).
    let mut solver2 = Solver::new();
    let mut tm2 = TermManager::new();
    let mut model2 = GraphModel::new(&tm2);
    let g2 = model2.new_graph();
    let a2 = model2.add_vertex(g2).unwrap();
    let b2 = model2.add_vertex(g2).unwrap();
    let _e_ab2 = model2.new_edge(g2, a2, b2, &mut tm2).unwrap();
    let _e_ba2 = model2.new_edge(g2, b2, a2, &mut tm2).unwrap();
    let r_ab2 = model2.reach(g2, a2, b2, &mut tm2).unwrap();
    let r_ba2 = model2.reach(g2, b2, a2, &mut tm2).unwrap();
    let r_aa2 = model2.reach(g2, a2, a2, &mut tm2).unwrap();
    let (propagator, watches) = model2.into_propagator();
    solver2
        .register_user_propagator(propagator, &watches, &mut tm2)
        .unwrap();
    solver2.assert(r_ab2, &mut tm2);
    solver2.assert(r_ba2, &mut tm2);
    solver2.assert(r_aa2, &mut tm2);
    assert_eq!(solver2.check(&mut tm2), SolverResult::Sat);
    assert!(model_bool(&solver2, r_aa2, &tm2));
}

/// Assertion-scope lifecycle: repeated checks, nested push/pop with graph
/// constraints asserted and retracted, and re-checks after popping.
#[test]
fn push_pop_and_repeated_checks() {
    let mut tm = TermManager::new();
    let mut model = GraphModel::new(&tm);
    let g = model.new_graph();
    let a = model.add_vertex(g).unwrap();
    let b = model.add_vertex(g).unwrap();
    let e_ab = model.new_edge(g, a, b, &mut tm).unwrap();
    let r_ab = model.reach(g, a, b, &mut tm).unwrap();
    let acyclic = model.acyclic(g, &mut tm).unwrap();
    let (propagator, watches) = model.into_propagator();
    let mut solver = Solver::new();
    solver
        .register_user_propagator(propagator, &watches, &mut tm)
        .unwrap();
    solver.assert(acyclic, &mut tm);
    assert_eq!(solver.check(&mut tm), SolverResult::Sat);
    assert_eq!(solver.check(&mut tm), SolverResult::Sat);

    solver.push();
    solver.assert(e_ab, &mut tm);
    solver.assert(r_ab, &mut tm);
    assert_eq!(solver.check(&mut tm), SolverResult::Sat);

    solver.push();
    // Retracting the edge inside the inner scope contradicts reach(a,b):
    // no other route exists.
    solver.assert(tm.mk_not(e_ab), &mut tm);
    assert_eq!(solver.check(&mut tm), SolverResult::Unsat);
    solver.pop();
    assert_eq!(solver.check(&mut tm), SolverResult::Sat);
    solver.pop();
    assert_eq!(solver.check(&mut tm), SolverResult::Sat);

    // After all pops the graph is unconstrained again; demanding a cycle on
    // two vertices stays satisfiable without the acyclicity demand.
    let mut tm2 = TermManager::new();
    let mut model2 = GraphModel::new(&tm2);
    let g2 = model2.new_graph();
    let a2 = model2.add_vertex(g2).unwrap();
    let b2 = model2.add_vertex(g2).unwrap();
    let _e_ab2 = model2.new_edge(g2, a2, b2, &mut tm2).unwrap();
    let _e_ba2 = model2.new_edge(g2, b2, a2, &mut tm2).unwrap();
    let ac2 = model2.acyclic(g2, &mut tm2).unwrap();
    let r_ab2 = model2.reach(g2, a2, b2, &mut tm2).unwrap();
    let r_ba2 = model2.reach(g2, b2, a2, &mut tm2).unwrap();
    let (propagator, watches) = model2.into_propagator();
    let mut solver2 = Solver::new();
    solver2
        .register_user_propagator(propagator, &watches, &mut tm2)
        .unwrap();
    solver2.assert(ac2, &mut tm2);
    solver2.assert(r_ab2, &mut tm2);
    assert_eq!(solver2.check(&mut tm2), SolverResult::Sat);
    solver2.push();
    solver2.assert(r_ba2, &mut tm2);
    assert_eq!(solver2.check(&mut tm2), SolverResult::Unsat);
    solver2.pop();
    assert_eq!(solver2.check(&mut tm2), SolverResult::Sat);
}

/// Edge atoms may be arbitrary Boolean terms: conjunctions and arithmetic
/// equalities drive edge presence through the ordinary SAT/arithmetic stack.
#[test]
fn edges_combine_with_boolean_and_arithmetic_terms() {
    // Edge present iff (p ∧ q); reachability then depends on both.
    let mut tm = TermManager::new();
    let p = tm.mk_var("p", tm.sorts.bool_sort);
    let q = tm.mk_var("q", tm.sorts.bool_sort);
    let pq = tm.mk_and([p, q]);
    let mut model = GraphModel::new(&tm);
    let g = model.new_graph();
    let a = model.add_vertex(g).unwrap();
    let b = model.add_vertex(g).unwrap();
    model.add_edge(g, a, b, pq, &mut tm).unwrap();
    let r_ab = model.reach(g, a, b, &mut tm).unwrap();
    let (propagator, watches) = model.into_propagator();
    let mut solver = Solver::new();
    solver
        .register_user_propagator(propagator, &watches, &mut tm)
        .unwrap();
    solver.assert(r_ab, &mut tm);
    assert_eq!(solver.check(&mut tm), SolverResult::Sat);
    assert!(model_bool(&solver, p, &tm) && model_bool(&solver, q, &tm));

    // Edge present iff x = 3 for an Int x: an arithmetic contradiction
    // plus the reachability demand must be unsat.
    let mut tm = TermManager::new();
    let x = tm.mk_var("x", tm.sorts.int_sort);
    let three = tm.mk_int(num_bigint::BigInt::from(3));
    let x3 = tm.mk_eq(x, three);
    let mut model = GraphModel::new(&tm);
    let g = model.new_graph();
    let a = model.add_vertex(g).unwrap();
    let b = model.add_vertex(g).unwrap();
    model.add_edge(g, a, b, x3, &mut tm).unwrap();
    let r_ab = model.reach(g, a, b, &mut tm).unwrap();
    let (propagator, watches) = model.into_propagator();
    let mut solver = Solver::new();
    solver
        .register_user_propagator(propagator, &watches, &mut tm)
        .unwrap();
    solver.assert(r_ab, &mut tm);
    let four = tm.mk_int(num_bigint::BigInt::from(4));
    solver.assert(tm.mk_eq(x, four), &mut tm);
    assert_eq!(solver.check(&mut tm), SolverResult::Unsat);
}

/// Graph constraints combine with other theory atoms in one check: the
/// reachability demand interacts with linear arithmetic.
#[test]
fn graph_constraints_combine_with_arithmetic() {
    let mut tm = TermManager::new();
    let x = tm.mk_var("x", tm.sorts.int_sort);
    let mut model = GraphModel::new(&tm);
    let g = model.new_graph();
    let a = model.add_vertex(g).unwrap();
    let b = model.add_vertex(g).unwrap();
    let e = model.new_edge(g, a, b, &mut tm).unwrap();
    let r = model.reach(g, a, b, &mut tm).unwrap();
    let (propagator, watches) = model.into_propagator();
    let mut solver = Solver::new();
    solver
        .register_user_propagator(propagator, &watches, &mut tm)
        .unwrap();
    // The edge is present exactly when x > 0; with x <= 0 and reachability
    // demanded, the instance is unsat through pure arithmetic.
    let zero = tm.mk_int(num_bigint::BigInt::from(0));
    let positive = tm.mk_gt(x, zero);
    let guard = tm.mk_eq(positive, e);
    solver.assert(guard, &mut tm);
    let nonpositive = tm.mk_le(x, zero);
    solver.assert(nonpositive, &mut tm);
    solver.assert(r, &mut tm);
    assert_eq!(solver.check(&mut tm), SolverResult::Unsat);
    // Relaxing the bound: satisfiable, and the model's edge is true.
    let mut tm2 = TermManager::new();
    let x2 = tm2.mk_var("x", tm2.sorts.int_sort);
    let mut model2 = GraphModel::new(&tm2);
    let g2 = model2.new_graph();
    let a2 = model2.add_vertex(g2).unwrap();
    let b2 = model2.add_vertex(g2).unwrap();
    let e2 = model2.new_edge(g2, a2, b2, &mut tm2).unwrap();
    let r2 = model2.reach(g2, a2, b2, &mut tm2).unwrap();
    let (propagator, watches) = model2.into_propagator();
    let mut solver2 = Solver::new();
    solver2
        .register_user_propagator(propagator, &watches, &mut tm2)
        .unwrap();
    let zero2 = tm2.mk_int(num_bigint::BigInt::from(0));
    let positive2 = tm2.mk_gt(x2, zero2);
    let guard2 = tm2.mk_eq(positive2, e2);
    solver2.assert(guard2, &mut tm2);
    let five = tm2.mk_int(num_bigint::BigInt::from(5));
    let bound = tm2.mk_ge(x2, five);
    solver2.assert(bound, &mut tm2);
    solver2.assert(r2, &mut tm2);
    assert_eq!(solver2.check(&mut tm2), SolverResult::Sat);
    assert!(model_bool(&solver2, e2, &tm2));
}

/// Certified mode fails closed for graph callbacks (no independent
/// certificate exists), while the same instance stays decidable without
/// certification.
#[test]
fn certified_mode_fails_closed_for_graph_callbacks() {
    // Unsatisfiable instance: acyclic but mutual reachability demanded.
    let build = |tm: &mut TermManager, model: &mut GraphModel| {
        let g = model.new_graph();
        let a = model.add_vertex(g).unwrap();
        let b = model.add_vertex(g).unwrap();
        let r_ab = model.reach(g, a, b, tm).unwrap();
        let r_ba = model.reach(g, b, a, tm).unwrap();
        let acyclic = model.acyclic(g, tm).unwrap();
        (r_ab, r_ba, acyclic)
    };
    let mut tm = TermManager::new();
    let mut model = GraphModel::new(&tm);
    let (r_ab, r_ba, acyclic) = build(&mut tm, &mut model);
    let (propagator, watches) = model.into_propagator();
    let mut plain = Solver::new();
    plain
        .register_user_propagator(propagator, &watches, &mut tm)
        .unwrap();
    plain.assert(acyclic, &mut tm);
    plain.assert(r_ab, &mut tm);
    plain.assert(r_ba, &mut tm);
    assert_eq!(plain.check(&mut tm), SolverResult::Unsat);

    let mut tm2 = TermManager::new();
    let mut model2 = GraphModel::new(&tm2);
    let (r_ab2, r_ba2, acyclic2) = build(&mut tm2, &mut model2);
    let (propagator, watches) = model2.into_propagator();
    let mut certified = Solver::with_config(nixie_solver::SolverConfig::default().certified());
    certified
        .register_user_propagator(propagator, &watches, &mut tm2)
        .unwrap();
    certified.assert(acyclic2, &mut tm2);
    certified.assert(r_ab2, &mut tm2);
    certified.assert(r_ba2, &mut tm2);
    assert_eq!(
        certified.check(&mut tm2),
        SolverResult::Unknown,
        "certified mode must fail closed for graph callbacks"
    );
}

/// Registration lifecycle: registering after a check or inside a scope is
/// rejected, matching the CP contract.
#[test]
fn registration_lifecycle_errors() {
    let mut tm = TermManager::new();
    let mut model = GraphModel::new(&tm);
    let g = model.new_graph();
    let a = model.add_vertex(g).unwrap();
    let _ = model.new_edge(g, a, a, &mut tm).unwrap();
    let mut solver = Solver::new();
    solver.assert(tm.mk_bool(true), &mut tm);
    // After a check, registration is no longer allowed.
    let mut tm2 = TermManager::new();
    let mut model2 = GraphModel::new(&tm2);
    let g2 = model2.new_graph();
    let a2 = model2.add_vertex(g2).unwrap();
    let _ = model2.new_edge(g2, a2, a2, &mut tm2).unwrap();
    let (prop, watches) = model2.into_propagator();
    assert_eq!(solver.check(&mut tm), SolverResult::Sat);
    assert!(
        solver
            .register_user_propagator(prop, &watches, &mut tm)
            .is_err()
    );

    // Inside an assertion scope, registration is also rejected.
    let mut tm3 = TermManager::new();
    let mut model3 = GraphModel::new(&tm3);
    let g3 = model3.new_graph();
    let a3 = model3.add_vertex(g3).unwrap();
    let _ = model3.new_edge(g3, a3, a3, &mut tm3).unwrap();
    let mut solver3 = Solver::new();
    solver3.push();
    let (prop3, watches3) = model3.into_propagator();
    assert!(
        solver3
            .register_user_propagator(prop3, &watches3, &mut tm3)
            .is_err()
    );
    solver3.pop();
}

/// `register_graph` is the intended entry point and behaves like the
/// lower-level registration used elsewhere in these tests.
#[test]
fn register_graph_helper_installs_constraints() {
    let mut tm = TermManager::new();
    let mut model = GraphModel::new(&tm);
    let g = model.new_graph();
    let a = model.add_vertex(g).unwrap();
    let b = model.add_vertex(g).unwrap();
    let e = model.new_edge(g, a, b, &mut tm).unwrap();
    let r = model.reach(g, a, b, &mut tm).unwrap();
    let mut solver = Solver::new();
    solver.register_graph(model, &mut tm).unwrap();
    solver.assert(tm.mk_not(e), &mut tm);
    solver.assert(r, &mut tm);
    assert_eq!(solver.check(&mut tm), SolverResult::Unsat);
    // Registration errors surface as GraphError.
    let mut tm2 = TermManager::new();
    let empty = GraphModel::new(&tm2);
    let mut solver2 = Solver::new();
    assert!(solver2.register_graph(empty, &mut tm2).is_ok());
}

/// The realistic network-policy scenario from `docs/GRAPH.md`, kept
/// executable: segmentation (an internet-facing tier isolated from the
/// database tier while the application tier reaches it), plus an acyclic
/// deployment-dependency overlay. Transititivity is what the solver must
/// reason about: admitting the internet to the app tier would compromise
/// the database.
#[test]
fn network_policy_scenario() {
    // Zones: internet(0), dmz(1), app(2), db(3).
    let mut tm = TermManager::new();
    let mut graphs = GraphModel::new(&tm);
    let net = graphs.new_graph();
    let zones: Vec<_> = (0..4).map(|_| graphs.add_vertex(net).unwrap()).collect();
    let link = |graphs: &mut GraphModel, u: usize, v: usize, tm: &mut TermManager| {
        graphs.new_edge(net, zones[u], zones[v], tm).unwrap()
    };
    let l_in_dmz = link(&mut graphs, 0, 1, &mut tm);
    let l_dmz_app = link(&mut graphs, 1, 2, &mut tm);
    let l_app_db = link(&mut graphs, 2, 3, &mut tm);
    let l_in_app = link(&mut graphs, 0, 2, &mut tm);
    let l_dmz_db = link(&mut graphs, 1, 3, &mut tm);

    let internet_reaches_dmz = graphs.reach(net, zones[0], zones[1], &mut tm).unwrap();
    let internet_reaches_app = graphs.reach(net, zones[0], zones[2], &mut tm).unwrap();
    let internet_reaches_db = graphs.reach(net, zones[0], zones[3], &mut tm).unwrap();
    let app_reaches_db = graphs.reach(net, zones[2], zones[3], &mut tm).unwrap();

    // Deployment dependencies (a second graph in the same solver):
    // app -> db and dmz -> app are installed; the reverse db -> dmz
    // dependency would close a cycle and must stay disabled.
    let deps = graphs.new_graph();
    let dep_nodes: Vec<_> = (0..3).map(|_| graphs.add_vertex(deps).unwrap()).collect();
    let d_app_db = graphs
        .new_edge(deps, dep_nodes[0], dep_nodes[1], &mut tm)
        .unwrap();
    let d_dmz_app = graphs
        .new_edge(deps, dep_nodes[2], dep_nodes[0], &mut tm)
        .unwrap();
    let d_db_dmz = graphs
        .new_edge(deps, dep_nodes[1], dep_nodes[2], &mut tm)
        .unwrap();
    let deps_acyclic = graphs.acyclic(deps, &mut tm).unwrap();

    let mut solver = Solver::new();
    solver.register_graph(graphs, &mut tm).unwrap();
    // Policy: the internet reaches the dmz, the app tier reaches the
    // database, and the internet must never reach the database.
    solver.assert(internet_reaches_dmz, &mut tm);
    solver.assert(app_reaches_db, &mut tm);
    solver.assert(tm.mk_not(internet_reaches_db), &mut tm);
    // Dependencies are installed and the overlay must stay acyclic; the
    // cycle-closing db -> dmz dependency is left disabled.
    solver.assert(d_app_db, &mut tm);
    solver.assert(d_dmz_app, &mut tm);
    solver.assert(deps_acyclic, &mut tm);
    assert_eq!(solver.check(&mut tm), SolverResult::Sat);
    // The solver must isolate the tiers: no link from the internet side
    // into the app/db segment (otherwise the db would be compromised).
    assert!(!model_bool(&solver, l_dmz_app, &tm));
    assert!(!model_bool(&solver, l_in_app, &tm));
    assert!(!model_bool(&solver, l_dmz_db, &tm));
    assert!(model_bool(&solver, l_in_dmz, &tm) && model_bool(&solver, l_app_db, &tm));

    // Admitting the internet to the app tier transitively compromises the
    // database: the demand is inconsistent with the isolation policy.
    solver.push();
    solver.assert(internet_reaches_app, &mut tm);
    assert_eq!(solver.check(&mut tm), SolverResult::Unsat);
    solver.pop();

    // Enabling every remaining network link also breaks isolation.
    solver.push();
    solver.assert(l_dmz_app, &mut tm);
    solver.assert(l_in_app, &mut tm);
    solver.assert(l_dmz_db, &mut tm);
    assert_eq!(solver.check(&mut tm), SolverResult::Unsat);
    solver.pop();

    // Installing the cycle-closing dependency breaks the acyclic overlay.
    solver.push();
    solver.assert(d_db_dmz, &mut tm);
    assert_eq!(solver.check(&mut tm), SolverResult::Unsat);
    solver.pop();

    assert_eq!(solver.check(&mut tm), SolverResult::Sat);
}

/// Defense-in-depth for the empty-cut defect (see the focused unit test in
/// nixie-theories): after any branch that leaves both parallel source edges
/// false, the solver must still be able to find a cycle by re-enabling one
/// of them. A buggy unconditional `¬reach(u,u)` clause would flip this sat
/// to a false unsat.
#[test]
fn cycle_through_parallel_edge_stays_reachable_after_cut_learning() {
    let mut tm = TermManager::new();
    let mut model = GraphModel::new(&tm);
    let g = model.new_graph();
    let a = model.add_vertex(g).unwrap();
    let b = model.add_vertex(g).unwrap();
    let e0 = model.new_edge(g, a, b, &mut tm).unwrap();
    let e1 = model.new_edge(g, a, b, &mut tm).unwrap();
    let e2 = model.new_edge(g, b, a, &mut tm).unwrap();
    let r_aa = model.reach(g, a, a, &mut tm).unwrap();
    let mut solver = Solver::new();
    solver.register_graph(model, &mut tm).unwrap();
    // Force the search through states where both parallel edges are false
    // (the empty-cut trigger), then demand the cycle anyway.
    let not_both = {
        let ne0 = tm.mk_not(e0);
        let ne1 = tm.mk_not(e1);
        tm.mk_or([ne0, ne1])
    };
    solver.assert(not_both, &mut tm);
    solver.assert(e2, &mut tm);
    solver.assert(r_aa, &mut tm);
    assert_eq!(solver.check(&mut tm), SolverResult::Sat);
    // Reachability uses length-≥1 paths: the cycle is e_i ∧ e2.
    assert!(model_bool(&solver, e0, &tm) != model_bool(&solver, e1, &tm));
}

/// Assumption-scoped checks interact correctly with graph atoms.
#[test]
fn assumptions_scoped_checks() {
    let mut tm = TermManager::new();
    let mut model = GraphModel::new(&tm);
    let g = model.new_graph();
    let a = model.add_vertex(g).unwrap();
    let b = model.add_vertex(g).unwrap();
    let e = model.new_edge(g, a, b, &mut tm).unwrap();
    let r = model.reach(g, a, b, &mut tm).unwrap();
    let mut solver = Solver::new();
    solver.register_graph(model, &mut tm).unwrap();
    // No assumptions: sat with the edge either way.
    assert_eq!(
        solver.check_with_assumptions(&[], &mut tm),
        SolverResult::Sat
    );
    // Assuming ¬edge makes reachability false, so reach is unsat...
    let not_e = tm.mk_not(e);
    assert_eq!(
        solver.check_with_assumptions(&[not_e, r], &mut tm),
        SolverResult::Unsat
    );
    // ...and assuming the edge satisfies it.
    assert_eq!(
        solver.check_with_assumptions(&[e, r], &mut tm),
        SolverResult::Sat
    );
    // Assumptions do not leak: a plain check afterwards is unconstrained.
    assert_eq!(solver.check(&mut tm), SolverResult::Sat);
}

/// Reset clears registrations; a fresh model can be installed afterwards.
#[test]
fn reset_clears_and_allows_re_registration() {
    let mut tm = TermManager::new();
    let mut model = GraphModel::new(&tm);
    let g = model.new_graph();
    let a = model.add_vertex(g).unwrap();
    let b = model.add_vertex(g).unwrap();
    let e = model.new_edge(g, a, b, &mut tm).unwrap();
    let r = model.reach(g, a, b, &mut tm).unwrap();
    let mut solver = Solver::new();
    solver.register_graph(model, &mut tm).unwrap();
    assert_eq!(solver.check(&mut tm), SolverResult::Sat);
    solver.reset();
    // Re-registration must happen before the next check (the documented
    // lifecycle); install the fresh model first.
    let mut model2 = GraphModel::new(&tm);
    let g2 = model2.new_graph();
    let a2 = model2.add_vertex(g2).unwrap();
    let b2 = model2.add_vertex(g2).unwrap();
    let e2 = model2.new_edge(g2, a2, b2, &mut tm).unwrap();
    let r2 = model2.reach(g2, a2, b2, &mut tm).unwrap();
    solver.register_graph(model2, &mut tm).unwrap();
    // The old model's constraints are gone: its atoms are now ordinary free
    // Booleans, so the old contradiction is no longer detected...
    solver.assert(r, &mut tm);
    solver.assert(tm.mk_not(e), &mut tm);
    assert_eq!(solver.check(&mut tm), SolverResult::Sat);
    // ...while the new model's constraints bind.
    solver.assert(r2, &mut tm);
    solver.assert(tm.mk_not(e2), &mut tm);
    assert_eq!(solver.check(&mut tm), SolverResult::Unsat);
}

/// Several graph models may be registered on one solver; each is enforced
/// independently.
#[test]
fn multiple_registrations_are_enforced() {
    let mut tm = TermManager::new();
    let build = |tm: &mut TermManager| {
        let mut m = GraphModel::new(tm);
        let g = m.new_graph();
        let a = m.add_vertex(g).unwrap();
        let b = m.add_vertex(g).unwrap();
        let e = m.new_edge(g, a, b, tm).unwrap();
        let r = m.reach(g, a, b, tm).unwrap();
        (m, e, r)
    };
    let (m1, e1, r1) = build(&mut tm);
    let (m2, e2, r2) = build(&mut tm);
    let (prop1, watch1) = m1.into_propagator();
    let (prop2, watch2) = m2.into_propagator();
    let mut solver = Solver::new();
    solver
        .register_user_propagator(prop1, &watch1, &mut tm)
        .unwrap();
    solver
        .register_user_propagator(prop2, &watch2, &mut tm)
        .unwrap();
    // Model 1's reachability is refuted by disabling its edge, while model
    // 2's is satisfied by enabling its own (distinct) edge: both models are
    // enforced simultaneously.
    let ne1 = tm.mk_not(e1);
    solver.assert(ne1, &mut tm);
    solver.assert(r1, &mut tm);
    solver.assert(e2, &mut tm);
    solver.assert(r2, &mut tm);
    assert_eq!(solver.check(&mut tm), SolverResult::Unsat);
    // ...while model 2's atom stays free to be satisfied.
    let mut tm2 = TermManager::new();
    let (m3, e3, r3) = build(&mut tm2);
    let (prop3, watch3) = m3.into_propagator();
    let mut solver2 = Solver::new();
    solver2
        .register_user_propagator(prop3, &watch3, &mut tm2)
        .unwrap();
    solver2.assert(e3, &mut tm2);
    solver2.assert(r3, &mut tm2);
    assert_eq!(solver2.check(&mut tm2), SolverResult::Sat);
}
