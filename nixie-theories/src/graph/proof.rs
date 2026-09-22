//! Standalone checking of finite-graph reachability and acyclicity lemmas.
//!
//! No callback state, incremental view, or propagation code is consulted:
//! the checker recomputes explicit closures over the immutable statement
//! with plain BFS/Kahn algorithms (different code from the propagator's
//! maintained views, like the exhaustive oracles). The caller must retain
//! and authenticate the original statement, then separately check current
//! premise truth.

use crate::prelude::*;
use nixie_core::ast::TermId;

/// Immutable original graph declaration: its fixed vertex universe, every
/// edge's ordered pair and Boolean presence atom (with negation), every
/// reified reachability atom, and the acyclicity atom if declared. Obtain
/// it through `GraphModel::statements` before consuming the model; term IDs
/// belong to that model's term manager.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct GraphStatement {
    /// Shared identity: two statements over one `Arc` are the same
    /// declaration (the edge list is append-only before registration).
    edges: Arc<[(u32, u32, TermId, TermId)]>,
    /// `(from, to, atom, negation)` per reified reach atom.
    reach: Arc<[(u32, u32, TermId, TermId)]>,
    /// Acyclicity atom and its negation, if declared.
    acyclic: Option<(TermId, TermId)>,
    vertices: usize,
    false_term: TermId,
}

/// Invalid graph lemma; malformed structure is an error, never a panic.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct GraphProofError(pub &'static str);
impl core::fmt::Display for GraphProofError {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        f.write_str(self.0)
    }
}
impl core::error::Error for GraphProofError {}

/// Untrusted witness for `premises => conclusion` relative to one original
/// graph declaration. The witness carries only the statement identity;
/// checking recomputes everything from the immutable declaration.
#[derive(Debug, Clone)]
pub struct GraphCertificate {
    statement: GraphStatement,
}

impl GraphCertificate {
    /// Construct an untrusted witness; call `check` before accepting it.
    #[must_use]
    pub fn new(statement: GraphStatement) -> Self {
        Self { statement }
    }

    /// Referenced statement, which a consumer must authenticate independently.
    #[must_use]
    pub fn statement(&self) -> &GraphStatement {
        &self.statement
    }

    /// Exact identity of a registered graph, preserved across clones.
    #[must_use]
    pub fn is_for(&self, original: &GraphStatement) -> bool {
        self.statement.is_same(original)
    }

    /// Check the exact implication against an independently retained
    /// original. Unused or foreign premises are harmless weakening; their
    /// current truth is the adapter's separate concern.
    pub fn check(
        &self,
        original: &GraphStatement,
        conclusion: TermId,
        premises: &[TermId],
    ) -> Result<(), GraphProofError> {
        if !self.statement.is_same(original) {
            return Err(GraphProofError("certificate references a different graph"));
        }
        original.check_lemma(conclusion, premises)
    }
}

/// How a premise participates in a graph lemma.
#[derive(Clone, Copy, PartialEq, Eq)]
enum PremiseKind {
    /// Edge presence atom: the edge is claimed true.
    EdgePresent(usize),
    /// Edge negation: the edge is claimed false.
    EdgeRefuted(usize),
    /// A reachability or acyclicity literal (conflict premises only).
    GraphLiteral,
    /// A term foreign to this statement: ignored (weakening).
    Foreign,
}

impl GraphStatement {
    /// Build a statement over an explicit declaration. The `edges` Arc is
    /// the identity anchor.
    #[must_use]
    pub fn new(
        vertices: usize,
        edges: Arc<[(u32, u32, TermId, TermId)]>,
        reach: Arc<[(u32, u32, TermId, TermId)]>,
        acyclic: Option<(TermId, TermId)>,
        false_term: TermId,
    ) -> Self {
        Self {
            edges,
            reach,
            acyclic,
            vertices,
            false_term,
        }
    }

    /// Same declaration (identity through the append-only edge list).
    #[must_use]
    pub fn is_same(&self, other: &GraphStatement) -> bool {
        Arc::ptr_eq(&self.edges, &other.edges)
    }

    /// The declaration's fixed vertex count.
    #[must_use]
    pub fn vertices_count(&self) -> usize {
        self.vertices
    }

    /// The declaration's edges as `(from, to, atom, negation)`.
    #[must_use]
    pub fn edges(&self) -> &[(u32, u32, TermId, TermId)] {
        &self.edges
    }

    /// The declaration's reified reach atoms as `(from, to, atom, negation)`.
    #[must_use]
    pub fn reach_atoms(&self) -> &[(u32, u32, TermId, TermId)] {
        &self.reach
    }

    /// The declaration's acyclicity atom, if any.
    #[must_use]
    pub fn acyclic_atom(&self) -> Option<TermId> {
        self.acyclic.map(|(atom, _)| atom)
    }

    fn classify(&self, term: TermId) -> PremiseKind {
        for (i, &(_, _, atom, negation)) in self.edges.iter().enumerate() {
            if atom == term {
                return PremiseKind::EdgePresent(i);
            }
            if negation == term {
                return PremiseKind::EdgeRefuted(i);
            }
        }
        for &(_, _, atom, negation) in self.reach.iter() {
            if atom == term || negation == term {
                return PremiseKind::GraphLiteral;
            }
        }
        if let Some((atom, negation)) = self.acyclic
            && (atom == term || negation == term)
        {
            return PremiseKind::GraphLiteral;
        }
        PremiseKind::Foreign
    }

    /// Vertices reachable from `source` through **at least one** edge
    /// selected by `keep` (explicit BFS; no incremental state). The
    /// length-≥1 closure matches the reach atoms' semantics exactly: for
    /// `target == source` membership means a directed cycle through the
    /// source (a self-loop included).
    fn closure_ge1(&self, source: u32, keep: &dyn Fn(usize) -> bool) -> Vec<bool> {
        let mut seen = vec![false; self.vertices];
        let mut queue = Vec::new();
        for (i, &(from, to, _, _)) in self.edges.iter().enumerate() {
            if from == source && keep(i) && (to as usize) < self.vertices {
                seen[to as usize] = true;
                queue.push(to);
            }
        }
        let mut head = 0;
        while let Some(&v) = queue.get(head) {
            head += 1;
            for (i, &(from, to, _, _)) in self.edges.iter().enumerate() {
                if from == v && keep(i) && !seen[to as usize] {
                    seen[to as usize] = true;
                    queue.push(to);
                }
            }
        }
        seen
    }

    /// Is the subgraph of `kept` edges acyclic? (Kahn's algorithm —
    /// iterative, explicit, independent of the propagator's detectors.)
    fn kept_is_acyclic(&self, keep: &dyn Fn(usize) -> bool) -> bool {
        let n = self.vertices;
        let mut indegree = vec![0usize; n];
        let mut outgoing: Vec<Vec<u32>> = vec![Vec::new(); n];
        for (i, &(from, to, _, _)) in self.edges.iter().enumerate() {
            if keep(i) {
                outgoing[from as usize].push(to);
                indegree[to as usize] += 1;
            }
        }
        let mut queue: Vec<usize> = (0..n).filter(|&v| indegree[v] == 0).collect();
        let mut removed = 0usize;
        let mut head = 0;
        while let Some(&v) = queue.get(head) {
            head += 1;
            removed += 1;
            for &w in &outgoing[v] {
                indegree[w as usize] -= 1;
                if indegree[w as usize] == 0 {
                    queue.push(w as usize);
                }
            }
        }
        removed == n
    }

    /// Does the subgraph of `kept` edges contain a directed cycle?
    /// (Iterative three-color DFS.)
    fn kept_has_cycle(&self, keep: &dyn Fn(usize) -> bool) -> bool {
        // colors: 0 white, 1 gray, 2 black
        let n = self.vertices;
        let mut color = vec![0u8; n];
        let mut outgoing: Vec<Vec<(u32, usize)>> = vec![Vec::new(); n];
        for (i, &(from, to, _, _)) in self.edges.iter().enumerate() {
            if keep(i) {
                outgoing[from as usize].push((to, i));
            }
        }
        for start in 0..n {
            if color[start] != 0 {
                continue;
            }
            // Stack of (vertex, next out-position).
            let mut stack: Vec<(usize, usize)> = vec![(start, 0)];
            color[start] = 1;
            while let Some(&mut (v, ref mut next)) = stack.last_mut() {
                if *next >= outgoing[v].len() {
                    color[v] = 2;
                    stack.pop();
                    continue;
                }
                let (to, _) = outgoing[v][*next];
                *next += 1;
                match color[to as usize] {
                    0 => {
                        color[to as usize] = 1;
                        stack.push((to as usize, 0));
                    }
                    1 => return true,
                    _ => {}
                }
            }
        }
        false
    }

    /// Check `premises => conclusion` against this immutable declaration.
    ///
    /// - `reach(u,v)` concluded: valid iff `v` lies in the length-≥1
    ///   closure of `u` over edges whose **presence atom** is a premise.
    /// - `¬reach(u,v)` concluded: valid iff `v` lies outside the closure
    ///   over edges **not refuted** by a premise negation.
    /// - `acyclic` concluded: valid iff the non-refuted edges are acyclic.
    /// - `¬acyclic` concluded: valid iff the present edges contain a cycle.
    /// - `false` concluded (conflict): the premises must include one graph
    ///   literal whose opposite the remaining premises imply (recursion).
    ///
    /// Foreign premises are ignored (weakening). Every check recomputes an
    /// explicit closure over the declaration — the propagator is untrusted.
    pub fn check_lemma(
        &self,
        conclusion: TermId,
        premises: &[TermId],
    ) -> Result<(), GraphProofError> {
        if conclusion == self.false_term {
            // Conflict: locate the single graph literal among the premises
            // and check the opposite implication of the rest.
            let mut literal = None;
            let mut rest = Vec::with_capacity(premises.len());
            for &p in premises {
                if self.classify(p) == PremiseKind::GraphLiteral {
                    if literal.is_some() {
                        // More than one graph literal: the pairwise
                        // contradiction case is covered by checking any
                        // single one against the rest (the adapter's truth
                        // gate guarantees both are currently true).
                        rest.push(p);
                    } else {
                        literal = Some(p);
                    }
                } else {
                    rest.push(p);
                }
            }
            let Some(literal) = literal else {
                return Err(GraphProofError(
                    "graph conflict premise cites no graph literal",
                ));
            };
            let opposite = self
                .negation_of(literal)
                .ok_or(GraphProofError("conflict literal has no graph negation"))?;
            return self.check_lemma(opposite, &rest);
        }
        // Reach conclusions.
        for &(from, to, atom, negation) in self.reach.iter() {
            let polarity = if conclusion == atom {
                true
            } else if conclusion == negation {
                false
            } else {
                continue;
            };
            let valid = if polarity {
                // Present edges: presence atom among the premises.
                let closure = self.closure_ge1(from, &|i| {
                    let atom = self.edges[i].2;
                    premises.contains(&atom)
                });
                closure[to as usize]
            } else {
                // Non-refuted edges: negation not among the premises.
                let closure = self.closure_ge1(from, &|i| {
                    let negation = self.edges[i].3;
                    !premises.contains(&negation)
                });
                !closure[to as usize]
            };
            return if valid {
                Ok(())
            } else {
                Err(GraphProofError("reachability lemma is not justified"))
            };
        }
        // Acyclicity conclusions.
        if let Some((atom, negation)) = self.acyclic {
            let polarity = if conclusion == atom {
                true
            } else if conclusion == negation {
                false
            } else {
                return Err(GraphProofError(
                    "conclusion is not a graph literal of this statement",
                ));
            };
            let valid = if polarity {
                self.kept_is_acyclic(&|i| !premises.contains(&self.edges[i].3))
            } else {
                self.kept_has_cycle(&|i| premises.contains(&self.edges[i].2))
            };
            return if valid {
                Ok(())
            } else {
                Err(GraphProofError("acyclicity lemma is not justified"))
            };
        }
        Err(GraphProofError(
            "conclusion is not a graph literal of this statement",
        ))
    }

    /// The statement's negation term for a graph literal, if it is one.
    #[must_use]
    fn negation_of(&self, term: TermId) -> Option<TermId> {
        for &(_, _, atom, negation) in self.reach.iter() {
            if atom == term {
                return Some(negation);
            }
            if negation == term {
                return Some(atom);
            }
        }
        if let Some((atom, negation)) = self.acyclic {
            if atom == term {
                return Some(negation);
            }
            if negation == term {
                return Some(atom);
            }
        }
        None
    }

    /// Independently validate a complete assignment against the
    /// declaration: every reach atom equals the closure truth over the
    /// `true`-valued edges, and the acyclicity atom equals the cycle test.
    /// `value` answers each edge atom's model value; `None` (unknown)
    /// fails closed. This is the model-level analogue of `check_lemma`,
    /// used by both the ordinary replay gate and certified checks.
    pub fn check_model(
        &self,
        value: &dyn Fn(TermId) -> Option<bool>,
    ) -> Result<(), GraphProofError> {
        let edge_values: Vec<bool> = self
            .edges
            .iter()
            .map(|&(_, _, atom, _)| value(atom))
            .collect::<Option<_>>()
            .ok_or(GraphProofError("edge atom has no model value"))?;
        for &(from, to, atom, _) in self.reach.iter() {
            let Some(expected) = value(atom) else {
                return Err(GraphProofError("reach atom has no model value"));
            };
            let closure = self.closure_ge1(from, &|i| edge_values[i]);
            if closure[to as usize] != expected {
                return Err(GraphProofError(
                    "reach atom disagrees with the closure oracle",
                ));
            }
        }
        if let Some((atom, _)) = self.acyclic {
            let Some(expected) = value(atom) else {
                return Err(GraphProofError("acyclic atom has no model value"));
            };
            if self.kept_is_acyclic(&|i| edge_values[i]) != expected {
                return Err(GraphProofError(
                    "acyclic atom disagrees with the cycle oracle",
                ));
            }
        }
        Ok(())
    }
}

#[cfg(test)]
mod tests {
    #![allow(clippy::unwrap_used)]
    use super::*;
    use nixie_core::ast::TermManager;

    /// Triangle 0→1→2→0 plus chord 0→2; reach (0,2), (0,0); acyclic.
    fn triangle(tm: &mut TermManager) -> (GraphStatement, Vec<TermId>, Vec<TermId>, TermId) {
        let edges = ["e01", "e12", "e20", "e02"]
            .iter()
            .map(|n| tm.mk_var(n, tm.sorts.bool_sort))
            .collect::<Vec<_>>();
        let negations: Vec<TermId> = edges.iter().map(|&a| tm.mk_not(a)).collect();
        let reach01 = tm.mk_var("r01", tm.sorts.bool_sort);
        let reach00 = tm.mk_var("r00", tm.sorts.bool_sort);
        let acyclic = tm.mk_var("acy", tm.sorts.bool_sort);
        let edge_list: Arc<[(u32, u32, TermId, TermId)]> = [
            (0, 1, edges[0], negations[0]),
            (1, 2, edges[1], negations[1]),
            (2, 0, edges[2], negations[2]),
            (0, 2, edges[3], negations[3]),
        ]
        .into();
        let reach_list: Arc<[(u32, u32, TermId, TermId)]> = [
            (0, 2, reach01, tm.mk_not(reach01)),
            (0, 0, reach00, tm.mk_not(reach00)),
        ]
        .into();
        let statement = GraphStatement::new(
            3,
            edge_list,
            reach_list,
            Some((acyclic, tm.mk_not(acyclic))),
            tm.mk_bool(false),
        );
        (statement, edges, vec![reach01, reach00], acyclic)
    }

    #[test]
    fn path_lemmas_check_exactly() {
        let mut tm = TermManager::new();
        let (statement, edges, reach, _) = triangle(&mut tm);
        // Premises make 0→1 and 1→2 present: reach(0,2) follows.
        assert!(
            statement
                .check_lemma(reach[0], &[edges[0], edges[1]])
                .is_ok()
        );
        // Missing the second edge: not justified.
        assert!(statement.check_lemma(reach[0], &[edges[0]]).is_err());
        // A foreign premise is harmless weakening.
        let foreign = tm.mk_var("zzz", tm.sorts.bool_sort);
        assert!(
            statement
                .check_lemma(reach[0], &[edges[0], edges[1], foreign])
                .is_ok()
        );
        // The direct chord alone also suffices.
        assert!(statement.check_lemma(reach[0], &[edges[3]]).is_ok());
    }

    #[test]
    fn cut_lemmas_check_exactly() {
        let mut tm = TermManager::new();
        let (statement, edges, reach, _) = triangle(&mut tm);
        let not_reach02 = tm.mk_not(reach[0]);
        // Refuting 0→1 and 0→2 cuts every path from 0 to 2.
        assert!(
            statement
                .check_lemma(not_reach02, &[tm.mk_not(edges[0]), tm.mk_not(edges[3])])
                .is_ok()
        );
        // Refuting only 0→1 leaves the chord: the cut is crossed.
        assert!(
            statement
                .check_lemma(not_reach02, &[tm.mk_not(edges[0])])
                .is_err()
        );
        // No premises at all: 0 reaches 2 through the chord.
        assert!(statement.check_lemma(not_reach02, &[]).is_err());
    }

    #[test]
    fn self_pair_cycle_lemmas_check_exactly() {
        let mut tm = TermManager::new();
        let (statement, edges, reach, _) = triangle(&mut tm);
        // reach(0,0): the full cycle 0→1→2→0 must be present.
        assert!(
            statement
                .check_lemma(reach[1], &[edges[0], edges[1], edges[2]])
                .is_ok()
        );
        // Dropping any cycle edge breaks it.
        assert!(
            statement
                .check_lemma(reach[1], &[edges[0], edges[1]])
                .is_err()
        );
        // ¬reach(0,0) holds when the cycle is cut (0→1 refuted and the
        // 0→2→... route back needs 2→0; refuting both out-edges of 0
        // cuts every cycle through 0).
        let not_r00 = tm.mk_not(reach[1]);
        assert!(
            statement
                .check_lemma(not_r00, &[tm.mk_not(edges[0]), tm.mk_not(edges[3])])
                .is_ok()
        );
        // ...but not when the cycle is alive.
        assert!(statement.check_lemma(not_r00, &[]).is_err());
    }

    #[test]
    fn acyclicity_lemmas_check_exactly() {
        let mut tm = TermManager::new();
        let (statement, edges, _, acyclic) = triangle(&mut tm);
        // ¬acyclic: the premise edges contain the directed cycle.
        assert!(
            statement
                .check_lemma(tm.mk_not(acyclic), &[edges[0], edges[1], edges[2]])
                .is_ok()
        );
        // Premise edges without a cycle do not justify ¬acyclic.
        assert!(
            statement
                .check_lemma(tm.mk_not(acyclic), &[edges[0], edges[1]])
                .is_err()
        );
        // acyclic: every edge refuted leaves the empty (acyclic) graph.
        assert!(
            statement
                .check_lemma(
                    acyclic,
                    &[
                        tm.mk_not(edges[0]),
                        tm.mk_not(edges[1]),
                        tm.mk_not(edges[2]),
                        tm.mk_not(edges[3])
                    ]
                )
                .is_ok()
        );
        // One live cycle edge keeps a cycle (the self-loop-free triangle
        // minus all-but-one edges is acyclic, so refute all but e20:
        // that single edge alone cannot cycle) — actually any single edge
        // is acyclic; refute three, keep e12.
        assert!(
            statement
                .check_lemma(
                    acyclic,
                    &[
                        tm.mk_not(edges[0]),
                        tm.mk_not(edges[2]),
                        tm.mk_not(edges[3])
                    ]
                )
                .is_ok()
        );
        // Keeping the full cycle refutes acyclicity's conclusion.
        assert!(
            statement
                .check_lemma(acyclic, &[tm.mk_not(edges[3])])
                .is_err()
        );
    }

    #[test]
    fn conflict_lemmas_recurse_through_the_graph_literal() {
        let mut tm = TermManager::new();
        let (statement, edges, reach, _) = triangle(&mut tm);
        let false_term = tm.mk_bool(false);
        // Guards force reach(0,2) while the premises also claim ¬reach(0,2):
        // contradictory, so the conflict lemma checks.
        assert!(
            statement
                .check_lemma(false_term, &[edges[0], edges[1], tm.mk_not(reach[0])])
                .is_ok()
        );
        // Without the graph literal there is nothing to contradict.
        assert!(
            statement
                .check_lemma(false_term, &[edges[0], edges[1]])
                .is_err()
        );
        // A consistent set must not check.
        assert!(
            statement
                .check_lemma(false_term, &[edges[0], tm.mk_not(reach[0])])
                .is_err()
        );
    }

    #[test]
    fn foreign_conclusions_and_statements_rejected() {
        let mut tm = TermManager::new();
        let (statement, edges, _, _) = triangle(&mut tm);
        let foreign = tm.mk_var("zzz", tm.sorts.bool_sort);
        assert!(statement.check_lemma(foreign, &[]).is_err());
        assert!(statement.check_lemma(tm.mk_bool(true), &edges).is_err());
        // Identity: a rebuilt-but-different statement cannot authenticate.
        let certificate = GraphCertificate::new(statement.clone());
        let mut tm2 = TermManager::new();
        let (other, other_edges, _, _) = triangle(&mut tm2);
        let _ = other_edges;
        assert!(!certificate.is_for(&other));
        assert!(certificate.check(&other, foreign, &[]).is_err());
        assert!(certificate.is_for(&statement));
    }

    #[test]
    fn model_checking_matches_closures() {
        let mut tm = TermManager::new();
        let (statement, edges, reach, acyclic) = triangle(&mut tm);
        // All edges present: 0 reaches 2 and itself; cyclic.
        let all = [true, true, true, true];
        let value = |t: TermId, vals: &[bool; 4]| -> Option<bool> {
            edges
                .iter()
                .position(|&e| e == t)
                .map(|i| vals[i])
                .or(match () {
                    _ if t == reach[0] => Some(vals[0] && vals[1] || vals[3]),
                    _ if t == reach[1] => Some(vals[0] && vals[1] && vals[2]),
                    _ if t == acyclic => Some(!(vals[0] && vals[1] && vals[2])),
                    _ => None,
                })
        };
        assert!(statement.check_model(&|t| value(t, &all)).is_ok());
        // A wrong reach value fails.
        let mut wrong = |t: TermId| -> Option<bool> {
            match () {
                _ if t == reach[0] => Some(false),
                _ => value(t, &all),
            }
        };
        let _ = &mut wrong;
        assert!(statement.check_model(&wrong).is_err());
        // An unknown edge value fails closed.
        let unknown = |t: TermId| -> Option<bool> {
            match () {
                _ if t == edges[3] => None,
                _ => value(t, &all),
            }
        };
        assert!(statement.check_model(&unknown).is_err());
        // Chord only: acyclic, 0 reaches 2 but not itself.
        let chord = [false, false, false, true];
        assert!(statement.check_model(&|t| value(t, &chord)).is_ok());
    }
}
