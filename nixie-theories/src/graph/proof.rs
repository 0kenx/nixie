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
    /// `(from, to)` per edge, packed back to back for the witness checks'
    /// edge scans — the full 16-byte tuples interleave the atom/negation
    /// payload the scans never touch, doubling their cache footprint.
    /// Behind an `Arc` so statement clones stay O(1). A pure function of
    /// `edges`, keeping derived `PartialEq` consistent.
    endpoints: Arc<[(u32, u32)]>,
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
/// graph declaration. The witness names the statement and carries an
/// explicit justification structure the checker verifies directly —
/// **no search, no closure recomputation** (the certificate path runs per
/// emitted consequence inside the CDCL loop, so it must be linear in the
/// witness; the recompute-based [`GraphStatement::check_lemma`] remains
/// the cold-boundary checker for recorded proof lemmas, where no witness
/// is available).
#[derive(Debug, Clone)]
pub enum GraphRule {
    /// `reach(from, to)` witnessed by an explicit edge-index walk: the
    /// first edge leaves `from`, each edge's head is the next one's tail,
    /// the last head is `to`, and every walked edge's presence atom is a
    /// premise. A closed walk (last head == from == to) witnesses the
    /// self-pair cycle reading.
    Path {
        /// Walk source vertex.
        from: u32,
        /// Walk target vertex.
        to: u32,
        /// Edge indices, in walk order.
        edges: Vec<u32>,
    },
    /// `¬reach(from, to)` witnessed by a successor-closed vertex set
    /// `closed`: `from ∈ closed`, `to ∉ closed`, and every edge whose
    /// tail is in `closed` while its head is not has its negation among
    /// the premises — so no premise-true edge leaves the set, and
    /// nothing reachable from `from` escapes it. The set is carried as a
    /// **membership bitmap** (vertex `v` ∈ closed ⇔ bit `v` set), shared
    /// by every rule the emitting memo produces: the emitting closure
    /// computes it once per lifetime as the packed complement of its
    /// `seen` array, and the per-consequence check then runs pure bit
    /// tests — no set materialization on the checking path at all.
    Cut {
        /// Separated source vertex.
        from: u32,
        /// Separated target vertex.
        to: u32,
        /// The closed vertex set as a membership bitmap (`vertices` bits).
        closed: Arc<[u64]>,
    },
    /// `¬acyclic` witnessed by an explicit directed cycle of edge
    /// indices, every walked edge's presence atom a premise.
    Cycle {
        /// Edge indices, in cycle order.
        edges: Vec<u32>,
    },
    /// `acyclic` witnessed by a topological order of the vertices: a
    /// permutation where every non-refuted edge ascends. Checking is
    /// O(vertices + edges) with O(1) work per edge — no search, no
    /// closure. (The all-edges-refuted form is the degenerate order.)
    TopoOrder {
        /// A permutation of all vertex indices.
        order: Vec<u32>,
    },
    /// `¬reach(v, v)` (the self-pair cycle reading) witnessed by the
    /// ≥1-step forward closure `closed` of `v` over non-refuted edges:
    /// `v ∉ closed`, and every non-refuted edge whose tail is in
    /// `closed ∪ {v}` has its head in `closed`. By induction `closed`
    /// contains every vertex reachable from `v` in ≥1 steps, so `v ∉
    /// closed` means no cycle through `v`. (A separating set cannot
    /// witness the self-pair — `v` would have to be on both sides.)
    NoCycleThrough {
        /// The vertex the cycle must pass through.
        v: u32,
        /// The ≥1-step forward closure as a membership bitmap
        /// (`vertices` bits).
        closed: Arc<[u64]>,
    },
}

/// A consequence's graph witness: the statement it refers to plus the
/// rule structure. Constructed by the propagator at emission (from data
/// its search already produced) and verified in linear time.
#[derive(Debug, Clone)]
pub struct GraphCertificate {
    statement: GraphStatement,
    rule: GraphRule,
}

impl GraphCertificate {
    /// Construct an untrusted witness; call `check` before accepting it.
    #[must_use]
    pub fn new(statement: GraphStatement, rule: GraphRule) -> Self {
        Self { statement, rule }
    }

    /// Referenced statement, which a consumer must authenticate independently.
    #[must_use]
    pub fn statement(&self) -> &GraphStatement {
        &self.statement
    }

    /// The witness structure (for introspection and tests).
    #[must_use]
    pub fn rule(&self) -> &GraphRule {
        &self.rule
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
        // A conflict (`false` concluded) recurses through its graph
        // literal: the premises include the offending literal, whose
        // opposite the rest must imply. Edge literals never collide with
        // graph literals, so the premise sets below are unaffected by the
        // substitution.
        let (conclusion, premises) = if conclusion == self.statement.false_term {
            let mut literal = None;
            let rest: Vec<TermId> = premises
                .iter()
                .copied()
                .filter(|&p| {
                    if self.statement.is_graph_literal(p) && literal.is_none() {
                        literal = Some(p);
                        false
                    } else {
                        true
                    }
                })
                .collect();
            let opposite = literal
                .and_then(|l| self.statement.negation_of(l))
                .ok_or(GraphProofError("conflict premise cites no graph literal"))?;
            (opposite, rest)
        } else {
            (conclusion, premises.to_vec())
        };
        // One premise-membership set; edges are classified individually
        // (a term may be one edge's atom AND another's negation when a
        // model uses `g` and `¬g` as guards, so a global atom/negation
        // partition would misfile it).
        let premise_set: FxHashSet<TermId> = premises.iter().copied().collect();
        let edges = self.statement.edges();
        let in_range = |i: u32| -> Result<usize, GraphProofError> {
            usize::try_from(i)
                .ok()
                .filter(|&i| i < edges.len())
                .ok_or(GraphProofError("witness cites an unknown edge"))
        };
        match &self.rule {
            GraphRule::Path {
                from,
                to,
                edges: walked,
            } => {
                let (want_from, want_to, _) = self.statement.reach_pair_of(conclusion)?;
                if *from != want_from || *to != want_to || walked.is_empty() {
                    return Err(GraphProofError("path witness endpoints mismatch"));
                }
                let mut at = *from;
                for &i in walked {
                    let e = edges[in_range(i)?];
                    if e.0 != at {
                        return Err(GraphProofError("path witness walk is broken"));
                    }
                    if !premise_set.contains(&e.2) {
                        return Err(GraphProofError(
                            "path witness edge is not a positive premise",
                        ));
                    }
                    at = e.1;
                }
                if at != *to {
                    return Err(GraphProofError("path witness does not arrive"));
                }
                Ok(())
            }
            GraphRule::Cut { from, to, closed } => {
                let (want_from, want_to, _) = self.statement.reach_pair_of_negation(conclusion)?;
                if *from != want_from || *to != want_to {
                    return Err(GraphProofError("cut witness endpoints mismatch"));
                }
                // The witness bitmap is used as-is (pure bit tests; no set
                // materialization on the checking path — this check runs
                // per emitted consequence, and over product-scale statements
                // both hash sets and per-check fills dominated certificate
                // checking). Endpoints come from the statement's packed
                // (from, to) array — half the cache footprint of the full
                // edge tuples — and only actual crossing edges touch the
                // atom/negation payload.
                let bits = closed;
                if bits.len() != self.statement.vertices_count().div_ceil(64) {
                    return Err(GraphProofError("cut witness bitmap is mis-sized"));
                }
                if !bit_get(bits, *from) || bit_get(bits, *to) {
                    return Err(GraphProofError(
                        "cut witness set does not separate the pair",
                    ));
                }
                let endpoints = self.statement.endpoints();
                for (i, &(from_e, to_e)) in endpoints.iter().enumerate() {
                    // A crossing edge has its tail in the set and its head
                    // outside; every crossing edge must be premise-refuted.
                    if bit_get(bits, from_e)
                        && !bit_get(bits, to_e)
                        && !premise_set.contains(&self.statement.edges[i].3)
                    {
                        return Err(GraphProofError(
                            "cut witness set is crossed by an unrefuted edge",
                        ));
                    }
                }
                Ok(())
            }
            GraphRule::Cycle { edges: walked } => {
                let (atom, negation) = self.statement.acyclic_pair_of(conclusion)?;
                let _ = atom;
                if conclusion != negation || walked.is_empty() {
                    return Err(GraphProofError(
                        "cycle witness must conclude the acyclicity negation",
                    ));
                }
                let start = edges[in_range(walked[0])?].0;
                let mut at = start;
                for &i in walked {
                    let e = edges[in_range(i)?];
                    if e.0 != at || !premise_set.contains(&e.2) {
                        return Err(GraphProofError("cycle witness is broken"));
                    }
                    at = e.1;
                }
                if at != start {
                    return Err(GraphProofError("cycle witness does not close"));
                }
                Ok(())
            }
            GraphRule::NoCycleThrough { v, closed } => {
                let (want_v, want_v2, _) = self.statement.reach_pair_of_negation(conclusion)?;
                if *v != want_v || want_v != want_v2 {
                    return Err(GraphProofError(
                        "no-cycle witness must conclude a self-pair negation",
                    ));
                }
                let bits = closed;
                if bits.len() != self.statement.vertices_count().div_ceil(64) {
                    return Err(GraphProofError("no-cycle witness bitmap is mis-sized"));
                }
                if bit_get(bits, *v) {
                    return Err(GraphProofError("no-cycle witness set contains the vertex"));
                }
                // The region whose leaving edges must be premise-refuted is
                // `closed ∪ {v}` (the `v` bit is tested inline — no copy of
                // the shared witness).
                let endpoints = self.statement.endpoints();
                for (i, &(from_e, to_e)) in endpoints.iter().enumerate() {
                    if (bit_get(bits, from_e) || from_e == *v)
                        && !bit_get(bits, to_e)
                        && !premise_set.contains(&self.statement.edges[i].3)
                    {
                        return Err(GraphProofError(
                            "no-cycle witness is left by an unrefuted edge",
                        ));
                    }
                }
                Ok(())
            }
            GraphRule::TopoOrder { order } => {
                let (atom, _) = self.statement.acyclic_pair_of(conclusion)?;
                if conclusion != atom {
                    return Err(GraphProofError(
                        "topological witness must conclude acyclicity",
                    ));
                }
                let vertices = self.statement.vertices_count();
                if order.len() != vertices || {
                    let mut seen = vec![false; vertices];
                    let mut ok = true;
                    for &v in order {
                        if v as usize >= vertices || seen[v as usize] {
                            ok = false;
                            break;
                        }
                        seen[v as usize] = true;
                    }
                    !ok
                } {
                    return Err(GraphProofError(
                        "topological witness is not a vertex permutation",
                    ));
                }
                let mut rank = vec![0u32; vertices];
                for (r, &v) in order.iter().enumerate() {
                    rank[v as usize] = r as u32;
                }
                for &(from_e, to_e, _, negation) in edges {
                    if !premise_set.contains(&negation)
                        && rank[from_e as usize] >= rank[to_e as usize]
                    {
                        return Err(GraphProofError(
                            "a non-refuted edge descends the topological order",
                        ));
                    }
                }
                Ok(())
            }
        }
    }
}

/// Membership test against a packed witness bitmap.
fn bit_get(bits: &[u64], v: u32) -> bool {
    let idx = v as usize;
    bits.get(idx / 64)
        .is_some_and(|word| word >> (idx % 64) & 1 == 1)
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
            endpoints: Arc::from(
                edges
                    .iter()
                    .map(|&(from, to, _, _)| (from, to))
                    .collect::<Vec<_>>()
                    .as_slice(),
            ),
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

    /// The declaration's edge endpoints as packed `(from, to)` pairs, in
    /// edge order (the witness checks' scan view).
    #[must_use]
    pub fn endpoints(&self) -> &[(u32, u32)] {
        &self.endpoints
    }

    /// The declaration's reified reach atoms as `(from, to, atom, negation)`.
    #[must_use]
    pub fn reach_atoms(&self) -> &[(u32, u32, TermId, TermId)] {
        &self.reach
    }

    /// The `(from, to)` pair of the reach atom `conclusion`, if it is one.
    fn reach_pair_of(&self, conclusion: TermId) -> Result<(u32, u32, TermId), GraphProofError> {
        self.reach
            .iter()
            .find(|&&(_, _, atom, _)| atom == conclusion)
            .map(|&(f, t, atom, _)| (f, t, atom))
            .ok_or(GraphProofError("conclusion is not a reach atom"))
    }

    /// The `(from, to)` pair whose **negation** is `conclusion`.
    fn reach_pair_of_negation(
        &self,
        conclusion: TermId,
    ) -> Result<(u32, u32, TermId), GraphProofError> {
        self.reach
            .iter()
            .find(|&&(_, _, _, negation)| negation == conclusion)
            .map(|&(f, t, _, negation)| (f, t, negation))
            .ok_or(GraphProofError("conclusion is not a reach negation"))
    }

    /// The acyclicity `(atom, negation)` pair, if declared.
    fn acyclic_pair_of(&self, conclusion: TermId) -> Result<(TermId, TermId), GraphProofError> {
        self.acyclic
            .ok_or(GraphProofError("no acyclicity atom declared"))
            .and_then(|pair| {
                if pair.0 == conclusion || pair.1 == conclusion {
                    Ok(pair)
                } else {
                    Err(GraphProofError("conclusion is not the acyclicity literal"))
                }
            })
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

    /// Is `term` a reach or acyclicity literal of this statement?
    #[must_use]
    fn is_graph_literal(&self, term: TermId) -> bool {
        self.reach
            .iter()
            .any(|&(_, _, atom, negation)| atom == term || negation == term)
            || self
                .acyclic
                .is_some_and(|(atom, negation)| atom == term || negation == term)
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

    /// Pack a membership bitmap for a test witness (mirrors the
    /// propagator's emission-side packer).
    fn proof_test_bits(vertices: usize, members: &[u32]) -> Arc<[u64]> {
        let mut bits = vec![0u64; vertices.div_ceil(64)];
        for &v in members {
            bits[v as usize / 64] |= 1 << (v % 64);
        }
        bits.into()
    }

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
        // The rule is irrelevant for the identity check; carry a valid one.
        let certificate = GraphCertificate::new(
            statement.clone(),
            GraphRule::TopoOrder {
                order: vec![0, 1, 2],
            },
        );
        let mut tm2 = TermManager::new();
        let (other, other_edges, _, _) = triangle(&mut tm2);
        let _ = other_edges;
        assert!(!certificate.is_for(&other));
        assert!(certificate.check(&other, foreign, &[]).is_err());
        assert!(certificate.is_for(&statement));
    }

    /// Witness-level checks: valid paths/cuts/cycles verify; broken walks,
    /// non-separating or crossed cut sets, wrong endpoints and missing
    /// premises are rejected. (The recompute-based `check_lemma` tests
    /// above remain the semantic oracle; these pin the hot-path checker.)
    #[test]
    fn witness_rules_check_exactly() {
        let mut tm = TermManager::new();
        let (statement, edges, reach, acyclic) = triangle(&mut tm);
        // Edge indices: e01=0, e12=1, e20=2, e02=3.
        // Valid path 0->2 via the chord.
        let cert = GraphCertificate::new(
            statement.clone(),
            GraphRule::Path {
                from: 0,
                to: 2,
                edges: vec![3],
            },
        );
        assert!(cert.check(&statement, reach[0], &[edges[3]]).is_ok());
        // Same walk, missing premise.
        assert!(cert.check(&statement, reach[0], &[]).is_err());
        // Broken walk (edge does not start at 0).
        let cert = GraphCertificate::new(
            statement.clone(),
            GraphRule::Path {
                from: 0,
                to: 2,
                edges: vec![1],
            },
        );
        assert!(cert.check(&statement, reach[0], &[edges[1]]).is_err());
        // Wrong endpoint pair.
        let cert = GraphCertificate::new(
            statement.clone(),
            GraphRule::Path {
                from: 1,
                to: 2,
                edges: vec![1],
            },
        );
        assert!(cert.check(&statement, reach[0], &[edges[1]]).is_err());
        // Valid self-pair cycle witness 0->1->2->0.
        let cert = GraphCertificate::new(
            statement.clone(),
            GraphRule::Path {
                from: 0,
                to: 0,
                edges: vec![0, 1, 2],
            },
        );
        assert!(
            cert.check(&statement, reach[1], &[edges[0], edges[1], edges[2]])
                .is_ok()
        );

        // Cut: S = {1,2} separates 1 from 0 when e12(1) and e20(2) are
        // refuted... use the complement form: ¬reach(0,2) with closed={1}
        // requires every crossing edge refuted: crossings are e01 (0->1)
        // and e12 (1->2).
        let cert = GraphCertificate::new(
            statement.clone(),
            GraphRule::Cut {
                from: 0,
                to: 2,
                closed: proof_test_bits(2, &[0, 1]),
            },
        );
        let not_reach02 = tm.mk_not(reach[0]);
        // e12 and e02 refuted: nothing leaves {0,1} toward 2.
        assert!(
            cert.check(
                &statement,
                not_reach02,
                &[tm.mk_not(edges[1]), tm.mk_not(edges[3])],
            )
            .is_ok()
        );
        // Unrefuted chord crosses the set.
        assert!(
            cert.check(&statement, not_reach02, &[tm.mk_not(edges[1])])
                .is_err()
        );
        // A set containing the target does not separate.
        let cert = GraphCertificate::new(
            statement.clone(),
            GraphRule::Cut {
                from: 0,
                to: 2,
                closed: proof_test_bits(3, &[0, 1, 2]),
            },
        );
        assert!(
            cert.check(
                &statement,
                not_reach02,
                &[tm.mk_not(edges[1]), tm.mk_not(edges[3])],
            )
            .is_err()
        );

        // Cycle witness for ¬acyclic: the directed triangle.
        let cert = GraphCertificate::new(
            statement.clone(),
            GraphRule::Cycle {
                edges: vec![0, 1, 2],
            },
        );
        let not_acy = tm.mk_not(acyclic);
        assert!(
            cert.check(&statement, not_acy, &[edges[0], edges[1], edges[2]])
                .is_ok()
        );
        assert!(
            cert.check(&statement, not_acy, &[edges[0], edges[1]])
                .is_err()
        );
        // TopoOrder for acyclic: order 0,1,2 with every non-refuted edge
        // ascending; refuting the cycle edges e20 (2->0) and e12 (1->2)
        // leaves e01 (0->1) and e02 (0->2), both ascending 0<1, 0<2.
        let cert = GraphCertificate::new(
            statement.clone(),
            GraphRule::TopoOrder {
                order: vec![0, 1, 2],
            },
        );
        assert!(
            cert.check(
                &statement,
                acyclic,
                &[tm.mk_not(edges[1]), tm.mk_not(edges[2])],
            )
            .is_ok()
        );
        // Without refuting e20 (2->0): it descends the order -> reject.
        assert!(
            cert.check(&statement, acyclic, &[tm.mk_not(edges[1])])
                .is_err()
        );
        // A non-permutation witness is rejected.
        let cert = GraphCertificate::new(
            statement.clone(),
            GraphRule::TopoOrder { order: vec![0, 1] },
        );
        assert!(
            cert.check(
                &statement,
                acyclic,
                &[tm.mk_not(edges[1]), tm.mk_not(edges[2])]
            )
            .is_err()
        );

        // Conflict recursion: premises contain the offending literal.
        let false_term = tm.mk_bool(false);
        let cert = GraphCertificate::new(
            statement.clone(),
            GraphRule::Path {
                from: 0,
                to: 2,
                edges: vec![0, 1],
            },
        );
        // Guards force reach(0,2) while the premises claim ¬reach(0,2).
        assert!(
            cert.check(
                &statement,
                false_term,
                &[edges[0], edges[1], tm.mk_not(reach[0])],
            )
            .is_ok()
        );
        // Without a graph literal among the premises: rejected.
        assert!(
            cert.check(&statement, false_term, &[edges[0], edges[1]])
                .is_err()
        );
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
