//! AND/XOR gate congruence detection, feeding equivalent-literal substitution.
//!
//! A *gate* is a clause pattern that pins an "output" literal to a Boolean
//! function of two "input" literals:
//!
//! * AND: `o ↔ (a ∧ b)`, witnessed by the three clauses `(¬a ∨ ¬b ∨ o)`,
//!   `(¬o ∨ a)`, `(¬o ∨ b)` — the last two are binary implications, so
//!   detection only needs the ternary clause plus a binary-graph lookup.
//! * XOR: `o ↔ (a ⊕ b)`, witnessed by all four ternary clauses
//!   `(¬o ∨ a ∨ b)`, `(¬o ∨ ¬a ∨ ¬b)`, `(o ∨ ¬a ∨ b)`, `(o ∨ a ∨ ¬b)`.
//!
//! Two gates of the *same* kind whose inputs are already known-equivalent
//! (up to swapping `a`/`b`) must have equivalent outputs — that is the
//! congruence step. Circuits built from repeated substructure (a multiplier's
//! partial-product AND gates, an adder chain's XOR gates) contain many such
//! congruent pairs, and folding them is what lets equivalent-literal
//! substitution collapse that redundancy instead of treating every gate copy
//! as an independent variable.
//!
//! This module only *detects* gates and *derives* the resulting output
//! equivalences as extra binary-implication-graph edges; folding those edges
//! into a substitution is [`Solver::fold_equivalent_literals`]'s job
//! (in `solver/equiv.rs`), via the ordinary Tarjan SCC pass over the graph.
//! The edges added here carry [`ClauseId::NULL`] instead of a real backing
//! clause: they are a purely structural hint for that SCC walk, not something
//! [`Solver::propagate`] should ever treat as a live binary clause (its own
//! trust check already requires a real 2-literal clause behind an edge before
//! using it, so a `NULL`-tagged edge is silently — and correctly — ignored
//! there).

use super::*;
use rustc_hash::FxHashMap;

#[derive(Clone, Copy, PartialEq, Eq, Hash)]
enum GateKind {
    And,
    Xor,
}

struct Gate {
    kind: GateKind,
    input_a: Lit,
    input_b: Lit,
    output: Lit,
}

/// Union-find over literal codes (`0..2*num_vars`) that keeps a merge
/// polarity-consistent: unioning `a` with `b` also unions `¬a` with `¬b`, so
/// "these two literals are equivalent" and "their negations are equivalent"
/// can never be tracked as independent facts that later disagree.
struct PolarityUnionFind {
    parent: Vec<u32>,
}

impl PolarityUnionFind {
    fn new(num_lit_codes: usize) -> Self {
        Self {
            parent: (0..num_lit_codes as u32).collect(),
        }
    }

    fn find(&mut self, mut node: u32) -> u32 {
        while self.parent[node as usize] != node {
            // Path-halving: point each visited node at its grandparent so
            // repeated finds on the same chain flatten it over time, without
            // the extra pass a full path-compression rewrite would need.
            let grandparent = self.parent[self.parent[node as usize] as usize];
            self.parent[node as usize] = grandparent;
            node = grandparent;
        }
        node
    }

    /// Merge the classes of `a` and `b` (and, to keep polarity consistent,
    /// of `¬a` and `¬b`). Returns `true` if this changed anything.
    fn union(&mut self, a: u32, b: u32) -> bool {
        let root_a = self.find(a);
        let root_b = self.find(b);
        if root_a == root_b {
            return false;
        }
        self.parent[root_a as usize] = root_b;
        let neg_root_a = self.find(a ^ 1);
        let neg_root_b = self.find(b ^ 1);
        if neg_root_a != neg_root_b {
            self.parent[neg_root_a as usize] = neg_root_b;
        }
        true
    }
}

impl Solver {
    /// Detect AND/XOR gates, close them under congruence to a fixpoint, and
    /// add a binary-graph edge between every pair of literals the closure
    /// proved equivalent. A no-op when fewer than two gates are found (no
    /// pair can possibly be congruent). See the module doc for the intended
    /// consumer of the edges this adds.
    pub(super) fn extend_binary_graph_with_gate_congruence(&mut self) {
        if self.num_vars == 0 {
            return;
        }
        let gates = self.detect_gates();
        if gates.len() < 2 {
            return;
        }

        let mut uf = PolarityUnionFind::new(self.num_vars * 2);

        // Fixpoint: canonicalize every gate's inputs through the union-find,
        // group by (kind, canonical inputs), and merge the outputs of any
        // group with more than one member. A merge can change another gate's
        // input canonicalization on the next pass (nested gates), so this
        // repeats until nothing changes rather than doing a single scan.
        loop {
            let mut representative_output: FxHashMap<(GateKind, u32, u32), u32> =
                FxHashMap::default();
            let mut merged = false;
            for gate in &gates {
                let ca = uf.find(gate.input_a.code());
                let cb = uf.find(gate.input_b.code());
                let signature = if ca <= cb {
                    (gate.kind, ca, cb)
                } else {
                    (gate.kind, cb, ca)
                };
                match representative_output.get(&signature) {
                    Some(&existing_output) => {
                        if uf.union(existing_output, gate.output.code()) {
                            merged = true;
                        }
                    }
                    None => {
                        representative_output.insert(signature, gate.output.code());
                    }
                }
            }
            if !merged {
                break;
            }
        }

        // Materialize each equivalence class of gate outputs (by union-find
        // root) and chain its members together with binary-graph edges, so
        // the SCC pass that consumes this graph later (in
        // `Solver::fold_equivalent_literals`) merges along the cycle
        // this chain forms rather than needing every pairwise edge directly.
        //
        // Each member is chained to the *previously emitted* member, not
        // simply the previous element of the (arbitrarily ordered) list:
        // that distinction matters because one case is skipped outright —
        // two entries that are the exact same literal code (congruence
        // re-proving a literal equivalent to itself carries no new
        // information) — and chaining to "the previous list element"
        // regardless would silently break the chain into two disconnected
        // pieces right there, losing connectivity for every member after
        // the skip. Chaining to "the previous *emitted* member" instead
        // means a skip just leaves the anchor where it was, so the next
        // member still links back to a real, already-connected node.
        //
        // A same-*variable*, opposite-polarity pair (`v` and `¬v`) is
        // deliberately **not** skipped: congruence proving those two
        // equivalent is an unconditional contradiction, and this chain is
        // the only place that fact can reach the SCC pass at all — its own
        // self-negation check only fires for literals already in the same
        // component, which requires an edge between them to exist in the
        // first place. Emitting the same four `binary_graph.add` calls as
        // the general case here happens to produce exactly the two-cycle
        // (`v → ¬v` and `¬v → v`) that check needs.
        let mut classes: FxHashMap<u32, Vec<u32>> = FxHashMap::default();
        for gate in &gates {
            let root = uf.find(gate.output.code());
            classes.entry(root).or_default().push(gate.output.code());
        }
        for members in classes.values() {
            let mut anchor: Option<u32> = None;
            for &code in members {
                let Some(anchor_code) = anchor else {
                    anchor = Some(code);
                    continue;
                };
                if anchor_code == code {
                    continue; // Exact duplicate of the anchor: nothing to add.
                }
                let lit_anchor = Lit::from_code(anchor_code);
                let lit_member = Lit::from_code(code);
                self.binary_graph
                    .add(lit_anchor, lit_member, ClauseId::NULL);
                self.binary_graph
                    .add(lit_member, lit_anchor, ClauseId::NULL);
                self.binary_graph
                    .add(lit_anchor.negate(), lit_member.negate(), ClauseId::NULL);
                self.binary_graph
                    .add(lit_member.negate(), lit_anchor.negate(), ClauseId::NULL);
                anchor = Some(code);
            }
        }
    }

    /// Scan the live clause set for AND/XOR gate patterns. Every gate found
    /// is backed by clauses genuinely present in the database right now, so
    /// each one really is entailed by the formula regardless of whether it
    /// was placed there deliberately (a real encoder-emitted gate) or is
    /// coincidental — soundness never depends on authorial intent.
    fn detect_gates(&self) -> Vec<Gate> {
        let ternary_clauses: Vec<[Lit; 3]> = self
            .clauses
            .iter_ids()
            .filter_map(|id| self.clauses.get(id))
            .filter(|c| !c.deleted && c.lits.len() == 3)
            .map(|c| [c.lits[0], c.lits[1], c.lits[2]])
            .collect();

        let mut gates = Vec::new();
        gates.extend(self.detect_and_gates(&ternary_clauses));
        gates.extend(Self::detect_xor_gates(&ternary_clauses));
        gates
    }

    /// AND gates: for a ternary clause `(x0 ∨ x1 ∨ x2)`, each literal is a
    /// candidate output `o` with the other two negated as inputs `a`, `b`;
    /// the clause is exactly `(¬a ∨ ¬b ∨ o)`, so it only remains to confirm
    /// the two implication clauses `o → a` and `o → b` are also present.
    fn detect_and_gates(&self, ternary_clauses: &[[Lit; 3]]) -> Vec<Gate> {
        let mut gates = Vec::new();
        for lits in ternary_clauses {
            for i in 0..3 {
                let output = lits[i];
                let input_a = lits[(i + 1) % 3].negate();
                let input_b = lits[(i + 2) % 3].negate();
                if input_a.var() == output.var()
                    || input_b.var() == output.var()
                    || input_a.var() == input_b.var()
                {
                    continue;
                }
                if self.has_live_binary_implication(output, input_a)
                    && self.has_live_binary_implication(output, input_b)
                {
                    gates.push(Gate {
                        kind: GateKind::And,
                        input_a,
                        input_b,
                        output,
                    });
                    break; // one AND-gate reading per ternary clause is enough
                }
            }
        }
        gates
    }

    /// XOR gates: `o ↔ (a ⊕ b)` needs all four of `(¬o∨a∨b)`, `(¬o∨¬a∨¬b)`,
    /// `(o∨¬a∨b)`, `(o∨a∨¬b)` to be present as clauses. Indexes the ternary
    /// clauses by their sorted literal codes for an O(1) membership check per
    /// candidate instead of an O(n) scan.
    ///
    /// Each of those four clauses carries the three variables in a
    /// *different* relative polarity, so no single one of them hands back
    /// `o`, `a`, `b` all in their canonical positive form the way an AND
    /// gate's single defining clause does — candidates are therefore drawn
    /// from each ternary clause's three *variables*, always tested in their
    /// positive-literal form, rather than from the literals as stored in
    /// whichever clause happened to be scanned. (An earlier version of this
    /// function used the scanned literal's polarity directly and could
    /// silently miss every real XOR gate: with `a`/`b` positive-canonical
    /// fixed, `o`'s polarity is what actually needs checking, and the scanned
    /// clause's own literal for `o` is right for at most one of the four
    /// required clauses.)
    fn detect_xor_gates(ternary_clauses: &[[Lit; 3]]) -> Vec<Gate> {
        let mut present: FxHashMap<(u32, u32, u32), ()> = FxHashMap::default();
        for lits in ternary_clauses {
            present.insert(sorted_codes(lits[0], lits[1], lits[2]), ());
        }
        let has_clause = |a: Lit, b: Lit, c: Lit| present.contains_key(&sorted_codes(a, b, c));

        let mut gates = Vec::new();
        for lits in ternary_clauses {
            for i in 0..3 {
                let output = Lit::pos(lits[i].var());
                let input_a = Lit::pos(lits[(i + 1) % 3].var());
                let input_b = Lit::pos(lits[(i + 2) % 3].var());
                if input_a.var() == output.var()
                    || input_b.var() == output.var()
                    || input_a.var() == input_b.var()
                {
                    continue;
                }
                let all_present = has_clause(output.negate(), input_a, input_b)
                    && has_clause(output.negate(), input_a.negate(), input_b.negate())
                    && has_clause(output, input_a.negate(), input_b)
                    && has_clause(output, input_a, input_b.negate());
                if all_present {
                    gates.push(Gate {
                        kind: GateKind::Xor,
                        input_a,
                        input_b,
                        output,
                    });
                    break;
                }
            }
        }
        gates
    }
}

fn sorted_codes(a: Lit, b: Lit, c: Lit) -> (u32, u32, u32) {
    let mut codes = [a.code(), b.code(), c.code()];
    codes.sort_unstable();
    (codes[0], codes[1], codes[2])
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_pr26_gates_detects_and_gate() {
        // o <-> (a ∧ b): (¬a ∨ ¬b ∨ o), (¬o ∨ a), (¬o ∨ b)
        let mut solver = Solver::new();
        let a = solver.new_var();
        let b = solver.new_var();
        let o = solver.new_var();
        solver.add_clause([Lit::neg(a), Lit::neg(b), Lit::pos(o)]);
        solver.add_clause([Lit::neg(o), Lit::pos(a)]);
        solver.add_clause([Lit::neg(o), Lit::pos(b)]);

        let gates = solver.detect_gates();
        assert!(
            gates
                .iter()
                .any(|g| g.kind == GateKind::And && g.output == Lit::pos(o)),
            "expected an AND gate with output o"
        );
    }

    #[test]
    fn test_pr26_gates_detects_xor_gate() {
        // o <-> (a ⊕ b): all four defining ternary clauses. XOR is symmetric
        // among all three variables (o=a⊕b ⟺ a=o⊕b ⟺ b=o⊕a), so the same
        // four clauses admit more than one equally valid "output" reading;
        // what matters is that the gate found spans exactly {a, b, o}, not
        // which of the three the detector happened to label "output".
        let mut solver = Solver::new();
        let a = solver.new_var();
        let b = solver.new_var();
        let o = solver.new_var();
        solver.add_clause([Lit::neg(o), Lit::pos(a), Lit::pos(b)]);
        solver.add_clause([Lit::neg(o), Lit::neg(a), Lit::neg(b)]);
        solver.add_clause([Lit::pos(o), Lit::neg(a), Lit::pos(b)]);
        solver.add_clause([Lit::pos(o), Lit::pos(a), Lit::neg(b)]);

        let gates = solver.detect_gates();
        let expected: std::collections::BTreeSet<Var> = [a, b, o].into_iter().collect();
        assert!(
            gates.iter().any(|g| {
                g.kind == GateKind::Xor
                    && [g.output.var(), g.input_a.var(), g.input_b.var()]
                        .into_iter()
                        .collect::<std::collections::BTreeSet<Var>>()
                        == expected
            }),
            "expected an XOR gate spanning {{a, b, o}}, got {:?}",
            gates
                .iter()
                .map(|g| (g.output, g.input_a, g.input_b))
                .collect::<Vec<_>>()
        );
    }

    #[test]
    fn test_pr26_gates_congruence_merges_repeated_and_gates() {
        // Two independent AND gates o1 <-> (a ∧ b) and o2 <-> (a ∧ b) over the
        // *same* inputs must be recognised as congruent: o1 and o2 are forced
        // equivalent, so the augmented binary graph must connect them.
        let mut solver = Solver::new();
        let a = solver.new_var();
        let b = solver.new_var();
        let o1 = solver.new_var();
        let o2 = solver.new_var();
        for &o in &[o1, o2] {
            solver.add_clause([Lit::neg(a), Lit::neg(b), Lit::pos(o)]);
            solver.add_clause([Lit::neg(o), Lit::pos(a)]);
            solver.add_clause([Lit::neg(o), Lit::pos(b)]);
        }

        solver.extend_binary_graph_with_gate_congruence();
        assert!(
            solver.has_binary_implication(Lit::pos(o1), Lit::pos(o2))
                || solver.has_binary_implication(Lit::pos(o2), Lit::pos(o1)),
            "congruent AND gates must yield an equivalence edge between their outputs"
        );
    }

    #[test]
    fn test_pr26_gatekeeper_sk7_congruence_chain_stays_connected_through_a_same_var_pair() {
        // Two AND gates over *identical* inputs (p, q) force a1 ≡ a2 on the
        // very first fixpoint pass (their signatures match literally, no
        // merge needed first). Two more AND gates then each use one of
        // those two (now-equivalent) variables paired with a common third
        // input `b`, read with *opposite* output polarity (`v` vs `¬v`).
        // Once a1 ≡ a2 is folded in, those two gates canonicalize to the
        // same (kind, inputs) signature on the very same pass, so
        // congruence proves `v ≡ ¬v` — an unconditional contradiction with
        // no unit clause anywhere in this formula and nothing for plain
        // unit propagation alone to derive it from.
        //
        // Before the SK-7 fix, the resulting 2-member class {v, ¬v} chained
        // via `windows(2)` hit exactly this "same variable" pair and was
        // skipped outright with no edge added at all — the contradiction
        // never reached the binary graph, so the SCC pass in
        // `fold_equivalent_literals` had no way to discover it.
        let mut solver = Solver::with_config(SolverConfig {
            enable_gate_congruence: true,
            enable_equiv_substitution: true,
            ..SolverConfig::default()
        });
        let p = solver.new_var();
        let q = solver.new_var();
        let b = solver.new_var();
        let a1 = solver.new_var();
        let a2 = solver.new_var();
        let v = solver.new_var();

        solver.add_clause([Lit::neg(p), Lit::neg(q), Lit::pos(a1)]);
        solver.add_clause([Lit::neg(a1), Lit::pos(p)]);
        solver.add_clause([Lit::neg(a1), Lit::pos(q)]);

        solver.add_clause([Lit::neg(p), Lit::neg(q), Lit::pos(a2)]);
        solver.add_clause([Lit::neg(a2), Lit::pos(p)]);
        solver.add_clause([Lit::neg(a2), Lit::pos(q)]);

        solver.add_clause([Lit::neg(a1), Lit::neg(b), Lit::pos(v)]);
        solver.add_clause([Lit::neg(v), Lit::pos(a1)]);
        solver.add_clause([Lit::neg(v), Lit::pos(b)]);

        solver.add_clause([Lit::neg(a2), Lit::neg(b), Lit::neg(v)]);
        solver.add_clause([Lit::pos(v), Lit::pos(a2)]);
        solver.add_clause([Lit::pos(v), Lit::pos(b)]);

        solver.extend_binary_graph_with_gate_congruence();
        assert!(
            solver.has_binary_implication(Lit::pos(v), Lit::neg(v))
                && solver.has_binary_implication(Lit::neg(v), Lit::pos(v)),
            "congruence proving v equivalent to its own negation must reach \
             the binary graph as a two-cycle, not be silently dropped"
        );

        // End-to-end: the downstream SCC pass must actually catch this as
        // UNSAT, not just leave a dangling graph edge nothing reads.
        // `fold_equivalent_literals` runs gate congruence again
        // internally (its one-shot latch has not fired yet, since this is
        // its first call), which is redundant with the direct call above
        // but harmless -- re-adding the same edges changes nothing.
        let outcome = solver.fold_equivalent_literals();
        assert!(
            matches!(outcome, equiv::PreprocessOutcome::Unsat),
            "v ≡ ¬v proven via gate congruence must be caught as UNSAT"
        );
    }

    #[test]
    fn test_pr26_gates_no_spurious_edges_for_unrelated_gates() {
        // Two AND gates over *different* inputs are not congruent; no edge
        // should appear between their outputs.
        let mut solver = Solver::new();
        let a = solver.new_var();
        let b = solver.new_var();
        let c = solver.new_var();
        let d = solver.new_var();
        let o1 = solver.new_var();
        let o2 = solver.new_var();
        solver.add_clause([Lit::neg(a), Lit::neg(b), Lit::pos(o1)]);
        solver.add_clause([Lit::neg(o1), Lit::pos(a)]);
        solver.add_clause([Lit::neg(o1), Lit::pos(b)]);
        solver.add_clause([Lit::neg(c), Lit::neg(d), Lit::pos(o2)]);
        solver.add_clause([Lit::neg(o2), Lit::pos(c)]);
        solver.add_clause([Lit::neg(o2), Lit::pos(d)]);

        solver.extend_binary_graph_with_gate_congruence();
        assert!(
            !solver.has_binary_implication(Lit::pos(o1), Lit::pos(o2))
                && !solver.has_binary_implication(Lit::pos(o2), Lit::pos(o1)),
            "unrelated gates must not be merged"
        );
    }
}
