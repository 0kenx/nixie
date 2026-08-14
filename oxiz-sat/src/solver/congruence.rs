//! Gate-based congruence closure (AND / XOR).
//!
//! A *gate* defines an output literal in terms of inputs:
//!
//! - AND: `o ↔ (a ∧ b)` ⇔ clauses `(¬a ∨ ¬b ∨ o)`, `(¬o ∨ a)`, `(¬o ∨ b)`
//! - XOR: `o ↔ (a ⊕ b)` ⇔ `(¬o ∨ a ∨ b)`, `(¬o ∨ ¬a ∨ ¬b)`, `(o ∨ ¬a ∨ b)`, `(o ∨ a ∨ ¬b)`
//!
//! Two gates of the same type over (congruent) inputs are *congruent* and their
//! outputs are equivalent. This is the structural reasoning that collapses
//! multiplier / adder circuits: the partial-product AND gates and the
//! full-adder XOR gates have many congruent copies whose outputs can be merged.
//!
//! We detect gates from the clause patterns, run a union-find congruence
//! closure to a fixpoint (re-canonicalizing each gate's inputs through the
//! union-find after every merge, so equivalences propagate through nested
//! gates – the step a one-shot pairwise scan misses), and add binary
//! implication edges between equivalent outputs. The existing SCC pass then
//! folds them into the substitution.

use super::*;
use crate::literal::LBool;
use rustc_hash::FxHashMap;

#[derive(Clone, Copy, PartialEq, Eq, Hash)]
enum GateType {
    And,
    Xor,
}

struct Gate {
    ty: GateType,
    in1: Lit,
    in2: Lit,
    out: Lit,
}

/// Signed union-find over literal codes (`pos(v)=2v`, `neg(v)=2v+1`). Unioning
/// two literals also unions their negations, keeping equivalence
/// polarity-consistent.
struct SignedUf {
    parent: Vec<u32>,
}
impl SignedUf {
    fn new(num_lits: usize) -> Self {
        Self {
            parent: (0..num_lits as u32).collect(),
        }
    }
    fn find(&mut self, mut x: u32) -> u32 {
        let mut root = x;
        while self.parent[root as usize] != root {
            root = self.parent[root as usize];
        }
        while self.parent[x as usize] != root {
            let nxt = self.parent[x as usize];
            self.parent[x as usize] = root;
            x = nxt;
        }
        root
    }
    /// Union `a` ≡ `b` and `¬a` ≡ `¬b`.
    fn union(&mut self, a: u32, b: u32) -> bool {
        let pa = self.find(a);
        let pb = self.find(b);
        if pa == pb {
            return false;
        }
        self.parent[pa as usize] = pb;
        // keep the negation symmetric
        let na = a ^ 1;
        let nb = b ^ 1;
        let pna = self.find(na);
        let pnb = self.find(nb);
        if pna != pnb {
            self.parent[pna as usize] = pnb;
        }
        true
    }
}

impl Solver {
    /// Detect AND/XOR gates, run congruence closure to a fixpoint, and add a
    /// binary implication edge between every pair of equivalent gate outputs so
    /// the subsequent SCC folds them in. Idempotent on the binary graph (adds
    /// only edges; the caller rebuilds the graph later).
    pub(super) fn augment_big_with_gate_congruence(&mut self) {
        let num_vars = self.num_vars;
        if num_vars == 0 {
            return;
        }
        let gates = self.detect_gates();
        if gates.len() < 2 {
            return;
        }

        let num_lits = num_vars * 2;
        let mut uf = SignedUf::new(num_lits);

        // Fixpoint: re-canonicalize every gate's inputs through the union-find,
        // group by (type, canonical inputs), and merge the outputs of any group
        // with more than one member. Repeat until no new merge.
        loop {
            // sig -> first output literal (code); track collisions.
            let mut first: FxHashMap<(GateType, u32, u32), u32> = FxHashMap::default();
            let mut merged_any = false;
            for g in &gates {
                let i1 = uf.find(g.in1.code());
                let i2 = uf.find(g.in2.code());
                let sig = if i1 <= i2 {
                    (g.ty, i1, i2)
                } else {
                    (g.ty, i2, i1)
                };
                if let Some(&prev) = first.get(&sig) {
                    if uf.find(prev) != uf.find(g.out.code()) && uf.union(prev, g.out.code()) {
                        merged_any = true;
                    }
                } else {
                    first.insert(sig, g.out.code());
                }
            }
            if !merged_any {
                break;
            }
        }

        // Materialize the equivalence classes and add binary implication edges
        // between class members so SCC merges them. Group outputs by find root.
        let mut classes: FxHashMap<u32, Vec<u32>> = FxHashMap::default();
        for g in &gates {
            let r = uf.find(g.out.code());
            classes.entry(r).or_default().push(g.out.code());
        }
        let sentinel = ClauseId::new(u32::MAX);
        for members in classes.values() {
            if members.len() < 2 {
                continue;
            }
            // chain consecutive members: o0 ≡ o1 ≡ o2 ...  (transitive via SCC)
            for w in members.windows(2) {
                let a = Lit::from_code(w[0]);
                let b = Lit::from_code(w[1]);
                if a.var() == b.var() {
                    continue;
                }
                self.binary_graph.add(a, b, sentinel);
                self.binary_graph.add(b, a, sentinel);
                self.binary_graph.add(a.negate(), b.negate(), sentinel);
                self.binary_graph.add(b.negate(), a.negate(), sentinel);
            }
        }
        let _ = LBool::Undef; // keep import used
    }

    /// Detect AND and XOR gates from the clause set. Sound: a gate is recorded
    /// only when its defining clauses are all present, so the gate equivalence
    /// is entailed regardless of whether it is a "real" gate.
    fn detect_gates(&self) -> Vec<Gate> {
        let mut gates: Vec<Gate> = Vec::new();

        // Ternary clauses indexed by the variables they contain (for XOR
        // lookup) and scanned directly for AND.
        let mut ternary: Vec<SmallVec<[Lit; 3]>> = Vec::new();
        for cid in self.clauses.iter_ids() {
            let Some(c) = self.clauses.get(cid) else {
                continue;
            };
            if c.deleted || c.lits.len() != 3 {
                continue;
            }
            ternary.push(c.lits.iter().copied().collect());
        }

        // ---- AND gates: for each ternary clause, each literal is a candidate
        // output; the other two (negated) are inputs, verified by the two
        // binary implications o→a, o→b. ----
        for lits in &ternary {
            for i in 0..3 {
                let o = lits[i];
                let a = lits[(i + 1) % 3].negate();
                let b = lits[(i + 2) % 3].negate();
                if a.var() == o.var() || b.var() == o.var() || a.var() == b.var() {
                    continue;
                }
                if self.has_binary_implication(o, a) && self.has_binary_implication(o, b) {
                    gates.push(Gate {
                        ty: GateType::And,
                        in1: a,
                        in2: b,
                        out: o,
                    });
                    break; // one gate per ternary clause
                }
            }
        }

        // ---- XOR gates: o ↔ a⊕b needs all four ternary clauses. Index them by
        // the (signed) multiset of literals for fast lookup. ----
        let mut ternary_set: FxHashMap<(u32, u32, u32), ()> = FxHashMap::default();
        for lits in &ternary {
            let mut c: [u32; 3] = [lits[0].code(), lits[1].code(), lits[2].code()];
            c.sort_unstable();
            ternary_set.insert((c[0], c[1], c[2]), ());
        }
        let has_ternary = |a: Lit, b: Lit, c: Lit, ts: &FxHashMap<(u32, u32, u32), ()>| -> bool {
            let mut k = [a.code(), b.code(), c.code()];
            k.sort_unstable();
            ts.contains_key(&(k[0], k[1], k[2]))
        };
        for lits in &ternary {
            // Try each literal as the output o; the other two are a candidate
            // (a, b). Verify the four XOR clauses are all present.
            for i in 0..3 {
                let o = lits[i];
                let a = lits[(i + 1) % 3];
                let b = lits[(i + 2) % 3];
                if a.var() == o.var() || b.var() == o.var() || a.var() == b.var() {
                    continue;
                }
                // one of the four clauses is the current `lits`; check the
                // other three. The four forms (modulo a/b swap):
                //   (¬o∨a∨b), (¬o∨¬a∨¬b), (o∨¬a∨b), (o∨a∨¬b)
                let forms = [
                    (o.negate(), a, b),
                    (o.negate(), a.negate(), b.negate()),
                    (o, a.negate(), b),
                    (o, a, b.negate()),
                ];
                if forms
                    .iter()
                    .all(|&(x, y, z)| has_ternary(x, y, z, &ternary_set))
                {
                    gates.push(Gate {
                        ty: GateType::Xor,
                        in1: a,
                        in2: b,
                        out: o,
                    });
                    break;
                }
            }
        }

        gates
    }
}
