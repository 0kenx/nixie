//! Gate-based congruence closure (AND / XOR / ITE).
//!
//! A *gate* defines an output literal in terms of inputs:
//!
//! - AND: `o ↔ (a ∧ b)` ⇔ clauses `(¬a ∨ ¬b ∨ o)`, `(¬o ∨ a)`, `(¬o ∨ b)`
//! - XOR: `o ↔ (a ⊕ b)` ⇔ `(¬o ∨ a ∨ b)`, `(¬o ∨ ¬a ∨ ¬b)`, `(o ∨ ¬a ∨ b)`, `(o ∨ a ∨ ¬b)`
//! - ITE: `o ↔ (c ? t : e)` ⇔ `(¬o ∨ ¬c ∨ t)`, `(¬o ∨ c ∨ e)`,
//!   `(o ∨ ¬c ∨ ¬t)`, `(o ∨ c ∨ ¬e)`
//!
//! Two gates of the same type over (congruent) inputs are *congruent* and
//! their outputs are equivalent. This is the structural reasoning that
//! collapses multiplier / adder circuits: the partial-product AND gates and
//! the full-adder XOR gates have many congruent copies whose outputs can be
//! merged.
//!
//! We detect gates from the clause patterns, run a union-find congruence
//! closure to a fixpoint (re-canonicalizing each gate's inputs through the
//! union-find after every merge, so equivalences propagate through nested
//! gates – the step a one-shot pairwise scan misses), and add binary
//! implication edges between equivalent outputs. The existing SCC pass then
//! folds them into the substitution.
//!
//! ITE congruence (kissat `congruence.c`, landed 2026-09-18): two ITE gates
//! over congruent `(cond, then, else)` triples have equivalent outputs; a
//! gate whose triple is the *complement* (`(c, ¬t, ¬e)`) of another's has
//! the negated output.  `(c ? t : e) ≡ (¬c ? e : t)` — the then/else SWAP
//! with the cond flip, **not** an all-three negation (that is the
//! complement's swap form) — so each function has two presentations and the
//! canonical key takes the lexicographic minimum of the two.  The trivial
//! gate `c ? t : t` proves `o ≡ t` outright (direct union).

use super::*;
use crate::literal::LBool;
use rustc_hash::FxHashMap;

#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug)]
enum GateType {
    And,
    Xor,
    Ite,
}

struct Gate {
    ty: GateType,
    in1: Lit,
    in2: Lit,
    /// ITE only: `else` input (`in1` = cond, `in2` = then).
    in3: Lit,
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
    /// Detect AND/XOR/ITE gates, run congruence closure to a fixpoint, and add
    /// a binary implication edge between every pair of equivalent gate outputs
    /// so the subsequent SCC folds them in. Idempotent on the binary graph
    /// (adds only edges; the caller rebuilds the graph later).
    pub(super) fn augment_big_with_gate_congruence(&mut self) {
        let num_vars = self.num_vars;
        if num_vars == 0 {
            return;
        }
        let gates = self.detect_gates();
        #[cfg(feature = "std")]
        if super::learn::inproc_round_trace_enabled() {
            let (nand, nxor, nite) = gates.iter().fold((0, 0, 0), |(a, x, i), g| match g.ty {
                GateType::And => (a + 1, x, i),
                GateType::Xor => (a, x + 1, i),
                GateType::Ite => (a, x, i + 1),
            });
            eprintln!(
                "gate_congruence: ternary_scan_complete gates={} (and={nand} xor={nxor} ite={nite})",
                gates.len()
            );
        }
        if gates.len() < 2 {
            return;
        }

        let num_lits = num_vars * 2;
        let mut uf = SignedUf::new(num_lits);

        // Trivial ITE gates first: `o ↔ (c ? t : t)` proves `o ≡ t` outright,
        // so fold it into the union-find before (and independently of) the
        // signature congruence below (kissat `congruent_trivial_ite`).
        for g in &gates {
            if g.ty == GateType::Ite && g.in2 == g.in3 && g.out.var() != g.in2.var() {
                uf.union(g.out.code(), g.in2.code());
            }
        }

        // Fixpoint: re-canonicalize every gate's inputs through the union-find,
        // group by (type, canonical inputs), and merge the outputs of any group
        // with more than one member. Repeat until no new merge.
        loop {
            // sig -> first output literal (code); track collisions.
            let mut first: FxHashMap<(GateType, bool, u32, u32, u32), u32> = FxHashMap::default();
            let mut merged_any = false;
            for g in &gates {
                if g.ty == GateType::Ite && g.in2 == g.in3 {
                    continue; // folded in the trivial pre-pass
                }
                // Merge rules (f_G = the gate's function; P its canonical
                // positive triple, N its complement's):
                //  1. map[(false,P)] = outH  ⇒ f_H = f_G    ⇒ outH ≡ out
                //  2. map[(true,N)]  = ¬outH ⇒ ¬f_H = ¬f_G  ⇒ outH ≡ out
                //  3. map[(true,P)]  = ¬outH ⇒ ¬f_H = f_G   ⇒ out ≡ ¬outH
                //  4. map[(false,N)] = outH  ⇒ f_H = ¬f_G   ⇒ out ≡ ¬outH
                // Rules 3+4 are mirrors: without rule 4 a complementary pair
                // collides only when scanned in one of the two orders.
                let (key, neg_key, out) = match g.ty {
                    GateType::And => {
                        let i1 = uf.find(g.in1.code());
                        let i2 = uf.find(g.in2.code());
                        let key = if i1 <= i2 {
                            (GateType::And, false, i1, i2, u32::MAX)
                        } else {
                            (GateType::And, false, i2, i1, u32::MAX)
                        };
                        (
                            key,
                            (GateType::And, true, key.2, key.3, u32::MAX),
                            g.out.code(),
                        )
                    }
                    GateType::Xor => {
                        let i1 = uf.find(g.in1.code());
                        let i2 = uf.find(g.in2.code());
                        let key = if i1 <= i2 {
                            (GateType::Xor, false, i1, i2, u32::MAX)
                        } else {
                            (GateType::Xor, false, i2, i1, u32::MAX)
                        };
                        (
                            key,
                            (GateType::Xor, true, key.2, key.3, u32::MAX),
                            g.out.code(),
                        )
                    }
                    GateType::Ite => {
                        // Same function, two presentations:
                        //   (c, t, e) and (¬c, e, t) — then/else SWAP with the
                        //   cond flip (NOT an all-three negation).
                        let c = uf.find(g.in1.code());
                        let t = uf.find(g.in2.code());
                        let e = uf.find(g.in3.code());
                        let cn = uf.find(g.in1.negate().code());
                        let tn = uf.find(g.in2.negate().code());
                        let en = uf.find(g.in3.negate().code());
                        let pos = if (c, t, e) <= (cn, e, t) {
                            (c, t, e)
                        } else {
                            (cn, e, t)
                        };
                        // Complement function: (c, ¬t, ¬e) / (¬c, ¬e, ¬t) —
                        // here flipping all three IS correct (the complement's
                        // swap form negates every input).
                        let neg = if (c, tn, en) <= (cn, en, tn) {
                            (c, tn, en)
                        } else {
                            (cn, en, tn)
                        };
                        (
                            (GateType::Ite, false, pos.0, pos.1, pos.2),
                            (GateType::Ite, true, neg.0, neg.1, neg.2),
                            g.out.code(),
                        )
                    }
                };
                if let Some(&prev) = first.get(&key) {
                    if uf.find(prev) != uf.find(out) && uf.union(prev, out) {
                        merged_any = true;
                    }
                    continue;
                }
                if let Some(&prev) = first.get(&neg_key) {
                    // ¬f_H = ¬f_G ⇒ outH ≡ outG; entries store the negated
                    // output, so union the ¬-side (the same class).
                    if uf.find(prev) != uf.find(out ^ 1) && uf.union(prev, out ^ 1) {
                        merged_any = true;
                    }
                    continue;
                }
                if g.ty == GateType::Ite {
                    // Rule 3: our POSITIVE triple recorded as a complement.
                    if let Some(&prev) = first.get(&(GateType::Ite, true, key.2, key.3, key.4)) {
                        // prev = ¬outH with ¬f_H = f_G ⇒ out ≡ prev.
                        if uf.find(prev) != uf.find(out) && uf.union(prev, out) {
                            merged_any = true;
                        }
                        continue;
                    }
                    // Rule 4: our COMPLEMENT recorded as a positive function.
                    if let Some(&prev) =
                        first.get(&(GateType::Ite, false, neg_key.2, neg_key.3, neg_key.4))
                    {
                        // f_H = ¬f_G ⇒ outH ≡ ¬out.
                        if uf.find(prev) != uf.find(out ^ 1) && uf.union(prev, out ^ 1) {
                            merged_any = true;
                        }
                        continue;
                    }
                }
                first.insert(key, out);
                first.insert(neg_key, out ^ 1);
            }
            if !merged_any {
                break;
            }
        }

        // Materialize the equivalence classes and add binary implication edges
        // between class members so SCC merges them. Each named literal is
        // keyed by its OWN union-find root: a complementary merge (o2 ≡ ¬o1)
        // puts {o2, ¬o1} in one UF class and {¬o2, o1} in the mirror class —
        // keying by `find(out)` would mix the two and consecutive chaining
        // would then assert false equivalences (the 2026-09-18 Iter22
        // false-unsat, round two). Both polarities of every output are named
        // so complementary classes have ≥2 members; trivial-ITE merges name
        // their `then` literal for the same reason.
        let mut classes: FxHashMap<u32, Vec<u32>> = FxHashMap::default();
        let name = |uf: &mut SignedUf, classes: &mut FxHashMap<u32, Vec<u32>>, code: u32| {
            let r = uf.find(code);
            classes.entry(r).or_default().push(code);
        };
        for g in &gates {
            let o = g.out.code();
            name(&mut uf, &mut classes, o);
            name(&mut uf, &mut classes, o ^ 1);
            if g.ty == GateType::Ite && g.in2 == g.in3 && g.out.var() != g.in2.var() {
                let t = g.in2.code();
                name(&mut uf, &mut classes, t);
                name(&mut uf, &mut classes, t ^ 1);
            }
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

    /// Detect AND, XOR and ITE gates from the clause set. Sound: a gate is
    /// recorded only when its defining clauses are all present, so the gate
    /// equivalence is entailed regardless of whether it is a "real" gate.
    /// Gate count for the diagnostic accessor (keeps `Gate` private).
    pub(super) fn detect_gate_count(&self) -> usize {
        self.detect_gates().len()
    }

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
                        in3: a, // unused
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
                        in3: a, // unused
                        out: o,
                    });
                    break;
                }
            }
        }

        // ---- ITE gates: `o ↔ (c ? t : e)` needs all four ternary clauses
        // (kissat `extract_ite_gates_with_base_clause`).  With the base clause
        // C = (o ∨ ¬c ∨ ¬t), the others are
        //   A = (¬o ∨ ¬c ∨ t)
        //   B = (¬o ∨  c ∨ e)      (e unknown — discovered by the scan)
        //   D = ( o ∨  c ∨ ¬e)
        // Scan every clause containing the pair (o, c) as a candidate D: its
        // third literal is ¬e; B then verifies e.  Pair lookup uses a CSR
        // index over ternary clauses by literal. ----
        if !ternary.is_empty() {
            let num_lits = self.num_vars * 2;
            // CSR: literal code -> ternary-clause indices.
            let mut counts = vec![0u32; num_lits];
            for lits in &ternary {
                for &l in lits.iter() {
                    counts[l.code() as usize] += 1;
                }
            }
            let mut offsets = vec![0u32; num_lits + 1];
            let mut acc = 0u32;
            for i in 0..num_lits {
                offsets[i] = acc;
                acc += counts[i];
            }
            offsets[num_lits] = acc;
            let mut entries = vec![u32::MAX; acc as usize];
            let mut fill = offsets.clone();
            for (ti, lits) in ternary.iter().enumerate() {
                for &l in lits.iter() {
                    let c = l.code() as usize;
                    entries[fill[c] as usize] = ti as u32;
                    fill[c] += 1;
                }
            }
            let clauses_with = |l: Lit| -> &[u32] {
                let s = l.code() as usize;
                &entries[offsets[s] as usize..offsets[s + 1] as usize]
            };

            for lits in &ternary {
                // Output candidates: positive literals only — every ITE
                // definition has a presentation with a positive output (the
                // four clauses of `o ↔ f` are those of `¬o ↔ ¬f` with roles
                // swapped), so this loses no equivalence: the complement
                // relation is merged by the cross rule at closure time.
                for oi in 0..3 {
                    let o = lits[oi];
                    if !o.is_pos() {
                        continue;
                    }
                    // cond candidate: any other literal of the clause plays
                    // ¬cond in C; cond is its negation.
                    for ci in 0..3 {
                        if ci == oi {
                            continue;
                        }
                        let not_cond = lits[ci];
                        let cond = not_cond.negate();
                        let then_lit = lits[3 - oi - ci].negate();
                        if cond.var() == o.var()
                            || then_lit.var() == o.var()
                            || cond.var() == then_lit.var()
                        {
                            continue;
                        }
                        // A = (¬o ∨ ¬c ∨ t) must exist.
                        if !has_ternary(o.negate(), not_cond, then_lit, &ternary_set) {
                            continue;
                        }
                        // Candidates for D: clauses containing both o and
                        // cond.  Walk the shorter CSR side, test the other
                        // literal against the clause's three literals.
                        let a = clauses_with(o);
                        let b = clauses_with(cond);
                        let (outer, probe) = if a.len() <= b.len() {
                            (a, cond)
                        } else {
                            (b, o)
                        };
                        for &ti in outer {
                            let d = &ternary[ti as usize];
                            if !d.contains(&probe) {
                                continue;
                            }
                            // D contains both o and cond; third is ¬e.
                            let Some(&not_e) = d.iter().find(|&&l| l != o && l != cond) else {
                                continue;
                            };
                            let e = not_e.negate();
                            if e == then_lit.negate() {
                                continue; // XOR shape (kissat leaves it to XOR)
                            }
                            if e.var() == o.var() || e.var() == cond.var() {
                                continue;
                            }
                            // B = (¬o ∨ c ∨ e) must exist.
                            if has_ternary(o.negate(), cond, e, &ternary_set) {
                                gates.push(Gate {
                                    ty: GateType::Ite,
                                    in1: cond,
                                    in2: then_lit,
                                    in3: e,
                                    out: o,
                                });
                            }
                        }
                    }
                }
            }
        }

        gates
    }
}
