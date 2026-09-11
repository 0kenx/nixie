//! Hash-consed boolean expression IR — the layer between term blasting
//! and CNF emission (Z3's `bit_blaster` produces exactly this: boolean
//! *expressions*, with Tseitin deferred to the very end).
//!
//! # Why this layer exists
//!
//! The clause-emitting gate layer materializes one SAT variable (plus its
//! defining clauses) for **every** gate and **every** intermediate term
//! bit.  Z3's post-blast passes get their power from the fact that its
//! blast output is an expression DAG:
//!
//! * structurally identical subcircuits are one node (hash-consing),
//!   regardless of which term built them;
//! * constants fold *through shared structure* at construction, so a
//!   late pin re-folds every consumer (a fixpoint pass, see
//!   [`BoolIr::refold_consts`]);
//! * **definitions inline**: a consumer that reads a defined signal
//!   references the definition's *node*, so intermediate bits never
//!   enter the CNF at all — the IR equivalent of `solve-eqs`
//!   substitution, and the mechanism that keeps z3's blasted goals
//!   small enough for its post-blast simplifier to close
//!   (`bit-blast → simplifier → solve-eqs` traces on the
//!   `maxandminor`/`cjpeg` families);
//! * dead definitions (nothing external ever reads them) are eliminated
//!   outright at Tseitin time.
//!
//! # Representation
//!
//! A node is `And`, `Xor`, `Mux(sel, t, f)` or `Var(v)`; a **literal** is
//! a `u32` code `(node_index << 1) | complement` — complement edges are
//! free, exactly as in an AIG.  Index `0` is the reserved constant-true
//! node, so code `1` reads *true* and code `0` reads *false*.
//!
//! Hash-consing plus construction-time folding give the normal form:
//! `and(c, x)`, `and(x, x)`, `and(x, ¬x)`, mux constant arms, and the
//! xor parity rules all fold before a node exists, so semantically
//! trivial structure never allocates.

use crate::prelude::FxHashMap;
use nixie_sat::Var;

/// One IR node.  Children are literal codes.
#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug)]
#[allow(dead_code)] // Mux + pin/refold land with the default-flip follow-up
pub enum IrNode {
    /// Reserved index 0: the constant true (its complement is false).
    ConstTrue,
    /// `and(a, b)` over two literal codes (commutative; canonicalized).
    And(u32, u32),
    /// `xor(a, b)` over two literal codes (commutative; canonicalized).
    Xor(u32, u32),
    /// `sel ? t : f` over three literal codes.
    Mux(u32, u32, u32),
    /// A free signal variable (a leaf: a term bit with no definition).
    Var(Var),
}

/// The boolean expression DAG.
#[derive(Debug, Default)]
pub struct BoolIr {
    nodes: Vec<IrNode>,
    /// Hash-cons table: node → index.
    table: FxHashMap<IrNode, u32>,
    /// Vars pinned to a constant after blasting (`refold_consts` input):
    /// var → its forced truth value.
    pinned: FxHashMap<Var, bool>,
    /// node index → folded literal (set by `refold_consts` when a node's
    /// value becomes constant); a present entry means "this index is dead,
    /// read the literal instead".
    folded: FxHashMap<u32, u32>,
}

/// Literal code helpers (module-private convention: code = idx<<1 | neg).
pub mod lit {
    /// The literal `true`.
    pub const TRUE: u32 = 1;
    /// The literal `false`.
    pub const FALSE: u32 = 0;

    #[inline]
    pub fn idx(code: u32) -> u32 {
        code >> 1
    }
    #[inline]
    pub fn neg(code: u32) -> u32 {
        code ^ 1
    }
    #[inline]
    pub fn make(idx: u32, complement: bool) -> u32 {
        (idx << 1) | u32::from(complement)
    }
}

#[allow(dead_code)] // len/node_kind/mux/pin/refold_consts: exercised by the
// unit tests now; the solver wiring (pin seeding from
// level-0 units, mux nodes) is the follow-up work.
impl BoolIr {
    pub fn new() -> Self {
        let mut ir = Self {
            nodes: Vec::new(),
            table: FxHashMap::default(),
            pinned: FxHashMap::default(),
            folded: FxHashMap::default(),
        };
        // Reserve index 0 for the constant true UNCONDITIONALLY: the
        // literal codes (code = idx<<1 | complement) give idx 0 the
        // reading true/false, so the first real node must never take it.
        // (A debug_assert here skipped the interning in release builds —
        // the first circuit node landed on index 0 and every constant
        // code misread as that node: the bitrev false-sat.  The interning
        // must run unconditionally; the assert only checks the invariant.)
        let const_true_idx = ir.intern(IrNode::ConstTrue);
        debug_assert_eq!(const_true_idx, 0);
        ir
    }

    /// Number of allocated nodes (diagnostics).
    pub fn len(&self) -> usize {
        self.nodes.len()
    }

    fn intern(&mut self, node: IrNode) -> u32 {
        if let Some(&idx) = self.table.get(&node) {
            return idx;
        }
        let idx = self.nodes.len() as u32;
        self.nodes.push(node);
        self.table.insert(node, idx);
        idx
    }

    fn node_kind(&self, code: u32) -> Option<IrNode> {
        match lit::idx(code) {
            0 => Some(IrNode::ConstTrue),
            i => self.nodes.get(i as usize).copied(),
        }
    }

    /// The literal for a free variable (a leaf with no definition).
    pub fn var(&mut self, v: Var) -> u32 {
        lit::make(self.intern(IrNode::Var(v)), false)
    }

    /// `and(a, b)` with construction-time folding and canonicalization.
    pub fn and(&mut self, a: u32, b: u32) -> u32 {
        let (a, b) = (self.canonical(a), self.canonical(b));
        if a == lit::FALSE || b == lit::FALSE {
            return lit::FALSE;
        }
        if a == lit::TRUE {
            return b;
        }
        if b == lit::TRUE {
            return a;
        }
        if a == b {
            return a;
        }
        if a == lit::neg(b) {
            return lit::FALSE;
        }
        let (x, y) = if a < b { (a, b) } else { (b, a) };
        lit::make(self.intern(IrNode::And(x, y)), false)
    }

    /// `or(a, b)` = `¬and(¬a, ¬b)` — a complement edge of the and node
    /// (De Morgan collision for free).
    pub fn or(&mut self, a: u32, b: u32) -> u32 {
        lit::neg(self.and(lit::neg(self.canonical(a)), lit::neg(self.canonical(b))))
    }

    /// `xor(a, b)` with folding: xor(x, ¬y) = ¬xor(x, y).
    pub fn xor(&mut self, a: u32, b: u32) -> u32 {
        let (a, b) = (self.canonical(a), self.canonical(b));
        if a == lit::FALSE {
            return b;
        }
        if b == lit::FALSE {
            return a;
        }
        if a == lit::TRUE {
            return lit::neg(self.canonical(b));
        }
        if b == lit::TRUE {
            return lit::neg(a);
        }
        if a == b {
            return lit::FALSE;
        }
        if a == lit::neg(b) {
            return lit::TRUE;
        }
        // Parity of input complements folds into the result polarity.
        let (pa, pb) = (a & 1, b & 1);
        let (xa, xb) = (a & !1, b & !1);
        let (x, y) = if xa < xb { (xa, xb) } else { (xb, xa) };
        let base = lit::make(self.intern(IrNode::Xor(x, y)), false);
        base ^ pa ^ pb
    }

    /// `mux(sel, t, f)` with folding: constant sel selects; equal arms
    /// collapse; both-arms-complemented flips the output.
    pub fn mux(&mut self, sel: u32, t: u32, f: u32) -> u32 {
        let (sel, t, f) = (self.canonical(sel), self.canonical(t), self.canonical(f));
        if sel == lit::TRUE {
            return t;
        }
        if sel == lit::FALSE {
            return f;
        }
        if t == f {
            return t;
        }
        if t == lit::TRUE && f == lit::FALSE {
            return sel;
        }
        if t == lit::FALSE && f == lit::TRUE {
            return lit::neg(sel);
        }
        // mux(s, ¬t, ¬f) = ¬mux(s, t, f).
        if (t & 1) == 1 && (f & 1) == 1 {
            return lit::neg(self.mux(sel, lit::neg(t), lit::neg(f)));
        }
        lit::make(self.intern(IrNode::Mux(sel, t, f)), false)
    }

    /// Resolve a literal through the folding table (dead indices read as
    /// their folded literal).
    fn canonical(&self, code: u32) -> u32 {
        if code <= 1 {
            // The reserved constants are their own canonical form (folding
            // node 0 onto itself alternates true/false forever).
            return code;
        }
        match self.folded.get(&lit::idx(code)) {
            Some(&repl) => {
                let repl_neg = repl ^ (code & 1);
                // The replacement may itself be folded (chains).
                self.canonical(repl_neg)
            }
            None => code,
        }
    }

    /// Pin a variable to a constant (a level-0 fact discovered after
    /// circuits referencing it were built — the input to the re-fold
    /// fixpoint).
    pub fn pin(&mut self, v: Var, value: bool) {
        self.pinned.insert(v, value);
    }

    /// **The semantic pass**: propagate pinned constants through the
    /// whole DAG, folding every node whose value becomes determined.
    /// This is the construction-retroactive constant propagation the
    /// clause layer cannot do (units propagate at *search* time there,
    /// after the dead structure is already in the CNF).
    ///
    /// Iterates to a fixpoint over node indices in reverse creation
    /// order (children before parents, mostly), requeuing parents of
    /// folded nodes.  Sound by construction: a fold entry maps a node to
    /// a literal that is equal to it under the pins.
    pub fn refold_consts(&mut self) -> usize {
        let mut folded_count = 0usize;
        // Seed: pinned vars fold to their constant.
        for (i, node) in self.nodes.iter().enumerate() {
            if let IrNode::Var(v) = node
                && let Some(&val) = self.pinned.get(v)
            {
                let repl = if val { lit::TRUE } else { lit::FALSE };
                self.folded.insert(i as u32, repl);
                folded_count += 1;
            }
        }
        // Fold determinate parents until quiet.
        let mut changed = true;
        while changed {
            changed = false;
            for i in 0..self.nodes.len() as u32 {
                if self.folded.contains_key(&i) {
                    continue;
                }
                let Some(node) = self.nodes.get(i as usize).copied() else {
                    continue;
                };
                let val: Option<bool> = match node {
                    IrNode::ConstTrue => Some(true),
                    IrNode::Var(v) => self.pinned.get(&v).copied(),
                    IrNode::And(a, b) => {
                        let fa = self.folded_lit(a);
                        let fb = self.folded_lit(b);
                        match (fa, fb) {
                            (Some(x), Some(y)) => Some(x && y),
                            (Some(false), _) | (_, Some(false)) => Some(false),
                            _ => None,
                        }
                    }
                    IrNode::Xor(a, b) => {
                        let fa = self.folded_lit(a);
                        let fb = self.folded_lit(b);
                        match (fa, fb) {
                            (Some(x), Some(y)) => Some(x != y),
                            _ => None,
                        }
                    }
                    IrNode::Mux(s, t, f) => {
                        let fs = self.folded_lit(s);
                        match fs {
                            Some(true) => self.folded_lit(t),
                            Some(false) => self.folded_lit(f),
                            None => {
                                // Constant arms under a symbolic selector
                                // with equal values.
                                let ft = self.folded_lit(t);
                                let ff = self.folded_lit(f);
                                match (ft, ff) {
                                    (Some(x), Some(y)) if x == y => Some(x),
                                    _ => None,
                                }
                            }
                        }
                    }
                };
                if let Some(v) = val {
                    self.folded
                        .insert(i, if v { lit::TRUE } else { lit::FALSE });
                    folded_count += 1;
                    changed = true;
                }
            }
        }
        folded_count
    }

    /// A node literal's constant value through the fold table (None when
    /// undetermined).
    fn folded_lit(&self, code: u32) -> Option<bool> {
        let c = self.canonical(code);
        match c {
            lit::TRUE => Some(true),
            lit::FALSE => Some(false),
            _ => None,
        }
    }

    /// Whether `code` reads as the constant `true`/`false`.
    pub fn as_const(&self, code: u32) -> Option<bool> {
        self.folded_lit(code)
    }

    /// Literal equality through the fold table: two literals are the
    /// *same signal* (same node, any polarity) — the check the equality
    /// encoder uses to fold bit-pair comparisons (`encode_eq_node`'s
    /// var-equality check, lifted to nodes).
    pub fn same_signal(&self, a: u32, b: u32) -> Option<bool> {
        let (ca, cb) = (self.canonical(a), self.canonical(b));
        if ca == cb {
            Some(true)
        } else if ca == lit::neg(cb) {
            Some(false)
        } else {
            None
        }
    }

    /// Tseitin-encode the sub-DAG reachable from `roots` into `sat`,
    /// allocating one SAT variable per **live** node (folded nodes read
    /// as their constant; hash-consed nodes encode once), and return the
    /// SAT literal for each root code.
    ///
    /// This is the only place the IR touches the SAT solver: dead
    /// definitions never reach it.
    pub fn tseitin(
        &self,
        sat: &mut nixie_sat::Solver,
        const_true: nixie_sat::Lit,
        roots: &[u32],
    ) -> Vec<nixie_sat::Lit> {
        use nixie_sat::{Lit, Var as SVar};
        let _ = SVar::new(0);
        // Pass 1: mark live nodes reachable from the roots (through the
        // fold table).
        let mut live: FxHashMap<u32, u32> = FxHashMap::default(); // node idx -> sat var code
        let mut stack: Vec<u32> = roots.to_vec();
        while let Some(code) = stack.pop() {
            let c = self.canonical(code);
            if c <= 1 {
                continue; // constants need no node
            }
            let idx = lit::idx(c);
            if live.contains_key(&idx) {
                continue;
            }
            live.insert(idx, 0); // placeholder; vars assigned in pass 2
            if let Some(node) = self.nodes.get(idx as usize) {
                match *node {
                    IrNode::ConstTrue | IrNode::Var(_) => {}
                    IrNode::And(a, b) | IrNode::Xor(a, b) => {
                        stack.push(a);
                        stack.push(b);
                    }
                    IrNode::Mux(s, t, f) => {
                        stack.push(s);
                        stack.push(t);
                        stack.push(f);
                    }
                }
            }
        }
        // Pass 2: allocate vars in a deterministic (creation-order) way
        // and emit clauses children-first.  Iterating creation order
        // guarantees children (created earlier) are emitted before their
        // parents.
        let mut out: Vec<Lit> = Vec::with_capacity(roots.len());
        let mut slot: Vec<Option<Lit>> = vec![None; self.nodes.len()];
        slot[0] = Some(const_true);
        for idx in 0..self.nodes.len() as u32 {
            if !live.contains_key(&idx) {
                continue;
            }
            let Some(node) = self.nodes.get(idx as usize).copied() else {
                continue;
            };
            let v = match node {
                IrNode::Var(v) => v, // a leaf: reuse the term bit's own var
                _ => {
                    sat.new_var()
                }
            };
            slot[idx as usize] = Some(Lit::pos(v));
            match node {
                IrNode::ConstTrue => {}
                IrNode::Var(_) => {}
                IrNode::And(a, b) => {
                    let out_l = Lit::pos(v);
                    let (x, y) = (self.sat_lit(&slot, a), self.sat_lit(&slot, b));
                    sat.add_clause([out_l.negate(), x]);
                    sat.add_clause([out_l.negate(), y]);
                    sat.add_clause([out_l, x.negate(), y.negate()]);
                }
                IrNode::Xor(a, b) => {
                    let out_l = Lit::pos(v);
                    let (x, y) = (self.sat_lit(&slot, a), self.sat_lit(&slot, b));
                    sat.add_clause([out_l.negate(), x.negate(), y.negate()]);
                    sat.add_clause([out_l.negate(), x, y]);
                    sat.add_clause([out_l, x.negate(), y]);
                    sat.add_clause([out_l, x, y.negate()]);
                }
                IrNode::Mux(s, t, f) => {
                    let out_l = Lit::pos(v);
                    let (sl, tl, fl) = (
                        self.sat_lit(&slot, s),
                        self.sat_lit(&slot, t),
                        self.sat_lit(&slot, f),
                    );
                    sat.add_clause([sl.negate(), tl.negate(), out_l]);
                    sat.add_clause([sl.negate(), tl, out_l.negate()]);
                    sat.add_clause([sl, fl.negate(), out_l]);
                    sat.add_clause([sl, fl, out_l.negate()]);
                }
            }
        }
        for &r in roots {
            out.push(self.sat_lit(&slot, r));
        }
        out
    }

    /// SAT literal for an IR code, reading constants as the reserved
    /// pair when available — but the constants here are *IR-level*
    /// (`true`/`false` codes); the caller-provided `const_true`/
    /// `const_false` mapping is passed via `slot[0]`.
    fn sat_lit(&self, slot: &[Option<nixie_sat::Lit>], code: u32) -> nixie_sat::Lit {
        let c = self.canonical(code);
        match c {
            lit::TRUE => slot[0].expect("slot 0 is the reserved constant true"),
            lit::FALSE => slot[0]
                .expect("slot 0 is the reserved constant true")
                .negate(),
            _ => {
                let idx = lit::idx(c) as usize;
                let base = slot[idx].expect("live node has a slot");
                if c & 1 == 1 { base.negate() } else { base }
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn folding_basics() {
        let mut ir = BoolIr::new();
        let a = ir.var(Var::new(1));
        let b = ir.var(Var::new(2));
        assert_eq!(ir.and(a, lit::TRUE), a);
        assert_eq!(ir.and(a, a), a);
        assert_eq!(ir.and(a, lit::neg(a)), lit::FALSE);
        assert_eq!(ir.or(a, lit::neg(a)), lit::TRUE);
        assert_eq!(ir.xor(a, lit::neg(a)), lit::TRUE);
        assert_eq!(ir.xor(a, a), lit::FALSE);
        assert_eq!(ir.xor(a, lit::neg(b)), lit::neg(ir.xor(a, b)));
        assert_eq!(ir.mux(a, lit::TRUE, lit::FALSE), a);
        // Both-arms-complemented flip: mux(s, ¬x, ¬y) = ¬mux(s, x, y).
        let c = ir.var(nixie_sat::Var::new(3));
        assert_eq!(
            ir.mux(a, lit::neg(b), lit::neg(c)),
            lit::neg(ir.mux(a, b, c))
        );
    }

    #[test]
    fn refold_through_shared_structure() {
        let mut ir = BoolIr::new();
        let a = ir.var(Var::new(1));
        let b = ir.var(Var::new(2));
        let g = ir.and(a, b);
        let h = ir.xor(g, a); // (a∧b) ⊕ a = a∧¬b … not folded structurally
        // Pin a = true: g → b, h → b.
        ir.pin(Var::new(1), true);
        let folded = ir.refold_consts();
        assert!(folded >= 1, "the pinned var folds");
        assert_eq!(ir.as_const(g), None, "g survives as b");
        // g and h are now *structurally* equal to b-derived nodes only
        // after canonicalization; same_signal still resolves them.
        assert_eq!(ir.same_signal(g, h), None);
        // Pin b = false as well: g = a∧b → false, h = g ⊕ a = false ⊕ true
        // → true.
        ir.pin(Var::new(2), false);
        ir.refold_consts();
        assert_eq!(ir.as_const(g), Some(false));
        assert_eq!(ir.as_const(h), Some(true));
    }

    #[test]
    fn tseitin_dce_skips_unreachable() {
        let mut ir = BoolIr::new();
        let a = ir.var(Var::new(1));
        let b = ir.var(Var::new(2));
        let live = ir.and(a, b);
        let _dead = ir.xor(a, b); // not rooted: must not allocate
        let mut sat = nixie_sat::Solver::new();
        let ct = {
            let v = sat.new_var();
            sat.add_clause([nixie_sat::Lit::pos(v)]);
            nixie_sat::Lit::pos(v)
        };
        let [root] = ir
            .tseitin(&mut sat, ct, &[live])
            .try_into()
            .expect("one root");
        // vars: the two leaves reuse their own vars (1, 2 → indexes 0/1
        // in this fresh solver) and ONE and-node — the dead xor allocated
        // nothing.
        assert_eq!(sat.num_vars(), 3, "2 leaves + 1 and node");
        let _ = root;
    }
}
