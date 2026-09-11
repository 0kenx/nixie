//! Sorting-network **order encoding** of large `distinct` over BitVec.
//!
//! The pairwise encoding of `distinct(a_1..a_n)` mints C(n,2) disequality
//! atoms; at large n that quadratic atom set is the bottleneck the
//! BV-circuit unification campaign measured
//! (`docs/studies/2026-09-distinct-theory-owned-sorts.md`, Attack 3).  The
//! order encoding instead *sorts* the arguments with a Batcher bitonic
//! network of `bvule`-comparators (O(n log² n) comparators, zero
//! disequality atoms) and constrains the sorted outputs to be strictly
//! increasing:
//!
//! ```text
//! result  <=>  s_1 <u s_2 <u … <u s_N
//! ```
//!
//! `distinct` holds exactly when the values admit a strictly increasing
//! arrangement, and a sorting network makes the arrangement *operational*:
//! comparators propagate mid-descent (in the unified main-core architecture
//! – see `bv_unified` in `nixie-solver` – every comparator is a clause the
//! CDCL search can use per decision, which is the property whose absence
//! made this encoding a wash in the embedded-instance era).
//!
//! # Soundness shape (why this is a *definition* plus an asserted unit)
//!
//! The network sorts `n2 = next_power_of_two(n)` wires: the arguments plus
//! `n2 − n` **pad** wires (free bit-vectors; the pigeonhole short-circuit
//! upstream guarantees `n <= 2^w`, hence `n2 <= 2^w`, so a strictly
//! increasing arrangement of all `n2` wires always exists when the
//! arguments are distinct).  With free pads, `result <=> strict-chain` is
//! *not* pointwise equal to `distinct` – a colliding pad can falsify the
//! chain while the arguments stay distinct – so the encoding would be
//! unsound for a negated `distinct` left to float.  The solver-side caller
//! therefore records a spec **only where the assertion spine asserts the
//! term as a unit** (`emit_assertion_clauses`'s fact position): with
//! `result` pinned true, the definition degenerates to the chain, every
//! other occurrence of the term reads `true`, and the model the search
//! returns has all wires distinct – which is exactly the semantics of the
//! asserted `distinct`.  Satisfiability is preserved in both directions:
//! distinct arguments admit good pads (`sat`), and any duplicate argument
//! forces an adjacent equality in the sorted sequence (`unsat`).
//!
//! # Totality whitelist
//!
//! The chain's completeness direction needs `bvult` to be a **total** order
//! over the sort; the builder is therefore only wired up for `BitVec`
//! (the handover's whitelist; `fp.lt`'s NaN incomparability is the live
//! counterexample).
//!
//! # Identity phase guidance
//!
//! The **identity arrangement** – input wire `i` carries the value `i` – is
//! already sorted, so it satisfies every comparator, the strict chain, and
//! the result.  After building, the builder *evaluates* the network under
//! that arrangement with the SAT solver's own unit propagation
//! ([`nixie_sat::Solver::assign_and_propagate_level0`]) and records every
//! derived value as a deterministic decision phase.  A descent that follows
//! the phases therefore walks a satisfying assignment; propagation does the
//! rest.  Phases constrain nothing – they only make the satisfying region
//! the first place the search looks.  (Hinting the gate variables by hand
//! instead – "comparators pass through", "control false" – pins a non-model
//! for the descending half-cleaners, whose swaps route through the mux
//! *arms*; the guided descent then thrashes: measured 43k decisions at
//! n=9 where propagation-derived phases need ~2k.)
//!
//! # Correctness proof of the network
//!
//! The 0-1 principle: a comparator network sorts all inputs iff it sorts
//! all 0/1 inputs.  The unit tests below exhaustively verify the generated
//! encoding (network *and* chain, through a real SAT solve) on every 0/1
//! assignment for small n, and randomly for wider inputs.

use super::*;
use nixie_core::ast::{TermKind, TermManager};

/// One network wire: its bits, LSB first.  Intermediate comparator outputs
/// never need a `TermId` – the builder works over raw bit vectors of the
/// active build target.
type Wire = SmallVec<[Var; 32]>;

/// Estimated-clause cap for one network (comparators dominate: ~12 clauses
/// per bit plus the `bvult` ripple; the chain adds ~4 clauses per bit per
/// gap).  A network over this estimate is refused (nothing built) – the
/// caller falls back – because the clause arena cost outruns any search
/// benefit at that shape.
const NETWORK_CLAUSE_CAP: u64 = 50_000_000;

impl BvSolver {
    /// Build the bitonic order-encoding network over `inputs` (arguments
    /// first, pads last; every wire `width` bits) and define `out` as
    /// `strictly increasing over the sorted outputs`.
    ///
    /// Must run inside the build target that owns `out` and the input bits
    /// (the caller's `build_with` window, or the embedded instance in unit
    /// tests).  Returns `false` – building nothing – when the wires have
    /// mismatched widths or the estimated circuit exceeds the size cap
    /// (see the `NETWORK_CLAUSE_CAP` constant).
    pub fn encode_distinct_order_network(&mut self, out: Var, inputs: &[Wire]) -> bool {
        let n2 = inputs.len();
        if n2 < 2 || !n2.is_power_of_two() {
            return false;
        }
        let width = inputs[0].len();
        if width == 0 || inputs.iter().any(|w| w.len() != width) {
            return false;
        }
        let log = n2.trailing_zeros() as u64;
        let comparators = (n2 as u64 / 2).saturating_mul(log.saturating_mul(log));
        let estimated = comparators
            .saturating_mul(width as u64 * 12 + 4)
            .saturating_add(n2 as u64 * width as u64 * 4);
        if estimated > NETWORK_CLAUSE_CAP {
            return false;
        }
        // The phase-guidance pass below creates no clauses, but its
        // evaluation only exists when the identity arrangement fits the
        // domain (n2 <= 2^width); past 63 bits the check itself would
        // overflow, and any realistic arity is far below that anyway.
        let hint_identity = width >= 64 || n2 <= (1usize << width);
        let first_network_var = self.sat.num_vars();

        let mut wires: Vec<Wire> = inputs.to_vec();

        // Batcher's bitonic sort, iterative form (depth log n2, no
        // recursion): pass `k` builds sorted blocks of size `k`; the
        // half-cleaner stride `j` merges them; direction per block from
        // `i & k`.  The final pass (`k == n2`) merges everything ascending.
        let mut k = 2usize;
        while k <= n2 {
            let mut j = k / 2;
            while j > 0 {
                for i in 0..n2 {
                    let partner = i ^ j;
                    if partner > i {
                        let ascending = (i & k) == 0;
                        self.compare_swap(&mut wires, i, partner, ascending);
                    }
                }
                j /= 2;
            }
            k *= 2;
        }

        // Strictly increasing chain over the sorted outputs, then
        // `out <=> AND(chain)` through a balanced AND-tree (the wide-clause
        // alternative propagates worse).
        let mut level: Vec<Sig> = Vec::with_capacity(n2 - 1);
        for gap in wires.windows(2) {
            let strict = self.sat.new_var();
            self.encode_ult_result(&gap[0], &gap[1], strict);
            level.push(Sig::Var(strict));
        }
        while level.len() > 1 {
            let mut next: Vec<Sig> = Vec::with_capacity(level.len() / 2 + 1);
            for pair in level.chunks(2) {
                let folded = if pair.len() == 2 {
                    self.gate_and(pair[0], pair[1])
                } else {
                    pair[0]
                };
                next.push(folded);
            }
            level = next;
        }
        match level.pop() {
            Some(root) => {
                self.wire(out, root);
            }
            None => {
                // Degenerate: a single wire is vacuously "strictly
                // increasing"; `distinct` of one argument is true.
                self.sat.add_clause([Lit::pos(out)]);
            }
        }

        if hint_identity {
            self.hint_identity_arrangement(first_network_var, inputs);
        }
        true
    }

    /// Dispatch-side eligibility for the order-encoding handoff (see
    /// `assert_formula_true`'s `Distinct` arm): arity above the pairwise
    /// threshold, every argument an already-blasted bit-vector of one
    /// width, no ground-constant argument (a pinned wire defeats the
    /// identity guidance – measured timeouts on constant-mixed shapes), and
    /// `n <= 2^width` so both the pigeonhole short-circuit and the identity
    /// arrangement hold.  `NIXIE_BV_DISTINCT_ORDER=0` disables.
    pub(super) fn distinct_order_dispatch_eligible(
        &self,
        args: &[TermId],
        manager: &TermManager,
    ) -> bool {
        const PAIRWISE_MAX_ARGS: usize = 32;
        if args.len() <= PAIRWISE_MAX_ARGS {
            return false;
        }
        if Self::order_env_disabled() {
            return false;
        }
        let Some(first) = self.term_to_bv.get(&args[0]) else {
            return false;
        };
        let width = first.width;
        if width < 63 && args.len() > (1usize << width) {
            return false;
        }
        if manager
            .get(args[0])
            .is_some_and(|t| matches!(t.kind, TermKind::BitVecConst { .. }))
        {
            return false;
        }
        args.iter().all(|&a| {
            manager
                .get(a)
                .is_some_and(|t| !matches!(t.kind, TermKind::BitVecConst { .. }))
                && self.term_to_bv.get(&a).is_some_and(|v| v.width == width)
        })
    }

    /// Whether `NIXIE_BV_DISTINCT_ORDER=0` disables the order encoding.
    pub(crate) fn order_env_disabled() -> bool {
        match std::env::var("NIXIE_BV_DISTINCT_ORDER") {
            Ok(v) => v == "0" || v.is_empty(),
            Err(_) => false,
        }
    }

    /// Build the bitonic network for an eligible dispatch-side `distinct`
    /// and pin its result var true.  Returns `false` – building nothing –
    /// when the builder refuses (size cap), so the caller falls back to the
    /// pairwise node.
    ///
    /// Pads are anonymous SAT variables (no `TermId` needs to exist for a
    /// wire that only the network ever sees).  If an already-asserted
    /// equality hits two of the arguments, the `distinct` is refuted on the
    /// spot – the guard the network cannot provide itself.
    pub(super) fn assert_distinct_order_network(
        &mut self,
        args: &[TermId],
        manager: &TermManager,
    ) -> bool {
        let width = self.term_to_bv.get(&args[0]).map_or(0, |v| v.width);
        let arg_set: FxHashSet<TermId> = args.iter().copied().collect();
        // Assert-first guard: an equality already pinned between two
        // arguments refutes the pinned-true distinct outright.
        for &(a, b) in &self.asserted_eq_pairs {
            if arg_set.contains(&a) && arg_set.contains(&b) {
                let _ = self.sat.add_clause([]);
                self.order_distinct_argsets.push(arg_set);
                return true;
            }
        }
        let n2 = args.len().next_power_of_two();
        let mut inputs: Vec<Wire> = Vec::with_capacity(n2);
        for &a in args {
            let Some(bits) = self.bv_bits(a) else {
                return false;
            };
            inputs.push(bits);
        }
        for _ in args.len()..n2 {
            let pad: Wire = (0..width).map(|_| self.sat.new_var()).collect();
            inputs.push(pad);
        }
        let out = self.sat.new_var();
        if !self.encode_distinct_order_network(out, &inputs) {
            return false;
        }
        self.pin_bool_var(out, true);
        self.order_distinct_argsets.push(arg_set);
        let _ = manager;
        true
    }

    /// One bitonic comparator: `c := wires[b] <u wires[a]`, then mux both
    /// wires (`min` to the ascending-low side, `max` to the high side).
    ///
    /// Both outputs are rebuilt from fresh mux gates so later stages read
    /// exactly this comparator's result; the folding gates keep constant
    /// inputs (narrow widths, constant arguments) nearly free.
    fn compare_swap(&mut self, wires: &mut [Wire], a: usize, b: usize, ascending: bool) {
        let wa = wires[a].clone();
        let wb = wires[b].clone();
        // c := b < a (the swap fires when the pair faces the wrong way for
        // its direction).
        let c = self.sat.new_var();
        self.encode_ult_result(&wb, &wa, c);

        let mut out_a: Wire = SmallVec::with_capacity(wa.len());
        let mut out_b: Wire = SmallVec::with_capacity(wa.len());
        for j in 0..wa.len() {
            // min = c ? b : a, max = c ? a : b.
            let min = self.gate_mux(Sig::Var(c), self.sig(wb[j]), self.sig(wa[j]));
            let max = self.gate_mux(Sig::Var(c), self.sig(wa[j]), self.sig(wb[j]));
            if ascending {
                out_a.push(self.sig_var(min));
                out_b.push(self.sig_var(max));
            } else {
                out_a.push(self.sig_var(max));
                out_b.push(self.sig_var(min));
            }
        }
        wires[a] = out_a;
        wires[b] = out_b;
    }

    /// Derive deterministic decision phases for the whole network under the
    /// identity arrangement, using the SAT core's own propagation as the
    /// circuit evaluator.
    ///
    /// Assigns every input bit to the identity value of its wire
    /// (`wire i` carries `i`), propagates, records the derived value of
    /// every variable created by this network (and of the input bits) as
    /// its deterministic phase, then rewinds the trail.  If propagation
    /// conflicts (the arrangement is not a model of the *rest* of the
    /// instance – other clauses already asserted on these variables), the
    /// phases are simply left as far as propagation got before the
    /// conflict: phases are guidance, never constraints.
    fn hint_identity_arrangement(&mut self, first_network_var: usize, inputs: &[Wire]) {
        // The guidance propagates the identity arrangement through the
        // *clauses* of the network; with deferred IR circuits those do not
        // exist yet, and the hint derives nothing (measured: the n=9
        // descent thrashed).  Materialize first — the clauses land in the
        // current build target, and defs created later re-materialize at
        // the window close.
        self.materialize_ir_pub();
        let snapshot = self.sat.trail_size();
        let mut lits: SmallVec<[Lit; 32]> = SmallVec::new();
        for (i, wire) in inputs.iter().enumerate() {
            for (j, &bit) in wire.iter().enumerate() {
                if j < 128 && ((i as u128 >> j) & 1 == 1) {
                    lits.push(Lit::pos(bit));
                } else {
                    lits.push(Lit::neg(bit));
                }
            }
        }
        let coherent = self.sat.assign_and_propagate_level0(&lits);
        if !coherent {
            // The arrangement already conflicts with clauses asserted on
            // these variables (pinned operands, other constraints): partial
            // hints would actively mislead, so record none.
            self.sat.restore_to_trail_size(snapshot);
            return;
        }
        // Read the derived values, then rewind before hinting (the trail
        // borrow must end before the next `&mut self.sat` call).
        let limit = self.sat.num_vars();
        let mut derived: SmallVec<[(Var, bool); 64]> = SmallVec::new();
        {
            let trail = self.sat.trail();
            for idx in 0..limit {
                let var = Var::new(idx as u32);
                let value = trail.value(var);
                if value.is_defined()
                    && (idx >= first_network_var || inputs.iter().any(|w| w.contains(&var)))
                {
                    derived.push((var, value.is_true()));
                }
            }
        }
        self.sat.restore_to_trail_size(snapshot);
        for (var, value) in derived {
            self.sat.set_deterministic_phase(var, value);
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::theory::Theory;
    use nixie_core::ast::TermManager;

    /// Build the network for `n` argument wires of `width` bits plus the
    /// matching pads, solve, and report the verdict on `out`.
    fn network_distinct_truth(n: usize, width: u32, arg_values: &[u64]) -> bool {
        let mut mgr = TermManager::new();
        let mut bv = BvSolver::new();
        let n2 = n.next_power_of_two();
        let bv_sort = mgr.sorts.bitvec(width);
        let mut inputs: Vec<Wire> = Vec::with_capacity(n2);
        for (i, &value) in arg_values.iter().enumerate() {
            let term = mgr.mk_var(&format!("a{i}"), bv_sort);
            let w = bv.new_bv(term, width).clone();
            inputs.push(w.bits.clone());
            // Pin the argument to its value.
            for (j, &bitv) in w.bits.iter().enumerate() {
                let b = (value >> j) & 1 == 1;
                bv.sat
                    .add_clause([if b { Lit::pos(bitv) } else { Lit::neg(bitv) }]);
            }
        }
        for i in n..n2 {
            let term = mgr.mk_var(&format!("p{i}"), bv_sort);
            let w = bv.new_bv(term, width).clone();
            inputs.push(w.bits.clone());
        }
        let out = bv.sat.new_var();
        bv.sat.add_clause([Lit::pos(out)]);
        assert!(
            bv.encode_distinct_order_network(out, &inputs),
            "network builder refused n={n} w={width}"
        );
        matches!(bv.check(), Ok(TheoryResult::Sat))
    }

    /// Semantic reference: pairwise distinctness of the argument values.
    fn all_distinct(arg_values: &[u64]) -> bool {
        arg_values
            .iter()
            .enumerate()
            .all(|(i, x)| arg_values.iter().skip(i + 1).all(|y| x != y))
    }

    /// 0-1 principle, end to end: every 0/1 assignment of up to 8 argument
    /// wires (pads free) must make the encoded `out` exactly as satisfiable
    /// as pairwise distinctness of the arguments.
    #[test]
    fn order_network_01_principle_exhaustive() {
        for n in 2..=8usize {
            for mask in 0..(1u64 << n) {
                let args: Vec<u64> = (0..n).map(|i| (mask >> i) & 1).collect();
                let got = network_distinct_truth(n, 1, &args);
                let want = all_distinct(&args);
                assert_eq!(
                    got, want,
                    "n={n} args={args:?}: encoded {got}, semantic {want}"
                );
            }
        }
    }

    /// Pads are free: distinct arguments must stay satisfiable for every
    /// padding count (the arrangement exists because n2 <= 2^width).
    #[test]
    fn order_network_pads_never_block_distinct_args() {
        for n in [3usize, 5, 9, 17] {
            let args: Vec<u64> = (0..n as u64).collect();
            assert!(
                network_distinct_truth(n, 8, &args),
                "distinct args of n={n} must be satisfiable"
            );
        }
    }

    /// Duplicates must refute through the sorted chain for every padding
    /// count and several widths.
    #[test]
    fn order_network_duplicates_refute() {
        for n in [3usize, 5, 9, 17] {
            for w in [2u32, 8, 16] {
                if n > (1usize << w) {
                    continue; // pigeonholed shape: the caller gates it out
                }
                let mut args: Vec<u64> = (0..n as u64).collect();
                args[n - 1] = 0; // duplicate of args[0]
                assert!(
                    !network_distinct_truth(n, w, &args),
                    "duplicate at n={n} w={w} must refute"
                );
            }
        }
    }

    /// Pigeonhole consistency: n2 > 2^width makes the chain unsatisfiable,
    /// which is exactly `distinct`'s truth value there.
    #[test]
    fn order_network_pigeonholed_domain_is_unsat() {
        // 5 wires of 1 bit: only 2 values exist.
        let args = vec![0u64, 1, 0, 1, 0];
        assert_eq!(network_distinct_truth(5, 1, &args), all_distinct(&args));
        let args = vec![0u64, 1];
        assert_eq!(network_distinct_truth(2, 1, &args), all_distinct(&args));
    }

    /// Randomised differential at wider widths (constants, powers of two,
    /// near-boundary values) against the semantic reference.
    #[test]
    fn order_network_random_differential() {
        let mut rng: u64 = 0x9E3779B97F4A7C15;
        let mut next = move || {
            rng ^= rng << 13;
            rng ^= rng >> 7;
            rng ^= rng << 17;
            rng
        };
        for trial in 0..40 {
            let n = 2 + (next() as usize % 16);
            let width = [2u32, 4, 5, 8, 13, 16][trial % 6];
            // Mirror the caller's pigeonhole gate: `n <= 2^width`.  Beyond
            // it the chain can only be refuted by counting through the
            // network (exponentially hard for CDCL, exactly like the
            // pigeonhole formula), which the real encoding never asks the
            // search to do -- the encoder's finite-domain short-circuit
            // refutes those inputs outright.
            if n > (1usize << width) {
                continue;
            }
            let domain = 1u64 << width.min(16);
            let args: Vec<u64> = (0..n).map(|_| next() % domain).collect();
            let got = network_distinct_truth(n, width, &args);
            let want = all_distinct(&args);
            assert_eq!(
                got, want,
                "trial {trial} n={n} w={width} args={args:?}: {got} vs {want}"
            );
        }
    }

    /// The identity phases make the free-variable satisfiable side a guided
    /// descent: with every wire free, the search should find the identity
    /// arrangement with a handful of conflicts, not a thrash.  (Before the
    /// propagation-derived phases this shape took 43k decisions at n=9 and
    /// 137 s at n=17; the bound here is generous to stay robust under
    /// parallel-test load while still catching the regression.)
    #[test]
    fn order_network_identity_descent_stays_guided() {
        for n in [9usize, 17, 33] {
            let width = 8u32;
            let mut mgr = TermManager::new();
            let mut bv = BvSolver::new();
            let n2 = n.next_power_of_two();
            let bv_sort = mgr.sorts.bitvec(width);
            let mut inputs: Vec<Wire> = Vec::with_capacity(n2);
            for i in 0..n2 {
                let term = mgr.mk_var(&format!("w{i}"), bv_sort);
                let w = bv.new_bv(term, width).clone();
                inputs.push(w.bits.clone());
            }
            let out = bv.sat.new_var();
            bv.sat.add_clause([Lit::pos(out)]);
            assert!(bv.encode_distinct_order_network(out, &inputs));
            let r = bv.check();
            assert!(
                matches!(r, Ok(TheoryResult::Sat)),
                "n={n}: identity-guided solve must be sat"
            );
            let conflicts = bv.sat.stats().conflicts;
            assert!(
                conflicts < 2000,
                "n={n}: identity descent thrashed ({conflicts} conflicts)"
            );
        }
    }

    /// Probe (scratch, not for landing): one duplicate pair, other wires
    /// free, embedded solve -- isolates the network's unsat side.
    /// End-to-end dispatch-path test: `assert_formula_true` on a
    /// `distinct` term runs the same arm the eager QF_BV dispatch uses
    /// (blast, then assert); `check()` solves the embedded instance.
    #[test]
    fn order_dispatch_free_vars_sat() {
        let mut mgr = TermManager::new();
        let bv_sort = mgr.sorts.bitvec(8);
        let args: Vec<TermId> = (0..40)
            .map(|i| mgr.mk_var(&format!("d{i}"), bv_sort))
            .collect();
        let mut bv = BvSolver::new();
        for &a in &args {
            bv.new_bv(a, 8);
        }
        let distinct = mgr.mk_distinct(args.iter().copied());
        assert!(bv.assert_formula_true(distinct, &mgr));
        assert!(matches!(bv.check(), Ok(TheoryResult::Sat)));
    }

    /// The equality guard, assert-first direction: an equality already
    /// asserted between two arguments must refute the pinned-true network
    /// `distinct` without searching through the sort.
    #[test]
    fn order_dispatch_eq_guard_refutes() {
        let mut mgr = TermManager::new();
        let bv_sort = mgr.sorts.bitvec(8);
        let args: Vec<TermId> = (0..40)
            .map(|i| mgr.mk_var(&format!("d{i}"), bv_sort))
            .collect();
        let mut bv = BvSolver::new();
        for &a in &args {
            bv.new_bv(a, 8);
        }
        // Assert `d0 = d17` first (bit-level, as the dispatch spine does)…
        let eq = mgr.mk_eq(args[0], args[17]);
        assert!(bv.assert_formula_true(eq, &mgr));
        // …then the distinct: the guard refutes on the spot.
        let distinct = mgr.mk_distinct(args.iter().copied());
        assert!(bv.assert_formula_true(distinct, &mgr));
        assert!(matches!(bv.check(), Ok(TheoryResult::Unsat(_))));
    }

    /// The equality guard, distinct-first direction: a later equality
    /// between two arguments of an already-built network refutes it.
    #[test]
    fn order_dispatch_eq_guard_later_refutes() {
        let mut mgr = TermManager::new();
        let bv_sort = mgr.sorts.bitvec(8);
        let args: Vec<TermId> = (0..40)
            .map(|i| mgr.mk_var(&format!("d{i}"), bv_sort))
            .collect();
        let mut bv = BvSolver::new();
        for &a in &args {
            bv.new_bv(a, 8);
        }
        let distinct = mgr.mk_distinct(args.iter().copied());
        assert!(bv.assert_formula_true(distinct, &mgr));
        let eq = mgr.mk_eq(args[3], args[39]);
        assert!(bv.assert_formula_true(eq, &mgr));
        assert!(matches!(bv.check(), Ok(TheoryResult::Unsat(_))));
    }

    /// The size cap refuses absurd shapes without building anything.
    #[test]
    fn order_network_refuses_oversized_shapes() {
        let mut bv = BvSolver::new();
        let n2 = 2048usize;
        let width = 96u32;
        let inputs: Vec<Wire> = (0..n2)
            .map(|_| (0..width).map(|_| bv.sat.new_var()).collect())
            .collect();
        let out = bv.sat.new_var();
        assert!(!bv.encode_distinct_order_network(out, &inputs));
    }
}
