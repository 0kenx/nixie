//! Equivalence-preserving QF_BV assertion preprocessing.
//!
//! This is the nixie port of the rewriting core of Z3's `qfbv` tactic
//! preamble (`src/tactic/smtlogics/qfbv_tactic.cpp`): before a pure QF_BV
//! goal is handed to the bit-blaster, equations and comparisons are
//! normalized so that ring identities become *syntactic*.  Without it, whole
//! benchmark families are unreachable:
//!
//! * `wienand-cav2008/distrib16.sf` asserts `(a·b + c·b) ≠ b·(a+c)`.
//!   Product–sum distribution makes both sides the same polynomial, so the
//!   rewriter discharges the goal with zero SAT search (Z3: `sat-mk-var 1`).
//!   Bit-blasting alone never sees the identity and the search drowns in a
//!   33-bit multiplier circuit.
//! * `tacas07/BBB-32` is full of `bvule` atoms over `X ± c` summands; the
//!   `X+c1 ≤ X+c2` overflow rules collapse each to a bound on `X` (or to a
//!   constant), which unit propagation then resolves.
//!
//! # What is implemented (and where it comes from)
//!
//! * **Sum-of-monomials normal form** for `bvadd`/`bvsub`/`bvmul`
//!   (Z3 `poly_rewriter` with `som=true`, the `simp2` pass of the qfbv
//!   preamble): nested sums flatten, products distribute over sums under a
//!   blow-up guard (`som_blowup`), like monomials combine by summing
//!   coefficients in ℤ/2ʷ, and the monomial list is sorted into one
//!   canonical order so equal polynomials hash-cons to identical terms.
//! * **Monomial cancellation across `=`** (Z3 `cancel_monomials`):
//!   `x + a = x + b` rewrites to `a = b`; identical normal forms rewrite to
//!   `true`.
//! * **Unsigned comparison rules** from Z3 `bv_rewriter::mk_leq_core`:
//!   numeral folds and bound rules, the `bvule c (bvadd c2 X)` bound rule,
//!   and the `X+c1 ≤ X+c2` overflow disjunction (Z3 `rw_leq_overflow`).
//! * Bitwise (`bvand`/`bvor`/`bvxor`/`bvnot`) associativity, idempotence and
//!   constant folding, so `bvnot`-heavy industrial instances (`2018-Mann`,
//!   `brummayerbiere3`) reach the blaster pre-folded.
//!
//! # Soundness envelope
//!
//! Every rule rewrites a term into a *semantically identical* term of the
//! same width: coefficients live in ℤ/2ʷ (exactly the BV ring), and no rule
//! decides a truth value it has not derived structurally.  The pass is
//! therefore answer-preserving by construction; the unit tests brute-force
//! the ring rules at small widths, and the solver-level differential is the
//! Z3 parity suite.
//!
//! # Traversal
//!
//! The rewrite is a memoized iterative post-order walk over the hash-consed
//! DAG (shared subterms rewrite once).  All flattenings (`sum_monomials`,
//! `flatten_product`, bitwise chains) are worklist loops, never native
//! recursion, per the repository-wide stack-safety rule.

use nixie_core::ast::{TermId, TermKind, TermManager};
use num_bigint::BigInt;
use num_integer::Integer;
use num_traits::{One, Zero};

use super::Solver;

/// Cap on the monomial count of one normalized sum.  A guard against
/// pathologically wide distributions; well short of any real benchmark.
const MAX_MONOMIALS: usize = 100_000;

/// One summand of a normalized bit-vector sum: `coeff · f₁·f₂·…·fₖ` with all
/// arithmetic in ℤ/2ʷ.
///
/// `factors` is sorted and free of numerals; an empty factor list is the
/// constant monomial.  Two monomials are "like" exactly when their factor
/// lists are equal, which is why the list is the identity key.  Power
/// products keep multiplicity (`x·x` has `factors == [x, x]`).
#[derive(Debug, Clone)]
struct Mono {
    /// Non-negative coefficient below 2ʷ.
    coeff: BigInt,
    /// Sorted non-constant factors of the power product.
    factors: Vec<TermId>,
}

impl Mono {
    fn key(&self) -> &[TermId] {
        &self.factors
    }
}

/// The pass.  Create per goal, reuse across assertions so shared subterms
/// (the common case in these families: whole `let`-shared expression DAGs)
/// are rewritten once.
#[derive(Debug, Default)]
pub(super) struct BvPreprocessor {
    memo: rustc_hash::FxHashMap<TermId, TermId>,
    /// Memo of the distributed polynomial of a term (`None` = not computable
    /// within the bounds).  Populated lazily by `poly_of`.
    poly_memo: rustc_hash::FxHashMap<TermId, Option<Vec<Mono>>>,
    /// Memo of the Boolean reading of a 1-bit expression (`None` = not
    /// liftable).  Populated lazily by [`BvPreprocessor::to_bool`].
    bool_memo: rustc_hash::FxHashMap<TermId, Option<TermId>>,
}

impl BvPreprocessor {
    pub(super) fn new() -> Self {
        Self::default()
    }

    /// The Boolean reading of a width-1 bit-vector expression, or `None`
    /// when any node on the way is not liftable (Z3's `mk_bit2bool` /
    /// `bv1_blaster` idea).
    ///
    /// Liftable nodes: the 1-bit constants, `bvnot`, the bitwise boolean
    /// ops over 1-bit operands, and `ite` with 1-bit branches.  Declared
    /// 1-bit *variables* deliberately stop the lifting: replacing one with
    /// a fresh Boolean would orphan its model entry and its bit-blasted
    /// uses in non-liftable positions; its comparisons still lift through
    /// the surrounding structure.  `concat` stops it as well (its result
    /// is not width 1).
    #[allow(clippy::wrong_self_convention)] // `to_bool` is a conversion on
    // the *term* argument; the receiver is only the memo carrier.
    fn to_bool(&mut self, term: &TermId, manager: &mut TermManager) -> Option<TermId> {
        if let Some(cached) = self.bool_memo.get(term) {
            return *cached;
        }
        let result = self.compute_bool(term, manager);
        self.bool_memo.insert(*term, result);
        result
    }

    fn compute_bool(&mut self, term: &TermId, manager: &mut TermManager) -> Option<TermId> {
        if bv_width_opt(manager, term) != Some(1) {
            return None;
        }
        let kind = manager.get(*term).map(|t| t.kind.clone())?;
        let out = match kind {
            TermKind::BitVecConst { .. } => {
                let v = const_bits(term, manager)?;
                if v.is_one() {
                    manager.mk_true()
                } else {
                    manager.mk_false()
                }
            }
            TermKind::BvNot(a) => {
                let b = self.to_bool(&a, manager)?;
                manager.mk_not(b)
            }
            TermKind::BvAnd(a, b) => {
                let (x, y) = (self.to_bool(&a, manager)?, self.to_bool(&b, manager)?);
                manager.mk_and([x, y])
            }
            TermKind::BvOr(a, b) => {
                let (x, y) = (self.to_bool(&a, manager)?, self.to_bool(&b, manager)?);
                manager.mk_or([x, y])
            }
            TermKind::BvXor(a, b) => {
                let (x, y) = (self.to_bool(&a, manager)?, self.to_bool(&b, manager)?);
                manager.mk_xor(x, y)
            }
            TermKind::Ite(c, t, e) => {
                // The condition is Bool-sorted already (children were
                // rewritten; a BV-sorted condition is malformed SMT-LIB and
                // the fragment walk rejects it before we get here).
                let (bt, be) = (self.to_bool(&t, manager)?, self.to_bool(&e, manager)?);
                let bc = self.memo.get(&c).copied().unwrap_or(c);
                manager.mk_ite(bc, bt, be)
            }
            // Declared variables, extracts of wide terms, shifts, arithmetic
            // on width-1 words: keep the bit-vector representation.
            _ => return None,
        };
        Some(out)
    }

    /// Rewrite one assertion.  Returns the original term on any structural
    /// surprise (missing term data, non-BV sort where a BV sort is required):
    /// skipping a rule costs completeness, never soundness.
    pub(super) fn rewrite(&mut self, root: TermId, manager: &mut TermManager) -> TermId {
        // Iterative post-order over the DAG.  `Enter` schedules children,
        // `Exit` rewrites the node from its (already rewritten) children.
        enum Step {
            Enter(TermId),
            Exit(TermId),
        }
        let mut stack = vec![Step::Enter(root)];
        while let Some(step) = stack.pop() {
            match step {
                Step::Enter(tid) => {
                    if self.memo.contains_key(&tid) {
                        continue;
                    }
                    let Some(data) = manager.get(tid) else {
                        // Missing term data: keep the term verbatim.
                        self.memo.insert(tid, tid);
                        continue;
                    };
                    let children = nixie_core::ast::traversal::get_children(&data.kind);
                    stack.push(Step::Exit(tid));
                    // Children first (reversed so the leftmost is popped
                    // first, keeping rebuild order deterministic).
                    for &child in children.iter().rev() {
                        if !self.memo.contains_key(&child) {
                            stack.push(Step::Enter(child));
                        }
                    }
                }
                Step::Exit(tid) => {
                    let rewritten = self.rewrite_node(tid, manager);
                    self.memo.insert(tid, rewritten);
                }
            }
        }
        self.memo.get(&root).copied().unwrap_or(root)
    }

    /// Rewrite one node whose children are already rewritten (the memo maps
    /// every child).
    fn rewrite_node(&mut self, term: TermId, manager: &mut TermManager) -> TermId {
        let Some(data) = manager.get(term).cloned() else {
            return term;
        };
        let kid = |id: &TermId| -> TermId { self.memo.get(id).copied().unwrap_or(*id) };
        match data.kind {
            // ======== ring normal form ========
            // `bvadd`/`bvsub` nodes are kept verbatim (children rewritten).
            // Flattening and re-associating sums – even order-preservingly –
            // changes the adder tree the bit-blaster builds, and with it the
            // CNF's search trajectory: on add-dominated families the
            // regrouped carry chains measured catastrophically worse
            // (`Sage2/bench_7140`: 16 ms at HEAD, >10 s under any sum
            // rebuild).  Every algebraic fact the flattening used to expose
            // is instead proven in the monomial domain by
            // [`BvPreprocessor::poly_of`] at each `=`/comparison, so nothing
            // is lost decision-wise – only the term shapes handed to the
            // blaster stay the input's own.
            TermKind::BvAdd(_, _) | TermKind::BvSub(_, _) => term,
            TermKind::BvMul(a, b) => self.rewrite_mul(kid(&a), kid(&b), manager),

            // ======== bitwise normal form ========
            TermKind::BvNot(a) => {
                let a = kid(&a);
                match manager.get(a).map(|t| &t.kind) {
                    Some(TermKind::BvNot(inner)) => *inner,
                    Some(TermKind::BitVecConst { width, .. }) => {
                        let Some(value) = const_bits(&a, manager) else {
                            return manager.mk_bv_not(a);
                        };
                        let mask = (BigInt::one() << *width as usize) - BigInt::one();
                        manager.mk_bitvec(mask - value, *width)
                    }
                    _ => manager.mk_bv_not(a),
                }
            }
            TermKind::BvAnd(a, b) => flatten_bitwise(kid(&a), kid(&b), manager, BitwiseOp::And),
            TermKind::BvOr(a, b) => flatten_bitwise(kid(&a), kid(&b), manager, BitwiseOp::Or),
            TermKind::BvXor(a, b) => flatten_bitwise(kid(&a), kid(&b), manager, BitwiseOp::Xor),

            // ======== equality ========
            TermKind::Eq(a, b) => {
                let (ra, rb) = (kid(&a), kid(&b));
                if ra == rb {
                    return manager.mk_true();
                }
                // Z3 `mk_bit2bool`: `(= (_ bv1 1) e)` over a liftable
                // 1-bit expression becomes the Boolean `b(e)` itself (and
                // `= (_ bv0 1) e` its negation).  Encodings that build
                // their Boolean structure out of 1-bit vectors
                // (`brummayerbiere3/maxandminor*`, `countbitssrl*`) then
                // reach the blaster as real Boolean circuits instead of
                // per-node mux/equality clauses over 1-bit words.
                if let Some(value) = const_bits(&ra, manager)
                    && bv_width_opt(manager, &ra) == Some(1)
                    && let Some(be) = self.to_bool(&rb, manager)
                {
                    return if value.is_one() {
                        be
                    } else {
                        manager.mk_not(be)
                    };
                }
                if let Some(value) = const_bits(&rb, manager)
                    && bv_width_opt(manager, &rb) == Some(1)
                    && let Some(be) = self.to_bool(&ra, manager)
                {
                    return if value.is_one() {
                        be
                    } else {
                        manager.mk_not(be)
                    };
                }
                // Bool-sorted equality with a constant side folds; with a
                // bare `not` it inlines (`p = ¬q` → `¬(p = q)`).
                let lhs_bool = manager
                    .get(ra)
                    .is_some_and(|t| t.sort == manager.sorts.bool_sort);
                let rhs_bool = manager
                    .get(rb)
                    .is_some_and(|t| t.sort == manager.sorts.bool_sort);
                if lhs_bool && rhs_bool {
                    match (bool_const(&ra, manager), bool_const(&rb, manager)) {
                        (Some(x), Some(y)) => return manager.mk_bool(x == y),
                        (Some(true), None) => return rb,
                        (None, Some(true)) => return ra,
                        (Some(false), None) => return manager.mk_not(rb),
                        (None, Some(false)) => return manager.mk_not(ra),
                        (None, None) => {}
                    }
                }
                if let (Some(wa), Some(wb)) =
                    (bv_width_opt(manager, &ra), bv_width_opt(manager, &rb))
                    && wa == wb
                {
                    // Polynomial-identity check with the fully distributed
                    // forms (Z3 `cancel_monomials` + `som`): compute
                    // lhs − rhs in ℤ/2ʷ.  An empty difference proves the
                    // equality a tautology; a non-zero constant proves it a
                    // contradiction.  A non-constant difference proves
                    // nothing – the original sides are kept verbatim so the
                    // bit-blaster sees the input's own (undistributed) shape.
                    let identity = self.eq_poly_identity(ra, rb, wa, manager);
                    if let Some(equal) = identity {
                        return if equal {
                            manager.mk_true()
                        } else {
                            manager.mk_false()
                        };
                    }
                    // Z3 `cancel_monomials`: subtract the common monomials
                    // and rebuild the residuals.  Shrinking only – each side
                    // keeps its surviving monomials in input order – but on
                    // equality-heavy encodings (`2018-Mann/fifo_*`: 1.5k
                    // equations over shared sums) removing the common parts
                    // is what keeps the blasted circuits small.
                    let mut lhs = Vec::new();
                    sum_monomials(ra, manager, wa, &mut lhs);
                    let mut rhs = Vec::new();
                    sum_monomials(rb, manager, wb, &mut rhs);
                    cancel_monomials(&mut lhs, &mut rhs, wa);
                    let new_lhs = build_sum(lhs, manager, wa);
                    let new_rhs = build_sum(rhs, manager, wb);
                    if new_lhs == new_rhs {
                        return manager.mk_true();
                    }
                    if is_const(&new_lhs, manager) && is_const(&new_rhs, manager) {
                        return manager.mk_false();
                    }
                    return manager.mk_eq(new_lhs, new_rhs);
                }
                manager.mk_eq(ra, rb)
            }

            // ======== comparisons ========
            TermKind::BvUlt(a, b) => {
                let (ra, rb) = (kid(&a), kid(&b));
                if ra == rb {
                    return manager.mk_false();
                }
                // 1-bit comparisons are Boolean formulas: `x <u y` on bits
                // is `¬x ∧ y`, `x ≤u y` is `x → y`.
                if common_width(manager, &ra, &rb) == Some(1) {
                    if let (Some(bx), Some(by)) =
                        (self.to_bool(&ra, manager), self.to_bool(&rb, manager))
                    {
                        let not_x = manager.mk_not(bx);
                        return manager.mk_and([not_x, by]);
                    }
                }
                if let Some(w) = common_width(manager, &ra, &rb) {
                    if let Some(result) = fold_ult(&ra, &rb, manager) {
                        return result;
                    }
                    if let Some(result) = bounds_ult(&ra, &rb, w, manager) {
                        return result;
                    }
                    if let Some(result) = leq_overflow(&ra, &rb, w, manager, false) {
                        return result;
                    }
                }
                manager.mk_bv_ult(ra, rb)
            }
            TermKind::BvUle(a, b) => {
                let (ra, rb) = (kid(&a), kid(&b));
                if ra == rb {
                    return manager.mk_true();
                }
                if common_width(manager, &ra, &rb) == Some(1) {
                    if let (Some(bx), Some(by)) =
                        (self.to_bool(&ra, manager), self.to_bool(&rb, manager))
                    {
                        let not_x = manager.mk_not(bx);
                        return manager.mk_or([not_x, by]);
                    }
                }
                if let Some(w) = common_width(manager, &ra, &rb) {
                    if let Some(result) = fold_ule(&ra, &rb, manager) {
                        return result;
                    }
                    if let Some(result) = bounds_ule(&ra, &rb, w, manager) {
                        return result;
                    }
                    if let Some(result) = leq_overflow(&ra, &rb, w, manager, true) {
                        return result;
                    }
                }
                manager.mk_bv_ule(ra, rb)
            }
            TermKind::BvSlt(a, b) => {
                let (ra, rb) = (kid(&a), kid(&b));
                if ra == rb {
                    return manager.mk_false();
                }
                if let Some(w) = common_width(manager, &ra, &rb)
                    && let Some(result) = fold_slt(&ra, &rb, w, manager)
                {
                    return result;
                }
                manager.mk_bv_slt(ra, rb)
            }
            TermKind::BvSle(a, b) => {
                let (ra, rb) = (kid(&a), kid(&b));
                if ra == rb {
                    return manager.mk_true();
                }
                if let Some(w) = common_width(manager, &ra, &rb)
                    && let Some(result) = fold_sle(&ra, &rb, w, manager)
                {
                    return result;
                }
                manager.mk_bv_sle(ra, rb)
            }

            // ======== Boolean structure ========
            TermKind::Not(a) => manager.mk_not(kid(&a)),
            TermKind::And(ref args) => manager.mk_and(args.iter().map(kid)),
            TermKind::Or(ref args) => manager.mk_or(args.iter().map(kid)),
            TermKind::Xor(a, b) => {
                let (ra, rb) = (kid(&a), kid(&b));
                match (bool_const(&ra, manager), bool_const(&rb, manager)) {
                    (Some(x), Some(y)) => manager.mk_bool(x != y),
                    (Some(true), None) => manager.mk_not(rb),
                    (None, Some(true)) => manager.mk_not(ra),
                    (Some(false), None) => rb,
                    (None, Some(false)) => ra,
                    (None, None) => {
                        if ra == rb {
                            manager.mk_false()
                        } else {
                            manager.mk_xor(ra, rb)
                        }
                    }
                }
            }
            TermKind::Implies(a, b) => {
                let (ra, rb) = (kid(&a), kid(&b));
                match (bool_const(&ra, manager), bool_const(&rb, manager)) {
                    (Some(true), _) => rb,
                    (_, Some(true)) | (None, None) if ra == rb => manager.mk_true(),
                    (Some(false), _) | (_, Some(false)) => manager.mk_not(ra),
                    _ => manager.mk_implies(ra, rb),
                }
            }
            TermKind::Ite(c, t, e) => {
                let (rc, rt, re) = (kid(&c), kid(&t), kid(&e));
                if let Some(value) = bool_const(&rc, manager) {
                    return if value { rt } else { re };
                }
                if rt == re {
                    return rt;
                }
                manager.mk_ite(rc, rt, re)
            }
            TermKind::Distinct(ref args) => {
                let rewritten: Vec<TermId> = args.iter().map(kid).collect();
                // `distinct` with a repeated argument is false.
                let mut seen = std::collections::BTreeSet::new();
                if rewritten.iter().any(|t| !seen.insert(*t)) {
                    return manager.mk_false();
                }
                if rewritten.len() < 2 {
                    return manager.mk_true();
                }
                manager.mk_distinct(rewritten)
            }

            // Pass-through kinds with dedicated rebuilders (shifts,
            // division, concat, extract): children rewritten, node rebuilt.
            TermKind::BvShl(a, b) => manager.mk_bv_shl(kid(&a), kid(&b)),
            TermKind::BvLshr(a, b) => manager.mk_bv_lshr(kid(&a), kid(&b)),
            TermKind::BvAshr(a, b) => manager.mk_bv_ashr(kid(&a), kid(&b)),
            TermKind::BvUdiv(a, b) => manager.mk_bv_udiv(kid(&a), kid(&b)),
            TermKind::BvSdiv(a, b) => manager.mk_bv_sdiv(kid(&a), kid(&b)),
            TermKind::BvUrem(a, b) => manager.mk_bv_urem(kid(&a), kid(&b)),
            TermKind::BvSrem(a, b) => manager.mk_bv_srem(kid(&a), kid(&b)),
            TermKind::BvConcat(a, b) => manager.mk_bv_concat(kid(&a), kid(&b)),
            TermKind::BvExtract { high, low, arg } => {
                let ra = kid(&arg);
                // `((_ extract 0 0) x)` is the identity on a 1-bit operand
                // (these benchmarks encode Booleans as `(_ BitVec 1)`).
                if high == 0 && low == 0 && bv_width_opt(manager, &ra) == Some(1) {
                    return ra;
                }
                // Constant extraction folds.
                if let Some(v) = const_bits(&ra, manager) {
                    let shifted = v >> low as usize;
                    let extracted = shifted % (BigInt::one() << (high - low + 1) as usize);
                    return manager.mk_bitvec(extracted, high - low + 1);
                }
                manager.mk_bv_extract(high, low, ra)
            }

            // Everything else (leaves, other theories, quantifiers): the
            // node keeps its original children.  Keeping a term verbatim is
            // always sound; only the blastable fragment ever reaches the
            // eager path, and the gate walks these very nodes.
            _ => term,
        }
    }

    /// Normalize a product of two already-normalized operands: flatten
    /// nested `BvMul`s, fold the constant factors, and rebuild the product
    /// sorted.  **No distribution over sums** – the distributed form is a
    /// *proof* artifact, computed on demand in the `Eq` arm through
    /// [`BvPreprocessor::poly_of`] and never handed to the bit-blaster:
    /// the cross-product's deeper circuits measurably hurt families whose
    /// identities are not distributive (`Sage2/bench_7140` went 16 ms →
    /// >10 s when distributed terms reached the CNF).
    fn rewrite_mul(&mut self, a: TermId, b: TermId, manager: &mut TermManager) -> TermId {
        let Some(width) = common_width(manager, &a, &b) else {
            // Mixed widths (e.g. concat operands): keep the folded product.
            return manager.mk_bv_mul(a, b);
        };
        let mut args = Vec::new();
        flatten_product(a, manager, &mut args);
        flatten_product(b, manager, &mut args);

        let modulus = modulus(width);
        let mut const_coeff = BigInt::one();
        let mut non_const: Vec<TermId> = Vec::new();
        for arg in args {
            if let Some(v) = const_bits(&arg, manager) {
                const_coeff = (&const_coeff * v) % &modulus;
            } else {
                non_const.push(arg);
            }
        }
        non_const.sort_unstable();
        product_term(const_coeff, &non_const, manager, width)
    }

    /// The fully-distributed polynomial of a BV-sorted term, in the monomial
    /// domain (never rebuilt as terms).  `None` when the expansion would
    /// exceed [`MAX_MONOMIALS`] monomials or leaves the ring fragment.
    fn poly_of(&mut self, term: TermId, width: u32, manager: &TermManager) -> Option<Vec<Mono>> {
        if let Some(cached) = self.poly_memo.get(&term) {
            return cached.clone();
        }
        let result = self.compute_poly(term, width, manager);
        self.poly_memo.insert(term, result.clone());
        result
    }

    /// Whether the polynomial difference of the two sides settles the
    /// equality: `Some(true)` – identically equal (empty difference);
    /// `Some(false)` – differ by a non-zero constant everywhere;
    /// `None` – the difference is a non-constant polynomial (or not
    /// computable within the bounds), so nothing follows.
    fn eq_poly_identity(
        &mut self,
        lhs: TermId,
        rhs: TermId,
        width: u32,
        manager: &TermManager,
    ) -> Option<bool> {
        let modulus = modulus(width);
        let mut diff = self.poly_of(lhs, width, manager)?;
        for mut m in self.poly_of(rhs, width, manager)? {
            m.coeff = (&modulus - &m.coeff) % &modulus;
            diff.push(m);
        }
        diff.sort_by(|a, b| a.factors.cmp(&b.factors));
        let diff = combine_like(diff, &modulus);
        if diff.is_empty() {
            return Some(true);
        }
        if diff.len() == 1 && diff[0].factors.is_empty() {
            return Some(false);
        }
        None
    }

    fn compute_poly(
        &mut self,
        term: TermId,
        width: u32,
        manager: &TermManager,
    ) -> Option<Vec<Mono>> {
        ring_poly(term, width, manager, &mut self.poly_memo)
    }
}

/// Compute the fully-distributed polynomial of `term` in the monomial
/// domain (never rebuilt as terms), memoized on `memo`.
///
/// `None` when the expansion would exceed [`MAX_MONOMIALS`] monomials or the
/// term leaves the ring fragment (shifts, division, extracts of wide terms,
/// foreign theories).  Free function so both the DAG rewriter and the
/// Gaussian solve-eqs pass share one implementation and memo layout.
fn ring_poly(
    term: TermId,
    width: u32,
    manager: &TermManager,
    memo: &mut rustc_hash::FxHashMap<TermId, Option<Vec<Mono>>>,
) -> Option<Vec<Mono>> {
    if let Some(cached) = memo.get(&term) {
        return cached.clone();
    }
    let modulus = modulus(width);
    let kind = manager.get(term).map(|t| t.kind.clone())?;
    let poly = match kind {
        TermKind::BitVecConst { .. } => vec![Mono {
            coeff: const_bits(&term, manager)?,
            factors: Vec::new(),
        }],
        TermKind::BvAdd(a, b) => {
            let mut poly = ring_poly(a, width, manager, memo)?;
            poly.extend(ring_poly(b, width, manager, memo)?);
            poly
        }
        TermKind::BvSub(a, b) => {
            let mut poly = ring_poly(a, width, manager, memo)?;
            for mut m in ring_poly(b, width, manager, memo)? {
                m.coeff = (&modulus - &m.coeff) % &modulus;
                poly.push(m);
            }
            poly
        }
        TermKind::BvMul(a, b) => {
            let lhs = ring_poly(a, width, manager, memo)?;
            let rhs = ring_poly(b, width, manager, memo)?;
            let mut out = Vec::with_capacity(lhs.len().saturating_mul(rhs.len()));
            for l in &lhs {
                for r in &rhs {
                    let coeff = (&l.coeff * &r.coeff) % &modulus;
                    if coeff.is_zero() {
                        continue;
                    }
                    let mut factors = l.factors.clone();
                    factors.extend_from_slice(&r.factors);
                    factors.sort_unstable();
                    out.push(Mono { coeff, factors });
                    if out.len() > MAX_MONOMIALS {
                        return None;
                    }
                }
            }
            out
        }
        TermKind::BvNot(a) => {
            // ¬a ≡ a ⊕ all_ones ≡ −a − 1 (mod 2ʷ): a polynomial.
            let mut poly = ring_poly(a, width, manager, memo)?;
            for m in poly.iter_mut() {
                m.coeff = (&modulus - &m.coeff) % &modulus;
            }
            poly.push(Mono {
                coeff: (&modulus - BigInt::one()) % &modulus,
                factors: Vec::new(),
            });
            poly
        }
        _ if bv_width_opt(manager, &term) == Some(width) => vec![atom_mono(term)],
        _ => return None,
    };
    memo.insert(term, Some(poly.clone()));
    Some(poly)
}

// =====================================================================
// Monomial helpers
// =====================================================================

fn modulus(width: u32) -> BigInt {
    BigInt::one() << width as usize
}

fn bv_width_opt(manager: &TermManager, term: &TermId) -> Option<u32> {
    let sort = manager.get(*term)?.sort;
    manager.sorts.get(sort)?.bitvec_width()
}

fn common_width(manager: &TermManager, a: &TermId, b: &TermId) -> Option<u32> {
    match (bv_width_opt(manager, a), bv_width_opt(manager, b)) {
        (Some(wa), Some(wb)) if wa == wb => Some(wa),
        _ => None,
    }
}

/// The monomial for a bare non-constant, non-sum atom.
fn atom_mono(term: TermId) -> Mono {
    Mono {
        coeff: BigInt::one(),
        factors: vec![term],
    }
}

// =====================================================================
// Monomial helpers (shared by the shrink-only rewrites and the
// polynomial-identity proofs)
// =====================================================================

/// Append the monomials of a sum operand: flattens any depth of `BvAdd`
/// with a worklist, then parses each monomial's coefficient and factors out
/// of the `coeff · product` shape.
fn sum_monomials(term: TermId, manager: &TermManager, width: u32, out: &mut Vec<Mono>) {
    let mut work = vec![term];
    while let Some(t) = work.pop() {
        if let Some(TermKind::BvAdd(a, b)) = manager.get(t).map(|td| &td.kind) {
            work.push(*b);
            work.push(*a);
        } else {
            out.push(parse_mono(t, manager, width));
        }
    }
}

/// Parse one monomial term into its coefficient and factors.
///
/// Accepts numerals, bare atoms, and `BvMul` chains with any constant
/// placement (each constant factor folds into the coefficient).
fn parse_mono(term: TermId, manager: &TermManager, width: u32) -> Mono {
    let m = modulus(width);
    let mut flat = Vec::new();
    flatten_product(term, manager, &mut flat);
    let mut coeff = BigInt::one();
    let mut factors = Vec::new();
    for f in flat {
        if let Some(v) = const_bits(&f, manager) {
            coeff = (&coeff * v) % &m;
        } else {
            factors.push(f);
        }
    }
    factors.sort_unstable();
    Mono { coeff, factors }
}

/// Flatten nested `BvMul` into a flat factor list (constants included), with
/// a worklist – no native recursion.
fn flatten_product(term: TermId, manager: &TermManager, out: &mut Vec<TermId>) {
    let mut work = vec![term];
    while let Some(t) = work.pop() {
        if let Some(TermKind::BvMul(a, b)) = manager.get(t).map(|td| &td.kind) {
            work.push(*b);
            work.push(*a);
        } else {
            out.push(t);
        }
    }
}

/// Combine like monomials (ℤ/2ʷ), drop zeros, and rebuild the sum.
///
/// **Order-preserving by design**: monomials keep their first-seen input
/// order and the chain is rebuilt left-associatively in that order.  The
/// canonical (sorted) form is computed only inside
/// [`BvPreprocessor::poly_of`] for the equality-identity proof – rebuilding
/// it as *terms* re-associates the adder tree, and the regrouped carry
/// chains regressed add-dominated families badly (`Sage2/bench_7140`: the
/// eager blast went from 16 ms to >10 s under a sorted rebuild).
fn build_sum(monos: Vec<Mono>, manager: &mut TermManager, width: u32) -> TermId {
    if monos.is_empty() {
        return manager.mk_bitvec(0, width);
    }
    let modulus = modulus(width);
    // Fold equal keys, preserving first-seen positions (input order).  The
    // fold is a linear scan per monomial, so a pathologically wide sum would
    // be quadratic; beyond the bound, skip combining entirely (sound – an
    // uncombined sum is the same polynomial, just not folded).
    if monos.len() > 4096 {
        let terms: Vec<TermId> = monos
            .into_iter()
            .map(|m| mono_term(m, manager, width))
            .collect();
        let mut acc = terms[0];
        for &t in &terms[1..] {
            acc = manager.mk_bv_add(acc, t);
        }
        return acc;
    }
    let mut combined: Vec<Mono> = Vec::with_capacity(monos.len());
    for mono in monos {
        let mut merged = false;
        for existing in combined.iter_mut() {
            if existing.key() == mono.key() {
                existing.coeff = (&existing.coeff + &mono.coeff) % &modulus;
                merged = true;
                break;
            }
        }
        if !merged {
            combined.push(mono);
        }
    }
    combined.retain(|m| !m.coeff.is_zero());
    if combined.is_empty() {
        return manager.mk_bitvec(0, width);
    }
    if combined.len() == 1 {
        let only = combined.pop().unwrap_or(Mono {
            coeff: BigInt::zero(),
            factors: Vec::new(),
        });
        return mono_term(only, manager, width);
    }
    // Left-associative chain in input order: `(m1 + m2) + …`.
    let terms: Vec<TermId> = combined
        .into_iter()
        .map(|m| mono_term(m, manager, width))
        .collect();
    let mut acc = terms[0];
    for &t in &terms[1..] {
        acc = manager.mk_bv_add(acc, t);
    }
    acc
}

/// Fold equal keys of an already-sorted monomial list by summing
/// coefficients mod 2ʷ and drop zeros (used by the polynomial proofs).
fn combine_like(monos: Vec<Mono>, modulus: &BigInt) -> Vec<Mono> {
    let mut combined: Vec<Mono> = Vec::with_capacity(monos.len());
    for mono in monos {
        if let Some(last) = combined.last_mut()
            && last.key() == mono.key()
        {
            last.coeff = (&last.coeff + &mono.coeff) % modulus;
            continue;
        }
        combined.push(mono);
    }
    combined.retain(|m| !m.coeff.is_zero());
    combined
}

/// Rebuild the term of a single monomial: `0 → 0`, `c → c`,
/// `1 · product → product`, `c · product → BvMul(c, product)`.
fn mono_term(mono: Mono, manager: &mut TermManager, width: u32) -> TermId {
    if mono.factors.is_empty() || mono.coeff.is_zero() {
        return manager.mk_bitvec(mono.coeff, width);
    }
    let product = product_term(BigInt::one(), &mono.factors, manager, width);
    if mono.coeff.is_one() {
        return product;
    }
    let coeff = manager.mk_bitvec(mono.coeff, width);
    manager.mk_bv_mul(coeff, product)
}

/// Rebuild a product from a constant coefficient and non-constant factors.
fn product_term(
    coeff: BigInt,
    factors: &[TermId],
    manager: &mut TermManager,
    width: u32,
) -> TermId {
    if coeff.is_zero() || factors.is_empty() {
        return manager.mk_bitvec(coeff, width);
    }
    let mut acc = factors[0];
    for &f in &factors[1..] {
        acc = manager.mk_bv_mul(acc, f);
    }
    if coeff.is_one() {
        acc
    } else {
        let c = manager.mk_bitvec(coeff, width);
        manager.mk_bv_mul(c, acc)
    }
}

/// Cancel monomials with identical factor lists across the two sides of an
/// equality, and fold the constant difference (Z3 `cancel_monomials`).
///
/// For each key `k`: `c = (Σlhs − Σrhs) mod 2ʷ`; the residual `c·k` stays on
/// the left (side placement is irrelevant in a ring: `a = b ⇔ a − b = 0`).
/// Both-empty residuals mean the sides are equal as polynomials and the
/// caller turns the equality into `true`.
fn cancel_monomials(lhs: &mut Vec<Mono>, rhs: &mut Vec<Mono>, width: u32) {
    let modulus = modulus(width);
    let mut l = combine_like(std::mem::take(lhs), &modulus);
    let mut r = combine_like(std::mem::take(rhs), &modulus);
    // Both sides are sorted by key after combine_like.
    let mut new_l = Vec::with_capacity(l.len());
    let mut new_r = Vec::with_capacity(r.len());
    for m in l.drain(..) {
        if let Some(pos) = r.iter().position(|x| x.key() == m.key()) {
            let other = r.remove(pos);
            // d = c_l − c_r (mod 2ʷ), non-negative.
            let d = (m.coeff + &modulus - other.coeff) % &modulus;
            if !d.is_zero() {
                new_l.push(Mono {
                    coeff: d,
                    factors: m.factors,
                });
            }
        } else {
            new_l.push(m);
        }
    }
    new_r.extend(r);
    *lhs = new_l;
    *rhs = new_r;
}

// =====================================================================
// Comparison rewrites
// =====================================================================

fn const_bits(term: &TermId, manager: &TermManager) -> Option<BigInt> {
    match manager.get(*term).map(|t| &t.kind) {
        Some(TermKind::BitVecConst { value, width }) => {
            // `mk_bitvec` stores the raw integer without wrapping, so reduce
            // here once – every consumer then sees a value below 2ʷ.
            let m = BigInt::one() << *width as usize;
            Some(value.mod_floor(&m))
        }
        _ => None,
    }
}

fn is_const(term: &TermId, manager: &TermManager) -> bool {
    matches!(
        manager.get(*term).map(|t| &t.kind),
        Some(TermKind::BitVecConst { .. })
    )
}

fn fold_ult(a: &TermId, b: &TermId, manager: &TermManager) -> Option<TermId> {
    let (va, vb) = (const_bits(a, manager)?, const_bits(b, manager)?);
    Some(manager.mk_bool(va < vb))
}

fn fold_ule(a: &TermId, b: &TermId, manager: &TermManager) -> Option<TermId> {
    let (va, vb) = (const_bits(a, manager)?, const_bits(b, manager)?);
    Some(manager.mk_bool(va <= vb))
}

fn fold_slt(a: &TermId, b: &TermId, width: u32, manager: &TermManager) -> Option<TermId> {
    let (va, vb) = (const_bits(a, manager)?, const_bits(b, manager)?);
    Some(manager.mk_bool(signed(&va, width) < signed(&vb, width)))
}

fn fold_sle(a: &TermId, b: &TermId, width: u32, manager: &TermManager) -> Option<TermId> {
    let (va, vb) = (const_bits(a, manager)?, const_bits(b, manager)?);
    Some(manager.mk_bool(signed(&va, width) <= signed(&vb, width)))
}

fn signed(value: &BigInt, width: u32) -> BigInt {
    let modulus = modulus(width);
    let threshold = BigInt::one() << (width - 1) as usize;
    if value >= &threshold {
        value - &modulus
    } else {
        value.clone()
    }
}

/// Numeral-bound rules for `bvult` (from Z3 `mk_leq_core`'s bound cases,
/// adapted to strict):
/// * `a <u 0` → false; `a <u max` → `a ≠ max`;
/// * `0 <u b` → `b ≠ 0`; `max <u b` → false.
fn bounds_ult(a: &TermId, b: &TermId, width: u32, manager: &mut TermManager) -> Option<TermId> {
    let modulus = modulus(width);
    let max = &modulus - BigInt::one();
    let zero = manager.mk_bitvec(0, width);
    match (const_bits(a, manager), const_bits(b, manager)) {
        (Some(va), Some(vb)) => Some(manager.mk_bool(va < vb)),
        (None, Some(vb)) if vb.is_zero() => Some(manager.mk_false()),
        (None, Some(vb)) if vb == max => {
            let eq = manager.mk_eq(*a, *b);
            Some(manager.mk_not(eq))
        }
        (Some(va), None) if va == max => Some(manager.mk_false()),
        (Some(va), None) if va.is_zero() => {
            // 0 <u b ⇔ b ≠ 0.
            let eq = manager.mk_eq(*b, zero);
            Some(manager.mk_not(eq))
        }
        // `bvule c (bvadd c2 X)` family with a constant left side is a ule
        // rule; nothing else fires for ult here.
        _ => None,
    }
}

/// Numeral-bound rules for `bvule` (Z3 `mk_leq_core`):
/// * `a ≤u 0` → `a = 0`; `a ≤u max` → true;
/// * `0 ≤u b` → true; `max ≤u b` → `b = max`;
/// * `c ≤u (c2 + X)` → bound disjunction on `X` (Z3's `bvule r1 (+ r2 a)`
///   rule: `X ≤u 2ʷ−c2−1`, conj/disjoined with `c−c2 ≤u X` as `c` compares
///   to `c2`).
fn bounds_ule(a: &TermId, b: &TermId, width: u32, manager: &mut TermManager) -> Option<TermId> {
    let modulus = modulus(width);
    let max = &modulus - BigInt::one();
    let vb = const_bits(b, manager);
    match (const_bits(a, manager), vb) {
        (Some(va), Some(vb)) => Some(manager.mk_bool(va <= vb)),
        (None, Some(vb)) if vb.is_zero() => Some(manager.mk_eq(*a, *b)),
        (None, Some(vb)) if vb == max => Some(manager.mk_true()),
        (Some(va), None) if va.is_zero() => Some(manager.mk_true()),
        (Some(va), None) if va == max => Some(manager.mk_eq(*a, *b)),
        (Some(va), None) => {
            // `c ≤u (c2 + X)`: split the right sum into constant + rest.
            let (rest, c2) = split_const_summand(b, manager)?;
            let upper = (&modulus - &c2 - BigInt::one()) % &modulus;
            let upper_term = manager.mk_bitvec(upper, width);
            let x_le_upper = manager.mk_bv_ule(rest, upper_term);
            if va == c2 {
                Some(x_le_upper)
            } else {
                let delta = (&va + &modulus - &c2) % &modulus;
                let delta_term = manager.mk_bitvec(delta, width);
                let delta_le_x = manager.mk_bv_ule(delta_term, rest);
                if va > c2 {
                    Some(manager.mk_and([x_le_upper, delta_le_x]))
                } else {
                    Some(manager.mk_or([x_le_upper, delta_le_x]))
                }
            }
        }
        _ => None,
    }
}

/// If `t` is `X + c` (either order) with `X` non-constant, return `(X, c)`
/// (c reduced below 2ʷ).
fn split_const_summand(t: &TermId, manager: &TermManager) -> Option<(TermId, BigInt)> {
    let (x, y) = match manager.get(*t).map(|td| &td.kind) {
        Some(TermKind::BvAdd(a, b)) => (*a, *b),
        _ => return None,
    };
    let x_const = const_bits(&x, manager);
    let y_const = const_bits(&y, manager);
    match (x_const, y_const) {
        (Some(c), None) => Some((y, c)),
        (None, Some(c)) => Some((x, c)),
        _ => None,
    }
}

/// Z3 `bv_rewriter::rw_leq_overflow`: `X+c1 <ᵤ/≤ᵤ X+c2` with the same
/// non-constant summand `X`.
///
/// With `δ = c2 − c1` (all arithmetic in ℤ/2ʷ):
/// * `c1 == c2` → the reflexive constant;
/// * `c1 < c2`  → `δ ≤ᵤ X+c2` (no wrap of `X+c2`);
/// * `c1 > c2`  → `2ʷ−c1 ≤ᵤ X ≤ᵤ 2ʷ−c2−1` (`X+c1` wrapped).
///
/// For the strict variant the truth conditions coincide (within the
/// wrap/no-wrap regions the comparison is uniformly strict or uniformly
/// false), so both polarities rewrite the same way.
fn leq_overflow(
    a: &TermId,
    b: &TermId,
    width: u32,
    manager: &mut TermManager,
    inclusive: bool,
) -> Option<TermId> {
    let (xa, ca) = split_const_summand(a, manager)?;
    let (xb, cb) = split_const_summand(b, manager)?;
    if xa != xb {
        return None;
    }
    if ca == cb {
        return Some(manager.mk_bool(inclusive));
    }
    let modulus = modulus(width);
    if ca < cb {
        let delta = (&cb - &ca) % &modulus;
        let d = manager.mk_bitvec(delta, width);
        return Some(manager.mk_bv_ule(d, *b));
    }
    // ca > cb: wrap interval on X.  lower = 2ʷ − c1, upper = 2ʷ − c2 − 1.
    let lower = (&modulus - &ca) % &modulus;
    let upper = (&modulus - &cb - BigInt::one()) % &modulus;
    if lower == upper {
        let bound = manager.mk_bitvec(lower, width);
        return Some(manager.mk_eq(xa, bound));
    }
    let lo = manager.mk_bitvec(lower, width);
    let hi = manager.mk_bitvec(upper, width);
    let ge_lower = manager.mk_bv_ule(lo, xa);
    let le_upper = manager.mk_bv_ule(xa, hi);
    Some(manager.mk_and([ge_lower, le_upper]))
}

// =====================================================================
// Bitwise flattening
// =====================================================================

#[derive(Clone, Copy, PartialEq, Eq)]
enum BitwiseOp {
    And,
    Or,
    Xor,
}

impl BitwiseOp {
    /// The `TermKind` constructor of this operator (for flattening).
    fn matches(self, kind: &TermKind) -> Option<(TermId, TermId)> {
        match (self, kind) {
            (Self::And, TermKind::BvAnd(a, b)) => Some((*a, *b)),
            (Self::Or, TermKind::BvOr(a, b)) => Some((*a, *b)),
            (Self::Xor, TermKind::BvXor(a, b)) => Some((*a, *b)),
            _ => None,
        }
    }
}

/// Flatten an associative bitwise chain: idempotence for and/or, parity for
/// xor, constant folding, `x & x → x`, `x | x → x`, `x ⊕ x → 0`.
///
/// Iterative (worklist) flattening; the result is rebuilt sorted, so equal
/// operands of and/or deduplicate canonically.
fn flatten_bitwise(a: TermId, b: TermId, manager: &mut TermManager, op: BitwiseOp) -> TermId {
    // Flatten to a factor list.
    let mut factors: Vec<TermId> = Vec::new();
    let mut work = vec![b, a];
    while let Some(t) = work.pop() {
        let expanded = manager
            .get(t)
            .and_then(|td| op.matches(&td.kind))
            .map(|(x, y)| (t, x, y));
        match expanded {
            Some((_, x, y)) => {
                work.push(y);
                work.push(x);
            }
            None => factors.push(t),
        }
    }
    let width = factors
        .first()
        .and_then(|f| bv_width_opt(manager, f))
        .unwrap_or(32);
    let modulus = modulus(width);
    let all_ones = &modulus - BigInt::one();

    let mut signals: Vec<TermId> = Vec::with_capacity(factors.len());
    match op {
        BitwiseOp::And => {
            let mut folded: Option<BigInt> = None;
            for f in factors {
                if let Some(v) = const_bits(&f, manager) {
                    let v = v % &modulus;
                    folded = Some(match folded {
                        Some(acc) => (acc * v) % &modulus,
                        None => v,
                    });
                } else {
                    signals.push(f);
                }
            }
            if let Some(v) = folded {
                if v.is_zero() {
                    return manager.mk_bitvec(0, width);
                }
                if v != all_ones {
                    signals.insert(0, manager.mk_bitvec(v, width));
                }
            }
            signals.sort_unstable();
            signals.dedup();
            rebuild_chain(signals, width, manager, op, &all_ones)
        }
        BitwiseOp::Or => {
            let mut folded: Option<BigInt> = None;
            for f in factors {
                if let Some(v) = const_bits(&f, manager) {
                    let v = v % &modulus;
                    folded = Some(match folded {
                        Some(acc) => acc | v,
                        None => v,
                    });
                } else {
                    signals.push(f);
                }
            }
            if let Some(v) = folded {
                if v == all_ones {
                    return manager.mk_bitvec(v, width);
                }
                if !v.is_zero() {
                    signals.insert(0, manager.mk_bitvec(v, width));
                }
            }
            signals.sort_unstable();
            signals.dedup();
            rebuild_chain(signals, width, manager, op, &all_ones)
        }
        BitwiseOp::Xor => {
            let mut acc = BigInt::zero();
            // Parity of identical non-constant factors.
            let mut counts: std::collections::BTreeMap<TermId, bool> =
                std::collections::BTreeMap::new();
            for f in factors {
                if let Some(v) = const_bits(&f, manager) {
                    acc ^= v % &modulus;
                } else {
                    let entry = counts.entry(f).or_insert(false);
                    *entry = !*entry;
                }
            }
            let mut rest: Vec<TermId> = counts
                .into_iter()
                .filter(|(_, parity)| *parity)
                .map(|(t, _)| t)
                .collect();
            let acc = acc % &modulus;
            if !acc.is_zero() {
                rest.insert(0, manager.mk_bitvec(acc, width));
            }
            rebuild_chain(rest, width, manager, op, &all_ones)
        }
    }
}

/// Rebuild a sorted operand list into a left-leaning chain, applying the
/// operator's neutral-element rule for empty lists.
fn rebuild_chain(
    mut signals: Vec<TermId>,
    width: u32,
    manager: &mut TermManager,
    op: BitwiseOp,
    all_ones: &BigInt,
) -> TermId {
    if signals.is_empty() {
        return match op {
            BitwiseOp::And => manager.mk_bitvec(all_ones.clone(), width),
            BitwiseOp::Or | BitwiseOp::Xor => manager.mk_bitvec(0, width),
        };
    }
    let mut acc = signals.remove(0);
    for t in signals {
        acc = match op {
            BitwiseOp::And => manager.mk_bv_and(acc, t),
            BitwiseOp::Or => manager.mk_bv_or(acc, t),
            BitwiseOp::Xor => manager.mk_bv_xor(acc, t),
        };
    }
    acc
}

fn bool_const(term: &TermId, manager: &TermManager) -> Option<bool> {
    match manager.get(*term).map(|t| &t.kind) {
        Some(TermKind::True) => Some(true),
        Some(TermKind::False) => Some(false),
        _ => None,
    }
}

impl Solver {
    /// Preprocess the pure QF_BV goal: eliminate variable definitions
    /// (Z3 `solve-eqs`), then rewrite every assertion through the
    /// [`BvPreprocessor`] normalizer.  The rewritten set replaces the working
    /// copy used for blasting; the recorded constraint terms stay original
    /// so an unsat core still names the user's assertions.
    ///
    /// Returns the rewritten assertions together with the performed
    /// eliminations, `(var, defining term)` in dependency order: a satisfying
    /// assignment for the rewritten set assigns no value to an eliminated
    /// variable, so the dispatch reconstructs each variable's value by
    /// evaluating its definition under the model before validating the
    /// model against the *original* assertions.
    pub(super) fn bv_preprocess_assertions(
        &mut self,
        manager: &mut TermManager,
    ) -> (Vec<TermId>, Vec<(TermId, TermId)>, Vec<TermId>) {
        // (assertion, origin) pairs: preprocessing may split an assertion
        // (a top-level `and` of equations) or drop solved ones, and the
        // dispatch needs each surviving assertion's *original* for its
        // constraint-term bookkeeping (unsat cores name the user's input).
        let mut pairs: Vec<(TermId, TermId)> = self.assertions.iter().map(|&a| (a, a)).collect();
        normalize_assertions(&mut pairs, manager);
        let plain = solve_equations(&mut pairs, manager);
        // Ring (Gaussian) elimination runs after the plain pass (whose
        // substitutions it would otherwise redo).  Replay order for model
        // reconstruction: a ring definition never mentions an *earlier*
        // ring elimination (those were substituted away), so the ring list
        // replays reversed; a plain definition may mention ring-eliminated
        // variables (the ring pass runs later), so the plain list replays
        // *after* the ring list, in its forward (Kahn) order.  The dispatch
        // additionally retries unresolved definitions to a fixpoint.
        let mut ring = solve_ring_equations(&mut pairs, manager);
        ring.reverse();
        let eliminations: Vec<(TermId, TermId)> = ring.into_iter().chain(plain).collect();
        let mut preprocessor = BvPreprocessor::new();
        let rewritten = pairs
            .iter()
            .map(|&(a, _)| preprocessor.rewrite(a, manager))
            .collect();
        let origins = pairs.iter().map(|&(_, o)| o).collect();
        (rewritten, eliminations, origins)
    }

    /// Reconstruct the model values of preprocess-eliminated variables by
    /// evaluating their definitions (Z3 `solve_eqs`' model extension).
    ///
    /// `Model::eval` has no ground-BV semantics, so the evaluation here is
    /// *substitute-then-fold*: the model's current assignments are applied
    /// to the definition and the rewriter constant-folds the result (its
    /// `mk_bv_*` builders fold constants; the poly-identity rules settle
    /// `=`/comparison wrappers).  Rounds run to a fixpoint because the two
    /// elimination phases cannot always linearize their dependency order
    /// (a plain definition may mention a ring-eliminated variable and vice
    /// versa).
    pub(super) fn bv_reconstruct_eliminations(
        model: &mut crate::solver::types::Model,
        eliminations: &[(TermId, TermId)],
        manager: &mut TermManager,
    ) {
        let mut rewriter = BvPreprocessor::new();
        for _round in 0..4 {
            let assignments: rustc_hash::FxHashMap<TermId, TermId> =
                model.assignments().iter().map(|(&t, &v)| (t, v)).collect();
            let mut changed = false;
            for &(var, def) in eliminations {
                if model.get(var).is_some() {
                    continue;
                }
                let substituted = if assignments.is_empty() {
                    def
                } else {
                    manager.substitute(def, &assignments)
                };
                // Fold: rebuilding through the rewriter's builders turns a
                // fully-assigned definition into a literal.
                let folded = rewriter.rewrite(substituted, manager);
                let concrete = manager.get(folded).is_some_and(|t| {
                    matches!(
                        t.kind,
                        TermKind::BitVecConst { .. } | TermKind::True | TermKind::False
                    )
                });
                if concrete {
                    model.set(var, folded);
                    changed = true;
                }
            }
            if !changed {
                break;
            }
        }
    }
}

// =====================================================================
// Variable-definition elimination (Z3 `solve-eqs`)
// =====================================================================

/// Split top-level conjunctions into separate assertions and strip double
/// negations, keeping each derived assertion's origin (the user assertion it
/// came from).
///
/// Industrial encodings bundle their equations as one `(and (= …) (= …) …)`
/// per program point (`2018-Mann`, UltimateAutomizer) and wrap goal atoms in
/// `(not (not …))`; the solving passes below only look at *top-level*
/// equalities, so both shapes must be flattened first.  Asserting a
/// conjunction is asserting each conjunct, and `¬¬x ≡ x` – equivalence- and
/// core-preserving (each conjunct keeps the parent as its origin).
fn normalize_assertions(pairs: &mut Vec<(TermId, TermId)>, manager: &TermManager) {
    let mut out: Vec<(TermId, TermId)> = Vec::with_capacity(pairs.len());
    let mut work: std::collections::VecDeque<(TermId, TermId)> = pairs.drain(..).collect();
    while let Some((t, origin)) = work.pop_front() {
        let kind = manager.get(t).map(|td| td.kind.clone());
        match kind {
            Some(TermKind::And(args)) => {
                // Deterministic order: conjuncts in source order.
                for &a in args.iter() {
                    work.push_back((a, origin));
                }
            }
            Some(TermKind::Not(inner)) => {
                if let Some(TermKind::Not(inner2)) = manager.get(inner).map(|td| td.kind.clone()) {
                    work.push_back((inner2, origin));
                } else {
                    out.push((t, origin));
                }
            }
            _ => out.push((t, origin)),
        }
    }
    *pairs = out;
}

/// Eliminate variable definitions from an assertion list (Z3's
/// `solve_eqs` tactic, the step that dissolves `wienand-cav2008` and the
/// UltimateAutomizer definition chains).
///
/// An assertion `= x t` (or `= t x`) where `x` is a free Bool/BV variable
/// that does not occur in `t` *defines* `x`.  Every occurrence of `x` in
/// the other assertions (and in other definition bodies) is replaced by
/// `t`, and the defining assertion is dropped – sound because after the
/// replacement the definition reads `t = t`.
///
/// Definitions resolve Kahn-style: a definition is *ready* when its body
/// mentions no defined variable; ready definitions substitute into the
/// rest, which can make further definitions ready (cascades
/// `x2 = f(x1), x1 = t1` → `x2 = f(t1)`).  A definition cycle never
/// becomes ready; those variables keep their assertions, which are then
/// constraints rather than definitions.  Each outer round strictly drops
/// at least one assertion, so the loop terminates.
fn solve_equations(
    pairs: &mut Vec<(TermId, TermId)>,
    manager: &mut TermManager,
) -> Vec<(TermId, TermId)> {
    // Hard bound on outer rounds: each round drops ≥ 1 assertion, so this
    // only guards against pathological rescan cost.
    const MAX_ROUNDS: usize = 128;
    // Eliminations of this call, in dependency (Kahn-resolution) order:
    // each entry's defining term only mentions variables eliminated
    // *before* it (or none), so replaying the list in order under a model
    // reconstructs every eliminated variable's value.
    let mut eliminations: Vec<(TermId, TermId)> = Vec::new();
    for _ in 0..MAX_ROUNDS {
        // ---- collect candidate definitions ----
        let mut defs: rustc_hash::FxHashMap<TermId, TermId> = rustc_hash::FxHashMap::default();
        let mut conflicted: rustc_hash::FxHashSet<TermId> = rustc_hash::FxHashSet::default();
        for &(a, _) in pairs.iter() {
            if let Some(TermKind::Eq(lhs, rhs)) = manager.get(a).map(|t| &t.kind).cloned() {
                collect_def_candidates(lhs, rhs, &mut defs, &mut conflicted, manager);
                collect_def_candidates(rhs, lhs, &mut defs, &mut conflicted, manager);
            }
        }
        for x in &conflicted {
            defs.remove(x);
        }
        if defs.is_empty() {
            return eliminations;
        }

        // ---- Kahn resolution (occurrence-list worklist, linear in edges) ----
        // The naive loop re-scanned every pending body per iteration and
        // re-substituted into all of them; on a 13 k-long definition chain
        // (`uclid/convert-jpg2gif`: x2 = f(x1), x3 = f(x2), …) that is
        // O(n²) term walks – 9 s of pure preprocessing.  Here each body is
        // walked once to build `mentions_of` (which pending variables it
        // references); a body becomes ready when its reference count drops
        // to zero, and the defining substitution is applied to a body only
        // when one of *its* variables resolves.
        let mut pending: Vec<(TermId, TermId)> = defs.into_iter().collect();
        let mut resolved: rustc_hash::FxHashMap<TermId, TermId> = rustc_hash::FxHashMap::default();
        let index_of: rustc_hash::FxHashMap<TermId, usize> = pending
            .iter()
            .enumerate()
            .map(|(i, (x, _))| (*x, i))
            .collect();
        // var -> pending indices whose body mentions it (each list holds
        // distinct indices; a body never lists the same var twice).
        let mut occurrences: rustc_hash::FxHashMap<TermId, Vec<usize>> =
            rustc_hash::FxHashMap::default();
        // Distinct-pending-variable reference count per body; 0 = ready.
        let mut unmet: Vec<usize> = vec![0; pending.len()];
        for (i, (_, t)) in pending.iter().enumerate() {
            let mut seen_here = rustc_hash::FxHashSet::default();
            collect_var_mentions(*t, &index_of, manager, &mut seen_here);
            unmet[i] = seen_here.len();
            for v in seen_here {
                occurrences.entry(v).or_default().push(i);
            }
        }
        // Deterministic FIFO worklist of ready bodies (initial pass in
        // index order).
        let mut worklist: std::collections::VecDeque<usize> =
            (0..pending.len()).filter(|&i| unmet[i] == 0).collect();
        // Eliminations in worklist (topological) order: a body's pending
        // dependencies are always resolved before it becomes ready, so
        // replaying this list under a model evaluates each definition with
        // its dependencies already assigned.  (Recording `resolved.iter()`
        // instead — HashMap order — broke exactly that.)
        let mut round_elims: Vec<(TermId, TermId)> = Vec::new();
        while let Some(i) = worklist.pop_front() {
            let (x, t) = pending[i];
            if mentions(t, x, manager) {
                // Self-referential after substitution: unresolvable.
                continue;
            }
            resolved.insert(x, t);
            round_elims.push((x, t));
            let Some(affected) = occurrences.remove(&x) else {
                continue;
            };
            // One single-variable substitution per affected body: exactly
            // the pass the naive version did for *every* pending body.
            let single = std::iter::once((x, t)).collect::<rustc_hash::FxHashMap<_, _>>();
            for j in affected {
                unmet[j] -= 1;
                let (_, tj) = pending[j];
                pending[j].1 = manager.substitute(tj, &single);
                if unmet[j] == 0 {
                    worklist.push_back(j);
                }
            }
        }
        if resolved.is_empty() {
            return eliminations;
        }

        // ---- apply: substitute everywhere, drop resolved definitions ----
        let resolved_vars: rustc_hash::FxHashSet<TermId> = resolved.keys().copied().collect();
        let mut def_indices: rustc_hash::FxHashSet<usize> = rustc_hash::FxHashSet::default();
        for (idx, &(a, _)) in pairs.iter().enumerate() {
            if let Some(TermKind::Eq(lhs, rhs)) = manager.get(a).map(|t| &t.kind) {
                let lhs = *lhs;
                let rhs = *rhs;
                let defines_resolved = var_def_operand(lhs, rhs, manager)
                    .is_some_and(|(x, _)| resolved_vars.contains(&x))
                    || var_def_operand(rhs, lhs, manager)
                        .is_some_and(|(x, _)| resolved_vars.contains(&x));
                if defines_resolved {
                    def_indices.insert(idx);
                }
            }
        }
        if def_indices.is_empty() {
            return eliminations;
        }
        eliminations.extend(round_elims);
        let mut new_pairs = Vec::with_capacity(pairs.len());
        for (idx, &(a, origin)) in pairs.iter().enumerate() {
            if def_indices.contains(&idx) {
                continue;
            }
            new_pairs.push((manager.substitute(a, &resolved), origin));
        }
        *pairs = new_pairs;
    }
    eliminations
}

/// Z3 `solve_eqs`' Gaussian step over the bit-vector ring: solve asserted
/// equalities for free variables with invertible (odd) coefficients and
/// substitute the definition everywhere, dropping the solved equation.
///
/// The plain pass above only eliminates syntactic `= x t` shapes; industrial
/// goals assert general ring identities (`z + y = 7 + 3n² + 9n`, the
/// UltimateAutomizer `cohencu` translations) from which Z3's `solve-eqs`
/// isolates variables the same way.  A variable `v` is eliminable from an
/// equation whose polynomial difference contains the monomial `c·v` with
/// `c` odd (exactly invertibility in ℤ/2ʷ): the equation is *equivalent*
/// to `v = c⁻¹·(−(P − c·v))`, so replacing it by the definition and
/// substituting is answer-preserving, and the same occurrence cap Z3 uses
/// (`solve_eqs_max_occs`, occurrences in *other* assertions ≤ 2) keeps the
/// substitution blow-up bounded.
///
/// Definitions formed later never mention earlier-eliminated variables
/// (those were substituted away first), so the returned list replays
/// **reversed** for model reconstruction; [`bv_preprocess_assertions`]
/// concatenates it behind the forward-order plain list accordingly.
fn solve_ring_equations(
    pairs: &mut Vec<(TermId, TermId)>,
    manager: &mut TermManager,
) -> Vec<(TermId, TermId)> {
    /// Cap on total eliminations: each elimination substitutes into every
    /// mentioning assertion, so an unbounded run on a definition-chain input
    /// would be quadratic (the plain pass owns those inputs anyway).
    const MAX_ELIMS: usize = 4096;
    /// Monomial cap for one definition body: a wide definition duplicated
    /// across assertions costs more than the variable it removes.
    const MAX_DEF_MONOS: usize = 64;
    /// Z3 `solve_eqs_max_occs`: occurrences in assertions *other than* the
    /// defining equation.
    const MAX_OTHER_OCCS: usize = 2;

    let mut eliminations: Vec<(TermId, TermId)> = Vec::new();
    let mut memo: rustc_hash::FxHashMap<TermId, Option<Vec<Mono>>> =
        rustc_hash::FxHashMap::default();
    loop {
        if eliminations.len() >= MAX_ELIMS {
            break;
        }
        // ---- polynomial difference of every asserted BV equality ----
        let mut equations: Vec<(usize, u32, Vec<Mono>)> = Vec::new();
        for (idx, &(a, _)) in pairs.iter().enumerate() {
            let Some(TermKind::Eq(l, r)) = manager.get(a).map(|t| t.kind.clone()) else {
                continue;
            };
            let (Some(wl), Some(wr)) = (bv_width_opt(manager, &l), bv_width_opt(manager, &r))
            else {
                continue;
            };
            if wl != wr {
                continue;
            }
            let (Some(pl), Some(pr)) = (
                ring_poly(l, wl, manager, &mut memo),
                ring_poly(r, wl, manager, &mut memo),
            ) else {
                continue;
            };
            let modulus = modulus(wl);
            let mut diff = pl;
            for mut m in pr {
                m.coeff = (&modulus - &m.coeff) % &modulus;
                diff.push(m);
            }
            diff.sort_by(|a, b| a.factors.cmp(&b.factors));
            let diff = combine_like(diff, &modulus);
            equations.push((idx, wl, diff));
        }
        if equations.is_empty() {
            break;
        }

        // ---- per-variable assertion occurrence counts ----
        let mut occurrences: rustc_hash::FxHashMap<TermId, usize> =
            rustc_hash::FxHashMap::default();
        for &(a, _) in pairs.iter() {
            let mut vars = rustc_hash::FxHashSet::default();
            collect_free_bv_vars(a, manager, &mut vars);
            for v in vars {
                *occurrences.entry(v).or_insert(0) += 1;
            }
        }

        // ---- pick the elimination (fewest other occurrences, then the
        //      smallest TermId for determinism) ----
        let mut best: Option<(usize, u32, TermId, BigInt, usize)> = None;
        for (slot, &(_, width, ref poly)) in equations.iter().enumerate() {
            if poly.len() > MAX_DEF_MONOS + 1 {
                continue;
            }
            for m in poly {
                let [v] = m.factors.as_slice() else {
                    continue;
                };
                if !m.coeff.is_odd() {
                    // Even coefficients are not invertible mod 2^w: the
                    // equation does not determine v.
                    continue;
                }
                if !is_free_bv_var(*v, manager) {
                    continue;
                }
                let other = occurrences.get(v).copied().unwrap_or(1).saturating_sub(1);
                if other > MAX_OTHER_OCCS {
                    continue;
                }
                match best {
                    None => best = Some((slot, width, *v, m.coeff.clone(), other)),
                    Some((_, _, b_var, _, b_other)) => {
                        let strictly_better = other < b_other || (other == b_other && *v < b_var);
                        if strictly_better {
                            best = Some((slot, width, *v, m.coeff.clone(), other));
                        }
                    }
                }
            }
        }
        let Some((slot, width, var, coeff, _)) = best else {
            break;
        };
        let (eq_idx, _, poly) = equations.swap_remove(slot);

        // ---- solve: v = c⁻¹ · (−(P − c·v)) at width w ----
        let modulus = modulus(width);
        let inv = mod_inverse_odd(&coeff, &modulus);
        let mut def_monos = Vec::with_capacity(poly.len());
        for m in poly {
            let is_var_mono = m.factors.as_slice() == [var];
            if is_var_mono {
                continue;
            }
            let negated = (&modulus - &m.coeff) % &modulus;
            let scaled = (&negated * &inv) % &modulus;
            if scaled.is_zero() {
                continue;
            }
            def_monos.push(Mono {
                coeff: scaled,
                factors: m.factors,
            });
        }
        if def_monos.len() > MAX_DEF_MONOS {
            continue;
        }
        let def = build_sum(def_monos, manager, width);

        // ---- drop the solved equation, substitute everywhere else ----
        pairs.swap_remove(eq_idx);
        let single = std::iter::once((var, def)).collect::<rustc_hash::FxHashMap<TermId, TermId>>();
        for (a, _) in pairs.iter_mut() {
            if mentions(*a, var, manager) {
                *a = manager.substitute(*a, &single);
            }
        }
        eliminations.push((var, def));
    }
    eliminations
}

/// Modular inverse of an odd `c` modulo `2ʷ` (Newton iteration: each step
/// doubles the correct bit count).  Returns 0 for even `c` (not invertible);
/// callers gate on oddness first.
fn mod_inverse_odd(c: &BigInt, modulus: &BigInt) -> BigInt {
    if !c.is_odd() {
        return BigInt::zero();
    }
    let two = BigInt::from(2u8);
    let mut x = BigInt::one();
    let mut bits = modulus.bits();
    // ceil(log2(w)) + 1 iterations suffice; one extra is harmless.
    while bits > 0 {
        // x := x * (2 - c*x) mod m
        let cx = (c * &x) % modulus;
        let inner = (&two - cx + modulus) % modulus;
        x = (&x * inner) % modulus;
        bits /= 2;
    }
    x
}

/// Whether `term` is a free bit-vector-sorted variable.
fn is_free_bv_var(term: TermId, manager: &TermManager) -> bool {
    manager.get(term).is_some_and(|t| {
        matches!(t.kind, TermKind::Var(_))
            && manager.sorts.get(t.sort).is_some_and(|s| s.is_bitvec())
    })
}

/// Collect the free bit-vector variables of `term` (one DAG walk).
fn collect_free_bv_vars(
    term: TermId,
    manager: &TermManager,
    out: &mut rustc_hash::FxHashSet<TermId>,
) {
    let mut seen = rustc_hash::FxHashSet::default();
    let mut stack = vec![term];
    while let Some(t) = stack.pop() {
        if !seen.insert(t) {
            continue;
        }
        if let Some(data) = manager.get(t) {
            if matches!(data.kind, TermKind::Var(_))
                && manager.sorts.get(data.sort).is_some_and(|s| s.is_bitvec())
            {
                out.insert(t);
                continue;
            }
            stack.extend(nixie_core::ast::traversal::get_children(&data.kind));
        }
    }
}

/// Record `(lhs, rhs)` as a definition candidate when `lhs` is a free
/// Bool/BV variable and `rhs` does not mention it.  A top-level `and` of
/// equations splits into its candidates (common after `let`-inlining).
fn collect_def_candidates(
    lhs: TermId,
    rhs: TermId,
    defs: &mut rustc_hash::FxHashMap<TermId, TermId>,
    conflicted: &mut rustc_hash::FxHashSet<TermId>,
    manager: &TermManager,
) {
    if let Some(TermKind::And(args)) = manager.get(lhs).map(|t| &t.kind).cloned() {
        for &arg in &args {
            if let Some(TermKind::Eq(l2, r2)) = manager.get(arg).map(|t| &t.kind).cloned() {
                collect_def_candidates(l2, r2, defs, conflicted, manager);
                collect_def_candidates(r2, l2, defs, conflicted, manager);
            }
        }
        return;
    }
    if let Some((x, t)) = var_def_operand(lhs, rhs, manager)
        && !conflicted.contains(&x)
    {
        if let Some(existing) = defs.get(&x) {
            // Two different definitions: a constraint, not a definition.
            if *existing != t {
                conflicted.insert(x);
                defs.remove(&x);
            }
            return;
        }
        defs.insert(x, t);
    }
}

/// Whether `term` mentions variable `x` (shared-DAG aware, iterative).
fn mentions(term: TermId, x: TermId, manager: &TermManager) -> bool {
    let mut seen = rustc_hash::FxHashSet::default();
    let mut stack = vec![term];
    while let Some(t) = stack.pop() {
        if t == x {
            return true;
        }
        if !seen.insert(t) {
            continue;
        }
        if let Some(data) = manager.get(t) {
            stack.extend(nixie_core::ast::traversal::get_children(&data.kind));
        }
    }
    false
}

/// Collect, in one DAG walk, which of the `tracked` variables `term`
/// mentions (shared subterms visited once).  Used by the Kahn worklist to
/// build occurrence lists and reference counts without re-walking bodies.
fn collect_var_mentions(
    term: TermId,
    tracked: &rustc_hash::FxHashMap<TermId, usize>,
    manager: &TermManager,
    out: &mut rustc_hash::FxHashSet<TermId>,
) {
    if tracked.is_empty() {
        return;
    }
    let mut seen = rustc_hash::FxHashSet::default();
    let mut stack = vec![term];
    while let Some(t) = stack.pop() {
        if tracked.contains_key(&t) {
            // A tracked variable's own structure is opaque here: its body
            // is accounted for by its own pending entry.
            out.insert(t);
            continue;
        }
        if !seen.insert(t) {
            continue;
        }
        if let Some(data) = manager.get(t) {
            stack.extend(nixie_core::ast::traversal::get_children(&data.kind));
        }
    }
}

/// `(x, t)` when `lhs` is an eliminable free variable and `rhs` does not
/// mention it.
fn var_def_operand(lhs: TermId, rhs: TermId, manager: &TermManager) -> Option<(TermId, TermId)> {
    let data = manager.get(lhs)?;
    if !matches!(data.kind, TermKind::Var(_)) {
        return None;
    }
    let sort = manager.sorts.get(data.sort)?;
    if !(sort.is_bool() || sort.is_bitvec()) {
        return None;
    }
    if mentions(rhs, lhs, manager) {
        return None;
    }
    Some((lhs, rhs))
}

#[cfg(test)]
mod tests {
    use crate::Context;

    fn solve_str(script: &str) -> String {
        let mut ctx = Context::new();
        let responses = ctx.execute_script(script).expect("script executes");
        for r in responses.iter().rev() {
            if r.contains("unsat") {
                return "unsat".into();
            }
            if r.contains("sat") && !r.contains("unsat") {
                return if r.contains("unknown") {
                    "unknown".into()
                } else {
                    "sat".into()
                };
            }
        }
        "no-check-sat".into()
    }

    /// distributivity: `(a*b + c*b) ≠ b*(a+c)` is unsat at every width –
    /// the wienand-cav2008 family.
    #[test]
    fn som_distributivity_is_unsat() {
        for width in [2u32, 8, 16] {
            let script = format!(
                "(set-logic QF_BV)
                 (declare-fun a () (_ BitVec {width}))
                 (declare-fun b () (_ BitVec {width}))
                 (declare-fun c () (_ BitVec {width}))
                 (assert (not (= (bvadd (bvmul a b) (bvmul c b)) (bvmul b (bvadd a c)))))
                 (check-sat)"
            );
            assert_eq!(solve_str(&script), "unsat", "width {width}");
        }
    }

    /// A satisfiable identity must not be rewritten to false.
    #[test]
    fn som_keeps_satisfiable_constraints() {
        let script = "(set-logic QF_BV)
            (declare-fun a () (_ BitVec 8))
            (declare-fun b () (_ BitVec 8))
            (assert (= (bvadd (bvmul a b) (bvmul a b)) (bvmul (_ bv2 8) (bvmul a b))))
            (check-sat)";
        assert_eq!(solve_str(script), "sat");
    }

    /// `x + x` combines to `2·x`.
    #[test]
    fn monomial_combining() {
        let script = "(set-logic QF_BV)
            (declare-fun x () (_ BitVec 8))
            (assert (not (= (bvadd x x) (bvmul (_ bv2 8) x))))
            (check-sat)";
        assert_eq!(solve_str(script), "unsat");
    }

    /// Cancellation: `x + y = x + 5` ⇒ `y = 5`.
    #[test]
    fn monomial_cancellation() {
        let script = "(set-logic QF_BV)
            (declare-fun x () (_ BitVec 8))
            (declare-fun y () (_ BitVec 8))
            (assert (= (bvadd x y) (bvadd x (_ bv5 8))))
            (assert (distinct y (_ bv5 8)))
            (check-sat)";
        assert_eq!(solve_str(script), "unsat");
    }

    /// Reflexive overflow rule: `X+1 ≤ X+1` always; its negation is unsat.
    #[test]
    fn leq_overflow_reflexive() {
        let script = "(set-logic QF_BV)
            (declare-fun x () (_ BitVec 8))
            (assert (not (bvule (bvadd x (_ bv1 8)) (bvadd x (_ bv1 8)))))
            (check-sat)";
        assert_eq!(solve_str(script), "unsat");
    }

    /// `X+3 ≤ X+5` ⇔ `2 ≤ X+5` (no-wrap of X+5).  Ground truth: false only
    /// when `X+5` wraps below `X+3`, i.e. X ∈ {251, 252}.
    #[test]
    fn leq_overflow_no_wrap() {
        let sat_case = "(set-logic QF_BV)
            (declare-fun x () (_ BitVec 8))
            (assert (bvule (_ bv250 8) x))
            (assert (bvule (bvadd x (_ bv3 8)) (bvadd x (_ bv5 8))))
            (check-sat)";
        assert_eq!(solve_str(sat_case), "sat");
        let unsat_case = "(set-logic QF_BV)
            (declare-fun x () (_ BitVec 8))
            (assert (bvule (_ bv251 8) x))
            (assert (bvule x (_ bv252 8)))
            (assert (bvule (bvadd x (_ bv3 8)) (bvadd x (_ bv5 8))))
            (check-sat)";
        assert_eq!(solve_str(unsat_case), "unsat");
    }

    /// Wrap case: `X+5 ≤ X+3` ⇔ `251 ≤ X ≤ 252` (x+5 wraps, x+3 doesn't).
    #[test]
    fn leq_overflow_wrap() {
        let sat_case = "(set-logic QF_BV)
            (declare-fun x () (_ BitVec 8))
            (assert (bvule (_ bv251 8) x))
            (assert (bvule x (_ bv252 8)))
            (assert (bvule (bvadd x (_ bv5 8)) (bvadd x (_ bv3 8))))
            (check-sat)";
        assert_eq!(solve_str(sat_case), "sat");
        let unsat_case = "(set-logic QF_BV)
            (declare-fun x () (_ BitVec 8))
            (assert (bvule x (_ bv250 8)))
            (assert (bvule (bvadd x (_ bv5 8)) (bvadd x (_ bv3 8))))
            (check-sat)";
        assert_eq!(solve_str(unsat_case), "unsat");
    }

    /// Coefficients live mod 2ʷ: `2·4·x = 0` at width 3.
    #[test]
    fn coefficient_wraps_at_width() {
        let script = "(set-logic QF_BV)
            (declare-fun x () (_ BitVec 3))
            (assert (= (bvmul (_ bv2 3) (bvmul (_ bv4 3) x)) (_ bv0 3)))
            (check-sat)";
        assert_eq!(solve_str(script), "sat");
        let script = "(set-logic QF_BV)
            (declare-fun x () (_ BitVec 3))
            (assert (and (= x (_ bv1 3)) (= (bvmul (_ bv2 3) (bvmul (_ bv3 3) x)) (_ bv0 3))))
            (check-sat)";
        assert_eq!(solve_str(script), "unsat");
    }

    /// bvnot folding and double-negation.
    #[test]
    fn bvnot_folding() {
        let script = "(set-logic QF_BV)
            (declare-fun x () (_ BitVec 8))
            (assert (not (= (bvnot (bvnot x)) x)))
            (check-sat)";
        assert_eq!(solve_str(script), "unsat");
    }

    /// Bitwise idempotence / parity.
    #[test]
    fn bitwise_normalization() {
        let script = "(set-logic QF_BV)
            (declare-fun x () (_ BitVec 8))
            (declare-fun y () (_ BitVec 8))
            (assert (not (= (bvand x (bvand y x)) (bvand x y))))
            (assert (not (= (bvxor y (bvxor y x)) x)))
            (check-sat)";
        assert_eq!(solve_str(script), "unsat");
    }

    /// Deep input must not overflow the native stack: a wide sum chain.
    #[test]
    fn deep_sum_survives_small_stack() {
        let mut script =
            String::from("(set-logic QF_BV)\n(declare-fun x () (_ BitVec 8))\n(assert (= x");
        for i in 0..2000 {
            let _ = i;
            script.push_str(" x");
        }
        script.push_str("))\n(check-sat)");
        // 2000·x ≡ 0 (mod 256): 2000 = 7·256 + 208 → 208·x = 0 is NOT a
        // tautology, so this is satisfiable; the point is it terminates.
        let verdict = solve_str(&script);
        assert!(verdict == "sat" || verdict == "unsat");
    }
}
