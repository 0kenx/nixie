//! The transcendental theory: dReal-style δ-satisfiability by interval
//! constraint propagation (ICP).
//!
//! # What this decides
//!
//! Ground, quantifier-free constraints over the reals built from
//! `+ − * /` and the transcendental functions `exp`, `log`, `sin`, `cos`,
//! `atan`, `sqrt`, compared with `≤ < > ≥ = ≠`, under a conjunction (the
//! caller's dPLL driver enumerates Boolean assignments; this engine decides
//! each conjunctive fragment).
//!
//! Real arithmetic with a transcendental function is **undecidable**, so no
//! decision procedure exists.  The honest calculus here is the
//! δ-decision procedure of Gao–Avigad–Clarke (as implemented by dReal):
//!
//! * **`unsat`** is returned only when *every* branch of the
//!   branch-and-prune search was emptied by pruning against the
//!   **δ-weakened** constraints — and δ-unsat implies unsat (weakening only
//!   ever adds solutions), so an `unsat` here is a real refutation.
//! * **`delta-sat`** is returned with a *witness point* (rounded to
//!   `Rational64` and re-verified after rounding, so exactly what is
//!   published was checked) whose every constraint holds within its
//!   δ-tolerance — a model of a δ-perturbation of the formula, never a
//!   claimed model of the formula itself.
//! * **`unknown`** when neither side could be established within the
//!   budget.  Never a guess.
//!
//! # How pruning stays sound
//!
//! All interval arithmetic is the outward-rounded `DI` of
//! `nixie_math::transcendental`, whose enclosures are mathematically
//! guaranteed (exact rational series + rigorous tails).  Two invariants:
//!
//! 1. Every node interval always **contains** the true range of the node
//!    over the current box (forward evaluation) — so narrowing that only
//!    intersects intervals never removes a solution.
//! 2. The δ-weakening is applied **only at constraint roots** (the
//!    right-hand constants).  Inner backward contractions are exact real
//!    arithmetic (`t ∈ log(v)` for `v = exp(t)`, `a ∈ v/b` when `0 ∉ b`,
//!    …), so they never cut a solution of the (weak or strong) constraint
//!    system either.
//!
//! Together: an empty box proves the δ-weakened conjunction empty on that
//! branch, and exhausting every branch proves δ-unsat, which implies unsat.
//! A verified box/point is a δ-witness.  Conflict dependencies track which
//! constraints produced contradicting bounds, which the dPLL driver turns
//! into blocking clauses.
//!
//! # Totalized semantics
//!
//! `log(x ≤ 0) = −∞` and `sqrt(x < 0) = 0` (dReal's totalizations,
//! `docs/TRANS.md`); `exp`, `sin`, `cos`, `atan` are total.  Division by an
//! interval containing 0 evaluates to the whole line (a sound
//! over-approximation) and *blocks* verification of any constraint whose
//! value flows through it.

#[cfg(not(feature = "std"))]
use alloc::collections::VecDeque;
#[cfg(not(feature = "std"))]
use alloc::vec;
#[cfg(not(feature = "std"))]
use alloc::vec::Vec;
use nixie_math::transcendental::DI;
use num_rational::Rational64;
use num_traits::ToPrimitive;
use rustc_hash::FxHashMap;
use smallvec::SmallVec;
#[cfg(feature = "std")]
use std::collections::VecDeque;

// ===========================================================================
// Options and outcomes
// ===========================================================================

/// Tuning knobs of a run.  The default δ follows dReal (`0.001`).
#[derive(Clone, Copy, Debug)]
pub struct TransOptions {
    /// The δ of δ-satisfiability: a constraint `e ⋈ c` is decided against
    /// the weakened bound `c ± δ·(1+|c|)`.
    pub delta: f64,
    /// Maximum branch nodes explored before conceding `Unknown`.
    pub max_branch_nodes: u64,
    /// Maximum total propagation steps for one whole run.
    pub max_propagations: u64,
}

impl Default for TransOptions {
    fn default() -> Self {
        Self {
            delta: 0.001,
            max_branch_nodes: 100_000,
            max_propagations: 8_000_000,
        }
    }
}

/// The verdict of one ICP run over a conjunction.
#[derive(Clone, Debug)]
pub enum TransOutcome {
    /// A δ-witness: the published rational values (one per variable, in
    /// problem-variable order) satisfy every constraint within its
    /// δ-tolerance.  Verified **after** rounding to `Rational64`, so
    /// publishing exactly these values is honest.
    DeltaSat {
        /// Witness values, parallel to `TransProblem::var_terms`.
        values: Vec<Rational64>,
    },
    /// The δ-weakened conjunction is empty — a sound refutation.  `culprits`
    /// are constraint indices (valid for the blocking clause; when no
    /// provenance was recorded, the driver negates the whole assignment,
    /// which is always valid).
    Unsat {
        /// Indices into the problem's constraint table.
        culprits: Vec<u32>,
    },
    /// Budget exhausted or fragment not decidable: no verdict.
    Unknown,
}

// ===========================================================================
// Problem representation
// ===========================================================================

/// One node of the shared arithmetic DAG; indices into
/// `TransProblem::nodes`.
#[derive(Clone, Debug)]
pub(crate) enum Node {
    /// A rational constant as a rigorous interval.
    Const(DI),
    /// A Real variable; the payload is its `var_terms` slot.
    Var(u32),
    /// `-a`
    Neg(u32),
    /// `a1 + … + an`
    Add(Vec<u32>),
    /// `a - b`
    Sub(u32, u32),
    /// `a1 · … · an`
    Mul(Vec<u32>),
    /// `a / b`
    Div(u32, u32),
    /// `e^a`
    Exp(u32),
    /// `log(a)`
    Log(u32),
    /// `sin(a)`
    Sin(u32),
    /// `cos(a)`
    Cos(u32),
    /// `atan(a)`
    Atan(u32),
    /// `sqrt(a)`
    Sqrt(u32),
}

impl Node {
    /// The node's child indices.
    #[must_use]
    pub(crate) fn children(&self) -> SmallVec<[u32; 4]> {
        match self {
            Self::Const(_) | Self::Var(_) => SmallVec::new(),
            Self::Neg(a)
            | Self::Exp(a)
            | Self::Log(a)
            | Self::Sin(a)
            | Self::Cos(a)
            | Self::Atan(a)
            | Self::Sqrt(a) => smallvec::smallvec![*a],
            Self::Add(xs) | Self::Mul(xs) => xs.iter().copied().collect(),
            Self::Sub(a, b) | Self::Div(a, b) => smallvec::smallvec![*a, *b],
        }
    }
}

/// The normalized comparison of a constraint.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Cmp {
    /// `root ≤ rhs`
    Le,
    /// `root ≥ rhs`
    Ge,
    /// `root = rhs`
    Eq,
    /// `root ≠ rhs`: never prunes (removing one point from an interval is
    /// disjunctive); verifies only when the intervals are certainly
    /// disjoint or a point witness separates them.
    Ne,
}

/// One constraint `root ⋈ rhs`, with the δ-weakened bound precomputed.
/// `rhs` is carried for diagnostics; the decided bound is the precomputed
/// `rhs_interval`.
#[allow(dead_code)]
#[derive(Clone, Debug)]
pub(crate) struct Constraint {
    /// Node whose value is compared.
    pub(crate) root: u32,
    /// The constant right-hand side.
    pub(crate) rhs: Rational64,
    /// The comparison.
    pub(crate) cmp: Cmp,
    /// The δ-weakened admissible interval for `root`.
    pub(crate) rhs_interval: DI,
}

/// A conjunctive ICP problem over the shared node DAG.
#[derive(Clone, Debug, Default)]
pub struct TransProblem {
    pub(crate) nodes: Vec<Node>,
    /// Reverse edges: nodes listing this node as a child.
    pub(crate) users: Vec<Vec<u32>>,
    /// Constraints reading each node's value.
    pub(crate) constraint_users: Vec<Vec<u32>>,
    pub(crate) constraints: Vec<Constraint>,
    /// The Real `TermId` of each `Node::Var` slot (for the witness).
    pub(crate) var_terms: Vec<nixie_core::ast::TermId>,
    /// Node index of each variable.
    pub(crate) var_nodes: Vec<u32>,
}

impl TransProblem {
    /// Whether the variable node feeds (transitively, downward is not
    /// needed — `users` points up) any compound arithmetic node.
    #[must_use]
    pub(crate) fn feeds_compound(&self, node: u32) -> bool {
        let mut seen = vec![false; self.nodes.len()];
        let mut stack = vec![node];
        while let Some(i) = stack.pop() {
            if seen[i as usize] {
                continue;
            }
            seen[i as usize] = true;
            for &u in &self.users[i as usize] {
                if !matches!(self.nodes[u as usize], Node::Var(_) | Node::Const(_)) {
                    return true;
                }
                stack.push(u);
            }
        }
        false
    }

    /// The Real `TermId` of each variable slot (for the witness).
    #[must_use]
    pub fn var_terms(&self) -> &[nixie_core::ast::TermId] {
        &self.var_terms
    }

    /// Whether any constraint transitively reads `node` (via `users`).
    #[must_use]
    pub(crate) fn constraint_reachable(&self, node: u32) -> bool {
        let mut seen = vec![false; self.nodes.len()];
        let mut stack = vec![node];
        while let Some(i) = stack.pop() {
            if seen[i as usize] {
                continue;
            }
            seen[i as usize] = true;
            if !self.constraint_users[i as usize].is_empty() {
                return true;
            }
            stack.extend(self.users[i as usize].iter().copied());
        }
        false
    }

    /// Intern `term` (bottom-up, explicit stack) as a node, deduplicating
    /// through `cache`.  `None` = the term is outside the decidable
    /// fragment (Apply, Select, numeric ite, datatypes, …): the caller must
    /// answer `Unknown` for the whole goal, never solve a weaker problem
    /// than the one it was given.
    #[allow(clippy::too_many_lines)]
    pub fn intern_term(
        &mut self,
        term: nixie_core::ast::TermId,
        manager: &nixie_core::ast::TermManager,
        cache: &mut FxHashMap<nixie_core::ast::TermId, Option<u32>>,
    ) -> Option<u32> {
        if let Some(cached) = cache.get(&term) {
            return *cached;
        }
        // Two-phase frames: Visit children first, then Combine.
        enum Frame {
            Visit(nixie_core::ast::TermId),
            Combine(nixie_core::ast::TermId),
        }
        let mut stack = vec![Frame::Visit(term)];
        let mut resolved: FxHashMap<nixie_core::ast::TermId, u32> = FxHashMap::default();
        while let Some(frame) = stack.pop() {
            match frame {
                Frame::Visit(t) => {
                    if resolved.contains_key(&t) {
                        continue;
                    }
                    // Cross-call dedup: a term interned by an earlier
                    // constraint reuses its node (hash-consed TermIds make
                    // the cache exact).
                    if let Some(cached) = cache.get(&t) {
                        if let Some(idx) = *cached {
                            resolved.insert(t, idx);
                        }
                        continue;
                    }
                    let node_term = manager.get(t)?;
                    let kind = node_term.kind.clone();
                    use nixie_core::ast::TermKind as K;
                    let compound = matches!(
                        kind,
                        K::Add(_)
                            | K::Sub(_, _)
                            | K::Mul(_)
                            | K::Div(_, _)
                            | K::Neg(_)
                            | K::Exp(_)
                            | K::Log(_)
                            | K::Sin(_)
                            | K::Cos(_)
                            | K::Atan(_)
                            | K::Sqrt(_)
                    );
                    if !compound {
                        // Leaf: constant or (Real) variable, or a decline.
                        let node = match &kind {
                            K::RealConst(r) => Some(Node::Const(DI::from_rational64(r))),
                            K::IntConst(n) => n.to_i64().map(|v| {
                                Node::Const(DI::from_rational64(&Rational64::from_integer(v)))
                            }),
                            K::Var(_) => {
                                if node_term.sort != manager.sorts.real_sort {
                                    // Int-sorted (or worse) variable: the
                                    // fragment requires pure Real.
                                    None
                                } else {
                                    Some(Node::Var(self.var_terms.len() as u32))
                                }
                            }
                            _ => None, // outside the fragment
                        };
                        match node {
                            Some(nd) => {
                                let idx = self.push_node(nd, t);
                                resolved.insert(t, idx);
                                cache.insert(t, Some(idx));
                            }
                            None => {
                                cache.insert(t, None);
                                return None;
                            }
                        }
                    } else {
                        let kids: SmallVec<[nixie_core::ast::TermId; 4]> = match &kind {
                            K::Add(args) | K::Mul(args) => args.iter().copied().collect(),
                            K::Sub(a, b) | K::Div(a, b) => smallvec::smallvec![*a, *b],
                            K::Neg(a)
                            | K::Exp(a)
                            | K::Log(a)
                            | K::Sin(a)
                            | K::Cos(a)
                            | K::Atan(a)
                            | K::Sqrt(a) => smallvec::smallvec![*a],
                            _ => unreachable!("compound filter above"),
                        };
                        stack.push(Frame::Combine(t));
                        for k in kids {
                            stack.push(Frame::Visit(k));
                        }
                    }
                }
                Frame::Combine(t) => {
                    // All children visited; collect their indices.  A child
                    // that declined kills the whole term.
                    let node_term = manager.get(t)?;
                    let kids: SmallVec<[nixie_core::ast::TermId; 4]> = match &node_term.kind {
                        nixie_core::ast::TermKind::Add(args)
                        | nixie_core::ast::TermKind::Mul(args) => args.iter().copied().collect(),
                        nixie_core::ast::TermKind::Sub(a, b)
                        | nixie_core::ast::TermKind::Div(a, b) => {
                            smallvec::smallvec![*a, *b]
                        }
                        nixie_core::ast::TermKind::Neg(a)
                        | nixie_core::ast::TermKind::Exp(a)
                        | nixie_core::ast::TermKind::Log(a)
                        | nixie_core::ast::TermKind::Sin(a)
                        | nixie_core::ast::TermKind::Cos(a)
                        | nixie_core::ast::TermKind::Atan(a)
                        | nixie_core::ast::TermKind::Sqrt(a) => {
                            smallvec::smallvec![*a]
                        }
                        _ => unreachable!("compound filter above"),
                    };
                    let mut idxs: SmallVec<[u32; 4]> = SmallVec::new();
                    for k in kids {
                        let Some(&i) = resolved.get(&k) else {
                            cache.insert(t, None);
                            return None;
                        };
                        idxs.push(i);
                    }
                    use nixie_core::ast::TermKind as K;
                    let node = match node_term.kind {
                        K::Neg(_) => Node::Neg(idxs[0]),
                        K::Add(_) => Node::Add(idxs.to_vec()),
                        K::Sub(_, _) => Node::Sub(idxs[0], idxs[1]),
                        K::Mul(_) => Node::Mul(idxs.to_vec()),
                        K::Div(_, _) => Node::Div(idxs[0], idxs[1]),
                        K::Exp(_) => Node::Exp(idxs[0]),
                        K::Log(_) => Node::Log(idxs[0]),
                        K::Sin(_) => Node::Sin(idxs[0]),
                        K::Cos(_) => Node::Cos(idxs[0]),
                        K::Atan(_) => Node::Atan(idxs[0]),
                        K::Sqrt(_) => Node::Sqrt(idxs[0]),
                        _ => unreachable!("compound filter above"),
                    };
                    let idx = self.push_node(node, t);
                    resolved.insert(t, idx);
                    cache.insert(t, Some(idx));
                }
            }
        }
        resolved.get(&term).copied()
    }

    fn push_node(&mut self, node: Node, term: nixie_core::ast::TermId) -> u32 {
        let idx = self.nodes.len() as u32;
        if let Node::Var(slot) = node {
            debug_assert_eq!(slot as usize, self.var_terms.len());
            self.var_terms.push(term);
            self.var_nodes.push(idx);
        }
        let kids = node.children();
        self.nodes.push(node);
        self.users.push(Vec::new());
        self.constraint_users.push(Vec::new());
        for c in kids {
            self.users[c as usize].push(idx);
        }
        idx
    }

    /// Add `root ⋈ rhs` with the δ-tolerance `δ·(1+|rhs|)` precomputed.
    pub fn add_constraint(&mut self, root: u32, rhs: Rational64, cmp: Cmp, delta: f64) {
        let tol = delta * (1.0 + rhs.to_f64().unwrap_or(0.0).abs());
        let widened = DI::from_rational64(&rhs).add(&DI { lo: -tol, hi: tol });
        let rhs_interval = match cmp {
            Cmp::Le => DI {
                lo: f64::NEG_INFINITY,
                hi: widened.hi,
            },
            Cmp::Ge => DI {
                lo: widened.lo,
                hi: f64::INFINITY,
            },
            Cmp::Eq | Cmp::Ne => widened,
        };
        let cid = self.constraints.len() as u32;
        self.constraint_users[root as usize].push(cid);
        self.constraints.push(Constraint {
            root,
            rhs,
            cmp,
            rhs_interval,
        });
    }
}

// ===========================================================================
// The propagation engine
// ===========================================================================

/// Dependency provenance of one bound: which constraints produced it.
type Deps = SmallVec<[u32; 2]>;

/// Mutable search state over a [`TransProblem`].
pub struct IcpEngine<'a> {
    prob: &'a TransProblem,
    iv: Vec<DI>,
    deps_lo: Vec<Deps>,
    deps_hi: Vec<Deps>,
    queue: VecDeque<u32>,
    constraint_queue: VecDeque<u32>,
    queued: Vec<bool>,
    /// Propagation steps remaining.
    budget: u64,
    /// Per-`propagate`-call step cap (ulp-creep guard).
    prop_cap: u32,
}

impl<'a> IcpEngine<'a> {
    /// Fresh engine over the initial box (constants at value, variables at
    /// the whole line), with every node queued.
    #[must_use]
    pub fn new(prob: &'a TransProblem, opts: &'a TransOptions) -> Self {
        let n = prob.nodes.len();
        let iv = prob
            .nodes
            .iter()
            .map(|nd| match nd {
                Node::Const(c) => *c,
                _ => DI::RN,
            })
            .collect();
        let mut eng = Self {
            prob,
            iv,
            deps_lo: (0..n).map(|_| Deps::new()).collect(),
            deps_hi: (0..n).map(|_| Deps::new()).collect(),
            queue: VecDeque::new(),
            constraint_queue: VecDeque::new(),
            queued: vec![false; n],
            budget: opts.max_propagations,
            // Large enough that one call reaches the useful fixpoint on
            // realistic graphs (the sin²+cos² refutation needs a few
            // thousand steps per branch at the top; 512 cut conflict
            // discovery so deep the bisection burned the node budget),
            // small enough that ulp-creep cannot eat the global budget.
            prop_cap: 8192,
        };
        for i in 0..n {
            eng.enqueue(i as u32);
        }
        for c in 0..prob.constraints.len() {
            eng.constraint_queue.push_back(c as u32);
        }
        eng
    }

    fn enqueue(&mut self, idx: u32) {
        if !self.queued[idx as usize] {
            self.queued[idx as usize] = true;
            self.queue.push_back(idx);
        }
    }

    /// Narrow node `idx` by intersecting with `new`, merging provenance
    /// (the tighter bound's deps win).  Returns `false` on emptiness — the
    /// caller abandons the branch (or records the conflict).  Fanout is
    /// queue-based, never recursive.
    fn tighten(&mut self, idx: u32, new: DI, d_lo: &Deps, d_hi: &Deps) -> bool {
        let i = idx as usize;
        let mut changed = false;
        if new.lo > self.iv[i].lo {
            self.iv[i].lo = new.lo;
            self.deps_lo[i] = d_lo.clone();
            changed = true;
        }
        if new.hi < self.iv[i].hi {
            self.iv[i].hi = new.hi;
            self.deps_hi[i] = d_hi.clone();
            changed = true;
        }
        if self.iv[i].is_empty() {
            return false;
        }
        // Fanout ONLY on an actual narrowing: re-enqueering unchanged
        // nodes makes the fixpoint loop spin forever.
        if changed {
            self.enqueue(idx);
            for &u in &self.prob.users[i] {
                self.enqueue(u);
            }
            for &c in &self.prob.constraint_users[i] {
                self.constraint_queue.push_back(c);
            }
        }
        true
    }

    /// Forward evaluation of `node` over the current box.
    fn eval_node(&self, node: &Node) -> DI {
        match node {
            Node::Const(c) => *c,
            Node::Var(_) => DI::RN,
            Node::Neg(a) => self.iv[*a as usize].neg(),
            Node::Add(args) => {
                let mut acc = DI::point(0.0);
                for &a in args {
                    acc = acc.add(&self.iv[a as usize]);
                }
                acc
            }
            Node::Sub(a, b) => self.iv[*a as usize].sub(&self.iv[*b as usize]),
            Node::Mul(args) => {
                // Squares are exact-range tight: [l,h]² = [0, max(l²,h²)]
                // when l ≤ 0 ≤ h, else the monotone hull.  The four-corner
                // product is sound but yields [−max², max²] — twice as wide
                // as the truth — and squares are everywhere (sin² + cos²,
                // variance, Lyapunov functions).
                if args.len() == 2 && args[0] == args[1] {
                    return self.iv[args[0] as usize].square();
                }
                let mut acc = DI::point(1.0);
                for &a in args {
                    acc = acc.mul(&self.iv[a as usize]);
                }
                acc
            }
            Node::Div(a, b) => self.iv[*a as usize].div(&self.iv[*b as usize]),
            Node::Exp(a) => self.iv[*a as usize].exp(),
            Node::Log(a) => self.iv[*a as usize].log(),
            Node::Sin(a) => self.iv[*a as usize].sin(),
            Node::Cos(a) => self.iv[*a as usize].cos(),
            Node::Atan(a) => self.iv[*a as usize].atan(),
            Node::Sqrt(a) => self.iv[*a as usize].sqrt(),
        }
    }

    /// One node's propagation step: forward re-evaluation then backward
    /// contraction of the children.  `false` = the node went empty.
    fn propagate_node(&mut self, idx: u32) -> bool {
        if self.budget == 0 {
            return true; // handled by the budget check in `propagate`
        }
        self.budget -= 1;
        let node = self.prob.nodes[idx as usize].clone();
        let fwd = self.eval_node(&node);
        if !self.tighten(idx, fwd, &Deps::new(), &Deps::new()) {
            return false;
        }
        let v = self.iv[idx as usize];
        let d = self.deps_of(idx);
        match node {
            Node::Const(_) | Node::Var(_) => {}
            Node::Neg(a) => {
                if !self.tighten(a, v.neg(), &d, &d) {
                    return false;
                }
            }
            Node::Add(args) => {
                for k in 0..args.len() {
                    let mut acc = DI::point(0.0);
                    for (j, &b) in args.iter().enumerate() {
                        if j != k {
                            acc = acc.add(&self.iv[b as usize]);
                        }
                    }
                    if !self.tighten(args[k], v.sub(&acc), &d, &d) {
                        return false;
                    }
                }
            }
            Node::Sub(a, b) => {
                if !self.tighten(a, v.add(&self.iv[b as usize]), &d, &d) {
                    return false;
                }
                let t_b = self.iv[a as usize].sub(&v);
                if !self.tighten(b, t_b, &d, &d) {
                    return false;
                }
            }
            Node::Mul(args) => {
                // v = a² with a's box sign-definite: a ∈ ±[√v.lo, √v.hi]
                // on the known side — tighter than dividing (which the
                // zero-containing factor blocks anyway).
                if args.len() == 2 && args[0] == args[1] {
                    let a = args[0];
                    let cur = self.iv[a as usize];
                    if cur.lo >= 0.0 && v.lo >= 0.0 {
                        let t = DI {
                            lo: v.sqrt().lo,
                            hi: v.sqrt().hi,
                        };
                        if !self.tighten(a, t, &d, &d) {
                            return false;
                        }
                    } else if cur.hi <= 0.0 && v.lo >= 0.0 {
                        let t = DI {
                            lo: -v.sqrt().hi,
                            hi: -v.sqrt().lo,
                        };
                        if !self.tighten(a, t, &d, &d) {
                            return false;
                        }
                    }
                    return true;
                }
                for k in 0..args.len() {
                    let mut acc = DI::point(1.0);
                    for (j, &b) in args.iter().enumerate() {
                        if j != k {
                            acc = acc.mul(&self.iv[b as usize]);
                        }
                    }
                    if acc.contains_zero() {
                        continue; // cannot divide soundly
                    }
                    if !self.tighten(args[k], v.div(&acc), &d, &d) {
                        return false;
                    }
                }
            }
            Node::Div(a, b) => {
                if !self.iv[b as usize].contains_zero()
                    && !self.tighten(a, v.mul(&self.iv[b as usize]), &d, &d)
                {
                    return false;
                }
                if !v.contains_zero() {
                    let t_b = self.iv[a as usize].div(&v);
                    if !self.tighten(b, t_b, &d, &d) {
                        return false;
                    }
                }
            }
            Node::Exp(t_) => {
                // e^t > 0 for every t (totalization gives e^(-∞) = 0).
                if v.hi <= 0.0 {
                    return false;
                }
                let dom = DI {
                    lo: if v.lo <= 0.0 { f64::NEG_INFINITY } else { v.lo },
                    hi: v.hi,
                };
                if !self.tighten(t_, dom.log(), &d, &d) {
                    return false;
                }
            }
            Node::Log(t_) => {
                // log(t) = −∞ for t ≤ 0 (totalized): a finite upper bound on
                // v caps t at e^{v.hi}; a lower bound above −∞ forces
                // t ≥ e^{v.lo} (only positive t reach finite log values).
                let mut t_new = DI::RN;
                if v.hi < f64::INFINITY {
                    t_new.hi = DI::point(v.hi).exp().hi;
                }
                if v.lo > f64::NEG_INFINITY {
                    t_new.lo = DI::point(v.lo).exp().lo;
                }
                if !self.tighten(t_, t_new, &d, &d) {
                    return false;
                }
            }
            Node::Sin(t_) => {
                if !self.contract_sin_like(idx, t_, v, true) {
                    return false;
                }
            }
            Node::Cos(t_) => {
                if !self.contract_sin_like(idx, t_, v, false) {
                    return false;
                }
            }
            Node::Atan(t_) => {
                // atan(t) ∈ (−π/2, π/2).  `[plo, phi]` brackets π/2 itself,
                // so "entirely above the range" is `v.lo > phi` and
                // "entirely below" is `v.hi < −phi`.
                let (plo, phi) = nixie_math::transcendental::pi2_bracket();
                if v.lo > phi || v.hi < -phi {
                    return false;
                }
                // Strictly inside (−π/2, π/2) — rigorous via the lower
                // bracket: `v.lo > −plo ⟹ v.lo > −π/2` and
                // `v.hi < plo ⟹ v.hi < π/2` — where cos > 0 and tan is
                // monotone: t ∈ tan(v) = sin(v)/cos(v).
                if v.lo > -plo && v.hi < plo {
                    #[cfg(feature = "std")]
                    let tsc = std::time::Instant::now();
                    let s = v.sin();
                    let c = v.cos();
                    #[cfg(feature = "std")]
                    eprintln!("[icp] sin/cos took {:?}", tsc.elapsed());
                    let dv = s.div(&c);
                    #[cfg(feature = "std")]
                    eprintln!("[icp] div took {:?} -> {dv:?}", tsc.elapsed());
                    if !self.tighten(t_, dv, &d, &d) {
                        return false;
                    }
                }
            }
            Node::Sqrt(t_) => {
                // sqrt ≥ 0 (totalized); positive lower bound squares.
                if v.hi < 0.0 {
                    return false;
                }
                let hi2 = DI::point(v.hi).mul(&DI::point(v.hi)).hi;
                let t_new = if v.lo > 0.0 {
                    DI {
                        lo: DI::point(v.lo).mul(&DI::point(v.lo)).lo,
                        hi: hi2,
                    }
                } else {
                    DI {
                        lo: f64::NEG_INFINITY,
                        hi: hi2,
                    }
                };
                if !self.tighten(t_, t_new, &d, &d) {
                    return false;
                }
            }
        }
        true
    }

    /// sin/cos child contraction: range check plus monotone inverse through
    /// `asin` when the argument window sits inside one monotone piece.
    fn contract_sin_like(&mut self, idx: u32, child: u32, v: DI, is_sin: bool) -> bool {
        if v.lo > 1.0 || v.hi < -1.0 {
            return false; // outside sin/cos range: empty
        }
        let t = self.iv[child as usize];
        let (_, pi_hi) = nixie_math::transcendental::pi_bracket();
        // Beyond width π/2 the inverse image may be a union of branches —
        // contraction would be unsound to pick one, so decline.
        if !t.width().is_finite() || t.width() >= pi_hi / 2.0 {
            return true;
        }
        // For cos, work with u = t + π/2 so that cos(t) = sin(u); the
        // window is shifted outward with the rigorous π/2 bracket.
        let (plo, phi) = nixie_math::transcendental::pi2_bracket();
        let (win_lo, win_hi) = if is_sin {
            (t.lo, t.hi)
        } else {
            (t.lo + plo, t.hi + phi)
        };
        let mid = (win_lo + win_hi) / 2.0;
        let k = ((mid + phi) / core::f64::consts::PI).floor();
        let kpi = k * core::f64::consts::PI;
        // sin increasing on [−π/2+kπ, π/2+kπ]; require the (outward-shifted)
        // window inside, with slack for the k·π f64 arithmetic.
        let slack = 1e-9;
        if win_lo < -phi + kpi - slack || win_hi > phi + kpi + slack {
            return true; // straddles a critical point: no contraction
        }
        let inv_lo = nixie_math::transcendental::asin_enclosure(v.lo.max(-1.0)).0;
        let inv_hi = nixie_math::transcendental::asin_enclosure(v.hi.min(1.0)).1;
        let new_t = if is_sin {
            DI {
                lo: inv_lo + kpi,
                hi: inv_hi + kpi,
            }
        } else {
            // u ∈ [inv_lo, inv_hi] + kπ  ⇒  t = u − π/2.
            DI {
                lo: inv_lo + kpi - phi,
                hi: inv_hi + kpi - plo,
            }
        };
        let d = self.deps_of(idx);
        self.tighten(child, new_t, &d, &d)
    }

    fn deps_of(&self, idx: u32) -> Deps {
        let mut d = self.deps_lo[idx as usize].clone();
        for &x in self.deps_hi[idx as usize].iter() {
            if !d.contains(&x) {
                d.push(x);
            }
        }
        d
    }

    /// The only place δ enters: intersect the constraint root with its
    /// weakened admissible interval.  `false` = empty.
    fn apply_constraint(&mut self, cid: u32) -> bool {
        let c = self.prob.constraints[cid as usize].clone();
        if c.cmp == Cmp::Ne {
            return true; // disequalities never prune
        }
        let cur = self.iv[c.root as usize];
        let new_iv = cur.intersect(&c.rhs_interval);
        if new_iv.lo == cur.lo && new_iv.hi == cur.hi {
            return true;
        }
        let mut d = Deps::new();
        d.push(cid);
        let dlo = if new_iv.lo > cur.lo {
            d.clone()
        } else {
            self.deps_lo[c.root as usize].clone()
        };
        let dhi = if new_iv.hi < cur.hi {
            d
        } else {
            self.deps_hi[c.root as usize].clone()
        };
        self.tighten(c.root, new_iv, &dlo, &dhi)
    }

    /// Drain both queues toward a fixpoint.  Returns the conflict set when
    /// a node went empty, `None` otherwise.
    ///
    /// The drain is CAPPED per call (`prop_cap`): interval fixpoints can
    /// converge ulp-by-ulp, and waiting for the exact fixed point lets one
    /// branch consume the whole budget.  Stopping early is sound — every
    /// contraction applied was valid on its own; only pruning POWER is
    /// lost, and the branching loop compensates.  (dReal/ibex cap their
    /// propagation the same way.)
    fn propagate(&mut self) -> Option<Vec<u32>> {
        let mut steps_left = self.prop_cap;
        loop {
            if self.budget == 0 || steps_left == 0 {
                return None;
            }
            steps_left -= 1;
            if let Some(cid) = self.constraint_queue.pop_front() {
                if !self.apply_constraint(cid) {
                    return Some(self.conflict_set());
                }
                continue;
            }
            let idx = self.queue.pop_front()?;
            self.queued[idx as usize] = false;
            if !self.propagate_node(idx) {
                return Some(self.conflict_set());
            }
        }
    }

    /// Union of the provenance of every empty node's two bounds.
    fn conflict_set(&self) -> Vec<u32> {
        let mut out: Vec<u32> = Vec::new();
        for i in 0..self.prob.nodes.len() {
            if self.iv[i].is_empty() {
                for &x in self.deps_lo[i].iter().chain(self.deps_hi[i].iter()) {
                    if !out.contains(&x) {
                        out.push(x);
                    }
                }
            }
        }
        out
    }

    /// Point witness: pin every variable to its midpoint rounded to
    /// `Rational64`, re-evaluate every node at exactly that point, and
    /// verify every constraint.  Returns the published values on success —
    /// what was verified is what gets returned.
    fn try_point_witness(&self) -> Option<Vec<Rational64>> {
        let mut pinned: Vec<Rational64> = Vec::with_capacity(self.prob.var_nodes.len());
        for &node_idx in &self.prob.var_nodes {
            let iv = self.iv[node_idx as usize];
            let m = iv.midpoint();
            if !m.is_finite() {
                return None;
            }
            pinned.push(rational64_from_f64(m));
        }
        let vals = self.evaluate_at(&pinned)?;
        for c in &self.prob.constraints {
            let r = vals[c.root as usize];
            let t = c.rhs_interval;
            let ok = match c.cmp {
                Cmp::Le => r.hi <= t.hi,
                Cmp::Ge => r.lo >= t.lo,
                Cmp::Eq => r.hi <= t.hi && r.lo >= t.lo,
                Cmp::Ne => !(r.lo <= t.hi && r.hi >= t.lo),
            };
            if !ok {
                return None;
            }
        }
        Some(pinned)
    }

    /// Bottom-up point evaluation of every node (`None` when a division by
    /// zero is hit — the witness is undefined there).
    fn evaluate_at(&self, pinned: &[Rational64]) -> Option<Vec<DI>> {
        let mut vals: Vec<DI> = Vec::with_capacity(self.prob.nodes.len());
        for node in &self.prob.nodes {
            let v = match node {
                Node::Const(c) => *c,
                Node::Var(slot) => DI::from_rational64(&pinned[*slot as usize]),
                Node::Neg(a) => vals[*a as usize].neg(),
                Node::Add(args) => {
                    let mut acc = DI::point(0.0);
                    for &a in args {
                        acc = acc.add(&vals[a as usize]);
                    }
                    acc
                }
                Node::Sub(a, b) => vals[*a as usize].sub(&vals[*b as usize]),
                Node::Mul(args) => {
                    if args.len() == 2 && args[0] == args[1] {
                        vals[args[0] as usize].square()
                    } else {
                        let mut acc = DI::point(1.0);
                        for &a in args {
                            acc = acc.mul(&vals[a as usize]);
                        }
                        acc
                    }
                }
                Node::Div(a, b) => {
                    let d = vals[*b as usize];
                    if d.contains_zero() {
                        return None;
                    }
                    vals[*a as usize].div(&d)
                }
                Node::Exp(a) => vals[*a as usize].exp(),
                Node::Log(a) => vals[*a as usize].log(),
                Node::Sin(a) => vals[*a as usize].sin(),
                Node::Cos(a) => vals[*a as usize].cos(),
                Node::Atan(a) => vals[*a as usize].atan(),
                Node::Sqrt(a) => vals[*a as usize].sqrt(),
            };
            vals.push(v);
        }
        Some(vals)
    }

    /// The branching variable.
    ///
    /// Order of preference:
    /// 1. any infinite-width constraint-reachable variable (establish
    ///    bounds first — nothing else prunes an unbounded box);
    /// 2. widest relative width among variables that FEED A COMPOUND node
    ///    (`Sin`/`Exp`/`Mul`/…): narrowing them activates the nonlinear
    ///    contractions.  Splitting a purely linear-intermediate variable
    ///    (a purified definition target like `s` in `s = sin(x)`) mostly
    ///    subdivides δ-slack — measured as the difference between
    ///    finishing the bounded sin²+cos² refutation and floundering to
    ///    the node budget (the s/c dimensions kept spawning slack-alive
    ///    boxes while x stayed wide);
    /// 3. fallback: widest relative width among all constraint-reachable
    ///    variables.
    fn pick_branch_var(&self) -> Option<u32> {
        let mut best_compound: Option<(f64, u32)> = None;
        let mut best_any: Option<(f64, u32)> = None;
        for &node_idx in &self.prob.var_nodes {
            let iv = self.iv[node_idx as usize];
            if iv.is_empty() || iv.is_point() {
                continue;
            }
            if !self.prob.constraint_reachable(node_idx) {
                continue;
            }
            let w = iv.width();
            if !w.is_finite() {
                return Some(node_idx);
            }
            let scale = iv.lo.abs().max(iv.hi.abs()).max(1.0);
            let rel = w / scale;
            if self.prob.feeds_compound(node_idx) {
                match best_compound {
                    Some((bw, _)) if bw >= rel => {}
                    _ => best_compound = Some((rel, node_idx)),
                }
            }
            match best_any {
                Some((bw, _)) if bw >= rel => {}
                _ => best_any = Some((rel, node_idx)),
            }
        }
        best_compound.or(best_any).map(|(_, i)| i)
    }
}

/// Convert an f64 to the nearest `Rational64` (exact when it fits; the
/// re-verification in `try_point_witness` certifies whatever lands here).
fn rational64_from_f64(x: f64) -> Rational64 {
    use num_traits::FromPrimitive;
    if let Some(q) = Rational64::from_f64(x) {
        return q;
    }
    // Out of i64 range: saturate (the witness check will almost surely
    // reject, which is the honest outcome).
    if x >= 9.0e18 {
        Rational64::from_integer(i64::MAX)
    } else if x <= -9.0e18 {
        Rational64::from_integer(i64::MIN)
    } else {
        Rational64::from_integer(x.trunc() as i64)
    }
}

/// The top-level δ-decision over one conjunctive problem:
/// branch-and-prune with snapshots.
///
/// * propagate; empty branch → record conflict, backtrack;
/// * verified (box or point witness) → `DeltaSat`;
/// * otherwise bisect the widest constrained variable;
/// * all branches emptied → `Unsat` (δ-unsat ⟹ unsat);
/// * budget or stuck → `Unknown`.
pub fn solve_conjunction(prob: &TransProblem, opts: &TransOptions) -> TransOutcome {
    struct Snapshot {
        iv: Vec<DI>,
        deps_lo: Vec<Deps>,
        deps_hi: Vec<Deps>,
    }
    let snapshot = |eng: &IcpEngine| Snapshot {
        iv: eng.iv.clone(),
        deps_lo: eng.deps_lo.clone(),
        deps_hi: eng.deps_hi.clone(),
    };
    let restore = |eng: &mut IcpEngine, snap: Snapshot| {
        eng.iv = snap.iv;
        eng.deps_lo = snap.deps_lo;
        eng.deps_hi = snap.deps_hi;
        eng.queue.clear();
        eng.constraint_queue.clear();
        for q in eng.queued.iter_mut() {
            *q = false;
        }
    };

    let mut nodes_left = opts.max_branch_nodes;
    let mut first_conflict: Option<Vec<u32>> = None;
    let mut root = IcpEngine::new(prob, opts);

    enum Task {
        Propagate,
        /// Restore the snapshot with the variable's interval replaced, then
        /// propagate.
        BranchInto {
            snap: Snapshot,
            var: u32,
        },
    }
    let mut tasks: Vec<Task> = vec![Task::Propagate];
    while let Some(task) = tasks.pop() {
        if nodes_left == 0 {
            return TransOutcome::Unknown;
        }
        nodes_left -= 1;
        match task {
            Task::BranchInto { snap, var } => {
                restore(&mut root, snap);
                // Re-establish the branch's fixpoint from scratch: the
                // restore reset every node's interval to the snapshot, so
                // the snapshot's subtree contractions are all stale.  (A
                // version that enqueued only the split variable left the
                // subtree on the parent's intervals — the box went
                // inconsistent, propagation went inert, and the search
                // floundered to the node budget.)
                for i in 0..root.prob.nodes.len() {
                    root.enqueue(i as u32);
                }
                for c in 0..root.prob.constraints.len() {
                    root.constraint_queue.push_back(c as u32);
                }
                let _ = var;
                tasks.push(Task::Propagate);
            }
            Task::Propagate => {
                if let Some(culprits) = root.propagate() {
                    // This branch is empty.  Record provenance (for the
                    // blocking clause) and backtrack — NOT a global verdict
                    // unless every other branch empties too.
                    if first_conflict.is_none() && !culprits.is_empty() {
                        first_conflict = Some(culprits);
                    }
                    continue;
                }
                if root.budget == 0 {
                    return TransOutcome::Unknown;
                }
                // The point witness is the acceptance route: it is what
                // gets published, re-verified after rounding.  (A box that
                // verifies universally makes its midpoint verify too, up to
                // the rounding double-check built into the witness.)
                if let Some(w) = root.try_point_witness() {
                    return TransOutcome::DeltaSat { values: w };
                }
                match root.pick_branch_var() {
                    Some(v) => {
                        let iv = root.iv[v as usize];
                        let m = iv.midpoint();
                        if !m.is_finite() {
                            return TransOutcome::Unknown;
                        }
                        // FINITE half first: a half-infinite ray only
                        // narrows exponentially under bisection and can
                        // never conflict for periodic functions (sin² +
                        // cos² = 0 over an unbounded x is the canonical
                        // case — the honest verdict there is Unknown, not
                        // a divergent dive).  The infinite half is pushed
                        // as the deferred sibling.
                        let left_finite = iv.lo.is_finite();
                        let (first, second) = if left_finite {
                            (DI { lo: iv.lo, hi: m }, DI { lo: m, hi: iv.hi })
                        } else {
                            (DI { lo: m, hi: iv.hi }, DI { lo: iv.lo, hi: m })
                        };
                        let mut deferred = snapshot(&root);
                        deferred.iv[v as usize] = second;
                        tasks.push(Task::BranchInto {
                            snap: deferred,
                            var: v,
                        });
                        if !root.tighten(v, first, &Deps::new(), &Deps::new()) {
                            // First half empty on arrival — the queued
                            // constraint applications will discover it on
                            // the next Propagate; popping tasks is also fine.
                            continue;
                        }
                        tasks.push(Task::Propagate);
                    }
                    None => {
                        // No branchable variable left and not verified:
                        // this branch is stuck — treat as unrefuted (the
                        // honest global answer once the loop ends depends
                        // on whether any branch was stuck: if so, Unknown).
                        return TransOutcome::Unknown;
                    }
                }
            }
        }
    }
    // Every branch was emptied (none was stuck, or the stuck ones returned
    // Unknown above): δ-unsat, which implies unsat.
    let culprits = first_conflict.unwrap_or_else(|| (0..prob.constraints.len() as u32).collect());
    TransOutcome::Unsat { culprits }
}

#[cfg(test)]
mod tests {
    use super::*;
    use nixie_core::ast::TermId;
    use nixie_core::ast::TermManager;

    fn manager() -> TermManager {
        TermManager::new()
    }

    /// Build a one-variable problem from the expression term `e` (which
    /// mentions `x`): used to test the engine without the solver-side
    /// collector.
    fn one_var_problem(
        m: &mut TermManager,
        x: TermId,
        e: TermId,
        cmp: Cmp,
        rhs: Rational64,
    ) -> (TransProblem, TermId) {
        let mut prob = TransProblem::default();
        let mut cache = FxHashMap::default();
        let root = prob.intern_term(e, m, &mut cache).expect("in fragment");
        prob.add_constraint(root, rhs, cmp, 0.001);
        (prob, x)
    }

    #[test]
    fn exp_eq_two_is_delta_sat_near_ln2() {
        let mut m = manager();
        let x = m.mk_var("x", m.sorts.real_sort);
        let e = m.mk_exp(x);
        let (prob, x) = one_var_problem(&mut m, x, e, Cmp::Eq, Rational64::from_integer(2));
        let out = solve_conjunction(&prob, &TransOptions::default());
        match out {
            TransOutcome::DeltaSat { values } => {
                assert_eq!(values.len(), 1);
                let v = values[0].to_f64().unwrap();
                assert!((v - core::f64::consts::LN_2).abs() < 1e-3, "got {v}");
            }
            other => panic!("expected DeltaSat, got {other:?}"),
        }
        let _ = x;
    }

    #[test]
    fn exp_upper_bound_unsat() {
        // x ≥ 1 ∧ exp(x) ≤ 1: exp(1) = e ≈ 2.718 > 1 + δ.
        let mut m = manager();
        let x = m.mk_var("x", m.sorts.real_sort);
        let mut prob = TransProblem::default();
        let mut cache = FxHashMap::default();
        let xv = prob.intern_term(x, &m, &mut cache).unwrap();
        let ex = prob.intern_term(m.mk_exp(x), &m, &mut cache).unwrap();
        prob.add_constraint(xv, Rational64::from_integer(1), Cmp::Ge, 0.001);
        prob.add_constraint(ex, Rational64::from_integer(1), Cmp::Le, 0.001);
        match solve_conjunction(&prob, &TransOptions::default()) {
            TransOutcome::Unsat { culprits } => {
                assert!(!culprits.is_empty());
            }
            other => panic!("expected Unsat, got {other:?}"),
        }
    }

    #[test]
    fn sin_root_in_interval() {
        // sin(x) = 0 ∧ x ≥ 3 ∧ x ≤ 3.5: root at π ≈ 3.14159.
        let mut m = manager();
        let x = m.mk_var("x", m.sorts.real_sort);
        let mut prob = TransProblem::default();
        let mut cache = FxHashMap::default();
        let xv = prob.intern_term(x, &m, &mut cache).unwrap();
        let sx = prob.intern_term(m.mk_sin(x), &m, &mut cache).unwrap();
        prob.add_constraint(sx, Rational64::from_integer(0), Cmp::Eq, 0.001);
        prob.add_constraint(xv, Rational64::new(3, 1), Cmp::Ge, 0.001);
        prob.add_constraint(xv, Rational64::new(35, 10), Cmp::Le, 0.001);
        match solve_conjunction(&prob, &TransOptions::default()) {
            TransOutcome::DeltaSat { values } => {
                let v = values[0].to_f64().unwrap();
                assert!((v - core::f64::consts::PI).abs() < 1e-2, "got {v}");
            }
            other => panic!("expected DeltaSat, got {other:?}"),
        }
    }

    #[test]
    fn log_domain_and_unsat() {
        // log(x) ≥ 1 ∧ x ≤ 2: log(2) ≈ 0.693 < 1 − δ.
        let mut m = manager();
        let x = m.mk_var("x", m.sorts.real_sort);
        let mut prob = TransProblem::default();
        let mut cache = FxHashMap::default();
        let xv = prob.intern_term(x, &m, &mut cache).unwrap();
        let lx = prob.intern_term(m.mk_log(x), &m, &mut cache).unwrap();
        prob.add_constraint(lx, Rational64::from_integer(1), Cmp::Ge, 0.001);
        prob.add_constraint(xv, Rational64::from_integer(2), Cmp::Le, 0.001);
        match solve_conjunction(&prob, &TransOptions::default()) {
            TransOutcome::Unsat { .. } => {}
            other => panic!("expected Unsat, got {other:?}"),
        }
    }

    #[test]
    fn sqrt_witness_and_atan() {
        // sqrt(x) = 2 ⇒ x = 4.
        let mut m = manager();
        let x = m.mk_var("x", m.sorts.real_sort);
        let mut prob = TransProblem::default();
        let mut cache = FxHashMap::default();
        let xv = prob.intern_term(x, &m, &mut cache).unwrap();
        let sx = prob.intern_term(m.mk_sqrt(x), &m, &mut cache).unwrap();
        prob.add_constraint(sx, Rational64::from_integer(2), Cmp::Eq, 0.001);
        let out = solve_conjunction(&prob, &TransOptions::default());
        match out {
            TransOutcome::DeltaSat { values } => {
                let v = values[0].to_f64().unwrap();
                assert!((v - 4.0).abs() < 1e-3, "got {v}");
            }
            other => panic!("expected DeltaSat, got {other:?}"),
        }
        // atan(x) = π/4-ish: atan(1) = 0.7853981…
        let mut prob = TransProblem::default();
        let mut cache = FxHashMap::default();
        let ax = prob.intern_term(m.mk_atan(x), &m, &mut cache).unwrap();
        prob.add_constraint(
            ax,
            Rational64::new(7853981633974483, 10_000_000_000_000_000),
            Cmp::Eq,
            0.001,
        );
        match solve_conjunction(&prob, &TransOptions::default()) {
            TransOutcome::DeltaSat { values } => {
                let v = values[0].to_f64().unwrap();
                assert!((v - 1.0).abs() < 1e-2, "got {v}");
            }
            other => panic!("expected DeltaSat, got {other:?}"),
        }
        let _ = xv;
    }

    #[test]
    fn unbounded_sum_is_sat_by_point_witness() {
        // x + y ≤ 5 with both free: the midpoint (0, 0) verifies.
        let mut m = manager();
        let x = m.mk_var("x", m.sorts.real_sort);
        let y = m.mk_var("y", m.sorts.real_sort);
        let mut prob = TransProblem::default();
        let mut cache = FxHashMap::default();
        let sum = prob.intern_term(m.mk_add([x, y]), &m, &mut cache).unwrap();
        prob.add_constraint(sum, Rational64::from_integer(5), Cmp::Le, 0.001);
        match solve_conjunction(&prob, &TransOptions::default()) {
            TransOutcome::DeltaSat { .. } => {}
            other => panic!("expected DeltaSat, got {other:?}"),
        }
    }
}

#[cfg(test)]
mod trig_probe {
    use super::*;
    use nixie_core::ast::TermManager;
    use num_traits::Zero;
    use rustc_hash::FxHashMap;

    /// sin²(x) + cos²(x) = 0 through the purified form (s = sin x, c = cos
    /// x), x bounded to [0, 6]: bisection covers a bounded domain, so the
    /// refutation completes.
    #[test]
    fn probe_pythagorean_zero_bounded() {
        let mut m = TermManager::new();
        let x = m.mk_var("x", m.sorts.real_sort);
        let s = m.mk_var("s", m.sorts.real_sort);
        let c = m.mk_var("c", m.sorts.real_sort);
        let six = m.mk_real(Rational64::from_integer(6));
        let sin_t = m.mk_sin(x);
        let cos_t = m.mk_cos(x);
        let sub1 = m.mk_sub(s, sin_t);
        let sub2 = m.mk_sub(c, cos_t);
        let s2 = m.mk_mul([s, s]);
        let c2 = m.mk_mul([c, c]);
        let sum_term = m.mk_add([s2, c2]);
        let mut prob = TransProblem::default();
        let mut cache = FxHashMap::default();
        let d1 = prob.intern_term(sub1, &m, &mut cache).unwrap();
        let d2 = prob.intern_term(sub2, &m, &mut cache).unwrap();
        let sum = prob.intern_term(sum_term, &m, &mut cache).unwrap();
        let z = Rational64::zero();
        prob.add_constraint(d1, z, Cmp::Eq, 0.001);
        prob.add_constraint(d2, z, Cmp::Eq, 0.001);
        prob.add_constraint(sum, z, Cmp::Eq, 0.001);
        // x ∈ [0, 6].
        let xv = prob.intern_term(x, &m, &mut cache).unwrap();
        let sixv = prob.intern_term(six, &m, &mut cache).unwrap();
        let _ = sixv;
        prob.add_constraint(xv, Rational64::zero(), Cmp::Ge, 0.001);
        prob.add_constraint(xv, Rational64::from_integer(6), Cmp::Le, 0.001);
        let out = solve_conjunction(&prob, &TransOptions::default());
        assert!(
            matches!(out, TransOutcome::Unsat { .. }),
            "bounded sin^2 + cos^2 = 0 is refutable, got {out:?}"
        );
    }

    /// The UNBOUNDED form: pure bisection cannot exhaust ℝ for a periodic
    /// identity — the honest verdict is `Unknown` (dReal shares this
    /// limitation; refuting it needs periodicity reasoning ICP does not
    /// carry).  This test pins that we never GUESS either direction.
    #[test]
    fn probe_pythagorean_zero_unbounded_is_unknown() {
        let mut m = TermManager::new();
        let x = m.mk_var("x", m.sorts.real_sort);
        let s = m.mk_var("s", m.sorts.real_sort);
        let c = m.mk_var("c", m.sorts.real_sort);
        let sin_t = m.mk_sin(x);
        let cos_t = m.mk_cos(x);
        let sub1 = m.mk_sub(s, sin_t);
        let sub2 = m.mk_sub(c, cos_t);
        let s2 = m.mk_mul([s, s]);
        let c2 = m.mk_mul([c, c]);
        let sum_term = m.mk_add([s2, c2]);
        let mut prob = TransProblem::default();
        let mut cache = FxHashMap::default();
        let d1 = prob.intern_term(sub1, &m, &mut cache).unwrap();
        let d2 = prob.intern_term(sub2, &m, &mut cache).unwrap();
        let sum = prob.intern_term(sum_term, &m, &mut cache).unwrap();
        let z = Rational64::zero();
        prob.add_constraint(d1, z, Cmp::Eq, 0.001);
        prob.add_constraint(d2, z, Cmp::Eq, 0.001);
        prob.add_constraint(sum, z, Cmp::Eq, 0.001);
        let out = solve_conjunction(&prob, &TransOptions::default());
        assert!(
            matches!(out, TransOutcome::Unknown),
            "unbounded periodic identity must stay Unknown, got {out:?}"
        );
    }
}

/// Regression for the `:delta` option plumbing at the engine level: a
/// δ-weakened `sin(x) = 0` over [3.2, 3.3] is δ-satisfiable at δ = 0.15
/// (|sin(3.25)| ≈ 0.108 < 0.15) and refutable at δ = 0.001.
#[cfg(test)]
mod d15_probe {
    use super::*;
    use nixie_core::ast::TermManager;
    use num_traits::Zero;
    use rustc_hash::FxHashMap;

    #[test]
    fn delta_weakening_widens_the_admissible_window() {
        let mut m = TermManager::new();
        let x = m.mk_var("x", m.sorts.real_sort);
        let sin_t = m.mk_sin(x);
        let lo32 = m.mk_real(Rational64::new(32, 10));
        let hi33 = m.mk_real(Rational64::new(33, 10));
        let mut prob = TransProblem::default();
        let mut cache = FxHashMap::default();
        let sx = prob.intern_term(sin_t, &m, &mut cache).unwrap();
        let xv = prob.intern_term(x, &m, &mut cache).unwrap();
        prob.add_constraint(sx, Rational64::zero(), Cmp::Eq, 0.15);
        prob.add_constraint(xv, Rational64::new(32, 10), Cmp::Ge, 0.15);
        prob.add_constraint(xv, Rational64::new(33, 10), Cmp::Le, 0.15);
        let _ = (lo32, hi33);
        let out = solve_conjunction(&prob, &TransOptions::default());
        eprintln!("[d15] {out:?}");
        assert!(matches!(out, TransOutcome::DeltaSat { .. }), "got {out:?}");
    }
}
