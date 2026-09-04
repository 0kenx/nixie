//! Equality Propagation Engine for Theory Combination.
#![allow(dead_code)] // Under development
//!
//! Implements efficient equality propagation between theories using:
//! - Congruence closure with union-find
//! - E-graph for term rewriting
//! - Equality explanation generation
//! - Watched equalities for lazy propagation

#[allow(unused_imports)]
use crate::prelude::*;
use nixie_core::ast::{RoundingMode, TermId, TermKind, TermManager, get_children};
use nixie_core::interner::Spur;

/// Equality propagation engine.
pub struct EqualityPropagator {
    /// Union-find for equality classes
    union_find: UnionFind,
    /// Congruence closure data structures
    congruence: CongruenceData,
    /// Pending equalities to propagate
    pending: VecDeque<(TermId, TermId, Explanation)>,
    /// Watched equalities: term → watchers
    watched: FxHashMap<TermId, Vec<EqualityWatch>>,
    /// E-graph for term canonicalization
    egraph: EGraph,
    /// Statistics
    stats: EqualityPropStats,
}

/// Union-find data structure for equivalence classes.
#[derive(Debug, Clone)]
pub struct UnionFind {
    /// Parent pointers
    parent: FxHashMap<TermId, TermId>,
    /// Rank for union-by-rank
    rank: FxHashMap<TermId, usize>,
    /// Size of equivalence class
    size: FxHashMap<TermId, usize>,
}

/// Congruence closure data.
///
/// Note that `use_list` currently has no producer: [`Self::merge_use_lists`]
/// only merges two possibly-empty lists and [`Self::get_parents`] only reads,
/// so nothing ever records "term `t` is an argument of term `p`".
/// `EqualityPropagator::propagate_equality` therefore always finds an empty
/// parent list, `pending_congruences` is never populated, and
/// `EqualityPropagator::check_congruences` is a no-op loop. The congruence
/// half of this engine is dormant, not wrong -- but
/// `EqualityPropagator::are_congruent` is the predicate any future wiring
/// would use, so it has to be right.
#[derive(Debug, Clone)]
pub struct CongruenceData {
    /// Use list: term → terms that use it
    use_list: FxHashMap<TermId, Vec<TermId>>,
    /// Lookup table: (function, args) → term
    lookup: FxHashMap<CongruenceKey, TermId>,
    /// Pending congruence checks
    pending_congruences: VecDeque<(TermId, TermId)>,
}

/// Key for congruence lookup.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct CongruenceKey {
    /// Function/operator
    pub function: TermKind,
    /// Canonical arguments (equivalence class representatives)
    pub args: Vec<TermId>,
}

/// E-graph for term canonicalization.
#[derive(Debug, Clone)]
pub struct EGraph {
    /// E-class membership: term → e-class
    eclass: FxHashMap<TermId, EClassId>,
    /// E-class contents: e-class → terms
    nodes: FxHashMap<EClassId, Vec<TermId>>,
    /// E-class data
    data: FxHashMap<EClassId, EClassData>,
    /// Next available e-class ID
    next_id: EClassId,
}

/// E-class identifier.
pub type EClassId = usize;

/// Data associated with an e-class.
#[derive(Debug, Clone)]
pub struct EClassData {
    /// Representative term
    pub representative: TermId,
    /// Size of e-class
    pub size: usize,
    /// Parent e-classes (for congruence)
    pub parents: Vec<EClassId>,
}

/// Explanation for an equality.
#[derive(Debug, Clone)]
pub enum Explanation {
    /// Given equality (axiom)
    Given,
    /// Equality by reflexivity
    Reflexivity,
    /// Equality by transitivity
    Transitivity(TermId, Box<Explanation>, Box<Explanation>),
    /// Equality by congruence
    Congruence(Vec<(TermId, TermId, Box<Explanation>)>),
    /// Theory propagation
    TheoryPropagation(TheoryExplanation),
}

/// Theory-specific explanation.
#[derive(Debug, Clone)]
pub struct TheoryExplanation {
    /// Theory ID
    pub theory_id: usize,
    /// Antecedent equalities
    pub antecedents: Vec<(TermId, TermId)>,
}

/// Watched equality for lazy propagation.
#[derive(Debug, Clone)]
pub struct EqualityWatch {
    /// Left-hand side
    pub lhs: TermId,
    /// Right-hand side
    pub rhs: TermId,
    /// Callback ID
    pub callback: usize,
}

/// How a `TermKind` participates in congruence closure.
///
/// Introduced with [`EqualityPropagator::congruence_shape`] so that the
/// classification is a single exhaustive `match` rather than a whitelist with a
/// silent catch-all.
enum CongruenceShape {
    /// A nullary symbol (literal or variable): no children, so congruence is
    /// just "the same symbol".
    Nullary,
    /// An ordinary operator: congruent to another node with the same
    /// [`OperatorIdentity`] whose children are pairwise in the same class.
    Operator(OperatorIdentity),
    /// A binding form (`Forall`/`Exists`/`Let`/`Match`): never congruent to a
    /// syntactically different term.
    Binder,
}

/// Everything that identifies an operator besides its children.
///
/// `core::mem::discriminant` alone is *not* operator identity: it cannot tell
/// `f` from `g` in `Apply`, one `extract` window from another, `head` from
/// `tail`, or two `fp.add`s with different rounding modes apart. Congruence
/// must compare all of it.
#[derive(Debug, Clone, PartialEq, Eq)]
struct OperatorIdentity {
    /// Which `TermKind` variant this is.
    discriminant: core::mem::Discriminant<TermKind>,
    /// Interned symbol for `Apply` / `DtConstructor` / `DtTester` /
    /// `DtSelector`; `None` for every other operator.
    symbol: Option<Spur>,
    /// Rounding mode for the floating-point operators that carry one.
    rounding: Option<RoundingMode>,
    /// Numeric operator parameters: `(high, low)` for `BvExtract`,
    /// `(eb, sb)` for the FP format conversions, `(width, 0)` for
    /// `fp.to_sbv` / `fp.to_ubv`, and `(0, 0)` for operators with none.
    params: (u32, u32),
}

/// Equality propagation statistics.
#[derive(Debug, Clone, Default)]
pub struct EqualityPropStats {
    /// Equalities propagated
    pub equalities_propagated: usize,
    /// Congruences found
    pub congruences_found: usize,
    /// E-graph merges
    pub egraph_merges: usize,
    /// Explanations generated
    pub explanations_generated: usize,
    /// Watched equality triggers
    pub watch_triggers: usize,
}

impl UnionFind {
    /// Create a new union-find structure.
    pub fn new() -> Self {
        Self {
            parent: FxHashMap::default(),
            rank: FxHashMap::default(),
            size: FxHashMap::default(),
        }
    }

    /// Find the representative of a set.
    pub fn find(&mut self, x: TermId) -> TermId {
        if let crate::prelude::hash_map::Entry::Vacant(e) = self.parent.entry(x) {
            e.insert(x);
            self.rank.insert(x, 0);
            self.size.insert(x, 1);
            return x;
        }

        let parent = self.parent[&x];
        if parent != x {
            // Path compression
            let root = self.find(parent);
            self.parent.insert(x, root);
            root
        } else {
            x
        }
    }

    /// Union two sets.
    pub fn union(&mut self, x: TermId, y: TermId) -> bool {
        let root_x = self.find(x);
        let root_y = self.find(y);

        if root_x == root_y {
            return false; // Already in same set
        }

        let rank_x = self.rank.get(&root_x).copied().unwrap_or(0);
        let rank_y = self.rank.get(&root_y).copied().unwrap_or(0);

        // Union by rank
        if rank_x < rank_y {
            self.parent.insert(root_x, root_y);
            let size_x = self.size.get(&root_x).copied().unwrap_or(1);
            *self.size.entry(root_y).or_insert(1) += size_x;
        } else if rank_x > rank_y {
            self.parent.insert(root_y, root_x);
            let size_y = self.size.get(&root_y).copied().unwrap_or(1);
            *self.size.entry(root_x).or_insert(1) += size_y;
        } else {
            self.parent.insert(root_y, root_x);
            *self.rank.entry(root_x).or_insert(0) += 1;
            let size_y = self.size.get(&root_y).copied().unwrap_or(1);
            *self.size.entry(root_x).or_insert(1) += size_y;
        }

        true
    }

    /// Check if two elements are in the same set.
    pub fn connected(&mut self, x: TermId, y: TermId) -> bool {
        self.find(x) == self.find(y)
    }

    /// Get size of the set containing x.
    pub fn set_size(&mut self, x: TermId) -> usize {
        let root = self.find(x);
        self.size[&root]
    }
}

impl EqualityPropagator {
    /// Create a new equality propagator.
    pub fn new() -> Self {
        Self {
            union_find: UnionFind::new(),
            congruence: CongruenceData::new(),
            pending: VecDeque::new(),
            watched: FxHashMap::default(),
            egraph: EGraph::new(),
            stats: EqualityPropStats::default(),
        }
    }

    /// Assert an equality.
    pub fn assert_equality(
        &mut self,
        lhs: TermId,
        rhs: TermId,
        explanation: Explanation,
        tm: &TermManager,
    ) -> Result<(), String> {
        // Check if already equal
        if self.union_find.connected(lhs, rhs) {
            return Ok(());
        }

        // Add to pending queue
        self.pending.push_back((lhs, rhs, explanation));

        // Propagate all pending equalities
        self.propagate(tm)?;

        Ok(())
    }

    /// Propagate all pending equalities.
    fn propagate(&mut self, tm: &TermManager) -> Result<(), String> {
        while let Some((lhs, rhs, explanation)) = self.pending.pop_front() {
            self.propagate_equality(lhs, rhs, explanation, tm)?;
        }

        // Check for new congruences
        self.check_congruences(tm)?;

        Ok(())
    }

    /// Propagate a single equality.
    fn propagate_equality(
        &mut self,
        lhs: TermId,
        rhs: TermId,
        _explanation: Explanation,
        _tm: &TermManager,
    ) -> Result<(), String> {
        // Union in union-find
        if !self.union_find.union(lhs, rhs) {
            return Ok(()); // Already merged
        }

        self.stats.equalities_propagated += 1;

        // Merge in e-graph
        self.egraph.merge(lhs, rhs);
        self.stats.egraph_merges += 1;

        // Update use lists
        self.congruence.merge_use_lists(lhs, rhs);

        // Trigger watches
        self.trigger_watches(lhs, rhs)?;

        // Add parents to pending congruence checks
        let lhs_parents = self.congruence.get_parents(lhs);
        let rhs_parents = self.congruence.get_parents(rhs);

        for lhs_parent in lhs_parents {
            for &rhs_parent in &rhs_parents {
                self.congruence
                    .pending_congruences
                    .push_back((lhs_parent, rhs_parent));
            }
        }

        Ok(())
    }

    /// Check for new congruences.
    fn check_congruences(&mut self, tm: &TermManager) -> Result<(), String> {
        while let Some((t1, t2)) = self.congruence.pending_congruences.pop_front() {
            // Check if they have congruent arguments
            if self.are_congruent(t1, t2, tm)? {
                self.stats.congruences_found += 1;

                // Generate congruence explanation
                let explanation = self.generate_congruence_explanation(t1, t2, tm)?;

                // Assert equality
                self.pending.push_back((t1, t2, explanation));
            }
        }

        Ok(())
    }

    /// Check if two terms are congruent.
    ///
    /// Congruence is `f(a1..an) ~ f(b1..bn)` when the two nodes carry the
    /// **same operator** and `ai ~ bi` for every `i`. Both halves matter:
    ///
    /// * This used to compare only [`core::mem::discriminant`] of the two
    ///   kinds, which is *not* operator identity for any parameterised kind.
    ///   `Apply { func: f, .. }` and `Apply { func: g, .. }` share a
    ///   discriminant, as do `f(a)`/`g(a)`, `((_ extract 7 0) x)`/
    ///   `((_ extract 3 0) x)`, `head(l)`/`tail(l)`, `cons(..)`/`nil(..)`,
    ///   and every `fp.add`/`fp.mul` pair that differs only in its rounding
    ///   mode. [`Self::operator_identity`] carries exactly the payload the
    ///   discriminant drops.
    /// * The argument list used to come from a `TermKind` whitelist whose
    ///   catch-all returned `vec![]`, so for two `Apply` nodes both lists were
    ///   empty, the pairwise loop never ran, and the function returned `true`
    ///   unconditionally -- `f(a)` and `g(b)` were reported congruent and
    ///   [`Self::assert_equality`] merged them. [`Self::get_args`] now covers
    ///   every kind.
    ///
    /// Sorts are compared as well. Two terms of different sorts can never be
    /// equal, so refusing to merge them is both sound and strictly cheaper
    /// than discovering the mismatch later.
    fn are_congruent(&mut self, t1: TermId, t2: TermId, tm: &TermManager) -> Result<bool, String> {
        if t1 == t2 {
            return Ok(true);
        }

        let term1 = tm.get(t1).ok_or("term not found")?;
        let term2 = tm.get(t2).ok_or("term not found")?;

        // A term is only ever equal to a term of its own sort.
        if term1.sort != term2.sort {
            return Ok(false);
        }

        match (
            Self::congruence_shape(&term1.kind),
            Self::congruence_shape(&term2.kind),
        ) {
            // Nullary symbols have no arguments, so congruence degenerates to
            // "the same symbol". Under hash-consing two distinct ids with the
            // same kind and sort do not arise, but comparing the payload is
            // what makes `IntConst(3)` and `IntConst(4)` -- same discriminant,
            // no children -- correctly *not* congruent.
            (CongruenceShape::Nullary, CongruenceShape::Nullary) => Ok(term1.kind == term2.kind),

            (CongruenceShape::Operator(op1), CongruenceShape::Operator(op2)) => {
                if op1 != op2 {
                    return Ok(false);
                }

                let args1 = self.get_args(&term1.kind);
                let args2 = self.get_args(&term2.kind);

                if args1.len() != args2.len() {
                    return Ok(false);
                }

                for (arg1, arg2) in args1.iter().zip(args2.iter()) {
                    if !self.union_find.connected(*arg1, *arg2) {
                        return Ok(false);
                    }
                }

                Ok(true)
            }

            // Binding forms. `Forall`/`Exists`/`Let`/`Match` are deliberately
            // never congruent to a *different* term (`t1 == t2` returned early
            // above). Congruence on a binder would have to compare the bound
            // variable list, the trigger patterns and the case patterns up to
            // alpha-equivalence, and comparing bodies alone is unsound:
            // `(forall ((x Int)) b1)` and `(forall ((y Bool)) b2)` bind
            // different variables even when `b1 ~ b2`. Reporting "not
            // congruent" only ever loses propagation, never soundness.
            (CongruenceShape::Binder, CongruenceShape::Binder) => Ok(false),

            // Different shapes cannot share a discriminant, so this is
            // "different operators".
            _ => Ok(false),
        }
    }

    /// Generate explanation for congruence.
    fn generate_congruence_explanation(
        &mut self,
        t1: TermId,
        t2: TermId,
        tm: &TermManager,
    ) -> Result<Explanation, String> {
        let term1 = tm.get(t1).ok_or("term not found")?;
        let term2 = tm.get(t2).ok_or("term not found")?;

        let args1 = self.get_args(&term1.kind);
        let args2 = self.get_args(&term2.kind);

        let mut arg_explanations = Vec::new();

        for (arg1, arg2) in args1.iter().zip(args2.iter()) {
            let expl = self.explain_equality(*arg1, *arg2)?;
            arg_explanations.push((*arg1, *arg2, Box::new(expl)));
        }

        self.stats.explanations_generated += 1;

        Ok(Explanation::Congruence(arg_explanations))
    }

    /// Explain why two terms are equal.
    pub fn explain_equality(&mut self, lhs: TermId, rhs: TermId) -> Result<Explanation, String> {
        if lhs == rhs {
            return Ok(Explanation::Reflexivity);
        }

        if !self.union_find.connected(lhs, rhs) {
            return Err("Terms are not equal".to_string());
        }

        // Simplified: return a generic explanation
        // Full implementation would trace union-find path
        Ok(Explanation::Given)
    }

    /// Watch an equality.
    pub fn watch_equality(&mut self, lhs: TermId, rhs: TermId, callback: usize) {
        let watch = EqualityWatch { lhs, rhs, callback };

        self.watched.entry(lhs).or_default().push(watch.clone());
        self.watched.entry(rhs).or_default().push(watch);
    }

    /// Trigger watches when an equality is established.
    fn trigger_watches(&mut self, lhs: TermId, rhs: TermId) -> Result<(), String> {
        let mut triggered = Vec::new();

        // Check watches on lhs
        if let Some(watches) = self.watched.get(&lhs) {
            for watch in watches {
                if self.union_find.connected(watch.lhs, watch.rhs) {
                    triggered.push(watch.callback);
                }
            }
        }

        // Check watches on rhs
        if let Some(watches) = self.watched.get(&rhs) {
            for watch in watches {
                if self.union_find.connected(watch.lhs, watch.rhs) {
                    triggered.push(watch.callback);
                }
            }
        }

        self.stats.watch_triggers += triggered.len();

        Ok(())
    }

    /// Get arguments of a term.
    ///
    /// Delegates to [`nixie_core::ast::get_children`], which has an arm for
    /// every `TermKind` and no catch-all, so a new variant is a compile error
    /// there rather than a silently empty argument list here. This function
    /// used to carry a six-arm whitelist (`And`/`Or`/`Not`/`Eq`/`Le`/`Lt`/
    /// `Add`/`Mul`) ending in `_ => vec![]`, which reported *zero* arguments
    /// for `Apply`, `Select`/`Store`, `Ge`/`Gt`/`Sub`/`Div`/`Mod`/`Neg`/`Ite`/
    /// `Implies`/`Xor`/`Distinct`, every bit-vector, string, floating-point
    /// and datatype operator, and every binder.
    fn get_args(&self, kind: &TermKind) -> Vec<TermId> {
        get_children(kind).into_vec()
    }

    /// Classify a term kind for the purposes of congruence closure.
    ///
    /// The `match` is exhaustive with no `_` arm: adding a `TermKind` variant
    /// must not silently acquire a congruence rule.
    fn congruence_shape(kind: &TermKind) -> CongruenceShape {
        /// An operator whose whole identity is its discriminant.
        fn plain(kind: &TermKind) -> CongruenceShape {
            CongruenceShape::Operator(OperatorIdentity {
                discriminant: core::mem::discriminant(kind),
                symbol: None,
                rounding: None,
                params: (0, 0),
            })
        }

        match kind {
            // ---- Nullary symbols: no children, all identity in the payload.
            TermKind::True
            | TermKind::False
            | TermKind::IntConst(_)
            | TermKind::RealConst(_)
            | TermKind::BitVecConst { .. }
            | TermKind::Var(_)
            | TermKind::StringLit(_)
            | TermKind::FpLit { .. }
            | TermKind::FpPlusInfinity { .. }
            | TermKind::FpMinusInfinity { .. }
            | TermKind::FpPlusZero { .. }
            | TermKind::FpMinusZero { .. }
            | TermKind::FpNaN { .. } => CongruenceShape::Nullary,

            // ---- Operators carrying no payload beyond their discriminant.
            TermKind::Not(_)
            | TermKind::And(_)
            | TermKind::Or(_)
            | TermKind::Xor(_, _)
            | TermKind::Implies(_, _)
            | TermKind::Ite(_, _, _)
            | TermKind::Eq(_, _)
            | TermKind::Distinct(_)
            | TermKind::Neg(_)
            | TermKind::Add(_)
            | TermKind::Sub(_, _)
            | TermKind::Mul(_)
            | TermKind::Div(_, _)
            | TermKind::Mod(_, _)
            | TermKind::Lt(_, _)
            | TermKind::Le(_, _)
            | TermKind::Gt(_, _)
            | TermKind::Ge(_, _)
            | TermKind::BvConcat(_, _)
            | TermKind::BvNot(_)
            | TermKind::BvAnd(_, _)
            | TermKind::BvOr(_, _)
            | TermKind::BvXor(_, _)
            | TermKind::BvAdd(_, _)
            | TermKind::BvSub(_, _)
            | TermKind::BvMul(_, _)
            | TermKind::BvUdiv(_, _)
            | TermKind::BvSdiv(_, _)
            | TermKind::BvUrem(_, _)
            | TermKind::BvSrem(_, _)
            | TermKind::BvShl(_, _)
            | TermKind::BvLshr(_, _)
            | TermKind::BvAshr(_, _)
            | TermKind::BvUlt(_, _)
            | TermKind::BvUle(_, _)
            | TermKind::BvSlt(_, _)
            | TermKind::BvSle(_, _)
            | TermKind::Select(_, _)
            | TermKind::Store(_, _, _)
            | TermKind::StrConcat(_, _)
            | TermKind::StrLen(_)
            | TermKind::StrSubstr(_, _, _)
            | TermKind::StrAt(_, _)
            | TermKind::StrContains(_, _)
            | TermKind::StrPrefixOf(_, _)
            | TermKind::StrSuffixOf(_, _)
            | TermKind::StrIndexOf(_, _, _)
            | TermKind::StrReplace(_, _, _)
            | TermKind::StrReplaceAll(_, _, _)
            | TermKind::StrReplaceRe(_, _, _)
            | TermKind::StrReplaceReAll(_, _, _)
            | TermKind::StrToInt(_)
            | TermKind::IntToStr(_)
            | TermKind::StrInRe(_, _)
            | TermKind::StrLt(_, _)
            | TermKind::StrLe(_, _)
            | TermKind::StrToCode(_)
            | TermKind::StrFromCode(_)
            | TermKind::FpAbs(_)
            | TermKind::FpNeg(_)
            | TermKind::FpRem(_, _)
            | TermKind::FpMin(_, _)
            | TermKind::FpMax(_, _)
            | TermKind::FpLeq(_, _)
            | TermKind::FpLt(_, _)
            | TermKind::FpGeq(_, _)
            | TermKind::FpGt(_, _)
            | TermKind::FpEq(_, _)
            | TermKind::FpIsNormal(_)
            | TermKind::FpIsSubnormal(_)
            | TermKind::FpIsZero(_)
            | TermKind::FpIsInfinite(_)
            | TermKind::FpIsNaN(_)
            | TermKind::FpIsNegative(_)
            | TermKind::FpIsPositive(_)
            | TermKind::FpToReal(_) => plain(kind),

            // ---- Indexed bit-vector operator: the bounds are part of the
            // operator, not arguments.
            TermKind::BvExtract { high, low, .. } => CongruenceShape::Operator(OperatorIdentity {
                discriminant: core::mem::discriminant(kind),
                symbol: None,
                rounding: None,
                params: (*high, *low),
            }),

            // ---- Floating-point operators parameterised by a rounding mode.
            TermKind::FpSqrt(rm, _)
            | TermKind::FpRoundToIntegral(rm, _)
            | TermKind::FpAdd(rm, _, _)
            | TermKind::FpSub(rm, _, _)
            | TermKind::FpMul(rm, _, _)
            | TermKind::FpDiv(rm, _, _)
            | TermKind::FpFma(rm, _, _, _) => CongruenceShape::Operator(OperatorIdentity {
                discriminant: core::mem::discriminant(kind),
                symbol: None,
                rounding: Some(*rm),
                params: (0, 0),
            }),

            // ---- Floating-point conversions: rounding mode plus target format.
            TermKind::FpToFp { rm, eb, sb, .. }
            | TermKind::RealToFp { rm, eb, sb, .. }
            | TermKind::SBVToFp { rm, eb, sb, .. }
            | TermKind::UBVToFp { rm, eb, sb, .. } => CongruenceShape::Operator(OperatorIdentity {
                discriminant: core::mem::discriminant(kind),
                symbol: None,
                rounding: Some(*rm),
                params: (*eb, *sb),
            }),
            TermKind::FpToSBV { rm, width, .. } | TermKind::FpToUBV { rm, width, .. } => {
                CongruenceShape::Operator(OperatorIdentity {
                    discriminant: core::mem::discriminant(kind),
                    symbol: None,
                    rounding: Some(*rm),
                    params: (*width, 0),
                })
            }

            // ---- Symbol-carrying operators: the interned name *is* the
            // operator. This is the arm whose absence made `f(a)` congruent to
            // `g(b)`.
            TermKind::Apply { func: symbol, .. }
            | TermKind::DtConstructor {
                constructor: symbol,
                ..
            }
            | TermKind::DtTester {
                constructor: symbol,
                ..
            }
            | TermKind::DtSelector {
                selector: symbol, ..
            } => CongruenceShape::Operator(OperatorIdentity {
                discriminant: core::mem::discriminant(kind),
                symbol: Some(*symbol),
                rounding: None,
                params: (0, 0),
            }),

            // ---- Binding forms; see `are_congruent`.
            TermKind::Forall { .. }
            | TermKind::Exists { .. }
            | TermKind::Let { .. }
            | TermKind::Match { .. } => CongruenceShape::Binder,
        }
    }

    /// Get statistics.
    pub fn stats(&self) -> &EqualityPropStats {
        &self.stats
    }
}

impl CongruenceData {
    /// Create new congruence data.
    pub fn new() -> Self {
        Self {
            use_list: FxHashMap::default(),
            lookup: FxHashMap::default(),
            pending_congruences: VecDeque::new(),
        }
    }

    /// Merge use lists when two terms become equal.
    pub fn merge_use_lists(&mut self, t1: TermId, t2: TermId) {
        // Simplified implementation
        let t1_uses = self.use_list.get(&t1).cloned().unwrap_or_default();
        let t2_uses = self.use_list.get(&t2).cloned().unwrap_or_default();

        let mut merged = t1_uses;
        merged.extend(t2_uses);

        self.use_list.insert(t1, merged.clone());
        self.use_list.insert(t2, merged);
    }

    /// Get parent terms.
    pub fn get_parents(&self, t: TermId) -> Vec<TermId> {
        self.use_list.get(&t).cloned().unwrap_or_default()
    }
}

impl EGraph {
    /// Create a new e-graph.
    pub fn new() -> Self {
        Self {
            eclass: FxHashMap::default(),
            nodes: FxHashMap::default(),
            data: FxHashMap::default(),
            next_id: 0,
        }
    }

    /// Get e-class for a term.
    pub fn get_eclass(&mut self, term: TermId) -> EClassId {
        if let Some(&id) = self.eclass.get(&term) {
            id
        } else {
            let id = self.next_id;
            self.next_id += 1;

            self.eclass.insert(term, id);
            self.nodes.insert(id, vec![term]);
            self.data.insert(
                id,
                EClassData {
                    representative: term,
                    size: 1,
                    parents: Vec::new(),
                },
            );

            id
        }
    }

    /// Merge two terms in the e-graph.
    pub fn merge(&mut self, t1: TermId, t2: TermId) {
        let id1 = self.get_eclass(t1);
        let id2 = self.get_eclass(t2);

        if id1 == id2 {
            return;
        }

        // Merge smaller into larger
        let size1 = self.data[&id1].size;
        let size2 = self.data[&id2].size;

        let (smaller, larger) = if size1 < size2 {
            (id1, id2)
        } else {
            (id2, id1)
        };

        // Update e-class membership
        let smaller_nodes = self.nodes[&smaller].clone();
        for &node in &smaller_nodes {
            self.eclass.insert(node, larger);
        }

        // Merge node lists
        if let Some(larger_nodes) = self.nodes.get_mut(&larger) {
            larger_nodes.extend(smaller_nodes);
        }
        self.nodes.remove(&smaller);

        // Update data
        let smaller_size = self.data.get(&smaller).map(|d| d.size).unwrap_or(0);
        if let Some(larger_data) = self.data.get_mut(&larger) {
            larger_data.size += smaller_size;
        }
        self.data.remove(&smaller);
    }
}

impl Default for EqualityPropagator {
    fn default() -> Self {
        Self::new()
    }
}

impl Default for UnionFind {
    fn default() -> Self {
        Self::new()
    }
}

impl Default for CongruenceData {
    fn default() -> Self {
        Self::new()
    }
}

impl Default for EGraph {
    fn default() -> Self {
        Self::new()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_union_find() {
        let mut uf = UnionFind::new();

        let t1 = TermId::from(1);
        let t2 = TermId::from(2);
        let t3 = TermId::from(3);

        assert!(!uf.connected(t1, t2));

        uf.union(t1, t2);
        assert!(uf.connected(t1, t2));

        uf.union(t2, t3);
        assert!(uf.connected(t1, t3));
    }

    #[test]
    fn test_equality_propagator() {
        let prop = EqualityPropagator::new();
        assert_eq!(prop.stats.equalities_propagated, 0);
    }

    // ======== Congruence regression tests ========
    //
    // These drive `are_congruent` directly. That is deliberate: nothing in the
    // workspace ever inserts into `CongruenceData::use_list` (only
    // `merge_use_lists` and `get_parents` touch it, and the former merges two
    // possibly-empty lists), so `get_parents` always returns an empty vector,
    // `pending_congruences` is never populated, and `check_congruences` is a
    // no-op loop. The wrong merge these tests pin was therefore latent rather
    // than live -- see the notes on `CongruenceData` -- but the predicate is
    // still the one any future wiring would use.

    /// `f(a)` and `g(b)` must never be congruent, whatever the union-find says
    /// about `a` and `b`.
    ///
    /// Before the fix this returned `true`: `get_args`' catch-all reported zero
    /// arguments for `Apply`, so the two (empty) argument lists had equal
    /// length, the pairwise loop never executed, and `are_congruent` fell
    /// through to `Ok(true)` on the strength of the shared discriminant alone.
    #[test]
    fn distinct_function_symbols_are_not_congruent() {
        let mut tm = TermManager::new();
        let bool_sort = tm.sorts.bool_sort;
        let a = tm.mk_var("a", bool_sort);
        let b = tm.mk_var("b", bool_sort);
        let fa = tm.mk_apply("f", [a], bool_sort);
        let gb = tm.mk_apply("g", [b], bool_sort);

        let mut prop = EqualityPropagator::new();
        // Even with a ~ b asserted, f and g are different functions.
        prop.union_find.union(a, b);

        assert_eq!(
            prop.are_congruent(fa, gb, &tm),
            Ok(false),
            "f(a) and g(b) have different function symbols"
        );
    }

    /// Same function symbol, arguments in the same class: congruent.
    #[test]
    fn same_function_symbol_with_equal_args_is_congruent() {
        let mut tm = TermManager::new();
        let bool_sort = tm.sorts.bool_sort;
        let a = tm.mk_var("a", bool_sort);
        let b = tm.mk_var("b", bool_sort);
        let fa = tm.mk_apply("f", [a], bool_sort);
        let fb = tm.mk_apply("f", [b], bool_sort);

        let mut prop = EqualityPropagator::new();
        assert_eq!(
            prop.are_congruent(fa, fb, &tm),
            Ok(false),
            "a ~ b not known yet"
        );
        prop.union_find.union(a, b);
        assert_eq!(
            prop.are_congruent(fa, fb, &tm),
            Ok(true),
            "f(a) ~ f(b) once a ~ b"
        );
    }

    /// Same function symbol but different arity: not congruent.
    #[test]
    fn same_function_symbol_with_different_arity_is_not_congruent() {
        let mut tm = TermManager::new();
        let bool_sort = tm.sorts.bool_sort;
        let a = tm.mk_var("a", bool_sort);
        let b = tm.mk_var("b", bool_sort);
        let f1 = tm.mk_apply("f", [a], bool_sort);
        let f2 = tm.mk_apply("f", [a, b], bool_sort);

        let mut prop = EqualityPropagator::new();
        prop.union_find.union(a, b);
        assert_eq!(prop.are_congruent(f1, f2, &tm), Ok(false));
    }

    /// A datatype selector is not its sibling selector, nor is a tester.
    #[test]
    fn distinct_datatype_accessors_are_not_congruent() {
        let mut tm = TermManager::new();
        let int_sort = tm.sorts.int_sort;
        let list = tm.mk_var("l", int_sort);
        let head = tm.mk_dt_selector("head", list, int_sort);
        let tail = tm.mk_dt_selector("tail", list, int_sort);

        let mut prop = EqualityPropagator::new();
        assert_eq!(prop.are_congruent(head, tail, &tm), Ok(false));
    }

    /// Two `extract` windows over the same argument are different operators.
    #[test]
    fn distinct_bv_extract_windows_are_not_congruent() {
        let mut tm = TermManager::new();
        let bv8 = tm.sorts.bitvec(8);
        let x = tm.mk_var("x", bv8);
        let lo = tm.mk_bv_extract(3, 0, x);
        let hi = tm.mk_bv_extract(7, 4, x);

        let mut prop = EqualityPropagator::new();
        assert_eq!(prop.are_congruent(lo, hi, &tm), Ok(false));
    }

    /// Bit-vector operands really are compared now: the old whitelist reported
    /// zero arguments for `bvadd`, so any two `bvadd` nodes were congruent.
    #[test]
    fn bv_operator_arguments_are_compared() {
        let mut tm = TermManager::new();
        let bv8 = tm.sorts.bitvec(8);
        let x = tm.mk_var("x", bv8);
        let y = tm.mk_var("y", bv8);
        let z = tm.mk_var("z", bv8);
        let xy = tm.mk_bv_add(x, y);
        let xz = tm.mk_bv_add(x, z);

        let mut prop = EqualityPropagator::new();
        assert_eq!(
            prop.are_congruent(xy, xz, &tm),
            Ok(false),
            "bvadd(x,y) and bvadd(x,z) are not congruent while y !~ z"
        );
        prop.union_find.union(y, z);
        assert_eq!(prop.are_congruent(xy, xz, &tm), Ok(true));
    }

    /// Quantifiers are never congruent to a different term, even when their
    /// bodies are in the same class.
    #[test]
    fn binders_are_never_congruent() {
        let mut tm = TermManager::new();
        let bool_sort = tm.sorts.bool_sort;
        let int_sort = tm.sorts.int_sort;
        let p = tm.mk_var("p", bool_sort);
        let q = tm.mk_var("q", bool_sort);
        let f1 = tm.mk_forall([("x", int_sort)], p);
        let f2 = tm.mk_forall([("y", bool_sort)], q);

        let mut prop = EqualityPropagator::new();
        prop.union_find.union(p, q);
        assert_eq!(prop.are_congruent(f1, f2, &tm), Ok(false));
        assert_eq!(prop.are_congruent(f1, f1, &tm), Ok(true), "reflexivity");
    }

    /// Distinct numerals share a discriminant and have no children.
    #[test]
    fn distinct_numerals_are_not_congruent() {
        let mut tm = TermManager::new();
        let three = tm.mk_int(3);
        let four = tm.mk_int(4);

        let mut prop = EqualityPropagator::new();
        assert_eq!(prop.are_congruent(three, four, &tm), Ok(false));
    }

    /// `get_args` must report the operands of kinds the old whitelist missed.
    #[test]
    fn get_args_covers_kinds_outside_the_old_whitelist() {
        let mut tm = TermManager::new();
        let bv8 = tm.sorts.bitvec(8);
        let int_sort = tm.sorts.int_sort;
        let bool_sort = tm.sorts.bool_sort;
        let prop = EqualityPropagator::new();

        let x = tm.mk_var("x", bv8);
        let y = tm.mk_var("y", bv8);
        let i = tm.mk_var("i", int_sort);
        let p = tm.mk_var("p", bool_sort);

        let apply = tm.mk_apply("f", [i], int_sort);
        let bvadd = tm.mk_bv_add(x, y);
        let arr = tm.mk_var("a", int_sort);
        let select = tm.mk_select(arr, i);
        let j = tm.mk_var("j", int_sort);
        let ite = tm.mk_ite(p, i, j);

        for (term, expected) in [(apply, 1usize), (bvadd, 2), (select, 2), (ite, 3)] {
            let kind = &tm.get(term).expect("term exists").kind;
            assert_eq!(
                prop.get_args(kind).len(),
                expected,
                "wrong arity reported for {kind:?}"
            );
        }
    }

    #[test]
    fn test_egraph() {
        let mut eg = EGraph::new();

        let t1 = TermId::from(1);
        let t2 = TermId::from(2);

        let id1 = eg.get_eclass(t1);
        let id2 = eg.get_eclass(t2);

        assert_ne!(id1, id2);

        eg.merge(t1, t2);

        let id1_after = eg.get_eclass(t1);
        let id2_after = eg.get_eclass(t2);

        assert_eq!(id1_after, id2_after);
    }
}
