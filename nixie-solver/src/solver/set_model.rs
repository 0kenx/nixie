//! Set model synthesis and the shared set-value evaluator.
//!
//! Two jobs, one module:
//!
//! * [`Solver::extract_set_model`] runs at model-build time, after the
//!   arithmetic / bit-vector / string passes have pinned the element
//!   values. It reads the final SAT assignment of every membership atom,
//!   the arithmetic value of every `set.card` term, and the equality /
//!   subset relations the reduction related, and synthesizes a **faithful
//!   finite value** for each set-sorted term: ground members from the
//!   member atoms, plus — where a cardinality target demands more elements
//!   than the ground part supplies — freshly minted elements, one pool per
//!   equivalence class of set terms, propagated along committed subset
//!   edges. This is the eager-reduction analogue of Z3's
//!   `theory_finite_set_size::init_model`, which materializes each slack
//!   region as a `set.unique` set of fresh elements and unions it into
//!   every set variable true in that region's signature.
//! * [`SetView`] is the evaluator both `(get-value)`/`(get-model)` folding
//!   ([`crate::solver::Model::eval`]) and the model-verification soundness
//!   gate ([`Solver::eval_in_model_outcome`]) use to answer set queries
//!   against a built model: membership, cardinality, subset, and the value
//!   of a set term as a canonical `set.union`-of-`set.singleton` term.
//!
//! # Soundness posture
//!
//! Synthesis is **verified before it is published**: after building values
//! for one element sort's family of set terms, every recorded cardinality
//! target, committed equality, committed subset and committed membership
//! atom is re-checked against the synthesized values, and on any mismatch
//! the whole sort's entries are rolled back. A declined sort leaves its
//! sets unassigned, which every consumer reads as *undetermined* — the
//! same honest non-answer these queries gave before this module existed —
//! so a synthesis bug can never publish a model that contradicts the
//! assertions. The verification gate, which becomes set-aware together
//! with this module, is the second, independent line of defense.
//!
//! Every walk in this module is iterative (explicit stacks): set terms are
//! user input and may nest arbitrarily.

use crate::prelude::*;
use nixie_core::ast::{TermId, TermKind, TermManager};
use nixie_core::sort::{SortId, SortKind};
use num_rational::Rational64;

use super::Solver;
use super::set_theory::ModelSurvey;
use super::types::Model;

/// Cap on freshly minted elements per element sort: a cardinality target
/// demanding more than this many anonymous elements declines the sort
/// (rolled back to unassigned) rather than building a value nobody will
/// read. Also bounds the synthesized value terms' size.
const MAX_MINTED_ELEMENTS: usize = 4096;

/// Cap on enumerating a finite universe (`set.universe`, complements) into
/// explicit elements: `Bool` (2) always qualifies, narrow bit-vectors when
/// `2^w` fits; anything larger stays structural (membership still answers,
/// enumeration-based queries decline).
const MAX_UNIVERSE_ENUM: u64 = 1024;

// =====================================================================
// Part 1: the shared evaluator
// =====================================================================

/// A read-only view over a built model that answers set questions.
pub(super) struct SetView<'a> {
    model: &'a Model,
    manager: &'a TermManager,
    /// Memo for [`SetView::elements`]: `None` = not materializable.
    memo_elements: FxHashMap<TermId, Option<Vec<TermId>>>,
    /// Memo for [`SetView::element_value`].
    memo_value: FxHashMap<TermId, Option<TermId>>,
}

/// One step of the iterative [`SetView::elements`] walk: a compound set
/// term whose operands are being materialized.
struct ElemFrame {
    /// The compound set term being combined.
    term: TermId,
    /// Operand results live in `vals[base..]`.
    base: usize,
}

impl<'a> SetView<'a> {
    pub(super) fn new(model: &'a Model, manager: &'a TermManager) -> Self {
        Self {
            model,
            manager,
            memo_elements: FxHashMap::default(),
            memo_value: FxHashMap::default(),
        }
    }

    /// The ground value of an element term, if the model pins one.
    ///
    /// A value is a constant term (numeric, bit-vector, string, field,
    /// IEEE-754, Boolean, datatype) or — for `Set (Set T)` elements — a
    /// canonical synthesized set-value term. Anything else (an unassigned
    /// variable, an opaque application) has no value here.
    pub(super) fn element_value(&mut self, term: TermId) -> Option<TermId> {
        if let Some(hit) = self.memo_value.get(&term) {
            return *hit;
        }
        let out = self.compute_element_value(term);
        self.memo_value.insert(term, out);
        out
    }

    fn compute_element_value(&mut self, term: TermId) -> Option<TermId> {
        if let Some(entry) = self.model.get(term)
            && self.is_ground_value(entry)
        {
            return Some(entry);
        }
        if self.is_ground_value(term) {
            return Some(term);
        }
        None
    }

    /// Whether `t` can serve as an element value: a constant, or a
    /// canonical set-value term (nested-set elements).
    fn is_ground_value(&self, t: TermId) -> bool {
        matches!(
            self.manager.get(t).map(|d| &d.kind),
            Some(
                TermKind::True
                    | TermKind::False
                    | TermKind::IntConst(_)
                    | TermKind::RealConst(_)
                    | TermKind::BitVecConst { .. }
                    | TermKind::StringLit(_)
                    | TermKind::FfConst { .. }
                    | TermKind::FpLit { .. }
                    | TermKind::FpPlusInfinity { .. }
                    | TermKind::FpMinusInfinity { .. }
                    | TermKind::FpPlusZero { .. }
                    | TermKind::FpMinusZero { .. }
                    | TermKind::FpNaN { .. }
                    | TermKind::DtConstructor { .. }
                    | TermKind::SetEmpty(_)
                    | TermKind::SetSingleton(_)
                    | TermKind::SetUnion(_, _)
            )
        )
    }

    /// The truth of a Boolean term as recorded in the model, if recorded.
    fn committed_bool(&self, term: TermId) -> Option<bool> {
        let value = self.model.get(term)?;
        match self.manager.get(value).map(|d| &d.kind) {
            Some(TermKind::True) => Some(true),
            Some(TermKind::False) => Some(false),
            _ => None,
        }
    }

    /// The sorted, distinct element values of a set term, when it can be
    /// written as a finite list.
    ///
    /// `None` is the honest non-answer: the universe (or a complement)
    /// over an infinite or unenumerated sort, or an operand with no value.
    pub(super) fn elements(&mut self, term: TermId) -> Option<Vec<TermId>> {
        if let Some(hit) = self.memo_elements.get(&term) {
            return hit.clone();
        }
        // Driver with an explicit two-state frame stack, mirroring the
        // evaluator pattern of `model_eval.rs` for the same stack-safety
        // reason: user input may nest arbitrarily deep.
        enum Frame {
            Open(TermId),
            Combine(ElemFrame),
        }
        let mut frames: Vec<Frame> = vec![Frame::Open(term)];
        let mut vals: Vec<Option<Vec<TermId>>> = Vec::new();
        while let Some(frame) = frames.pop() {
            match frame {
                Frame::Open(t) => {
                    if let Some(hit) = self.memo_elements.get(&t) {
                        vals.push(hit.clone());
                        continue;
                    }
                    let Some(kind) = self.manager.get(t).map(|d| d.kind.clone()) else {
                        self.memo_elements.insert(t, None);
                        vals.push(None);
                        continue;
                    };
                    match kind {
                        TermKind::SetEmpty(_) => {
                            self.memo_elements.insert(t, Some(Vec::new()));
                            vals.push(Some(Vec::new()));
                        }
                        TermKind::SetSingleton(y) => {
                            let v = self.element_value(y).map(|val| vec![val]);
                            self.memo_elements.insert(t, v.clone());
                            vals.push(v);
                        }
                        // The universe stays structural in the read-only
                        // view: enumerating it needs term construction
                        // (synthesis does that via `universe_elements_of`).
                        // Membership still answers through the structural
                        // path below; cardinality of a universe declines.
                        TermKind::SetUniv(_) => {
                            self.memo_elements.insert(t, None);
                            vals.push(None);
                        }
                        // An opaque set (variable, application, select):
                        // its value is the model's entry, a canonical term.
                        TermKind::Var(_)
                        | TermKind::Apply { .. }
                        | TermKind::Select(_, _)
                        | TermKind::DtSelector { .. } => {
                            let v = self
                                .model
                                .get(t)
                                .and_then(|entry| self.parse_value_elements(entry));
                            self.memo_elements.insert(t, v.clone());
                            vals.push(v);
                        }
                        TermKind::Ite(cond, a, b) => {
                            // The condition is a Boolean the model recorded
                            // (the SAT assignment pins every encoded atom);
                            // without a recorded value the term has none.
                            let picked = match self.committed_bool(cond) {
                                Some(true) => Some(a),
                                Some(false) => Some(b),
                                None => None,
                            };
                            match picked {
                                None => {
                                    self.memo_elements.insert(t, None);
                                    vals.push(None);
                                }
                                Some(branch) => {
                                    let base = vals.len();
                                    frames.push(Frame::Combine(ElemFrame { term: t, base }));
                                    frames.push(Frame::Open(branch));
                                }
                            }
                        }
                        TermKind::SetUnion(a, b)
                        | TermKind::SetInter(a, b)
                        | TermKind::SetMinus(a, b) => {
                            let base = vals.len();
                            frames.push(Frame::Combine(ElemFrame { term: t, base }));
                            // Reverse order so `a` opens (and lands) first.
                            frames.push(Frame::Open(b));
                            frames.push(Frame::Open(a));
                        }
                        TermKind::SetComplement(inner) => {
                            let base = vals.len();
                            frames.push(Frame::Combine(ElemFrame { term: t, base }));
                            frames.push(Frame::Open(inner));
                        }
                        // A relation compound's value is whatever the
                        // cross-sort synthesis pass installed (its operands
                        // live in other element sorts, so it cannot be
                        // folded here); without an entry it is
                        // undetermined, never guessed.
                        TermKind::SetRelJoin(_, _)
                        | TermKind::SetRelProduct(_, _)
                        | TermKind::SetRelTranspose(_)
                        | TermKind::SetRelIden(_) => {
                            let v = self
                                .model
                                .get(t)
                                .and_then(|entry| self.parse_value_elements(entry));
                            self.memo_elements.insert(t, v.clone());
                            vals.push(v);
                        }
                        _ => {
                            self.memo_elements.insert(t, None);
                            vals.push(None);
                        }
                    }
                }
                Frame::Combine(ElemFrame { term: t, base }) => {
                    let parts = vals.split_off(base);
                    let combined = self.combine_elements(t, parts);
                    self.memo_elements.insert(t, combined.clone());
                    vals.push(combined);
                }
            }
        }
        vals.pop().flatten()
    }

    /// Combine a compound set's operand lists per its kind. Every input is
    /// normalized (sorted, distinct); every output is too.
    fn combine_elements(
        &mut self,
        term: TermId,
        parts: Vec<Option<Vec<TermId>>>,
    ) -> Option<Vec<TermId>> {
        let kind = self.manager.get(term).map(|d| d.kind.clone())?;
        match kind {
            TermKind::SetUnion(_, _) => {
                let mut out: Vec<TermId> = Vec::new();
                for part in parts {
                    out.extend(part?);
                }
                out.sort_unstable();
                out.dedup();
                Some(out)
            }
            TermKind::SetInter(_, _) => {
                let mut iter = parts.into_iter();
                let mut acc = iter.next()??;
                for part in iter {
                    let other = part?;
                    acc.retain(|v| other.contains(v));
                }
                Some(acc)
            }
            TermKind::SetMinus(_, _) => {
                let mut iter = parts.into_iter();
                let mut acc = iter.next()??;
                for part in iter {
                    let sub = part?;
                    acc.retain(|v| !sub.contains(v));
                }
                Some(acc)
            }
            TermKind::SetComplement(_) => {
                // Not materializable in the read-only view; membership
                // answers structurally.
                None
            }
            // Passthrough of the taken branch (chosen at open time).
            TermKind::Ite(_, _, _) => parts.into_iter().next().flatten(),
            _ => None,
        }
    }

    /// Membership of `element`'s value in `set`: concrete when the model
    /// determines both, `None` otherwise.
    pub(super) fn member(&mut self, element: TermId, set: TermId) -> Option<bool> {
        let value = match self.element_value(element) {
            Some(v) => Some(v),
            None => match self.manager.get(element).map(|d| d.kind.clone()) {
                // An unvalued `choose(t)` — one that appears only in a
                // query, never in an assertion: its value is a member of
                // `t` whenever `t` is nonempty, so resolve through `t`'s
                // own value. An empty or unset `t` leaves it undetermined.
                Some(TermKind::SetChoose(t)) => self
                    .elements(t)
                    .and_then(|members| members.first().copied()),
                _ => None,
            },
        }?;
        self.member_value(value, set)
    }

    /// Membership of a *value* in `set`. Succeeds strictly more often than
    /// [`SetView::elements`]: complements and universes answer without a
    /// materializable list.
    ///
    /// Decomposes the set term into an AND/OR forest over leaf containment
    /// tests, with complement polarities folded into the children; the
    /// walk is iterative for the same depth-safety reason as everything
    /// else here.
    pub(super) fn member_value(&mut self, value: TermId, set: TermId) -> Option<bool> {
        enum Frame {
            /// One AND/OR node: which operand terms still decide it, at
            /// which polarity, and the results landed so far.
            Node {
                /// AND (`∩`, `\`, passthrough) or OR (`∪`).
                conjunct: bool,
                children: Vec<(TermId, bool)>,
                next: usize,
                results: Vec<Option<bool>>,
            },
        }
        // The top frame's next move, computed by value so the frame
        // borrow ends before the state below mutates the stack.
        enum Step {
            /// Open this child next.
            Child(TermId, bool),
            /// The node is decided: combine its results.
            Combine(bool, Vec<Option<bool>>),
        }
        fn push_result(frames: &mut [Frame], v: Option<bool>) {
            match frames.last_mut() {
                Some(Frame::Node { results, .. }) => results.push(v),
                None => {}
            }
        }
        let mut frames: Vec<Frame> = Vec::new();
        // The root: a leaf answers directly; a compound opens a node. The
        // root's polarity is TRUE — "is the value a member" — with `false`
        // reserved for complemented subtrees (see `member_children`).
        if let Some(v) = self.open_member(value, set, true) {
            return Some(v);
        }
        let (conjunct, children) = member_children(set, true, self.manager)?;
        frames.push(Frame::Node {
            conjunct,
            children,
            next: 0,
            results: Vec::new(),
        });
        loop {
            let step = match frames.last_mut() {
                Some(Frame::Node {
                    conjunct,
                    children,
                    next,
                    results,
                }) => {
                    if *next < children.len() {
                        let (child, polarity) = children[*next];
                        *next += 1;
                        Step::Child(child, polarity)
                    } else {
                        Step::Combine(*conjunct, std::mem::take(results))
                    }
                }
                // Only a `Combine` empties the stack, and it returns; an
                // empty stack here means the driver lost its root.
                None => return None,
            };
            match step {
                Step::Child(child, polarity) => {
                    if let Some(v) = self.open_member(value, child, polarity) {
                        push_result(&mut frames, Some(v));
                    } else if let Some((c_conjunct, c_children)) =
                        member_children(child, polarity, self.manager)
                    {
                        frames.push(Frame::Node {
                            conjunct: c_conjunct,
                            children: c_children,
                            next: 0,
                            results: Vec::new(),
                        });
                    } else {
                        // Neither a decidable leaf nor a decomposable node.
                        push_result(&mut frames, None);
                    }
                }
                Step::Combine(conjunct, results) => {
                    let answer = if conjunct {
                        // AND: any false decides false; any residual None
                        // keeps the node undetermined.
                        if results.contains(&Some(false)) {
                            Some(false)
                        } else if results.contains(&None) {
                            None
                        } else {
                            Some(true)
                        }
                    } else {
                        // OR: any true decides true; any residual None
                        // keeps the node undetermined.
                        if results.contains(&Some(true)) {
                            Some(true)
                        } else if results.contains(&None) {
                            None
                        } else {
                            Some(false)
                        }
                    };
                    // Pop the finished node; the root's pop empties the
                    // stack, which is the loop's exit.
                    frames.pop();
                    match frames.last_mut() {
                        Some(Frame::Node {
                            results: parent, ..
                        }) => parent.push(answer),
                        None => return answer,
                    }
                }
            }
        }
    }

    /// A leaf membership test: `value ∈ (term at polarity)`.
    fn open_member(&mut self, value: TermId, term: TermId, polarity: bool) -> Option<bool> {
        // Fast path: a materializable set answers by containment.
        if let Some(elements) = self.elements(term) {
            return Some(elements.contains(&value) == polarity);
        }
        match self.manager.get(term).map(|d| d.kind.clone())? {
            TermKind::SetUniv(_) => Some(polarity),
            _ => None,
        }
    }

    /// Cardinality as a plain `i64`, when concretely determined and small
    /// enough (the callers' numeric domain is `Rational64`, and a
    /// materialized list never exceeds the caps above).
    pub(super) fn card(&mut self, set: TermId) -> Option<i64> {
        if let Some(elements) = self.elements(set) {
            return i64::try_from(elements.len()).ok();
        }
        match self.manager.get(set).map(|d| d.kind.clone())? {
            // A finite universe's size needs no enumeration, only the
            // sort's arithmetic.
            TermKind::SetUniv(set_sort) => {
                let size = self.universe_size(element_sort_of(self.manager, set_sort)?)?;
                i64::try_from(size).ok()
            }
            TermKind::SetComplement(inner) => {
                let inner_count = self.card(inner)?;
                let set_sort = self.manager.get(set)?.sort;
                let size = self.universe_size(element_sort_of(self.manager, set_sort)?)?;
                Some(i64::try_from(size).ok()? - inner_count)
            }
            _ => None,
        }
    }

    /// Subset between two set terms, when both sides are determined.
    pub(super) fn subset(&mut self, a: TermId, b: TermId) -> Option<bool> {
        if a == b {
            return Some(true);
        }
        let (ea, eb) = (self.elements(a)?, self.elements(b)?);
        if eb.len() < ea.len() {
            return Some(false);
        }
        Some(ea.iter().all(|v| eb.contains(v)))
    }

    /// Set equality between two terms, when determined.
    pub(super) fn set_eq(&mut self, a: TermId, b: TermId) -> Option<bool> {
        if a == b {
            return Some(true);
        }
        let (ea, eb) = (self.elements(a)?, self.elements(b)?);
        Some(ea == eb)
    }

    /// Read a canonical value term back into its sorted element list.
    fn parse_value_elements(&mut self, value: TermId) -> Option<Vec<TermId>> {
        let mut out: Vec<TermId> = Vec::new();
        let mut stack = vec![value];
        while let Some(t) = stack.pop() {
            match self.manager.get(t).map(|d| &d.kind) {
                Some(TermKind::SetEmpty(_)) => {}
                Some(TermKind::SetSingleton(v)) => out.push(*v),
                Some(TermKind::SetUnion(a, b)) => {
                    stack.push(*a);
                    stack.push(*b);
                }
                // Not a canonical value term.
                _ => return None,
            }
        }
        out.sort_unstable();
        out.dedup();
        Some(out)
    }

    /// The exact size of a finite element sort, when known and it fits a
    /// `u64`.
    fn universe_size(&self, sort: SortId) -> Option<u64> {
        universe_size_of(self.manager, sort)
    }
}

/// The inhabitants of a finite, small element sort (`Bool`, narrow
/// bit-vectors), as constant terms.
fn universe_elements_of(manager: &mut TermManager, set_sort: SortId) -> Option<Vec<TermId>> {
    let elem = element_sort_of(manager, set_sort)?;
    let size = universe_size_of(manager, elem)?;
    if size > MAX_UNIVERSE_ENUM {
        return None;
    }
    match manager.sorts.get(elem).map(|s| s.kind.clone()) {
        Some(SortKind::Bool) => Some(vec![manager.mk_true(), manager.mk_false()]),
        Some(SortKind::BitVec(width)) => {
            let mut out = Vec::with_capacity(size as usize);
            for v in 0..size {
                out.push(manager.mk_bitvec(num_bigint::BigInt::from(v), width));
            }
            Some(out)
        }
        _ => None,
    }
}

/// The exact size of a finite element sort, when known and it fits a `u64`.
fn universe_size_of(manager: &TermManager, sort: SortId) -> Option<u64> {
    match manager.sorts.get(sort).map(|s| &s.kind) {
        Some(SortKind::Bool) => Some(2),
        Some(SortKind::RoundingMode) => Some(5),
        Some(SortKind::BitVec(w)) => {
            if *w < 64 {
                Some(1u64 << *w)
            } else {
                None
            }
        }
        Some(SortKind::FiniteField(id)) => manager
            .sorts
            .field_desc(*id)
            .and_then(|d| u64::try_from(d.modulus().clone()).ok()),
        _ => None,
    }
}

/// The children of a membership node: which operand terms decide it, at
/// which polarity, and whether they conjoin or disjoin.
fn member_children(
    term: TermId,
    polarity: bool,
    manager: &TermManager,
) -> Option<(bool, Vec<(TermId, bool)>)> {
    match manager.get(term).map(|d| &d.kind) {
        Some(TermKind::SetUnion(a, b)) => Some((false, vec![(*a, polarity), (*b, polarity)])),
        Some(TermKind::SetInter(a, b)) => Some((true, vec![(*a, polarity), (*b, polarity)])),
        Some(TermKind::SetMinus(a, b)) => Some((true, vec![(*a, polarity), (*b, !polarity)])),
        Some(TermKind::SetComplement(inner)) => Some((true, vec![(*inner, !polarity)])),
        _ => None,
    }
}

fn element_sort_of(manager: &TermManager, set_sort: SortId) -> Option<SortId> {
    match manager.sorts.get(set_sort).map(|s| &s.kind) {
        Some(SortKind::Set(e)) => Some(*e),
        _ => None,
    }
}

// =====================================================================
// Part 2: synthesis
// =====================================================================

/// A tiny union-find over set terms (equality classes of committed-equal
/// sets). Path-halving `find`; no ranks needed at these sizes.
struct Classes {
    parent: FxHashMap<TermId, TermId>,
}

impl Classes {
    fn new() -> Self {
        Self {
            parent: FxHashMap::default(),
        }
    }

    fn add(&mut self, t: TermId) {
        self.parent.entry(t).or_insert(t);
    }

    fn union(&mut self, a: TermId, b: TermId) {
        self.add(a);
        self.add(b);
        let (ra, rb) = (self.find(a), self.find(b));
        if ra != rb {
            self.parent.insert(ra, rb);
        }
    }

    fn find(&mut self, t: TermId) -> TermId {
        // Find the root.
        let mut root = t;
        while let Some(p) = self.parent.get(&root).copied()
            && p != root
        {
            root = p;
        }
        // Path halving, iteratively.
        let mut cur = t;
        while cur != root {
            let Some(p) = self.parent.get(&cur).copied() else {
                break;
            };
            if let Some(&grandparent) = self.parent.get(&p)
                && grandparent != p
            {
                self.parent.insert(cur, grandparent);
            }
            cur = p;
        }
        root
    }
}

impl Solver {
    /// Synthesize set values into `model`; see the module doc.
    pub(super) fn extract_set_model(&mut self, model: &mut Model, manager: &mut TermManager) {
        if self.set_terms_unconstrained {
            // The honesty gate will discard this model; nothing here can
            // make a cardinality resting on unreduced terms faithful.
            return;
        }
        if self.assertions.is_empty() {
            return;
        }
        let survey = super::set_theory::survey_for_model(&self.assertions, manager);
        if survey.sets.is_empty() {
            return;
        }
        // Group the set terms by element sort.
        let mut by_elem: FxHashMap<SortId, Vec<TermId>> = FxHashMap::default();
        for &set in &survey.sets {
            if let Some(elem) = set_element_sort(set, manager) {
                by_elem.entry(elem).or_default().push(set);
            }
        }
        // Bottom-up over Set nesting: `Set (Set Int)` needs the inner
        // `Set Int` values as element values first.
        let mut ordered: Vec<(SortId, Vec<TermId>)> = by_elem.into_iter().collect();
        ordered.sort_by_key(|(elem, _)| sort_nesting_depth(*elem, manager));

        for (elem_sort, sets) in ordered {
            self.synthesize_sort(&survey, elem_sort, &sets, model, manager);
        }
        // Relation compounds: their operands live in *other* element sorts
        // (the transposed, paired, joined or diagonalized tuple sorts), so
        // their values are computed once every sort's opaque values are
        // installed, in a fixpoint over nesting.
        self.synthesize_rel_values(&survey, model, manager);
    }

    /// Synthesize values for one element sort's sets, verifying before
    /// publishing (rollback on any definite mismatch).
    fn synthesize_sort(
        &mut self,
        survey: &ModelSurvey,
        elem_sort: SortId,
        sets: &[TermId],
        model: &mut Model,
        manager: &mut TermManager,
    ) {
        let empty_list: Vec<TermId> = Vec::new();
        let elements: &[TermId] = survey.elements.get(&elem_sort).unwrap_or(&empty_list);

        // ---- element values: resolve what the model pins ----
        let mut used: FxHashSet<TermId> = FxHashSet::default();
        let mut elem_values: FxHashMap<TermId, Option<TermId>> = FxHashMap::default();
        {
            let mut view = SetView::new(model, manager);
            for &e in elements {
                let v = view.element_value(e);
                if let Some(v) = v {
                    used.insert(v);
                }
                elem_values.insert(e, v);
            }
        }
        // Which elements are committed members of which sets (the same
        // hash-consed atoms the reduction created axioms for).
        let mut member_true: Vec<(TermId, Vec<TermId>)> = Vec::new();
        for &set in sets {
            let mut members: Vec<TermId> = Vec::new();
            for &e in elements {
                let atom = manager.mk_set_member(e, set);
                if self.committed_bool_model(atom, model, manager) == Some(true) {
                    members.push(e);
                }
            }
            member_true.push((set, members));
        }
        let needs_value = |e: TermId| -> bool { member_true.iter().any(|(_, ms)| ms.contains(&e)) };
        // Mint distinct values for member-true elements the model did not
        // pin. The values must not collide with any used value: two
        // elements minted equal would merge in the printed model while
        // their membership atoms never agreed.
        // A choose term's value must be one of its set's members, so it is
        // valued after the class values exist (below), not here.
        let is_choose =
            |e: TermId| -> bool { survey.chooses.iter().any(|&(choose, _)| choose == e) };
        let mut minted_total: usize = 0;
        for &e in elements {
            if is_choose(e) || !needs_value(e) {
                continue;
            }
            // One of **our own skolems** — a disequality witness or a join
            // middle — keeps whatever value a committed-true equality pins
            // it to; any *default* it picked up (the arithmetic pass zeros
            // unconstrained integers, the datatype reconstruction repeats
            // its canonical tuple) is overridden with a fresh, distinct
            // witness. Two witnesses of the two directions of one
            // disequality defaulted equal is exactly the collision that
            // used to decline the whole sort.
            if elem_values.get(&e).is_some_and(Option::is_some)
                && !(is_our_set_skolem(e, manager) && self.skolem_pinned_to(e).is_none())
            {
                continue;
            }
            // The overridden default stops being anyone's value; free it
            // so the mint takes the natural smallest witness instead of
            // skipping past it (a stale `0` in `used` pushed the witness
            // to 3 and changed which memberships folded).
            if let Some(Some(old)) = elem_values.get(&e).copied() {
                used.remove(&old);
            }
            match self.mint_element_value(elem_sort, &used, manager) {
                Some(v) => {
                    used.insert(v);
                    elem_values.insert(e, Some(v));
                    model.set(e, v);
                    minted_total += 1;
                }
                None => {
                    // An element sort with no mintable witness: any set it
                    // is a member of cannot be given a faithful value.
                    return;
                }
            }
        }
        if minted_total > MAX_MINTED_ELEMENTS {
            return;
        }

        // ---- tuple-element component resolution ----
        //
        // A tuple constructor element may spell unresolvable terms inside
        // (a join skolem, an unconstrained variable): `(1, k)`. The
        // model's value for `k` exists (minted or pinned above), so the
        // tuple's *value* is the constructor over the resolved
        // components. Install it as the element's entry — the read-only
        // evaluator then compares values with values, and without this a
        // committed membership over such a tuple compared its spelling
        // against the synthesized value and verification rolled the whole
        // sort back (found on `(1,3) ∈ r ⨝ s`: the split `(1, k)` is a
        // committed member of `r` whose spelling is not in `r`'s value).
        // Nested tuples resolve innermost-first by element order; one
        // sweep per nesting level.
        for _sweep in 0..4 {
            let mut changed = false;
            for &e in elements {
                let Some(TermKind::DtConstructor { args, .. }) =
                    manager.get(e).map(|d| d.kind.clone())
                else {
                    continue;
                };
                if model.get(e).is_some() {
                    continue;
                }
                let mut resolved: Vec<TermId> = Vec::with_capacity(args.len());
                let mut all = true;
                for &arg in &args {
                    // A **join skolem** is our own existential witness: its
                    // value is ours to choose, and the arithmetic pass has
                    // already defaulted every unconstrained integer to 0 —
                    // so several distinct skolems all read 0, their splits
                    // collide as equal-valued tuples with independently
                    // decided memberships, and the collision repair (rightly)
                    // refuses. A committed-true guard equality pins the
                    // skolem to its partner; anything else gets a fresh,
                    // distinct witness that overrides the default.
                    let is_join_skolem = matches!(
                        manager.get(arg).map(|d| &d.kind),
                        Some(TermKind::Var(n))
                            if manager.resolve_str(*n).starts_with("@set_join_")
                    ) && self.skolem_pinned_to(arg).is_none();
                    let value =
                        if is_join_skolem {
                            if let Some(old) = model.get(arg) {
                                used.remove(&old);
                            }
                            match self.mint_component_value(
                                manager.get(arg).map_or(manager.sorts.int_sort, |d| d.sort),
                                &used,
                                manager,
                            ) {
                                Some(v) => {
                                    used.insert(v);
                                    model.set(arg, v);
                                    v
                                }
                                None => {
                                    all = false;
                                    break;
                                }
                            }
                        } else {
                            match model.get(arg) {
                                Some(v) if is_value_term(v, manager) => v,
                                _ if is_value_term(arg, manager) => arg,
                                // An unvalued component (an unconstrained
                                // variable *inside* a committed member): mint a
                                // fresh witness for it, exactly as for a
                                // member-true element. Both splits of a join
                                // resolve through the one entry, so the middles
                                // meet.
                                _ => match manager.get(arg).map(|d| d.sort).and_then(|sort| {
                                    self.mint_component_value(sort, &used, manager)
                                }) {
                                    Some(v) => {
                                        used.insert(v);
                                        model.set(arg, v);
                                        v
                                    }
                                    None => {
                                        all = false;
                                        break;
                                    }
                                },
                            }
                        };
                    resolved.push(value);
                }
                if all {
                    let value = manager.mk_tuple(&resolved);
                    model.set(e, value);
                    if let Some(v) = elem_values.insert(e, Some(value)) {
                        let _ = v;
                    }
                    changed = true;
                }
            }
            if !changed {
                break;
            }
        }

        // ---- value-collision repair ----
        // The arithmetic pass defaults every unconstrained integer variable
        // to 0, so two element terms the formula never related can carry the
        // same displayed value while their membership atoms disagree — an
        // arrangement no set family realizes. If both elements' values were
        // genuinely pinned, the congruence axioms over the (chained)
        // equalities would have forced the memberships to agree, so a
        // disagreement means at least one of the shared values is a pure
        // default: re-mint every colliding element no recorded constraint
        // mentions. An unrepairable collision declines the sort.
        {
            // Membership vector per element: the committed truth of its
            // atom in every set of the sort.
            let mut membership: FxHashMap<TermId, Vec<Option<bool>>> = FxHashMap::default();
            for &e in elements {
                if elem_values.get(&e).is_none_or(Option::is_none) {
                    continue;
                }
                let mut vector: Vec<Option<bool>> = Vec::with_capacity(sets.len());
                for &set in sets {
                    let atom = manager.mk_set_member(e, set);
                    vector.push(self.committed_bool_model(atom, model, manager));
                }
                membership.insert(e, vector);
            }
            // Group the valued elements by value.
            let mut groups: FxHashMap<TermId, Vec<TermId>> = FxHashMap::default();
            for &e in elements {
                if let Some(Some(v)) = elem_values.get(&e) {
                    groups.entry(*v).or_default().push(e);
                }
            }
            for (_, mut group) in groups {
                if group.len() < 2 {
                    continue;
                }
                group.sort_unstable();
                // The anchor is the first **pinned** member — its value is
                // the one a committed equality fixes, so every other
                // member of the group conforms to it, not the reverse.
                // Without a pinned member the first is the anchor and all
                // dissenters (it excluded) re-mint.
                group.sort_by_key(|&e| !self.element_value_is_pinned(e));
                let anchor = group[0];
                let reference = membership
                    .get(&anchor)
                    .cloned()
                    .unwrap_or_else(|| vec![None; sets.len()]);
                for &e in group.iter().skip(1) {
                    let vector = membership
                        .get(&e)
                        .cloned()
                        .unwrap_or_else(|| vec![None; sets.len()]);
                    // A disagreement is two *decided* atoms that differ.
                    // An undecided atom (`None`) is not a conflict: the
                    // encoder never gave it a variable, so nothing pins
                    // it.
                    let disagrees = reference
                        .iter()
                        .zip(vector.iter())
                        .any(|(a, b)| matches!((a, b), (Some(x), Some(y)) if x != y));
                    if !disagrees {
                        continue;
                    }
                    if self.element_value_is_pinned(e) {
                        // Two pinned members disagreeing is a genuine
                        // contradiction the model cannot repair.
                        return;
                    }
                    match self.mint_element_value(elem_sort, &used, manager) {
                        Some(fresh) => {
                            used.insert(fresh);
                            elem_values.insert(e, Some(fresh));
                            model.set(e, fresh);
                        }
                        None => {
                            return;
                        }
                    }
                }
            }
        }

        // ---- cardinality targets (the arithmetic solver's word) ----
        let mut target: FxHashMap<TermId, i64> = FxHashMap::default();
        for &set in sets {
            let card = manager.mk_set_card(set);
            // The arithmetic solver's value first; the model entry the
            // arith pass recorded (an `IntConst`) second — the counting
            // equations reach the tableau through the conjoined axioms,
            // and the pass may have pinned the term where `value` has no
            // entry for it.
            let int_entry = |t: TermId| -> Option<i64> {
                match manager.get(t).map(|d| &d.kind) {
                    Some(TermKind::IntConst(n)) => num_traits::ToPrimitive::to_i64(n),
                    _ => None,
                }
            };
            // A `set.card` term is a foreign numeric leaf to the arithmetic
            // encoder: it is purified to a `$p*` proxy whose arithmetic
            // value IS the target. Resolution order: the tableau, the
            // model entry the arith pass recorded, then the proxy's.
            let mut v: Option<i64> = self.arith.value(card).map_or_else(
                || model.get(card).and_then(int_entry),
                |r| Some(r.to_integer()),
            );
            if v.is_none()
                && let Some(proxy) = self.arith_purify.proxy_of(card)
            {
                v = self.arith.value(proxy).map_or_else(
                    || model.get(proxy).and_then(int_entry),
                    |r| Some(r.to_integer()),
                );
            }
            if let Some(value) = v {
                target.insert(set, value);
            }
        }

        // ---- ground members ----
        let mut ground: FxHashMap<TermId, Vec<TermId>> = FxHashMap::default();
        for (set, members) in &member_true {
            let mut vals: Vec<TermId> = members
                .iter()
                .filter_map(|e| elem_values.get(e).copied().flatten())
                .collect();
            vals.sort_unstable();
            vals.dedup();
            ground.insert(*set, vals);
        }

        // ---- equality classes ----
        let mut classes = Classes::new();
        for &set in sets {
            classes.add(set);
        }
        let mut eq_true: Vec<(TermId, TermId)> = Vec::new();
        for &(a, b) in &survey.eq_pairs {
            if a == b || !sets.contains(&a) || !sets.contains(&b) {
                continue;
            }
            let atom = manager.mk_eq(a, b);
            if self.committed_bool_model(atom, model, manager) == Some(true) {
                classes.union(a, b);
                eq_true.push((a, b));
            }
        }
        let mut subset_true: Vec<(TermId, TermId)> = Vec::new();
        for &(atom, a, b) in &survey.subsets {
            if !sets.contains(&a) || !sets.contains(&b) {
                continue;
            }
            if self.committed_bool_model(atom, model, manager) == Some(true) {
                subset_true.push((a, b));
            }
        }
        // Mutual committed subsets are equal sets.
        for &(a, b) in &subset_true {
            if subset_true.contains(&(b, a)) {
                classes.union(a, b);
            }
        }
        // Every term's class peers (itself included), for the DAG pass.
        let mut peers: FxHashMap<TermId, Vec<TermId>> = FxHashMap::default();
        for &t in sets {
            let rep = classes.find(t);
            peers.entry(rep).or_default().push(t);
        }
        let peers_of = |t: TermId, peers: &FxHashMap<TermId, Vec<TermId>>| -> Vec<TermId> {
            peers
                .values()
                .find(|v| v.contains(&t))
                .cloned()
                .unwrap_or_else(|| vec![t])
        };

        // ---- synthesized values ----
        let mut values: FxHashMap<TermId, Option<Vec<TermId>>> = FxHashMap::default();
        let mut fresh: FxHashMap<TermId, Vec<TermId>> = FxHashMap::default();

        // Pure-opaque classes first: their values come from the member
        // atoms and minting, never from a compound operand, so they can be
        // decided before the term DAG is folded. A class with a compound
        // member takes that compound's value (computed in the DAG pass).
        let mut opaque_reps: Vec<TermId> = Vec::new();
        {
            let mut seen: FxHashSet<TermId> = FxHashSet::default();
            for &t in sets {
                let rep = classes.find(t);
                if seen.insert(rep) {
                    opaque_reps.push(rep);
                }
            }
        }
        // Subset edges between classes, for fresh propagation.
        let mut edges: Vec<(TermId, TermId)> = Vec::new();
        for &(a, b) in &subset_true {
            let (ra, rb) = (classes.find(a), classes.find(b));
            if ra != rb {
                edges.push((ra, rb));
            }
        }
        let rep_members =
            |rep: TermId| -> Vec<TermId> { peers.get(&rep).cloned().unwrap_or_default() };
        for rep in topo_order(&opaque_reps, &edges) {
            let members = rep_members(rep);
            // Classes with a compound member take the compound's value.
            if members.iter().any(|t| !is_opaque_set(*t, manager)) {
                continue;
            }
            let class_target = members.iter().find_map(|t| target.get(t).copied());
            let mut class_ground = members
                .iter()
                .filter_map(|t| ground.get(t).cloned())
                .next()
                .unwrap_or_default();
            class_ground.sort_unstable();
            class_ground.dedup();
            // Fresh elements inherited from subsets of this class.
            let mut inherited: Vec<TermId> = Vec::new();
            for &(sub, sup) in &edges {
                if sup == rep
                    && let Some(pool) = fresh.get(&sub)
                {
                    inherited.extend(pool.iter().copied());
                }
            }
            inherited.sort_unstable();
            inherited.dedup();
            let Some(class_target) = class_target else {
                // No cardinality constraint: ground members plus whatever
                // subclasses force in is already faithful.
                let mut value = class_ground;
                value.extend(inherited.iter().copied());
                value.sort_unstable();
                value.dedup();
                fresh.insert(rep, inherited);
                for t in members {
                    values.insert(t, Some(value.clone()));
                }
                continue;
            };
            let ground_len = i64::try_from(class_ground.len()).unwrap_or(i64::MAX);
            let need = class_target - ground_len;
            if need < 0 {
                return; // the ground part alone exceeds the target
            }
            let inherited_len = i64::try_from(inherited.len()).unwrap_or(i64::MAX);
            if inherited_len > need {
                return; // a subset's fresh pool exceeds this target
            }
            let private = usize::try_from(need - inherited_len).unwrap_or(usize::MAX);
            if minted_total.saturating_add(private) > MAX_MINTED_ELEMENTS {
                return;
            }
            let mut pool = inherited;
            for _ in 0..private {
                match self.mint_element_value(elem_sort, &used, manager) {
                    Some(v) => {
                        used.insert(v);
                        pool.push(v);
                        minted_total += 1;
                    }
                    None => {
                        return;
                    }
                }
            }
            pool.sort_unstable();
            pool.dedup();
            let mut value = class_ground;
            value.extend(pool.iter().copied());
            value.sort_unstable();
            value.dedup();
            fresh.insert(rep, pool);
            for t in members {
                values.insert(t, Some(value.clone()));
            }
        }

        // ---- choose elements: a member of their set, now that the
        // members exist ----
        for &(choose, set) in &survey.chooses {
            if !sets.contains(&set) || elem_values.get(&choose).is_some_and(Option::is_some) {
                continue;
            }
            let member_atom = manager.mk_set_member(choose, set);
            let committed = self.committed_bool_model(member_atom, model, manager);
            let value = match (committed, values.get(&set).cloned().flatten()) {
                // Nonempty and a member: any element of the value (the
                // model's choice; the choose axioms only demand membership
                // and congruence, and class-equal sets share values, so
                // congruent chooses agree).
                (Some(true), Some(members)) => members.first().copied(),
                // Not a member (the set is empty) or no value: any fresh
                // element of the sort — `choose` of an empty set is
                // underspecified, and an unset set makes the query
                // undetermined anyway.
                _ => self.mint_element_value(elem_sort, &used, manager),
            };
            match value {
                Some(v) => {
                    used.insert(v);
                    elem_values.insert(choose, Some(v));
                    model.set(choose, v);
                }
                None => {
                    return;
                }
            }
        }

        // ---- the term DAG, operands first ----
        // Relation compounds are skipped here: their operands live in
        // other element sorts, so their values come from the cross-sort
        // pass in [`Self::extract_set_model`] instead.
        let mut order: Vec<TermId> = sets
            .iter()
            .copied()
            .filter(|&t| !is_rel_shaped(t, manager))
            .collect();
        order.sort_by_key(|&t| term_depth(t, manager));
        for &t in &order {
            structural_value(t, &mut values, &peers_of(t, &peers), &elem_values, manager);
        }

        // ---- intersection-sharing repair ----
        // A compound whose target is smaller than its operands' combined
        // values needs the operands to SHARE elements (inclusion–
        // exclusion). Private pools swap: an element of `a`'s pool replaces
        // an element of `b`'s pool in `b`'s value, shrinking `a ∪ b` (and
        // growing `a ∩ b`) by one per swap while every class target stays
        // met. The twin targets are the same arithmetic, so consistency
        // holds by construction; the final verification re-checks
        // everything regardless.
        for _round in 0..4 {
            let mut swapped = false;
            for &t in &order {
                let Some(&want) = target.get(&t) else {
                    continue;
                };
                let Some(TermKind::SetUnion(a, b)) = manager.get(t).map(|d| d.kind.clone()) else {
                    continue;
                };
                let Some(Some(value)) = values.get(&t).cloned() else {
                    continue;
                };
                let size = i64::try_from(value.len()).unwrap_or(i64::MAX);
                if size <= want {
                    continue;
                }
                let deficit = usize::try_from(size - want).unwrap_or(usize::MAX);
                let (ra, rb) = (classes.find(a), classes.find(b));
                if ra == rb {
                    continue;
                }
                let (pool_a, pool_b) = match (fresh.get(&ra), fresh.get(&rb)) {
                    (Some(pa), Some(pb)) => (pa.clone(), pb.clone()),
                    _ => continue,
                };
                let val_a = values.get(&a).cloned().flatten().unwrap_or_default();
                let mut val_b = values.get(&b).cloned().flatten().unwrap_or_default();
                // Candidates: `a`-private pool elements outside `b`, and
                // `b`-private pool elements outside `a`.
                let sharable: Vec<TermId> = pool_a
                    .iter()
                    .copied()
                    .filter(|e| val_a.contains(e) && !val_b.contains(e))
                    .collect();
                let replaceable: Vec<TermId> = pool_b
                    .iter()
                    .copied()
                    .filter(|e| val_b.contains(e) && !val_a.contains(e))
                    .collect();
                let count = deficit.min(sharable.len()).min(replaceable.len());
                if count == 0 {
                    continue;
                }
                for i in 0..count {
                    let e = sharable[i];
                    let f = replaceable[i];
                    val_b.retain(|x| *x != f);
                    if !val_b.contains(&e) {
                        val_b.push(e);
                    }
                    val_b.sort_unstable();
                    val_b.dedup();
                    used.insert(f); // retired from every value; not re-minted
                }
                let mut new_pool_b = pool_b.clone();
                for i in 0..count {
                    new_pool_b.retain(|x| *x != replaceable[i]);
                    if !new_pool_b.contains(&sharable[i]) {
                        new_pool_b.push(sharable[i]);
                    }
                }
                new_pool_b.sort_unstable();
                new_pool_b.dedup();
                fresh.insert(rb, new_pool_b);
                // Every member of `b`'s class takes the repaired value.
                let members_b: Vec<TermId> = peers.get(&rb).cloned().unwrap_or_else(|| vec![b]);
                for m in members_b {
                    values.insert(m, Some(val_b.clone()));
                }
                swapped = true;
            }
            if !swapped {
                break;
            }
            // Recompute every compound from the repaired class values.
            let compounds: Vec<TermId> = order
                .iter()
                .copied()
                .filter(|t| !is_opaque_set(*t, manager))
                .collect();
            for t in compounds {
                values.remove(&t);
            }
            for &t in &order {
                structural_value(t, &mut values, &peers_of(t, &peers), &elem_values, manager);
            }
        }

        // Propagate within classes: a committed-equal class shares one
        // value, whichever member computed it (a class holding both a
        // variable and its asserted compound definition takes the
        // compound's value, which the depth-ordered DAG pass may have
        // computed only after visiting the variable).
        for members in peers.values() {
            let Some(shared) = members
                .iter()
                .filter_map(|m| values.get(m).cloned())
                .find(Option::is_some)
            else {
                continue;
            };
            for &m in members {
                values.insert(m, shared.clone());
            }
        }

        // ---- publish: opaque terms only (compounds fold structurally) ----
        let mut installed: Vec<TermId> = Vec::new();
        for &t in sets {
            if !is_opaque_set(t, manager) {
                continue;
            }
            if let Some(Some(elems)) = values.get(&t) {
                // Sort sanity: every element of a synthesized value must
                // carry the set's element sort. The datatype
                // reconstruction defaults tuple-sorted variables with
                // constructors of the wrong arity (an internally-declared
                // tuple sort resolved by prefix), and printing such a
                // value would publish an ill-sorted — wrong — model.
                // Declining is the honest answer.
                let well_sorted = elems
                    .iter()
                    .all(|&e| manager.get(e).is_some_and(|d| d.sort == elem_sort));
                if !well_sorted {
                    continue;
                }
                let mut elems = elems.clone();
                elems.sort_unstable();
                let set_sort = manager
                    .get(t)
                    .map(|d| d.sort)
                    .unwrap_or_else(|| manager.sorts.set(elem_sort));
                let mut acc = manager.mk_set_empty_at(set_sort);
                for &e in &elems {
                    let singleton = manager.mk_set_singleton(e);
                    acc = manager.mk_set_union(acc, singleton);
                }
                model.set(t, acc);
                installed.push(t);
            }
        }

        // ---- verify, then roll back on any definite mismatch ----
        // Commitments first (the atoms are cheap to read while `manager`
        // is freely borrowable); the view second.
        let mut member_checks: Vec<(TermId, TermId, bool)> = Vec::new();
        for &t in sets {
            for &e in elements {
                let atom = manager.mk_set_member(e, t);
                if let Some(b) = self.committed_bool_model(atom, model, manager) {
                    member_checks.push((e, t, b));
                }
            }
        }
        let mut choose_checks: Vec<(TermId, TermId, bool)> = Vec::new();
        for &(choose, set) in &survey.chooses {
            if !sets.contains(&set) {
                continue;
            }
            let atom = manager.mk_set_member(choose, set);
            if let Some(b) = self.committed_bool_model(atom, model, manager) {
                choose_checks.push((choose, set, b));
            }
        }
        let mut eq_checks: Vec<(TermId, TermId)> = eq_true.clone();
        eq_checks.retain(|(a, b)| sets.contains(a) && sets.contains(b));
        let mut subset_checks: Vec<(TermId, TermId)> = subset_true.clone();
        subset_checks.retain(|(a, b)| sets.contains(a) && sets.contains(b));
        let target_checks: Vec<(TermId, i64)> = sets
            .iter()
            .filter(|&&t| !is_rel_shaped(t, manager))
            .filter_map(|t| target.get(t).map(|c| (*t, *c)))
            .collect();

        let ok = {
            let mut view = SetView::new(model, manager);
            let mut ok = true;
            for &(t, want) in &target_checks {
                if view.card(t) != Some(want) {
                    ok = false;
                    break;
                }
            }
            if ok {
                for &(a, b) in &eq_checks {
                    if view.set_eq(a, b) == Some(false) {
                        ok = false;
                        break;
                    }
                }
            }
            if ok {
                for &(a, b) in &subset_checks {
                    if view.subset(a, b) == Some(false) {
                        ok = false;
                        break;
                    }
                }
            }
            if ok {
                for &(e, t, committed) in &member_checks {
                    if view.member(e, t) == Some(!committed) {
                        ok = false;
                        break;
                    }
                }
            }
            if ok {
                for &(choose, set, committed) in &choose_checks {
                    if view.member(choose, set) == Some(!committed) {
                        ok = false;
                        break;
                    }
                }
            }
            ok
        };

        if !ok {
            for t in &installed {
                model.remove(*t);
            }
        }
    }

    /// Synthesize values for the relation compounds, cross-sort.
    ///
    /// Operands and compound live in different element sorts (the
    /// transposed, paired, joined or diagonalized tuple sorts), so these
    /// run after every sort's opaque values are installed, reading the
    /// operands through [`SetView`] (which resolves installed entries,
    /// including rel entries from earlier fixpoint rounds — nesting) and
    /// building the compound's canonical value with the tuple builders.
    /// Every installed entry is verified against its arithmetic
    /// cardinality target and its committed membership atoms; a definite
    /// mismatch rolls the rel entries back (the per-sort values stay).
    fn synthesize_rel_values(
        &mut self,
        survey: &ModelSurvey,
        model: &mut Model,
        manager: &mut TermManager,
    ) {
        // The rel terms of the survey, outermost-last is unnecessary — a
        // bounded fixpoint handles any nesting order.
        let rel_terms: Vec<TermId> = survey
            .sets
            .iter()
            .copied()
            .filter(|&t| is_rel_shaped(t, manager))
            .collect();
        if rel_terms.is_empty() {
            return;
        }

        let mut installed: Vec<TermId> = Vec::new();
        // Fixpoint: nested rel compounds read rel entries from earlier
        // rounds; the round count is bounded by the nesting depth.
        for _round in 0..4 {
            let mut changed = false;
            for &t in &rel_terms {
                if model.get(t).is_some() {
                    continue;
                }
                let value: Option<Vec<TermId>> = {
                    let mut view = SetView::new(model, manager);
                    match manager.get(t).map(|d| d.kind.clone()) {
                        Some(TermKind::SetRelTranspose(r)) => view.elements(r).map(|elems| {
                            elems
                                .iter()
                                .map(|&v| reverse_tuple_value(v, manager))
                                .collect()
                        }),
                        Some(TermKind::SetRelIden(x)) => view.elements(x).map(|elems| {
                            elems
                                .iter()
                                .map(|&v| duplicate_tuple_value(v, manager))
                                .collect()
                        }),
                        Some(TermKind::SetRelProduct(a, b)) => {
                            match (view.elements(a), view.elements(b)) {
                                (Some(xs), Some(ys)) => {
                                    const MAX_REL_PRODUCT: usize = 4096;
                                    if xs.len().saturating_mul(ys.len()) > MAX_REL_PRODUCT {
                                        None
                                    } else {
                                        let mut out = Vec::with_capacity(xs.len() * ys.len());
                                        let mut ok = true;
                                        'outer: for &u in &xs {
                                            for &v in &ys {
                                                match concat_values(u, v, manager) {
                                                    Some(glued) => out.push(glued),
                                                    None => {
                                                        ok = false;
                                                        break 'outer;
                                                    }
                                                }
                                            }
                                        }
                                        if ok { Some(out) } else { None }
                                    }
                                }
                                _ => None,
                            }
                        }
                        Some(TermKind::SetRelJoin(r1, r2)) => {
                            match (view.elements(r1), view.elements(r2)) {
                                (Some(us), Some(vs)) => {
                                    let mut out = Vec::new();
                                    let mut ok = true;
                                    'join: for &u in &us {
                                        for &v in &vs {
                                            match join_glue_values(u, v, manager) {
                                                Some(Some(glued)) => out.push(glued),
                                                Some(None) => {}
                                                None => {
                                                    ok = false;
                                                    break 'join;
                                                }
                                            }
                                        }
                                    }
                                    if ok { Some(out) } else { None }
                                }
                                _ => None,
                            }
                        }
                        _ => None,
                    }
                };
                if let Some(mut elems) = value {
                    elems.sort_unstable();
                    elems.dedup();
                    let set_sort = manager.get(t).map(|d| d.sort);
                    let elem_ok = set_element_sort(t, manager).is_some_and(|es| {
                        elems
                            .iter()
                            .all(|&e| manager.get(e).is_some_and(|d| d.sort == es))
                    });
                    if !elem_ok {
                        continue;
                    }
                    if let Some(set_sort) = set_sort {
                        let mut acc = manager.mk_set_empty_at(set_sort);
                        for &e in &elems {
                            let singleton = manager.mk_set_singleton(e);
                            acc = manager.mk_set_union(acc, singleton);
                        }
                        model.set(t, acc);
                        installed.push(t);
                        changed = true;
                    }
                }
            }
            if !changed {
                break;
            }
        }

        // ---- verify the installed rel entries ----
        // Targets: the arithmetic solver's word for the compound's size.
        let int_entry = |t: TermId, manager: &TermManager| -> Option<i64> {
            match manager.get(t).map(|d| &d.kind) {
                Some(TermKind::IntConst(n)) => num_traits::ToPrimitive::to_i64(n),
                _ => None,
            }
        };
        let mut ok = true;
        for &t in &installed {
            let card = manager.mk_set_card(t);
            let want: Option<i64> = self.arith.value(card).map_or_else(
                || model.get(card).and_then(|v| int_entry(v, manager)),
                |r| Some(r.to_integer()),
            );
            let Some(want) = want else {
                continue;
            };
            let got = {
                let mut view = SetView::new(model, manager);
                view.card(t)
            };
            if got != Some(want) {
                ok = false;
                break;
            }
        }
        // Committed membership atoms over the rel compounds.
        if ok {
            'checks: for &t in &installed {
                let Some(es) = set_element_sort(t, manager) else {
                    continue;
                };
                let empty: Vec<TermId> = Vec::new();
                let elems = survey.elements.get(&es).unwrap_or(&empty);
                for &e in elems {
                    let atom = manager.mk_set_member(e, t);
                    let Some(committed) = self.committed_bool_model(atom, model, manager) else {
                        continue;
                    };
                    let got = {
                        let mut view = SetView::new(model, manager);
                        view.member(e, t)
                    };
                    if got == Some(!committed) {
                        ok = false;
                        break 'checks;
                    }
                }
            }
        }
        if !ok {
            for t in &installed {
                model.remove(*t);
            }
        }
    }

    /// The partner of a **committed-true** equality mentioning `e`, if
    /// one exists: the term whose value `e`'s value must equal.
    fn skolem_pinned_to(&self, e: TermId) -> Option<TermId> {
        for (&var, constraint) in &self.var_to_constraint {
            if let super::types::Constraint::Eq(l, r) = constraint
                && self.sat.model_value(var) == nixie_sat::LBool::True
            {
                if *l == e {
                    return Some(*r);
                }
                if *r == e {
                    return Some(*l);
                }
            }
        }
        None
    }

    /// Whether an element's *value* is genuinely pinned by a constraint:
    ///
    /// * a **committed-true equality** mentioning it — an asserted or
    ///   derived `e = v` fixes the value (a *refuted* equality fixes
    ///   nothing; the counting guards are exactly this shape, and every
    ///   derived tuple element sits in one, so treating guards as pins
    ///   made the collision repair decline the whole sort);
    /// * any **order/disequality constraint** mentioning it — those bound
    ///   arithmetic values and only exist for numeric elements.
    fn element_value_is_pinned(&self, e: TermId) -> bool {
        for (&var, constraint) in &self.var_to_constraint {
            match constraint {
                super::types::Constraint::Eq(l, r) => {
                    if (*l == e || *r == e) && self.sat.model_value(var) == nixie_sat::LBool::True {
                        return true;
                    }
                }
                super::types::Constraint::Diseq(l, r)
                | super::types::Constraint::Lt(l, r)
                | super::types::Constraint::Le(l, r)
                | super::types::Constraint::Gt(l, r)
                | super::types::Constraint::Ge(l, r) => {
                    if *l == e || *r == e {
                        return true;
                    }
                }
                super::types::Constraint::BoolApp(t) => {
                    let _ = t;
                }
            }
        }
        false
    }

    /// The committed truth of a Boolean atom: the model entry first, then
    /// the SAT assignment.
    fn committed_bool_model(
        &self,
        atom: TermId,
        model: &Model,
        manager: &TermManager,
    ) -> Option<bool> {
        if let Some(v) = model.get(atom) {
            match manager.get(v).map(|d| &d.kind) {
                Some(TermKind::True) => return Some(true),
                Some(TermKind::False) => return Some(false),
                _ => {}
            }
        }
        let &var = self.term_to_var.get(&atom)?;
        match self.sat.model_value(var) {
            nixie_sat::LBool::True => Some(true),
            nixie_sat::LBool::False => Some(false),
            _ => None,
        }
    }

    /// Mint a fresh **scalar** component value (no set nesting: a
    /// component of a tuple, not an element of a set-of-tuples).
    fn mint_component_value(
        &mut self,
        sort: SortId,
        used: &FxHashSet<TermId>,
        manager: &mut TermManager,
    ) -> Option<TermId> {
        let kind = manager.sorts.get(sort).map(|s| s.kind.clone());
        let mut candidate: i64 = 0;
        loop {
            let term = match &kind {
                Some(SortKind::Int) => manager.mk_int(num_bigint::BigInt::from(candidate)),
                Some(SortKind::Real) => manager.mk_real(Rational64::from_integer(candidate)),
                Some(SortKind::BitVec(w)) => {
                    manager.mk_bitvec(num_bigint::BigInt::from(candidate), *w)
                }
                Some(SortKind::String) => {
                    manager.mk_string_lit(&format!("__nixie_set_elem_{candidate}"))
                }
                _ => return None,
            };
            if !used.contains(&term) {
                return Some(term);
            }
            candidate += 1;
        }
    }

    /// Mint a fresh element value of `sort`, distinct from every value in
    /// `used`. `None` for sorts with no mintable witness.
    fn mint_element_value(
        &mut self,
        sort: SortId,
        used: &FxHashSet<TermId>,
        manager: &mut TermManager,
    ) -> Option<TermId> {
        // Walk down through Set nesting to a directly mintable base sort
        // (iteratively: sort nesting is finite but unbounded).
        let mut chain: Vec<SortId> = vec![sort];
        loop {
            let next = match manager.sorts.get(*chain.last()?).map(|s| s.kind.clone()) {
                Some(SortKind::Set(inner)) => inner,
                _ => break,
            };
            chain.push(next);
        }
        let base = *chain.last()?;
        let base_kind = manager.sorts.get(base).map(|s| s.kind.clone());
        // A tuple base (a relation's witnesses and join skolems are
        // exactly this shape): a fresh component per field.
        if matches!(&base_kind, Some(SortKind::Datatype(_))) {
            let fields = manager.tuple_field_sorts_of(base)?;
            if fields.is_empty() || fields.len() > 8 {
                return None;
            }
            let mut parts: Vec<TermId> = Vec::with_capacity(fields.len());
            for &field in &fields {
                parts.push(self.mint_component_value(field, used, manager)?);
            }
            let mut term = manager.mk_tuple(&parts);
            for _level in chain[..chain.len() - 1].iter().rev() {
                term = manager.mk_set_singleton(term);
            }
            if used.contains(&term) {
                return None;
            }
            return Some(term);
        }
        let mut candidate: i64 = 0;
        let base_term = loop {
            let term = match &base_kind {
                Some(SortKind::Int) => manager.mk_int(num_bigint::BigInt::from(candidate)),
                Some(SortKind::Real) => manager.mk_real(Rational64::from_integer(candidate)),
                Some(SortKind::BitVec(w)) => {
                    manager.mk_bitvec(num_bigint::BigInt::from(candidate), *w)
                }
                Some(SortKind::String) => {
                    manager.mk_string_lit(&format!("__nixie_set_elem_{candidate}"))
                }
                _ => return None,
            };
            if !used.contains(&term) {
                break term;
            }
            candidate += 1;
        };
        // Wrap back up through the Set levels: a fresh singleton per level.
        let mut term = base_term;
        for level in chain[..chain.len() - 1].iter().rev() {
            let _ = level;
            term = manager.mk_set_singleton(term);
        }
        if used.contains(&term) {
            return None;
        }
        Some(term)
    }
}

/// The structural value of one set term from its operands (or its class
/// value for opaque terms). Iterative over the term DAG.
fn structural_value(
    t: TermId,
    values: &mut FxHashMap<TermId, Option<Vec<TermId>>>,
    peers: &[TermId],
    elem_values: &FxHashMap<TermId, Option<TermId>>,
    manager: &mut TermManager,
) {
    if values.contains_key(&t) {
        return;
    }
    enum Frame {
        Open(TermId),
        Combine(TermId, usize),
    }
    let mut frames: Vec<Frame> = vec![Frame::Open(t)];
    let mut vals: Vec<Option<Vec<TermId>>> = Vec::new();
    while let Some(frame) = frames.pop() {
        match frame {
            Frame::Open(cur) => {
                if let Some(v) = values.get(&cur).cloned() {
                    vals.push(v);
                    continue;
                }
                let Some(kind) = manager.get(cur).map(|d| d.kind.clone()) else {
                    vals.push(None);
                    continue;
                };
                match kind {
                    TermKind::SetEmpty(_) => vals.push(Some(Vec::new())),
                    TermKind::SetSingleton(y) => {
                        // The element's value, resolved (and minted, where
                        // needed) before this pass ran.
                        vals.push(elem_values.get(&y).copied().flatten().map(|v| vec![v]));
                    }
                    TermKind::SetUniv(set_sort) => {
                        vals.push(universe_elements_of(manager, set_sort));
                    }
                    TermKind::Ite(_, _, _) => {
                        // Conditions were decided before this pass (the
                        // committed branch); fold through the operand.
                        // Handled by `combine` below via a passthrough on
                        // the already-chosen branch recorded in `values`
                        // by the caller when the branch was opened.
                        let base = vals.len();
                        frames.push(Frame::Combine(cur, base));
                        frames.push(Frame::Open(ite_branch_of(cur, values, manager)));
                    }
                    TermKind::SetUnion(a, b)
                    | TermKind::SetInter(a, b)
                    | TermKind::SetMinus(a, b) => {
                        let base = vals.len();
                        frames.push(Frame::Combine(cur, base));
                        frames.push(Frame::Open(b));
                        frames.push(Frame::Open(a));
                    }
                    TermKind::SetComplement(inner) => {
                        let base = vals.len();
                        frames.push(Frame::Combine(cur, base));
                        frames.push(Frame::Open(inner));
                    }
                    // Opaque: any peer's value (a compound member of the
                    // same class may have landed one already).
                    _ => {
                        let peer_value = peers
                            .iter()
                            .filter_map(|p| values.get(p).cloned())
                            .find(Option::is_some)
                            .flatten();
                        vals.push(peer_value);
                    }
                }
            }
            Frame::Combine(cur, base) => {
                let parts = vals.split_off(base);
                let combined = combine_lists(cur, parts, manager);
                values.insert(cur, combined.clone());
                vals.push(combined);
            }
        }
    }
    if let Some(v) = vals.pop().flatten()
        && !values.contains_key(&t)
    {
        values.insert(t, Some(v));
    }
}

/// The committed branch of an ite set term, as recorded for it. Returns
/// the branch whose value is already known, else the then-branch.
fn ite_branch_of(
    t: TermId,
    values: &FxHashMap<TermId, Option<Vec<TermId>>>,
    manager: &TermManager,
) -> TermId {
    if let Some(TermKind::Ite(_, a, b)) = manager.get(t).map(|d| &d.kind) {
        if values.get(a).is_some() {
            return *a;
        }
        if values.get(b).is_some() {
            return *b;
        }
        return *a;
    }
    t
}

/// Combine operand lists per the compound's kind.
fn combine_lists(
    term: TermId,
    parts: Vec<Option<Vec<TermId>>>,
    manager: &mut TermManager,
) -> Option<Vec<TermId>> {
    match manager.get(term).map(|d| d.kind.clone()) {
        Some(TermKind::SetUnion(_, _)) => {
            let mut out: Vec<TermId> = Vec::new();
            for part in parts {
                out.extend(part?);
            }
            out.sort_unstable();
            out.dedup();
            Some(out)
        }
        Some(TermKind::SetInter(_, _)) => {
            let mut iter = parts.into_iter();
            let mut acc = iter.next()??;
            for part in iter {
                let other = part?;
                acc.retain(|v| other.contains(v));
            }
            Some(acc)
        }
        Some(TermKind::SetMinus(_, _)) => {
            let mut iter = parts.into_iter();
            let mut acc = iter.next()??;
            for part in iter {
                let sub = part?;
                acc.retain(|v| !sub.contains(v));
            }
            Some(acc)
        }
        Some(TermKind::SetComplement(_)) => {
            // The universe minus the operand, over an enumerable sort.
            let inner = parts.into_iter().next()??;
            let set_sort = manager.get(term)?.sort;
            let universe = universe_elements_of(manager, set_sort)?;
            let mut out: Vec<TermId> = universe
                .into_iter()
                .filter(|v| !inner.contains(v))
                .collect();
            out.sort_unstable();
            Some(out)
        }
        // Passthrough of the taken branch.
        Some(TermKind::Ite(_, _, _)) => parts.into_iter().next().flatten(),
        _ => None,
    }
}

/// Kahn topological order (subclasses first); cycle remainders appended in
/// arrival order (verification catches any inconsistency this leaves).
fn topo_order(nodes: &[TermId], edges: &[(TermId, TermId)]) -> Vec<TermId> {
    let mut indegree: FxHashMap<TermId, usize> = FxHashMap::default();
    for &n in nodes {
        indegree.entry(n).or_insert(0);
    }
    for &(from, to) in edges {
        if indegree.contains_key(&to) {
            *indegree.entry(to).or_insert(0) += 1;
        }
        let _ = from;
    }
    let mut queue: Vec<TermId> = nodes
        .iter()
        .copied()
        .filter(|n| indegree.get(n).is_some_and(|d| *d == 0))
        .collect();
    let mut out: Vec<TermId> = Vec::with_capacity(nodes.len());
    while let Some(n) = queue.pop() {
        out.push(n);
        for &(from, to) in edges {
            if from == n
                && let Some(d) = indegree.get_mut(&to)
            {
                *d -= 1;
                if *d == 0 {
                    queue.push(to);
                }
            }
        }
    }
    for &n in nodes {
        if !out.contains(&n) {
            out.push(n);
        }
    }
    out
}

fn set_element_sort(t: TermId, manager: &TermManager) -> Option<SortId> {
    let sort = manager.get(t)?.sort;
    match manager.sorts.get(sort).map(|s| &s.kind) {
        Some(SortKind::Set(e)) => Some(*e),
        _ => None,
    }
}

/// The components of a *value* term: a tuple constructor's arguments, or
/// the value itself as a one-field tuple (plain-set elements in products).
fn value_components(v: TermId, manager: &mut TermManager) -> Vec<TermId> {
    match manager.get(v).map(|d| d.kind.clone()) {
        Some(TermKind::DtConstructor { args, .. }) if !args.is_empty() => args.to_vec(),
        _ => vec![v],
    }
}

/// The component-reversed tuple of a value.
fn reverse_tuple_value(v: TermId, manager: &mut TermManager) -> TermId {
    let mut parts = value_components(v, manager);
    parts.reverse();
    manager.mk_tuple(&parts)
}

/// The diagonal pair of a value.
fn duplicate_tuple_value(v: TermId, manager: &mut TermManager) -> TermId {
    manager.mk_tuple(&[v, v])
}

/// The full concatenation of two values (the product's pairing).
fn concat_values(u: TermId, v: TermId, manager: &mut TermManager) -> Option<TermId> {
    let mut parts = value_components(u, manager);
    parts.extend(value_components(v, manager));
    Some(manager.mk_tuple(&parts))
}

/// The join glue of two values: `u`'s components except the last, then
/// `v`'s except the first — when the boundary components match. The outer
/// `None` marks a malformed value; the inner `None` a non-matching pair.
fn join_glue_values(u: TermId, v: TermId, manager: &mut TermManager) -> Option<Option<TermId>> {
    let us = value_components(u, manager);
    let vs = value_components(v, manager);
    let (Some(last_u), Some(first_v)) = (us.last().copied(), vs.first().copied()) else {
        return None;
    };
    if last_u != first_v {
        return Some(None);
    }
    let mut parts: Vec<TermId> = us[..us.len().saturating_sub(1)].to_vec();
    parts.extend(vs[1..].to_vec());
    Some(Some(manager.mk_tuple(&parts)))
}

/// Whether a term is one of the reduction's own existential witnesses: a
/// disequality pair witness (`@set_ext_*`) or a join middle
/// (`@set_join_*`). Their values are the solver's to choose; any default
/// they carry can be overridden by a fresh distinct witness.
fn is_our_set_skolem(t: TermId, manager: &TermManager) -> bool {
    match manager.get(t).map(|d| &d.kind) {
        Some(TermKind::Var(n)) => {
            let name = manager.resolve_str(*n);
            name.starts_with("@set_ext_") || name.starts_with("@set_join_")
        }
        _ => false,
    }
}

/// Whether a set term is one of the four relation operators.
fn is_rel_shaped(t: TermId, manager: &TermManager) -> bool {
    matches!(
        manager.get(t).map(|d| &d.kind),
        Some(
            TermKind::SetRelJoin(_, _)
                | TermKind::SetRelProduct(_, _)
                | TermKind::SetRelTranspose(_)
                | TermKind::SetRelIden(_)
        )
    )
}

/// Whether `t` can serve directly as a *value*: a ground constant, or a
/// tuple constructor (whose own components are resolved recursively by
/// the callers' sweeps).
fn is_value_term(t: TermId, manager: &TermManager) -> bool {
    matches!(
        manager.get(t).map(|d| &d.kind),
        Some(
            TermKind::True
                | TermKind::False
                | TermKind::IntConst(_)
                | TermKind::RealConst(_)
                | TermKind::BitVecConst { .. }
                | TermKind::StringLit(_)
                | TermKind::FfConst { .. }
                | TermKind::FpLit { .. }
                | TermKind::FpPlusInfinity { .. }
                | TermKind::FpMinusInfinity { .. }
                | TermKind::FpPlusZero { .. }
                | TermKind::FpMinusZero { .. }
                | TermKind::FpNaN { .. }
                | TermKind::DtConstructor { .. }
                | TermKind::SetEmpty(_)
                | TermKind::SetSingleton(_)
                | TermKind::SetUnion(_, _)
        )
    )
}

/// Whether a term is an opaque set (its membership atoms are free, its
/// value decided by the model): a variable, an application, a select.
fn is_opaque_set(t: TermId, manager: &TermManager) -> bool {
    matches!(
        manager.get(t).map(|d| &d.kind),
        Some(
            TermKind::Var(_)
                | TermKind::Apply { .. }
                | TermKind::Select(_, _)
                | TermKind::DtSelector { .. }
        )
    )
}

/// Structural depth of a set term (operands first bottoms out by sorting
/// on this). Iterative; bounded by the term's own finite size.
fn term_depth(t: TermId, manager: &TermManager) -> usize {
    let mut max_depth = 0usize;
    let mut depths: FxHashMap<TermId, usize> = FxHashMap::default();
    let mut stack = vec![(t, 0usize)];
    while let Some((cur, d)) = stack.pop() {
        max_depth = max_depth.max(d);
        if depths.get(&cur).is_some_and(|seen| *seen >= d) {
            continue;
        }
        depths.insert(cur, d);
        if let Some(kind) = manager.get(cur).map(|dd| dd.kind.clone()) {
            let children: Vec<TermId> = match kind {
                TermKind::SetUnion(a, b) | TermKind::SetInter(a, b) | TermKind::SetMinus(a, b) => {
                    vec![a, b]
                }
                TermKind::SetComplement(a) | TermKind::SetSingleton(a) => vec![a],
                TermKind::Ite(c, a, b) => vec![c, a, b],
                _ => Vec::new(),
            };
            for child in children {
                stack.push((child, d + 1));
            }
        }
    }
    max_depth
}

/// Nesting depth of a sort through `Set` constructors (`Set (Set Int)` is
/// deeper than `Set Int`). Iterative.
fn sort_nesting_depth(sort: SortId, manager: &TermManager) -> u32 {
    let mut depth = 0u32;
    let mut current = sort;
    while let Some(kind) = manager.sorts.get(current).map(|s| s.kind.clone()) {
        match kind {
            SortKind::Set(inner) => {
                depth += 1;
                current = inner;
            }
            _ => break,
        }
    }
    depth
}
