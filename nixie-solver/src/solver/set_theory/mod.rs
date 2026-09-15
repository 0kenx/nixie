//! Finite sets: the defining axioms, generated at assert time.
//!
//! # Where this sits
//!
//! CVC5 solves finite sets *lazily* (`src/theory/sets`): an equality engine
//! over set terms plus membership facts, with `checkDownwardsClosure`,
//! `checkUpwardsClosure` and `checkDisequalities` run to a fixpoint, and
//! cardinality in a module of its own. It also has `set_reduction.cpp`, which
//! reduces some set constructs to definitions up front.
//!
//! This is the reduction, done for the whole quantifier-free fragment. Every
//! membership atom the problem can reach is given its defining clauses when
//! the assertion is encoded, so the SAT layer and EUF decide sets without a
//! mid-search propagator. The reason is not simplicity: a theory solver here
//! holds only `&TermManager` during search and cannot create the membership
//! atoms or disequality witnesses it would need — the same constraint that
//! makes `ArrayTheory` pre-create its extensionality witnesses at encode time.
//!
//! # The axioms
//!
//! For an element `e` and each shape of set, the membership atom is *defined*:
//!
//! ```text
//! e in (as set.empty T)   <=>  false
//! e in (set.singleton y)  <=>  e = y
//! e in (set.union a b)    <=>  e in a  \/  e in b
//! e in (set.inter a b)    <=>  e in a  /\  e in b
//! e in (set.minus a b)    <=>  e in a  /\  ~(e in b)
//! ```
//!
//! and the two relations between whole sets are decided by their members:
//!
//! ```text
//! (set.subset a b)  =>  (e in a => e in b)          for every element e
//! ~(set.subset a b) =>  k in a /\ ~(k in b)         for a fresh witness k
//! (= a b)           =>  (e in a <=> e in b)         for every element e
//! ~(= a b)          =>  (k in a) xor (k in b)       for a fresh witness k
//! ```
//!
//! The witness is what makes **extensionality** decidable: two sets that are
//! not equal must differ *somewhere*, and naming that place is the only way to
//! turn a disequality into something the rest of the solver can use. It is the
//! same move as `ArrayTheory`'s extensionality witness, and as CVC5's
//! `checkDisequalities`.
//!
//! # Cardinality
//!
//! [`cardinality`](self::cardinality) decides the ground cardinality
//! fragment: counting equations over the ground elements with one slack per
//! (set, element-list), inclusion–exclusion over twin terms, the slack
//! lattice, subset↔size rules, finite-universe bounds, complement over
//! finite sorts, and `set.choose`. Its caps (cone size, element-list length)
//! and the constructs it declines raise the honesty gate
//! ([`Solver::set_terms_unconstrained`](super::super::Solver)) so a `Sat`
//! resting on an unreduced cardinality degrades to `Unknown`.

#![allow(missing_docs)]

use crate::prelude::*;
use nixie_core::{SortKind, TermId, TermKind, TermManager};

mod cardinality;

/// How a set term is built.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum Shape {
    Empty,
    Singleton(TermId),
    Union(TermId, TermId),
    Inter(TermId, TermId),
    Minus(TermId, TermId),
    /// `(ite c a b)` at a set sort.
    ///
    /// Structured, and it must be treated as such here rather than left
    /// opaque. The generic mux pass ([`Solver::eliminate_nonbool_ite`]) does
    /// own this sort, but it runs *after* this reduction, so by the time the
    /// conditional equalities exist the survey that would have picked them up
    /// has already happened. Leaving it opaque made `(= (ite c {1} {2}) {})`
    /// answer `Sat` — a wrong `sat`, since neither branch is empty.
    ///
    /// [`Solver::eliminate_nonbool_ite`]: super::super::Solver::eliminate_nonbool_ite
    Ite(TermId, TermId, TermId),
    /// `(set.complement s)`.
    Complement(TermId),
    /// `(rel.join r s)`.
    Join(TermId, TermId),
    /// `(rel.product r s)`.
    Product(TermId, TermId),
    /// `(rel.transpose r)`.
    Transpose(TermId),
    /// `(rel.iden s)` — the operand is a plain set.
    Iden(TermId),
    /// `(as set.universe (Set T))`.
    Univ,
    /// A set-sorted variable or other opaque term: it has no structure, so its
    /// membership atoms are free and constrained only by the relations the
    /// problem states about it.
    ///
    /// Sound only because every *structured* set-sorted term is either matched
    /// above or reaches its structure through EUF congruence: `f(x)`,
    /// `(select a i)` and a datatype selector are all opaque *as terms* but are
    /// merged with whatever they are equal to, and a membership atom over a
    /// merged term is congruent to one over its representative. A bound
    /// variable is the case that is **not** rescued that way, which is why
    /// [`survey`] refuses to walk under a binder.
    Opaque,
}

fn shape_of(set: TermId, manager: &TermManager) -> Shape {
    match manager.get(set).map(|t| &t.kind) {
        Some(TermKind::SetEmpty(_)) => Shape::Empty,
        Some(TermKind::SetSingleton(e)) => Shape::Singleton(*e),
        Some(TermKind::SetUnion(a, b)) => Shape::Union(*a, *b),
        Some(TermKind::SetInter(a, b)) => Shape::Inter(*a, *b),
        Some(TermKind::SetMinus(a, b)) => Shape::Minus(*a, *b),
        Some(TermKind::SetComplement(a)) => Shape::Complement(*a),
        Some(TermKind::SetUniv(_)) => Shape::Univ,
        Some(TermKind::Ite(c, a, b)) => Shape::Ite(*c, *a, *b),
        Some(TermKind::SetRelJoin(a, b)) => Shape::Join(*a, *b),
        Some(TermKind::SetRelProduct(a, b)) => Shape::Product(*a, *b),
        Some(TermKind::SetRelTranspose(a)) => Shape::Transpose(*a),
        Some(TermKind::SetRelIden(a)) => Shape::Iden(*a),
        _ => Shape::Opaque,
    }
}

/// The statically known members a set is confined to, if there are any.
///
/// Cardinality is only exact when the answer is `Some`. The recursion is finer
/// than "every leaf is a literal", because two of the three operators only
/// ever *shrink* their left operand:
///
/// ```text
/// set.empty        known, with no members at all
/// set.singleton x  known: {x}
/// a \cup b         known iff BOTH are: a union can grow past either side
/// a \cap b         known iff EITHER is: the result is inside both
/// a \minus b       known iff `a` is:    the result is inside `a`
/// anything else    unknown: an opaque set variable may hold anything
/// ```
///
/// So `S \cap v` and `S \minus v` have exact cardinalities even when `v` is an
/// unconstrained set variable, which is the common shape in practice and one a
/// coarser rule would decline.
///
/// The returned list may contain duplicates and terms that are only
/// *candidates* — membership still decides which are really in. That is what
/// makes the de-duplication in [`cardinality_axiom`] necessary.
fn support(set: TermId, manager: &mut TermManager, depth: usize) -> Option<Vec<TermId>> {
    // Bounded: the walk follows a term the user wrote.
    const MAX_SUPPORT_DEPTH: usize = 64;
    if depth > MAX_SUPPORT_DEPTH {
        return None;
    }
    match shape_of(set, manager) {
        Shape::Empty => Some(Vec::new()),
        Shape::Singleton(e) => Some(vec![e]),
        Shape::Union(a, b) => {
            let mut xs = support(a, manager, depth + 1)?;
            xs.extend(support(b, manager, depth + 1)?);
            Some(xs)
        }
        Shape::Inter(a, b) => {
            support(a, manager, depth + 1).or_else(|| support(b, manager, depth + 1))
        }
        Shape::Minus(a, _) => support(a, manager, depth + 1),
        // The result *is* one of the branches, so the two supports together
        // confine it — the same argument as a union, and it needs both.
        Shape::Ite(_, a, b) => {
            let mut xs = support(a, manager, depth + 1)?;
            xs.extend(support(b, manager, depth + 1)?);
            Some(xs)
        }
        // A complement's members are everything *but* the operand's — not
        // confined to any finite list.
        Shape::Complement(_) => None,
        // The universe set's members are the whole element sort: confined
        // only when that sort is finite, whose inhabitants are not
        // term-enumerable here. `cardinality` states |U| directly instead.
        Shape::Univ => None,
        // The converse's members are the operand's reversed, so a confined
        // operand confines it — each reversed once, bounded by the same
        // list.
        Shape::Transpose(r) => support(r, manager, depth + 1)
            .map(|xs| xs.iter().map(|&e| reverse_tuple(e, manager)).collect()),
        // The diagonal of a confined set is confined: one pair per member.
        Shape::Iden(x) => support(x, manager, depth + 1)
            .map(|xs| xs.iter().map(|&e| duplicate_tuple(e, manager)).collect()),
        // A product's members are the pairs of the operands': confined
        // when both are, with the pair count the product of the two —
        // bounded, because a support list is already bounded by the caps
        // upstream.
        Shape::Product(a, b) => {
            let xs = support(a, manager, depth + 1)?;
            let ys = support(b, manager, depth + 1)?;
            const MAX_PRODUCT_SUPPORT: usize = 256;
            if xs.len().saturating_mul(ys.len()) > MAX_PRODUCT_SUPPORT {
                return None;
            }
            let mut out = Vec::with_capacity(xs.len() * ys.len());
            for &x in &xs {
                for &y in &ys {
                    out.push(full_concat_tuple(x, y, manager));
                }
            }
            Some(out)
        }
        // A join's members pair through an existentially witnessed middle:
        // not statically confined (which middles connect is what the search
        // decides).
        Shape::Join(_, _) => None,
        Shape::Opaque => None,
    }
}

// ===== tuple helpers (the relation operators' term algebra) =====
//
// Tuples are single-constructor datatypes (`TermManager::tuple_sort`), so
// these are thin structural builders; every one is hash-consed and
// therefore stable across the per-assert re-runs of `reduce`.

/// The number of components of a tuple-sorted term's sort.
fn tuple_arity(t: TermId, manager: &TermManager) -> Option<usize> {
    let sort = manager.get(t)?.sort;
    manager.tuple_field_sorts_of(sort).map(|f| f.len())
}

/// The shared-boundary sorts of a join: `(n₁ - 1, middle, n₂ - 1)` from
/// the two operand tuple arities, when they are relations whose boundary
/// sorts agree.
fn join_arities(
    r1: TermId,
    r2: TermId,
    manager: &TermManager,
) -> Option<(usize, nixie_core::SortId, usize)> {
    let e1 = element_sort(r1, manager)?;
    let e2 = element_sort(r2, manager)?;
    let f1 = manager.tuple_field_sorts_of(e1)?;
    let f2 = manager.tuple_field_sorts_of(e2)?;
    let (n1, n2) = (f1.len(), f2.len());
    if n1 == 0 || n2 == 0 {
        return None;
    }
    let middle = *f1.last()?;
    if *f2.first()? != middle {
        return None;
    }
    Some((n1 - 1, middle, n2 - 1))
}

/// `sel_i(t)`: the i-th component as a selector term. Uniform for any
/// tuple term — constructor or variable — because EUF and the datatype
/// axioms own selector semantics (a selector of a constructor folds at
/// encode time; of a variable it is the accessor the theory decides).
fn select_i(t: TermId, i: usize, manager: &mut TermManager) -> TermId {
    manager.mk_tuple_select(i, t)
}

/// The tuple arity of a set's element sort (non-tuple elements read as 1).
fn tuple_arity_of_set(set: TermId, manager: &TermManager) -> Option<usize> {
    element_sort(set, manager)
        .and_then(|e| manager.tuple_field_sorts_of(e))
        .map(|f| f.len())
}

/// The component-reversed tuple of `t` (`(a, b) -> (b, a)`).
fn reverse_tuple(t: TermId, manager: &mut TermManager) -> TermId {
    let arity = tuple_arity(t, manager).unwrap_or(0);
    if arity == 0 {
        return t;
    }
    let mut parts: Vec<TermId> = (0..arity).map(|i| select_i(t, i, manager)).collect();
    parts.reverse();
    manager.mk_tuple(&parts)
}

/// The diagonal pair `(e, e)`.
fn duplicate_tuple(e: TermId, manager: &mut TermManager) -> TermId {
    manager.mk_tuple(&[e, e])
}

/// The **product** concatenation: all of `u`'s columns then all of `v`'s.
fn full_concat_tuple(u: TermId, v: TermId, manager: &mut TermManager) -> TermId {
    let nu = tuple_arity(u, manager).unwrap_or(1).max(1);
    let nv = tuple_arity(v, manager).unwrap_or(1).max(1);
    let mut parts: Vec<TermId> = (0..nu).map(|i| select_i(u, i, manager)).collect();
    parts.extend((0..nv).map(|i| select_i(v, i, manager)));
    manager.mk_tuple(&parts)
}

/// The **join** concatenation: `u`'s columns except its last, then `v`'s
/// except its first — the shared middle column is dropped (CVC5's
/// `computeMembersForBinOpRel` glue; `(a,b) ⨝ (b,c) = (a,c)`).
fn concat_tuple(u: TermId, v: TermId, manager: &mut TermManager) -> TermId {
    let nu = tuple_arity(u, manager).unwrap_or(1).max(1);
    let nv = tuple_arity(v, manager).unwrap_or(1).max(1);
    let mut parts: Vec<TermId> = (0..nu.saturating_sub(1))
        .map(|i| select_i(u, i, manager))
        .collect();
    parts.extend((1..nv).map(|i| select_i(v, i, manager)));
    manager.mk_tuple(&parts)
}

/// Whether a term is *plausible as an element* for the purposes of
/// membership-congruence traversal.
///
/// The congruence block ties `member(x, s)` to `member(y, s)` across
/// equalities `x = y`. Traversing through **arithmetic composites** —
/// `set.card` terms, the counting sums, the slack variables inside them —
/// used to make each pass's own axioms seed the next pass's element list
/// with those composites (12 → 19 → 59 elements in four asserts), which
/// both quadratically grew the de-duplication guards and eventually tripped
/// the element cap. The composites the *reduction* introduces never appear
/// in a user membership atom, so refusing to traverse them keeps the
/// element list stable across passes at no cost to user inputs: an element
/// term the user actually wrote (`x`, `x + 1`, `f x`) still enters the
/// element list directly from the survey of their membership atoms, and
/// its equalities to other plausible terms still tie.
fn element_plausible(t: TermId, manager: &TermManager) -> bool {
    let Some(data) = manager.get(t) else {
        return false;
    };
    match &data.kind {
        // Encoder-internal variables (`__nixie_*`, `$p*`) are never user
        // elements; their defining equalities (`$p = ite …`) are the ite/
        // purification rewrites, and traversing them only mints membership
        // atoms for proxies — which then grow the element list every pass.
        TermKind::Var(name) => {
            let n = manager.resolve_str(*name);
            !(n.starts_with("__nixie") || n.starts_with("$p"))
        }
        TermKind::IntConst(_)
        | TermKind::RealConst(_)
        | TermKind::BitVecConst { .. }
        | TermKind::FfConst { .. }
        | TermKind::StringLit(_)
        | TermKind::FpLit { .. }
        | TermKind::FpPlusInfinity { .. }
        | TermKind::FpMinusInfinity { .. }
        | TermKind::FpPlusZero { .. }
        | TermKind::FpMinusZero { .. }
        | TermKind::FpNaN { .. }
        | TermKind::Apply { .. }
        | TermKind::DtConstructor { .. }
        | TermKind::DtSelector { .. }
        | TermKind::Select(_, _)
        // Set-valued terms are elements of nested `Set (Set …)` sorts.
        | TermKind::SetEmpty(_)
        | TermKind::SetUniv(_)
        | TermKind::SetSingleton(_)
        | TermKind::SetUnion(_, _)
        | TermKind::SetInter(_, _)
        | TermKind::SetMinus(_, _)
        | TermKind::SetComplement(_)
        | TermKind::SetChoose(_) => true,
        // Arithmetic composites (`set.card`, sums, `ite`, the linear
        // operators), Booleans, and string projections do not participate
        // in congruence *traversal*. A user membership over such a term
        // still counts it — via the survey — as an element.
        _ => false,
    }
}

/// Whether a term is set-sorted.
fn is_set_sorted(t: TermId, manager: &TermManager) -> bool {
    manager
        .get(t)
        .and_then(|d| manager.sorts.get(d.sort))
        .is_some_and(|s| matches!(s.kind, SortKind::Set(_)))
}

/// The element sort of a set-sorted term.
fn element_sort(t: TermId, manager: &TermManager) -> Option<nixie_core::SortId> {
    let d = manager.get(t)?;
    match manager.sorts.get(d.sort).map(|s| &s.kind) {
        Some(SortKind::Set(e)) => Some(*e),
        _ => None,
    }
}

/// Everything a formula's set reasoning needs, gathered in one walk.
#[derive(Default)]
struct Survey {
    /// Every set-sorted term, in discovery order.
    sets: Vec<TermId>,
    seen_sets: FxHashSet<TermId>,
    /// Element terms, grouped by their sort — an `Int` element can never be a
    /// member of a `Set Bool`, so instantiating across sorts would be waste.
    elements: FxHashMap<nixie_core::SortId, Vec<TermId>>,
    seen_elements: FxHashSet<TermId>,
    /// `(= a b)` atoms between set-sorted terms.
    set_equalities: Vec<(TermId, TermId, TermId)>,
    /// `(= a b)` atoms between terms that are *not* sets, which are the
    /// element equalities membership has to be congruent over.
    element_equalities: Vec<(TermId, TermId)>,
    /// `(set.subset a b)` atoms.
    subsets: Vec<(TermId, TermId, TermId)>,
    /// `set.card(s)` terms seen, paired with their argument.
    cardinalities: Vec<(TermId, TermId)>,
    /// `set.choose(s)` terms seen, paired with their argument.
    chooses: Vec<(TermId, TermId)>,
}

impl Survey {
    fn add_set(&mut self, s: TermId) {
        if self.seen_sets.insert(s) {
            self.sets.push(s);
        }
    }

    fn add_element(&mut self, e: TermId, sort: nixie_core::SortId) {
        if self.seen_elements.insert(e) {
            self.elements.entry(sort).or_default().push(e);
        }
    }
}

/// Walk the formulas, collecting set terms, element terms and set relations.
///
/// Explicit stack: an asserted formula is user input and may nest arbitrarily.
///
/// # Walking under a binder
///
/// This descends into quantifier bodies, and a bound variable in this AST is
/// an ordinary named `Var` — so a set-sorted bound name is the *same*
/// hash-consed term as a free one of that name, and any axiom mentioning it
/// is emitted at the top level, where the name reads free.
///
/// That is sound, and the argument is worth writing down because the shape
/// looks like variable capture. Every axiom [`reduce`] emits is a **tautology
/// of the theory of finite sets in all of its variables** — `e \in {y}` is
/// `e = y` for *every* `e` and `y`, `(= a b)` implies agreement on every
/// element for *every* `a` and `b`. Reading a bound name as a free one
/// therefore instantiates a valid universally-quantified lemma at a fresh
/// variable, which is still valid. The unguarded arms (`Empty`, `Singleton`)
/// are over ground constructors, and the guarded arms carry their own
/// hypothesis.
///
/// What it is not is *complete*: a membership atom that only exists after a
/// quantifier is instantiated never gets an axiom of its own, because
/// instantiation happens after this runs. The cost of that is `Unknown`, not a
/// wrong answer — memberships over an opaque set are free atoms the SAT layer
/// owns, and an instantiated copy is the same term.
fn survey(roots: &[TermId], manager: &TermManager) -> Survey {
    let mut out = Survey::default();
    let mut seen: FxHashSet<TermId> = FxHashSet::default();
    let mut stack: Vec<TermId> = roots.to_vec();
    while let Some(t) = stack.pop() {
        if !seen.insert(t) {
            continue;
        }
        let Some(data) = manager.get(t) else { continue };

        if is_set_sorted(t, manager) {
            out.add_set(t);
        }
        match &data.kind {
            TermKind::SetMember(e, s) => {
                if let Some(es) = element_sort(*s, manager) {
                    out.add_element(*e, es);
                }
            }
            TermKind::SetSingleton(e) => {
                if let Some(es) = element_sort(t, manager) {
                    out.add_element(*e, es);
                }
            }
            TermKind::SetChoose(s) => {
                out.chooses.push((t, *s));
                // `set.choose(s)` participates in element counting as well:
                // it *is* an element of `s` whenever `s` is nonempty, so its
                // membership atom has to exist for the cardinality equation
                // to see it.
                if let Some(es) = element_sort(*s, manager) {
                    out.add_element(t, es);
                }
            }
            TermKind::SetSubset(a, b) => out.subsets.push((t, *a, *b)),
            TermKind::SetCard(a) => out.cardinalities.push((t, *a)),
            TermKind::Eq(a, b) if is_set_sorted(*a, manager) => {
                out.set_equalities.push((t, *a, *b));
            }
            TermKind::Eq(a, b) => {
                out.element_equalities.push((*a, *b));
            }
            _ => {}
        }
        stack.extend(nixie_core::ast::traversal::get_children(&data.kind));
    }
    out
}

/// The result of reducing a formula's set constraints.
pub(crate) struct Reduction {
    /// Formulas to assert alongside the original.
    pub axioms: Vec<TermId>,
    /// Whether a construct outside this reduction was seen, so the caller
    /// must keep the honesty gate raised.
    pub incomplete: bool,
}

/// Generate the defining axioms for every set constraint in `roots`.
///
/// **All assertions together, never one at a time.** An element introduced by
/// one assertion has to meet an equality asserted in another: given `a = b`,
/// `x \in a` and `x \notin b` as three separate assertions, surveying each
/// alone produces no axiom relating `x` to the equality, and the solver
/// answers `Sat` to an unsatisfiable problem. That is a wrong `sat`, and it is
/// what this signature exists to prevent.
///
/// The axioms are *valid* — each is a consequence of the theory of finite sets
/// — so asserting them alongside the original formula preserves both
/// satisfiability and unsatisfiability. They are also *sufficient* for the
/// fragment they cover: every membership atom the formula can reach is defined
/// in terms of its children, down to `set.empty`, a singleton, or an opaque
/// set-sorted variable whose members are genuinely free.
pub(crate) fn reduce(roots: &[TermId], manager: &mut TermManager) -> Reduction {
    let mut s = survey(roots, manager);
    let mut axioms = Vec::new();

    if s.sets.is_empty() {
        return Reduction {
            axioms,
            incomplete: !s.cardinalities.is_empty(),
        };
    }

    // Disequality witnesses first, because a witness is itself an element and
    // must take part in every membership definition below.
    let mut witnesses: Vec<(TermId, TermId, TermId, TermId)> = Vec::new();
    let mut elements = s.elements.clone();
    // The witness is named after **the pair it witnesses**, not by a counter.
    //
    // `reduce` runs once per `assert`, over the whole assertion stack, and a
    // counter restarts each time — so the same name, and therefore (names
    // being hash-consed) the same SMT variable, was handed to a *different*
    // pair on a later call. The axioms from the two calls then demanded that
    // one element witness two unrelated disequalities, which is not a
    // consequence of anything and can make a satisfiable problem `unsat`.
    // Keying on the pair makes the witness stable across calls and unique to
    // its pair, which is what the axiom means.
    let pair_witness =
        |manager: &mut TermManager, sort: nixie_core::SortId, a: TermId, b: TermId| -> TermId {
            manager.mk_var(&format!("@set_ext_{}_{}", a.0, b.0), sort)
        };

    // One witness per set relation. `(= a b)` and `(set.subset a b)` both need
    // a place where the two sets can differ.
    //
    // **Every pair of same-sorted set terms is a relation here, not only the
    // ones the formula writes down.** There is no set theory *solver* — the
    // classification `TermTheory::Set` has no consumer — so `set.member` is
    // not a congruence-closed symbol, and two membership atoms over sets the
    // solver merges *at solve time* are unrelated SAT variables. Every
    // equality this reduction does not see is therefore invisible:
    //
    // ```smt2
    // (assert (set.member 5 (select (store a 1 (as set.empty (Set Int))) 1)))
    // ```
    //
    // answered `sat`. The array theory merges the select with the empty set,
    // but nothing connects `(set.member 5 <select>)` to `(set.member 5
    // set.empty)`, whose axiom says it is false. The same happens between two
    // set *variables* the solver equates through `f(x)`/`f(y)` with `x = y`.
    //
    // Relating such a pair restores what congruence would have given: the
    // equality atom is decided by EUF whatever derived it, and the axioms
    // below then force the memberships to agree.
    //
    // Only pairs with an **opaque** side. Two structurally determined sets —
    // `set.empty`, a singleton, a union, an `ite` over those — have every
    // membership atom defined by their children, so a derived equality between
    // them says nothing their definitions do not already; being hash-consed,
    // the solver can only merge two of them through an equality that *is* in
    // the formula, and that one is surveyed. An opaque term is the one whose
    // value another theory decides: a variable, a `select`, an uninterpreted
    // application. That is the whole source of the problem, and restricting to
    // it keeps the quadratic small.
    //
    // The cap exists because the pair count is quadratic in set terms and each
    // pair costs a witness, which is itself an element every set then needs an
    // axiom against — `sets x pairs`, so cubic if pairs were left unbounded.
    // Overflowing it raises the honesty gate, so the price of the bound is
    // `Unknown` rather than a silently weaker encoding. A control run with
    // these pairs switched off entirely was no faster on the corpus, so the
    // bound is insurance rather than a measured hot spot.
    const MAX_PAIRS: usize = 48;
    let mut relations: Vec<(TermId, TermId)> = s
        .set_equalities
        .iter()
        .chain(s.subsets.iter())
        .map(|&(_, a, b)| (a, b))
        .collect();
    // The equality-shaped subset of `relations`: the pairs whose atom,
    // when committed true, makes the two sets *one* set. Cardinality needs
    // these separately from the subsets (an equality forces the card
    // terms equal; a subset only bounds them) — see [`cardinality::reduce`]
    // — and the model synthesizer needs them for its equality classes.
    let mut eq_pairs: Vec<(TermId, TermId)> =
        s.set_equalities.iter().map(|&(_, a, b)| (a, b)).collect();
    // The implicit opaque/constructor pairs, shared verbatim with the
    // model synthesizer ([`survey_for_model`]) so the two never diverge.
    let (implicit, mut pair_budget_exceeded) =
        implicit_pairs(&s, relations.len(), MAX_PAIRS, manager);
    relations.extend(implicit.iter().copied());
    eq_pairs.extend(implicit);
    for &(a, b) in &relations {
        let Some(es) = element_sort(a, manager) else {
            continue;
        };
        if witnesses
            .iter()
            .any(|(wa, wb, _, _)| (*wa == a && *wb == b) || (*wa == b && *wb == a))
        {
            continue;
        }
        let k = pair_witness(manager, es, a, b);
        let ka = manager.mk_set_member(k, a);
        let kb = manager.mk_set_member(k, b);
        witnesses.push((a, b, ka, kb));
        // The witness may already be an element: prior passes' conjoined
        // axioms contain its membership atoms, so the fresh survey lists it
        // again. Pushing duplicates made the element list grow by every
        // witness on every pass, tripping the counting cap on the most
        // ordinary multi-set inputs.
        let list = elements.entry(es).or_default();
        if !list.contains(&k) {
            list.push(k);
        }
    }

    // Cardinality comes *before* the membership definitions below, because
    // building the counting cone introduces new set terms — the `a ∩ b`
    // twins of every `a ∪ b` whose size the problem constrains — and those
    // twins need membership definitions of their own from the loop that
    // follows. See [`cardinality`].
    let pre_card_len = axioms.len();
    let card = cardinality::reduce(&s, &elements, &relations, &eq_pairs, manager, &mut axioms);
    // The counting equations mint de-duplication guards — equality atoms
    // BETWEEN ELEMENTS (`e = earlier`) — that did not exist when this pass's
    // survey ran. The congruence block below reads `s.element_equalities`,
    // so without this extension those guard equalities are unaudited for
    // exactly one pass: SAT may commit `k = 5` while `k ∈ S` and `5 ∉ S`
    // coexist, an arrangement no set family realizes (an unfaithful model,
    // and the membership disagreement it hides is a wrong-`sat` shape).
    // Re-surveying just the new axioms and extending the equality list
    // closes the gap in the same pass that opened it.
    {
        let mut seen: FxHashSet<(TermId, TermId)> = s
            .element_equalities
            .iter()
            .map(|&(a, b)| if a.0 < b.0 { (a, b) } else { (b, a) })
            .collect();
        let mut stack: Vec<TermId> = axioms[pre_card_len..].to_vec();
        while let Some(t) = stack.pop() {
            let Some(data) = manager.get(t) else { continue };
            if let TermKind::Eq(a, b) = &data.kind {
                let (ea, eb) = (*a, *b);
                if element_plausible(ea, manager)
                    && element_plausible(eb, manager)
                    && manager.get(ea).map(|d| d.sort) == manager.get(eb).map(|d| d.sort)
                    && seen.insert(if ea.0 < eb.0 { (ea, eb) } else { (eb, ea) })
                {
                    s.element_equalities.push((ea, eb));
                }
            }
            stack.extend(nixie_core::ast::traversal::get_children(&data.kind));
        }
    }
    // Relation constructs the reduction cannot faithfully relate raise
    // this (a malformed join, or a compose-pair budget overflow below).
    let mut rel_incomplete = false;

    // ---- derived elements: the relation operators' projections ----
    //
    // `transpose`, `product` and `iden` define their memberships through
    // tuples built from *their element list's* selectors — reversed
    // tuples, projections and diagonals that live in the OPERANDS' sorts.
    // Adding them to those sorts' lists before the definition loop runs
    // means a compound operand's own definition covers them in this same
    // pass, not the next.
    {
        let mut derived: Vec<(nixie_core::SortId, TermId)> = Vec::new();
        for &set in &s.sets {
            match shape_of(set, manager) {
                Shape::Transpose(r) => {
                    if let (Some(es_t), Some(es_r)) =
                        (element_sort(set, manager), element_sort(r, manager))
                        && let Some(elems) = elements.get(&es_t).cloned()
                    {
                        for e in elems {
                            derived.push((es_r, reverse_tuple(e, manager)));
                        }
                    }
                }
                Shape::Product(a, b) => {
                    let (Some(es_p), Some(es_a), Some(es_b)) = (
                        element_sort(set, manager),
                        element_sort(a, manager),
                        element_sort(b, manager),
                    ) else {
                        continue;
                    };
                    let na = tuple_arity_of_set(a, manager).unwrap_or(1);
                    let elems = elements.get(&es_p).cloned().unwrap_or_default();
                    for e in elems {
                        let left: Vec<TermId> = (0..na).map(|i| select_i(e, i, manager)).collect();
                        let proj_a = if na == 1 {
                            left.first().copied().unwrap_or(e)
                        } else {
                            manager.mk_tuple(&left)
                        };
                        let arity = tuple_arity(e, manager).unwrap_or(na);
                        let right: Vec<TermId> =
                            (na..arity).map(|i| select_i(e, i, manager)).collect();
                        let proj_b = if right.len() == 1 {
                            right[0]
                        } else {
                            manager.mk_tuple(&right)
                        };
                        derived.push((es_a, proj_a));
                        derived.push((es_b, proj_b));
                    }
                }
                Shape::Iden(x) => {
                    if let (Some(es_i), Some(es_x)) =
                        (element_sort(set, manager), element_sort(x, manager))
                        && let Some(elems) = elements.get(&es_i).cloned()
                    {
                        for e in elems {
                            derived.push((es_x, select_i(e, 0, manager)));
                        }
                    }
                }
                _ => {}
            }
        }
        for (sort, term) in derived {
            if let Some(list) = elements.get_mut(&sort)
                && !list.contains(&term)
            {
                list.push(term);
            }
        }
    }

    // ---- tuple surjectivity ----
    //
    // Every tuple-sorted element equals its selector rebuild
    // (`e = (sel₁ e, …, selₙ e)`): the datatype constructor-surjectivity
    // axiom, which the internally-declared tuple sorts never receive from
    // a `declare-datatype`. Without it, a rebuilt spelling of a witness
    // (built by the model layer, or by anything else that projects and
    // reconstructs) carried independently decided membership atoms, and
    // the model could not value both spellings faithfully — the collision
    // that used to decline relation sorts wholesale.
    {
        let mut surjectivity: Vec<(TermId, TermId)> = Vec::new();
        for (&sort, list) in elements.iter() {
            let fields = manager.tuple_field_sorts_of(sort);
            let Some(fields) = fields else {
                continue;
            };
            for &e in list {
                let parts: Vec<TermId> = (0..fields.len())
                    .map(|i| manager.mk_tuple_select(i, e))
                    .collect();
                let rebuild = manager.mk_tuple(&parts);
                surjectivity.push((e, rebuild));
            }
        }
        for (e, rebuild) in surjectivity {
            axioms.push(manager.mk_eq(e, rebuild));
        }
    }

    let mut definition_sets: Vec<TermId> = s.sets.clone();
    definition_sets.extend(card.extra_sets.iter().copied());

    // Define every membership atom, for every element of the matching sort.
    for &set in &definition_sets {
        let Some(es) = element_sort(set, manager) else {
            continue;
        };
        let Some(elems) = elements.get(&es).cloned() else {
            continue;
        };
        let shape = shape_of(set, manager);
        for e in elems {
            let atom = manager.mk_set_member(e, set);
            match shape {
                // Nothing is in the empty set.
                Shape::Empty => {
                    let neg = manager.mk_not(atom);
                    axioms.push(neg);
                }
                Shape::Singleton(y) => {
                    let same = manager.mk_eq(e, y);
                    axioms.push(manager.mk_eq(atom, same));
                }
                Shape::Union(a, b) => {
                    let ia = manager.mk_set_member(e, a);
                    let ib = manager.mk_set_member(e, b);
                    let either = manager.mk_or([ia, ib]);
                    axioms.push(manager.mk_eq(atom, either));
                }
                Shape::Inter(a, b) => {
                    let ia = manager.mk_set_member(e, a);
                    let ib = manager.mk_set_member(e, b);
                    let both = manager.mk_and([ia, ib]);
                    axioms.push(manager.mk_eq(atom, both));
                }
                Shape::Minus(a, b) => {
                    let ia = manager.mk_set_member(e, a);
                    let ib = manager.mk_set_member(e, b);
                    let not_b = manager.mk_not(ib);
                    let both = manager.mk_and([ia, not_b]);
                    axioms.push(manager.mk_eq(atom, both));
                }
                // `e \in (ite c a b)` is `ite c (e \in a) (e \in b)`: the
                // condition is a Bool the SAT layer already owns, so this
                // needs no case split of its own.
                Shape::Ite(c, a, b) => {
                    let ia = manager.mk_set_member(e, a);
                    let ib = manager.mk_set_member(e, b);
                    let picked = manager.mk_ite(c, ia, ib);
                    axioms.push(manager.mk_eq(atom, picked));
                }
                // `e \in ~s` is exactly `e \notin s`: complement is
                // pointwise, which is what makes its membership fragment
                // decidable without any universe reasoning.
                Shape::Complement(inner) => {
                    let ii = manager.mk_set_member(e, inner);
                    let not_inner = manager.mk_not(ii);
                    axioms.push(manager.mk_eq(atom, not_inner));
                }
                // Every element of the element sort is in the universe set.
                // (The builder already folds `x \in U` to `true`; this arm
                // is the belt to that braces for elements introduced after
                // the term was built.)
                Shape::Univ => {
                    axioms.push(atom);
                }
                // ===== relations (CVC5 `theory_sets_rels` rules, eager) =====
                //
                // `e \in transpose(r)  <=>  rev(e) \in r`: the converse's
                // members are the operand's, reversed. `rev(e)` is built
                // from selectors, so it works for any tuple term.
                Shape::Transpose(r) => {
                    let rev = reverse_tuple(e, manager);
                    let in_r = manager.mk_set_member(rev, r);
                    axioms.push(manager.mk_eq(atom, in_r));
                }
                // `(t, u) \in a × b  <=>  t \in a ∧ u \in b`: the pair's
                // projections. A non-tuple operand reads as a one-field
                // tuple, so plain sets pair too.
                Shape::Product(a, b) => {
                    let na = tuple_arity_of_set(a, manager)
                        .or_else(|| element_sort(a, manager).map(|_| 1))
                        .unwrap_or(1);
                    let nb = tuple_arity_of_set(b, manager)
                        .or_else(|| element_sort(b, manager).map(|_| 1))
                        .unwrap_or(1);
                    let total = na + nb;
                    let left: Vec<TermId> = (0..na).map(|i| select_i(e, i, manager)).collect();
                    let right: Vec<TermId> = (na..total).map(|i| select_i(e, i, manager)).collect();
                    let proj_a = if na == 1 {
                        left[0]
                    } else {
                        manager.mk_tuple(&left)
                    };
                    let proj_b = if nb == 1 {
                        right[0]
                    } else {
                        manager.mk_tuple(&right)
                    };
                    let ia = manager.mk_set_member(proj_a, a);
                    let ib = manager.mk_set_member(proj_b, b);
                    let both = manager.mk_and([ia, ib]);
                    axioms.push(manager.mk_eq(atom, both));
                }
                // `(a, b) \in iden(s)  <=>  a \in s ∧ a = b`: the diagonal.
                Shape::Iden(x) => {
                    let f0 = select_i(e, 0, manager);
                    let f1 = select_i(e, 1, manager);
                    let same = manager.mk_eq(f0, f1);
                    let in_s = manager.mk_set_member(f0, x);
                    let both = manager.mk_and([same, in_s]);
                    axioms.push(manager.mk_eq(atom, both));
                }
                // `e \in r ⨝ s  =>  ∃x. split₁ \in r ∧ split₂ \in s`, with
                // the witness skolemized per (element, join) exactly like
                // the disequality witnesses. The converse is the compose
                // rule below, over ground pairs.
                Shape::Join(r1, r2) => {
                    let Some((n1, middle_sort, _n2)) = join_arities(r1, r2, manager) else {
                        // Malformed (the parser checks this; a
                        // builder-made term may still slip through) —
                        // decline honestly.
                        rel_incomplete = true;
                        continue;
                    };
                    // The result tuple's columns are `e[0..n1-1] ++ (the
                    // middle) ++ e[n1-1..]`: the forward split recovers an
                    // `r1` member (e's front plus the witness) and an `r2`
                    // member (the witness plus e's back).
                    let total = tuple_arity(e, manager).unwrap_or(n1.max(1));
                    let k = manager.mk_var(&format!("@set_join_{}_{}", set.0, e.0), middle_sort);
                    let mut left: Vec<TermId> = (0..n1.saturating_sub(1))
                        .map(|i| select_i(e, i, manager))
                        .collect();
                    left.push(k);
                    let mut r2_parts = vec![k];
                    r2_parts.extend((n1.saturating_sub(1)..total).map(|i| select_i(e, i, manager)));
                    let u = manager.mk_tuple(&left);
                    let v = manager.mk_tuple(&r2_parts);
                    let iu = manager.mk_set_member(u, r1);
                    let iv = manager.mk_set_member(v, r2);
                    let both = manager.mk_and([iu, iv]);
                    axioms.push(manager.mk_implies(atom, both));
                    // The witness and its splits are elements: the next
                    // pass's survey sees their atoms and the counting
                    // equations account for them.
                    for derived in [u, v] {
                        if let Some(ds) = element_sort(derived, manager)
                            && let Some(list) = elements.get_mut(&ds)
                            && !list.contains(&derived)
                        {
                            list.push(derived);
                        }
                    }
                    if let Some(list) = elements.get_mut(&middle_sort)
                        && !list.contains(&k)
                    {
                        list.push(k);
                    }
                }
                // An opaque set's members are free *of a definition*. They
                // are not free of each other; see the congruence axioms
                // below.
                Shape::Opaque => {}
            }
        }
    }

    // **Membership is a function of the element**, so two elements the solver
    // makes equal are in exactly the same sets.
    //
    // A theory solver gets this from congruence closure and never states it. A
    // ground reduction has to, and not stating it is a wrong `sat`: with
    // `Nodes` an opaque set, `x \in Nodes`, `y = x` and `~(y \in Nodes)` were
    // three independent Booleans and all three could be satisfied at once. The
    // shape that found it is the most ordinary one there is —
    //
    //     Init == x \in Nodes     Next == UNCHANGED x     Inv == x \in Nodes
    //
    // — which has no counterexample at all and was reported as violated at
    // step 1, because `x@1 = x@0` said nothing about their membership.
    //
    // Stated over the equalities the formula **contains**, not over every pair
    // of elements. Every pair is what congruence means, and it is also what
    // made a two-line satisfiable problem take fifty seconds and come back
    // `Unknown`: a candidate list is mostly literals, and the axiom for two
    // distinct literals has a false antecedent and no content. Chains still
    // close, because `x = y` and `y = z` each get their axiom and the two
    // compose.
    //
    // Stated for every set of the matching sort, not only the opaque ones: for
    // a structured set the property follows from its definition, but only
    // because the *base* atoms it is defined from are congruent, and those
    // bottom out in opaque sets.
    // Congruence is only ever stated at an **opaque** set (see below), so a
    // formula with none needs none of this — not the adjacency map, not the
    // closure, not the axioms. That is most of them: a TLA+ specification's
    // sets are overwhelmingly literals, ranges and unions of those, whose
    // membership is *defined* above. Checking first is what keeps the cost on
    // the specifications that actually have an opaque set in them.
    // ---- the join compose rule (CVC5's `computeMembersForBinOpRel`) ----
    //
    // `u \in r1 ∧ v \in r2 ∧ last(u) = first(v)  =>  concat(u, v) \in J`:
    // the backward half of the join's membership definition, over ground
    // pairs. The equality guard makes it conditional, so it is stated for
    // every pair rather than only the matching ones; the pair count is
    // quadratic in the element lists, so it is capped and an overflow
    // raises the honesty gate.
    const MAX_JOIN_PAIRS: usize = 512;
    let mut join_pairs = 0usize;
    for &set in &s.sets {
        let Shape::Join(r1, r2) = shape_of(set, manager) else {
            continue;
        };
        let Some((n1, _middle, _n2)) = join_arities(r1, r2, manager) else {
            rel_incomplete = true;
            continue;
        };
        let (Some(es_j), Some(es1), Some(es2)) = (
            element_sort(set, manager),
            element_sort(r1, manager),
            element_sort(r2, manager),
        ) else {
            continue;
        };
        let empty: Vec<TermId> = Vec::new();
        let us = elements.get(&es1).unwrap_or(&empty).clone();
        let vs = elements.get(&es2).unwrap_or(&empty).clone();
        for &u in &us {
            let arity_u = tuple_arity(u, manager).unwrap_or(n1 + 1);
            let Some(last_u) = (0..arity_u).map(|i| select_i(u, i, manager)).last() else {
                continue;
            };
            for &v in &vs {
                let arity_v = tuple_arity(v, manager).unwrap_or(1);
                let Some(first_v) = (arity_v > 0).then(|| select_i(v, 0, manager)) else {
                    continue;
                };
                if join_pairs >= MAX_JOIN_PAIRS {
                    rel_incomplete = true;
                    break;
                }
                join_pairs += 1;
                let glued = concat_tuple(u, v, manager);
                let _ = es_j;
                let in_u = manager.mk_set_member(u, r1);
                let in_v = manager.mk_set_member(v, r2);
                let boundary = manager.mk_eq(last_u, first_v);
                let prem = manager.mk_and([in_u, in_v, boundary]);
                let conc = manager.mk_set_member(glued, set);
                axioms.push(manager.mk_implies(prem, conc));
                // The glued tuple is an element of the join's sort: the
                // next pass's survey (and this pass's counting, via the
                // elements map) account for it.
                if let Some(list) = elements.get_mut(&es_j)
                    && !list.contains(&glued)
                {
                    list.push(glued);
                }
            }
        }
    }

    let any_opaque = s
        .sets
        .iter()
        .any(|&set| shape_of(set, manager) == Shape::Opaque);
    if any_opaque {
        // Which terms congruence is worth stating for: those **connected by
        // equalities to something the formula actually tests for membership**.
        //
        // Not every equality, and not only the ones whose sides are already
        // elements. Not every equality, because the axiom's own `set.member` makes
        // its term an element, the definition loop above instantiates every set
        // against every element, and `reduce` runs once per `assert` — stating it
        // for `pc' = pc + 1` and its like turned a four-minute corpus into a
        // quarter of an hour by that route. Not only the already-elements,
        // because an unrolling connects `x@0` to `x@2` *through* `x@1`, which
        // appears in no membership atom of its own and would break the chain.
        //
        // So: seed with the elements, then close over the equalities.
        let mut connected: FxHashMap<nixie_core::SortId, FxHashSet<TermId>> = elements
            .iter()
            .map(|(k, v)| (*k, v.iter().copied().collect()))
            .collect();
        {
            // A single walk out from the seeds, over an adjacency map built once.
            //
            // The obvious way to close this is to sweep the equalities until
            // nothing changes, and that is **quadratic** in their number — which
            // in a bounded unrolling is every `x' = e` and every `s = "foo"` in
            // every step, thousands of them, re-swept once per `assert`. That, and
            // not the axioms it produces, is what made the corpus take twenty
            // minutes.
            let mut adjacent: FxHashMap<TermId, Vec<TermId>> = FxHashMap::default();
            for &(x, y) in &s.element_equalities {
                // Only plausible-element edges are traversable; see
                // [`element_plausible`]. Without this filter the reduction's
                // own counting equations (`|s| = Σ + slack`) enter as element
                // equalities and each pass seeds the next with fresh
                // composites.
                if !element_plausible(x, manager) || !element_plausible(y, manager) {
                    continue;
                }
                adjacent.entry(x).or_default().push(y);
                adjacent.entry(y).or_default().push(x);
            }
            for (es, group) in &mut connected {
                let mut frontier: Vec<TermId> = group.iter().copied().collect();
                while let Some(t) = frontier.pop() {
                    let Some(nexts) = adjacent.get(&t) else {
                        continue;
                    };
                    for &n in nexts {
                        if manager.get(n).map(|d| d.sort) != Some(*es) {
                            continue;
                        }
                        if group.insert(n) {
                            frontier.push(n);
                        }
                    }
                }
            }
        }
        for &(x, y) in &s.element_equalities {
            if !element_plausible(x, manager) || !element_plausible(y, manager) {
                continue;
            }
            let Some(es) = manager.get(x).map(|d| d.sort) else {
                continue;
            };
            let Some(group) = connected.get(&es) else {
                continue;
            };
            if !group.contains(&x) || !group.contains(&y) {
                continue;
            }
            for &set in &s.sets {
                if element_sort(set, manager) != Some(es) {
                    continue;
                }
                // **Opaque sets only.** A structured set's membership is *defined*
                // from its bases by the loop above — `e \in (a \cup b)` is
                // `e \in a \/ e \in b` — so congruence at the bases gives it at
                // the union, and every chain of definitions bottoms out in opaque
                // sets. Stating it at every set as well is redundant, and it is
                // not cheap redundancy: it took the corpus from four minutes to
                // twenty.
                if shape_of(set, manager) != Shape::Opaque {
                    continue;
                }
                let same = manager.mk_eq(x, y);
                let mx = manager.mk_set_member(x, set);
                let my = manager.mk_set_member(y, set);
                let agree = manager.mk_eq(mx, my);
                axioms.push(manager.mk_implies(same, agree));
            }
        }
    }

    // `(= a b)` for sets is extensional equality.
    //
    // Iterated over the **witnessed pairs**, not over the equality atoms the
    // formula happens to contain: an equality the solver derives rather than
    // reads is exactly the case that was answering `sat`. The atom is built
    // here where the formula does not have one; it is hash-consed, so a
    // surveyed `(= a b)` is the same term and nothing is duplicated.
    for &(a, b, ka, kb) in &witnesses {
        let Some(es) = element_sort(a, manager) else {
            continue;
        };
        let Some(elems) = elements.get(&es).cloned() else {
            continue;
        };
        let atom = manager.mk_eq(a, b);
        for e in elems {
            let ia = manager.mk_set_member(e, a);
            let ib = manager.mk_set_member(e, b);
            let agree = manager.mk_eq(ia, ib);
            axioms.push(manager.mk_implies(atom, agree));
        }
        // ...and if they differ, they differ *somewhere*.
        let differs = manager.mk_xor(ka, kb);
        let neg = manager.mk_not(atom);
        axioms.push(manager.mk_implies(neg, differs));
    }

    // `(set.subset a b)`.
    for &(atom, a, b) in &s.subsets {
        let Some(es) = element_sort(a, manager) else {
            continue;
        };
        let Some(elems) = elements.get(&es).cloned() else {
            continue;
        };
        for e in elems {
            let ia = manager.mk_set_member(e, a);
            let ib = manager.mk_set_member(e, b);
            let implies = manager.mk_implies(ia, ib);
            axioms.push(manager.mk_implies(atom, implies));
        }
        if let Some(&(_, _, ka, kb)) = witnesses.iter().find(|(wa, wb, _, _)| *wa == a && *wb == b)
        {
            let not_kb = manager.mk_not(kb);
            let escapes = manager.mk_and([ka, not_kb]);
            let neg = manager.mk_not(atom);
            axioms.push(manager.mk_implies(neg, escapes));
        }
    }

    // **`choose` is a function symbol: equal arguments give equal results.**
    // Z3 and CVC5 get this from the equality engine (`choose` is an ordinary
    // congruence-tracked application); here a set-sorted equality atom is a
    // SAT variable the reduction itself relates, so the congruence has to be
    // stated over the pairs of choose terms the survey found. Without it,
    // `S = T ∧ |S| ≥ 1 ∧ choose(S) ≠ choose(T)` answered `Sat` — the member
    // axioms let both chooses sit in the (equal) sets as two distinct
    // elements, and nothing forced the two applications to agree.
    //
    // The antecedent is the equality atom of the two *arguments*; for an
    // opaque pair that is exactly the atom the pair machinery above relates
    // (and EUF commits when a derivation exists), and for an asserted
    // equality it is the assertion itself, hash-consed to the same term.
    const MAX_CHOOSE_PAIRS: usize = 128;
    let mut choose_pairs = 0usize;
    for (i, &(ua, ta)) in s.chooses.iter().enumerate() {
        for &(ub, tb) in s.chooses.iter().skip(i + 1) {
            if ta == tb || element_sort(ta, manager) != element_sort(tb, manager) {
                continue;
            }
            if choose_pairs >= MAX_CHOOSE_PAIRS {
                pair_budget_exceeded = true;
                break;
            }
            choose_pairs += 1;
            let same = manager.mk_eq(ta, tb);
            let agree = manager.mk_eq(ua, ub);
            axioms.push(manager.mk_implies(same, agree));
        }
    }
    // `choose(ite c a b) = ite c (choose a) (choose b)`: with `c` the ite
    // *is* `a`, so the two chooses must agree — but the equality atom the
    // pair rule above conditions on (`ite c a b = a`) is never asserted by
    // anyone, so without this the valid identity went unstated and
    // `c ∧ choose(ite c A B) ≠ choose(A)` answered `Sat`. The cardinality
    // analogue (`|ite c a b| = ite c |a| |b|`) is already exact in
    // [`cardinality`]; this is the same shape for the element the ite
    // yields. Minting `choose a`/`choose b` is sound — the SET_CHOOSE axiom
    // the next survey emits for a minted term is valid for every set — and
    // hash-consing keeps it stable across the per-assert re-runs.
    for &(u, t) in &s.chooses {
        if let Shape::Ite(c, a, b) = shape_of(t, manager) {
            let ca = manager.mk_set_choose(a);
            let cb = manager.mk_set_choose(b);
            let picked = manager.mk_ite(c, ca, cb);
            axioms.push(manager.mk_eq(u, picked));
        }
    }

    // `set.card`, exact where the members are confined to a known list and
    // *declined* otherwise: an under-constrained cardinality is a free
    // integer, and a model that picks one arbitrarily is not a model.
    let incomplete = pair_budget_exceeded || rel_incomplete || card.incomplete;

    Reduction { axioms, incomplete }
}

/// The implicit opaque/constructor pairs: every pair of same-sorted set
/// terms with an opaque side that the formula never equates explicitly.
///
/// Factored out of [`reduce`] so the model synthesizer
/// ([`survey_for_model`]) relates *exactly* the same pairs — the equality
/// classes the synthesizer builds must match the equality atoms the
/// reduction created axioms for, or the two would disagree about which
/// sets are one set. `start_len` is the number of relations already
/// collected (asserted equalities and subsets), so the `budget` accounting
/// is identical to the inline loop this replaced.
fn implicit_pairs(
    s: &Survey,
    start_len: usize,
    budget: usize,
    manager: &TermManager,
) -> (Vec<(TermId, TermId)>, bool) {
    let mut pairs: Vec<(TermId, TermId)> = Vec::new();
    let mut overflowed = false;
    let mut by_sort: FxHashMap<nixie_core::SortId, Vec<TermId>> = FxHashMap::default();
    for &set in &s.sets {
        if let Some(es) = element_sort(set, manager) {
            by_sort.entry(es).or_default().push(set);
        }
    }
    // Pair-eligibility: opaque terms pair with opaque terms and with the
    // *constructors* (`∅`, `{x}`, `U`) — never with compound `∪`/`∩`/`\`/
    // `ite` terms. Constructors are stable under hash-consing, so the pair
    // set — and with it the witness element list — is stable across the
    // per-assert re-runs of `reduce`; the compound terms the reduction
    // itself creates (twins, chain unions) would otherwise mint fresh
    // pairs every pass and grow the element list without bound. A compound
    // term's memberships are *defined* from its operands, and the operands
    // are already paired, so the insurance this loop buys for them is
    // negligible — and the one documented case it exists for
    // (`select`-over-`store` merged with `(as set.empty …)`) is a
    // constructor pair, kept.
    let pair_eligible = |t: TermId| {
        matches!(
            shape_of(t, manager),
            Shape::Opaque | Shape::Empty | Shape::Singleton(_) | Shape::Univ
        )
    };
    'pairs: for group in by_sort.values() {
        for (i, a) in group.iter().enumerate() {
            let a_opaque = shape_of(*a, manager) == Shape::Opaque;
            for b in group.iter().skip(i + 1) {
                if !a_opaque && shape_of(*b, manager) != Shape::Opaque {
                    continue;
                }
                if !pair_eligible(*a) || !pair_eligible(*b) {
                    continue;
                }
                if start_len + pairs.len() >= budget {
                    overflowed = true;
                    break 'pairs;
                }
                // Canonical order (by term id): the survey's discovery
                // order changes as assertions accumulate, and an
                // order-flipped pass minted a *second* witness for the
                // same disequality (`@set_ext_a_b` beside `@set_ext_b_a`)
                // with the opposite xor orientation — two skolems the
                // model then had to value, whose defaulted-equal collision
                // declined the whole sort. One unordered pair, one
                // witness, stable across passes.
                let (lo, hi) = if a.0 < b.0 { (*a, *b) } else { (*b, *a) };
                if pairs.contains(&(lo, hi)) || pairs.contains(&(hi, lo)) {
                    continue;
                }
                pairs.push((lo, hi));
            }
        }
    }
    (pairs, overflowed)
}

/// The model-time view of a formula's set constraints, for
/// [`super::set_model`]. Deterministic from the assertion stack (the same
/// survey the reduction ran), so the relations here are exactly the ones
/// the reduction created atoms for.
pub(crate) struct ModelSurvey {
    /// Every set-sorted term, in discovery order.
    pub(crate) sets: Vec<TermId>,
    /// Element terms grouped by sort.
    pub(crate) elements: FxHashMap<nixie_core::SortId, Vec<TermId>>,
    /// Asserted `(set.subset a b)` atoms: `(atom, a, b)`.
    pub(crate) subsets: Vec<(TermId, TermId, TermId)>,
    /// Every pair whose equality atom `mk_eq(a, b)` the reduction relates:
    /// asserted equalities plus the implicit pairs.
    pub(crate) eq_pairs: Vec<(TermId, TermId)>,
    /// `set.choose` terms: `(choose, set)`.
    pub(crate) chooses: Vec<(TermId, TermId)>,
}

/// Survey the assertion stack for model synthesis. The reduction's axioms
/// are conjoined onto the user's assertions, so surveying the stack sees
/// every term the reduction created (twins, witnesses, counting sums) as
/// well as the user's own.
pub(crate) fn survey_for_model(roots: &[TermId], manager: &TermManager) -> ModelSurvey {
    let s = survey(roots, manager);
    const MAX_PAIRS: usize = 48;
    let (implicit, _overflowed) = implicit_pairs(
        &s,
        s.set_equalities.len() + s.subsets.len(),
        MAX_PAIRS,
        manager,
    );
    let mut eq_pairs: Vec<(TermId, TermId)> =
        s.set_equalities.iter().map(|&(_, a, b)| (a, b)).collect();
    eq_pairs.extend(implicit);
    ModelSurvey {
        sets: s.sets.clone(),
        elements: s.elements.clone(),
        subsets: s.subsets.clone(),
        eq_pairs,
        chooses: s.chooses.clone(),
    }
}
