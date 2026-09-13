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
//! # What is not covered
//!
//! `set.card`. Cardinality couples set structure to integer arithmetic — it is
//! why CVC5 gives it a separate Venn-region module — and it is not reduced
//! here. A problem containing `set.card` keeps
//! [`Solver::set_terms_unconstrained`](super::Solver), so its `Sat` degrades
//! to `Unknown` rather than resting on an unconstrained integer.

#![allow(missing_docs)]

use crate::prelude::*;
use nixie_core::{SortKind, TermId, TermKind, TermManager};

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
    /// [`Solver::eliminate_nonbool_ite`]: super::Solver::eliminate_nonbool_ite
    Ite(TermId, TermId, TermId),
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
        Some(TermKind::Ite(c, a, b)) => Shape::Ite(*c, *a, *b),
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
fn support(set: TermId, manager: &TermManager, depth: usize) -> Option<Vec<TermId>> {
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
        Shape::Opaque => None,
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
    /// `(set.subset a b)` atoms.
    subsets: Vec<(TermId, TermId, TermId)>,
    /// `set.card(s)` terms seen, paired with their argument.
    cardinalities: Vec<(TermId, TermId)>,
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
            TermKind::SetSubset(a, b) => out.subsets.push((t, *a, *b)),
            TermKind::SetCard(a) => out.cardinalities.push((t, *a)),
            TermKind::Eq(a, b) if is_set_sorted(*a, manager) => {
                out.set_equalities.push((t, *a, *b));
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
    let s = survey(roots, manager);
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
    let mut pair_budget_exceeded = false;
    let mut relations: Vec<(TermId, TermId)> = s
        .set_equalities
        .iter()
        .chain(s.subsets.iter())
        .map(|&(_, a, b)| (a, b))
        .collect();
    {
        let mut by_sort: FxHashMap<nixie_core::SortId, Vec<TermId>> = FxHashMap::default();
        for &set in &s.sets {
            if let Some(es) = element_sort(set, manager) {
                by_sort.entry(es).or_default().push(set);
            }
        }
        'pairs: for group in by_sort.values() {
            for (i, a) in group.iter().enumerate() {
                let a_opaque = shape_of(*a, manager) == Shape::Opaque;
                for b in group.iter().skip(i + 1) {
                    if !a_opaque && shape_of(*b, manager) != Shape::Opaque {
                        continue;
                    }
                    if relations.len() >= MAX_PAIRS {
                        pair_budget_exceeded = true;
                        break 'pairs;
                    }
                    relations.push((*a, *b));
                }
            }
        }
    }
    for (a, b) in relations {
        let Some(es) = element_sort(a, manager) else {
            continue;
        };
        if witnesses.iter().any(|(wa, wb, _, _)| *wa == a && *wb == b) {
            continue;
        }
        let k = pair_witness(manager, es, a, b);
        let ka = manager.mk_set_member(k, a);
        let kb = manager.mk_set_member(k, b);
        witnesses.push((a, b, ka, kb));
        elements.entry(es).or_default().push(k);
    }

    // Define every membership atom, for every element of the matching sort.
    for &set in &s.sets {
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
                // An opaque set's members are free; only the relations the
                // problem states constrain them.
                Shape::Opaque => {}
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

    // `set.card`, exact where the members are confined to a known list and
    // *declined* otherwise: an under-constrained cardinality is a free
    // integer, and a model that picks one arbitrarily is not a model.
    let mut incomplete = pair_budget_exceeded;
    for &(card_term, set) in &s.cardinalities {
        match support(set, manager, 0) {
            Some(sup) => axioms.push(cardinality_axiom(card_term, set, &sup, manager)),
            None => incomplete = true,
        }
    }

    Reduction { axioms, incomplete }
}

/// `(= (set.card s) n)`, where `n` counts the members of `s` once each.
///
/// The candidates in `support` are **not distinct**: `{x} \cup {y}` has two and
/// they denote one value when `x = y`. A plain sum of indicators would report
/// `2` for every model that equates them. A candidate therefore counts only
/// when no **earlier** candidate is both present and equal to it, which picks
/// exactly one representative per equivalence class.
///
/// This is the same de-duplicating sum the TLA+ arena builds
/// (`nixie-tla-check::arena::cardinality`), and it is the shape that exposed
/// the string-literal false `sat`: the guards are element equalities, so they
/// have to be decided for the count to mean anything.
fn cardinality_axiom(
    card_term: TermId,
    set: TermId,
    support: &[TermId],
    manager: &mut TermManager,
) -> TermId {
    let zero = manager.mk_int(0);
    let one = manager.mk_int(1);
    let mut terms: Vec<TermId> = Vec::with_capacity(support.len());
    for (i, &e) in support.iter().enumerate() {
        let present = manager.mk_set_member(e, set);
        let mut counts = vec![present];
        for &earlier in &support[..i] {
            let earlier_in = manager.mk_set_member(earlier, set);
            let same = manager.mk_eq(e, earlier);
            let dup = manager.mk_and([earlier_in, same]);
            counts.push(manager.mk_not(dup));
        }
        let fresh = manager.mk_and(counts);
        terms.push(manager.mk_ite(fresh, one, zero));
    }
    let total = if terms.is_empty() {
        zero
    } else {
        manager.mk_add(terms)
    };
    manager.mk_eq(card_term, total)
}
