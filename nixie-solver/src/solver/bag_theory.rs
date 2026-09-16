//! The finite-bag (multiset) theory: an eager count reduction.
//!
//! A bag is a finite map from elements to multiplicities, and every bag
//! constraint is equivalent to arithmetic over `bag.count` terms — that is
//! the whole decision idea, and it is why the reduction can stay eager:
//! there is no Venn-region geometry to maintain (as the set theory's
//! cardinality module must), only pointwise integer identities.
//!
//! The reference is CVC5's `src/theory/bags` (`theory_bags.cpp`, the
//! `bag_solver` count propagation), compiled to a ground reduction the way
//! the finite-set theory compiles `theory_sets.cpp`:
//!
//! ```text
//! count(x, ∅)            = 0
//! count(x, (bag y n))    = ite(x = y, n, 0)
//! count(x, a ⊎max b)     = max(count(x,a), count(x,b))
//! count(x, a ⊎ b)        = count(x,a) + count(x,b)
//! count(x, a ⊓ b)        = min(count(x,a), count(x,b))
//! count(x, a \ b)        = max(count(x,a) − count(x,b), 0)
//! count(x, a ⧵ b)        = ite(count(x,b) > 0, 0, count(x,a))
//! count(x, setof b)      = ite(count(x,b) > 0, 1, 0)
//! x ∈ b                  ⇔ count(x, b) ≥ 1
//! a ⊑ b                  ⇔ ∀x. count(x,a) ≤ count(x,b)
//! a = b                  ⇔ ∀x. count(x,a) = count(x,b)
//! |b|                    = Σ_x count(x,b) + slack(b)
//! ```
//!
//! Per (element, bag) pair the reduction mints the count term — an `Int`
//! the arithmetic solver owns — and states the identity as an equation.
//! Membership, subbag and extensional equality follow through those `Int`s.
//! The negated subbag/equality directions need a witness *element* the
//! formula may not name; like the set theory's `@set_ext_*` witnesses, it
//! is skolemized per pair (`@bag_ext_*`) and its counts constrained.
//!
//! Honest degradation, the same contract as the set reduction: anything
//! outside the fragment (an element sort with no mintable witness for the
//! negated directions, an oversized element list) raises `incomplete`, and
//! a `Sat` resting on it degrades to `Unknown` — never a guess.

use crate::prelude::*;
use nixie_core::{SortId, TermId, TermKind, TermManager};

/// The result of reducing a formula's bag constraints.
#[derive(Default)]
pub(crate) struct Reduction {
    /// Formulas to assert alongside the original.
    pub axioms: Vec<TermId>,
    /// Whether a construct outside this reduction was seen, so the caller
    /// must keep the honesty gate raised.
    pub incomplete: bool,
}

/// What the survey found, keyed by nothing yet: the reduction groups by
/// element sort as it walks.
struct Survey {
    /// Every bag-sorted term (variables and compounds alike), with its
    /// element sort.
    bags: Vec<(TermId, SortId)>,
    /// `(element, bag)` pairs the formula counts or tests membership of —
    /// the ground element list grows from these.
    elements: Vec<(TermId, SortId)>,
    /// `bag.count` terms: `(term, element, bag)`.
    counts: Vec<(TermId, TermId, TermId)>,
    /// `bag.member` atoms: `(atom, element, bag)`.
    members: Vec<(TermId, TermId, TermId)>,
    /// `bag.subbag` atoms: `(atom, a, b)`.
    subbags: Vec<(TermId, TermId, TermId)>,
    /// `bag.card` terms: `(term, bag)`.
    cards: Vec<(TermId, TermId)>,
    /// Equalities between bag-sorted terms (the extensionality inputs).
    bag_equalities: Vec<(TermId, TermId, TermId)>,
}

fn survey(roots: &[TermId], manager: &TermManager) -> Survey {
    let mut out = Survey {
        bags: Vec::new(),
        elements: Vec::new(),
        counts: Vec::new(),
        members: Vec::new(),
        subbags: Vec::new(),
        cards: Vec::new(),
        bag_equalities: Vec::new(),
    };
    let mut seen: FxHashSet<TermId> = FxHashSet::default();
    let mut stack: Vec<TermId> = roots.to_vec();
    while let Some(t) = stack.pop() {
        if !seen.insert(t) {
            continue;
        }
        let Some(data) = manager.get(t) else { continue };
        let bag_es = |sort: SortId| -> Option<SortId> {
            manager.sorts.get(sort).and_then(|s| match &s.kind {
                nixie_core::SortKind::Bag(e) => Some(*e),
                _ => None,
            })
        };
        if let Some(es) = bag_es(data.sort)
            && !out.bags.iter().any(|&(b, _)| b == t)
        {
            out.bags.push((t, es));
        }
        match &data.kind {
            TermKind::BagCount(e, b) => {
                out.counts.push((t, *e, *b));
                if let Some(es) = manager.get(*b).map(|d| d.sort).and_then(bag_es) {
                    out.elements.push((*e, es));
                }
            }
            TermKind::BagMember(e, b) => {
                out.members.push((t, *e, *b));
                if let Some(es) = manager.get(*b).map(|d| d.sort).and_then(bag_es) {
                    out.elements.push((*e, es));
                }
            }
            TermKind::BagSubbag(a, b) => out.subbags.push((t, *a, *b)),
            TermKind::BagCard(b) => out.cards.push((t, *b)),
            TermKind::Eq(a, b) => {
                let a_bag = manager.get(*a).map(|d| d.sort).and_then(bag_es);
                let b_bag = manager.get(*b).map(|d| d.sort).and_then(bag_es);
                if let (Some(x), Some(y)) = (a_bag, b_bag)
                    && x == y
                {
                    out.bag_equalities.push((t, *a, *b));
                }
            }
            _ => {}
        }
        stack.extend(nixie_core::ast::traversal::get_children(&data.kind));
    }
    out
}

/// Whether a bag term is **closed**: built entirely from `bag.empty`,
/// `(bag e n)` and the operators over closed operands, with no opaque
/// node (variable, application, select) anywhere. A closed bag's support
/// is exactly the union of its `bag.make` elements — all of which the
/// support walk collected into the known list — so its cardinality is
/// the exact sum of the known counts. An opaque bag may hold elements
/// the formula never names; its cardinality carries a nonnegative slack
/// for exactly those. Without the distinction, a closed compound could
/// satisfy `|b| = Σ + slack` past its true size — a false `sat`
/// (`|(1:3) ⊎ (2:1)| = 5` answered `sat`; CVC5: `unsat`).
fn bag_is_closed(b: TermId, manager: &TermManager) -> bool {
    let mut stack = vec![b];
    let mut seen: FxHashSet<TermId> = FxHashSet::default();
    while let Some(t) = stack.pop() {
        if !seen.insert(t) {
            continue;
        }
        match manager.get(t).map(|d| d.kind.clone()) {
            Some(TermKind::BagEmpty(_)) | Some(TermKind::BagMake(_, _)) => {}
            Some(TermKind::BagUnionMax(a, c))
            | Some(TermKind::BagUnionDisjoint(a, c))
            | Some(TermKind::BagInterMin(a, c))
            | Some(TermKind::BagDifferenceSubtract(a, c))
            | Some(TermKind::BagDifferenceRemove(a, c)) => {
                stack.push(a);
                stack.push(c);
            }
            Some(TermKind::BagSetof(a)) => stack.push(a),
            _ => return false,
        }
    }
    true
}

/// The element sort of a bag-sorted term, when it is one.
fn bag_element_of(t: TermId, manager: &TermManager) -> Option<SortId> {
    manager
        .sorts
        .get(manager.get(t)?.sort)
        .and_then(|s| match &s.kind {
            nixie_core::SortKind::Bag(e) => Some(*e),
            _ => None,
        })
}

/// The count of `e` in `b`, as a term: the existing `bag.count` when the
/// formula already has one (hash-consed), a fresh one otherwise. The
/// arithmetic solver owns the result as an ordinary integer column.
fn count_term(e: TermId, b: TermId, manager: &mut TermManager) -> TermId {
    manager.mk_bag_count(e, b)
}

/// The defining identity for `count(e, b)`, computed structurally.
/// `None` marks a construct outside this fragment (raising the honesty
/// gate) — never a guess.
fn count_definition(
    e: TermId,
    b: TermId,
    zero: TermId,
    manager: &mut TermManager,
) -> Option<TermId> {
    let ca = |x: TermId, manager: &mut TermManager| count_term(e, x, manager);
    match manager.get(b).map(|d| d.kind.clone())? {
        TermKind::BagEmpty(_) => Some(zero),
        TermKind::BagMake(y, n) => {
            let same = manager.mk_eq(e, y);
            Some(manager.mk_ite(same, n, zero))
        }
        TermKind::BagUnionMax(a, c) => {
            let (x, y) = (ca(a, manager), ca(c, manager));
            let ge = manager.mk_ge(x, y);
            Some(manager.mk_ite(ge, x, y))
        }
        TermKind::BagUnionDisjoint(a, c) => {
            let (x, y) = (ca(a, manager), ca(c, manager));
            Some(manager.mk_add([x, y]))
        }
        TermKind::BagInterMin(a, c) => {
            let (x, y) = (ca(a, manager), ca(c, manager));
            let le = manager.mk_le(x, y);
            Some(manager.mk_ite(le, x, y))
        }
        TermKind::BagDifferenceSubtract(a, c) => {
            let (x, y) = (ca(a, manager), ca(c, manager));
            let diff = manager.mk_sub(x, y);
            let pos = manager.mk_gt(x, y);
            Some(manager.mk_ite(pos, diff, zero))
        }
        TermKind::BagDifferenceRemove(a, c) => {
            let (x, y) = (ca(a, manager), ca(c, manager));
            let y_pos = manager.mk_gt(y, zero);
            Some(manager.mk_ite(y_pos, zero, x))
        }
        TermKind::BagSetof(s) => {
            let x = ca(s, manager);
            let one = manager.mk_int(1);
            let pos = manager.mk_gt(x, zero);
            Some(manager.mk_ite(pos, one, zero))
        }
        // An opaque bag (variable, application): its counts are free
        // integers — exactly the interface the arithmetic solver needs.
        TermKind::Var(_) | TermKind::Apply { .. } | TermKind::Select(_, _) => None,
        _ => None,
    }
}

/// Budget on the ground element list per sort: the identities are
/// |elements| × |bags| equations, and the set theory's counting cap
/// (`MAX_COUNT_ELEMENTS`) bounds the same product for the same reason.
const MAX_BAG_ELEMENTS: usize = 24;

/// Reduce the bag constraints of `roots` to arithmetic over `bag.count`.
pub(crate) fn reduce(roots: &[TermId], manager: &mut TermManager) -> Reduction {
    let mut out = Reduction::default();
    let s = survey(roots, manager);
    if s.bags.is_empty() {
        return out;
    }

    // Group the ground elements by sort, deduplicated.
    let mut by_sort: FxHashMap<SortId, Vec<TermId>> = FxHashMap::default();
    for &(e, es) in &s.elements {
        if !by_sort.entry(es).or_default().contains(&e) {
            by_sort.entry(es).or_default().push(e);
        }
    }
    // The **support** of every bag term: an equality or subbag between two
    // compounds mentions no `bag.count` term at all, so the element list
    // built from counts alone is empty for
    // `(bag 1 2) = (bag 1 3)` — and the extensionality axioms then state
    // nothing. Every `BagMake` operand inside every surveyed bag is an
    // element the formula cares about; collect them (explicit stack: the
    // compound DAG is user-shaped).
    {
        let mut seen: FxHashSet<TermId> = FxHashSet::default();
        for &(b, es) in &s.bags {
            let mut stack = vec![b];
            while let Some(t) = stack.pop() {
                if !seen.insert(t) {
                    continue;
                }
                let Some(data) = manager.get(t) else { continue };
                match &data.kind {
                    TermKind::BagMake(y, _) => {
                        if !by_sort.entry(es).or_default().contains(y) {
                            by_sort.entry(es).or_default().push(*y);
                        }
                    }
                    TermKind::BagUnionMax(a, c)
                    | TermKind::BagUnionDisjoint(a, c)
                    | TermKind::BagInterMin(a, c)
                    | TermKind::BagDifferenceSubtract(a, c)
                    | TermKind::BagDifferenceRemove(a, c) => {
                        stack.push(*a);
                        stack.push(*c);
                    }
                    TermKind::BagSetof(a) => {
                        stack.push(*a);
                    }
                    _ => {}
                }
            }
        }
    }
    let zero = manager.mk_int(0);

    // ---- the witnesses join the element list first ----
    // The negated subbag/equality directions constrain a skolem element's
    // counts; those count terms need their identities like any other, so
    // the skolems are pushed here, before the identity loop below.
    for &(_atom, a, b) in &s.subbags {
        let (Some(ea), Some(eb)) = (bag_element_of(a, manager), bag_element_of(b, manager)) else {
            continue;
        };
        if ea != eb {
            continue;
        }
        let k = manager.mk_var(&format!("@bag_ext_{}_{}", a.0, b.0), ea);
        if !by_sort.entry(ea).or_default().contains(&k) {
            by_sort.entry(ea).or_default().push(k);
        }
    }
    for &(_, a, b) in &s.bag_equalities {
        let (Some(ea), Some(eb)) = (bag_element_of(a, manager), bag_element_of(b, manager)) else {
            continue;
        };
        if ea != eb {
            continue;
        }
        let k = manager.mk_var(&format!("@bag_ext_{}_{}", a.0, b.0), ea);
        if !by_sort.entry(ea).or_default().contains(&k) {
            by_sort.entry(ea).or_default().push(k);
        }
    }

    // ---- the count identities ----
    // For every (element, compound-bag) pair: count(e, b) = def. The
    // builder already folds the `BagEmpty`/`BagMake` bases; these arms
    // cover the operators and re-state the bases uniformly (hash-consing
    // keeps duplicates identical).
    for &(b, es) in &s.bags {
        let Some(elems) = by_sort.get(&es) else {
            continue;
        };
        if elems.len() > MAX_BAG_ELEMENTS {
            out.incomplete = true;
            continue;
        }
        for &e in elems {
            let Some(def) = count_definition(e, b, zero, manager) else {
                continue;
            };
            let c = count_term(e, b, manager);
            let eq = manager.mk_eq(c, def);
            out.axioms.push(eq);
        }
    }

    // ---- membership ----
    for &(atom, e, b) in &s.members {
        let c = count_term(e, b, manager);
        let one = manager.mk_int(1);
        let ge = manager.mk_ge(c, one);
        out.axioms.push(manager.mk_eq(atom, ge));
    }

    // ---- subbag, both directions ----
    // Forward: every known element's counts order. Negated: a witness
    // element (skolemized per pair, like `@set_ext_*`) whose counts
    // disagree — the formula may not name it, so it is minted here and
    // its count terms join the identities next pass (the same
    // re-derivation discipline as the set witnesses).
    for &(atom, a, b) in &s.subbags {
        let (Some(ea), Some(eb)) = (bag_element_of(a, manager), bag_element_of(b, manager)) else {
            continue;
        };
        if ea != eb {
            continue;
        }
        let Some(elems) = by_sort.get(&ea) else {
            continue;
        };
        for &e in elems {
            let (ca, cb) = (count_term(e, a, manager), count_term(e, b, manager));
            let le = manager.mk_le(ca, cb);
            out.axioms.push(manager.mk_implies(atom, le));
        }
        let k = manager.mk_var(&format!("@bag_ext_{}_{}", a.0, b.0), ea);
        let (ca, cb) = (count_term(k, a, manager), count_term(k, b, manager));
        let gt = manager.mk_gt(ca, cb);
        let neg = manager.mk_not(atom);
        out.axioms.push(manager.mk_implies(neg, gt));
    }

    // ---- extensional equality ----
    // Both directions over the known elements: equal counts elementwise,
    // and a differing witness when the equality is false.
    for &(atom, a, b) in &s.bag_equalities {
        let (Some(ea), Some(eb)) = (bag_element_of(a, manager), bag_element_of(b, manager)) else {
            continue;
        };
        if ea != eb {
            continue;
        }
        let Some(elems) = by_sort.get(&ea) else {
            continue;
        };
        for &e in elems {
            let (ca, cb) = (count_term(e, a, manager), count_term(e, b, manager));
            let agree = manager.mk_eq(ca, cb);
            out.axioms.push(manager.mk_implies(atom, agree));
        }
        let k = manager.mk_var(&format!("@bag_ext_{}_{}", a.0, b.0), ea);
        let (ca, cb) = (count_term(k, a, manager), count_term(k, b, manager));
        let same = manager.mk_eq(ca, cb);
        let differs = manager.mk_not(same);
        let neg = manager.mk_not(atom);
        out.axioms.push(manager.mk_implies(neg, differs));
    }

    // ---- cardinality ----
    // A **closed** bag's size is the exact sum of the known counts (its
    // support is the makes inside it, all collected); an opaque bag may
    // hold elements the formula never names, and carries a nonnegative
    // slack for exactly those. The list is part of the slack's name for
    // the same cross-pass reason as the set theory's list-keyed slacks.
    for &(card, b) in &s.cards {
        let Some(es) = bag_element_of(b, manager) else {
            continue;
        };
        let Some(elems) = by_sort.get(&es) else {
            continue;
        };
        let counts: Vec<TermId> = elems.iter().map(|&e| count_term(e, b, manager)).collect();
        if bag_is_closed(b, manager) {
            let total = manager.mk_add(counts);
            out.axioms.push(manager.mk_eq(card, total));
            continue;
        }
        let mut name = format!("@bag_card_slack_{}", b.0);
        for e in elems {
            name.push_str(&format!("_{}", e.0));
        }
        let slack = manager.mk_var(&name, manager.sorts.int_sort);
        let mut sum = counts;
        sum.push(slack);
        let total = manager.mk_add(sum);
        out.axioms.push(manager.mk_eq(card, total));
        let ge = manager.mk_ge(slack, zero);
        out.axioms.push(ge);
    }

    if out.axioms.len() > 20_000 {
        out.incomplete = true;
    }

    Reduction {
        axioms: {
            let mut seen: FxHashSet<TermId> = FxHashSet::default();
            out.axioms.retain(|a| seen.insert(*a));
            out.axioms
        },
        incomplete: out.incomplete,
    }
}
