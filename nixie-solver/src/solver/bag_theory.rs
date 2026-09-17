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
            // An ite of closed bags is closed: its support is exactly
            // the branches' makes (all collected — the support walk has
            // the same arm), so its cardinality is the exact sum.
            Some(TermKind::Ite(_, a, c)) => {
                stack.push(a);
                stack.push(c);
            }
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

/// Whether a bag term is **opaque**: a variable, application or select —
/// a bag whose value no structural definition pins, so a *derived*
/// equality onto it (EUF congruence, the array theory) can change its
/// meaning without any surveyed equality atom. Exactly the terms the
/// pair-congruence pass exists for.
fn bag_is_opaque(t: TermId, manager: &TermManager) -> bool {
    matches!(
        manager.get(t).map(|d| &d.kind),
        Some(TermKind::Var(_) | TermKind::Apply { .. } | TermKind::Select(_, _))
    )
}

/// Whether a bag term is a **constructor**: `bag.empty` or `bag.make` —
/// stable under hash-consing, so pairs over them (like the set theory's
/// constructor pairs) cannot mint fresh terms across the per-assert
/// re-runs of the reduction.
fn bag_is_constructor(t: TermId, manager: &TermManager) -> bool {
    matches!(
        manager.get(t).map(|d| &d.kind),
        Some(TermKind::BagEmpty(_) | TermKind::BagMake(_, _))
    )
}

/// The count of `e` in `b`, as a term: the existing `bag.count` when the
/// formula already has one (hash-consed), a fresh one otherwise. The
/// arithmetic solver owns the result as an ordinary integer column.
fn count_term(e: TermId, b: TermId, manager: &mut TermManager) -> TermId {
    manager.mk_bag_count(e, b)
}

/// The defining identity for `count(e, b)`, computed structurally.
/// [`CountDef::Unsupported`] marks a construct outside this fragment —
/// the caller raises the honesty gate rather than letting the counts
/// float free. A free count on a *determined* bag is a false-`sat` hole:
/// before the `Ite` arm landed, a bag-shaped `(ite c a b)` fell through
/// to exactly that (`x ≤ 0 ∧ count(1, ite(x > 0, (1:2), (2:2))) = 1`
/// answered `sat`; CVC5: `unsat`).
enum CountDef {
    /// `count(e, b) = t` for the computed right-hand side.
    Defined(TermId),
    /// An opaque bag (variable, application, select): its counts are
    /// free nonnegative integers — exactly the interface the arithmetic
    /// solver needs for a bag whose value nobody has determined yet.
    Opaque,
    /// A shape this reduction does not know: raise `incomplete`, never
    /// a silent default.
    Unsupported,
}

fn count_definition(e: TermId, b: TermId, zero: TermId, manager: &mut TermManager) -> CountDef {
    let ca = |x: TermId, manager: &mut TermManager| count_term(e, x, manager);
    match manager.get(b).map(|d| d.kind.clone()) {
        Some(TermKind::BagEmpty(_)) => CountDef::Defined(zero),
        Some(TermKind::BagMake(y, n)) => {
            // CVC5 clamps: `ite(e = y ∧ n ≥ 1, n, 0)`.
            let same = manager.mk_eq(e, y);
            let one = manager.mk_int(1);
            let positive = manager.mk_ge(n, one);
            let present = manager.mk_and([same, positive]);
            CountDef::Defined(manager.mk_ite(present, n, zero))
        }
        Some(TermKind::BagUnionMax(a, c)) => {
            let (x, y) = (ca(a, manager), ca(c, manager));
            let ge = manager.mk_ge(x, y);
            CountDef::Defined(manager.mk_ite(ge, x, y))
        }
        Some(TermKind::BagUnionDisjoint(a, c)) => {
            let (x, y) = (ca(a, manager), ca(c, manager));
            CountDef::Defined(manager.mk_add([x, y]))
        }
        Some(TermKind::BagInterMin(a, c)) => {
            let (x, y) = (ca(a, manager), ca(c, manager));
            let le = manager.mk_le(x, y);
            CountDef::Defined(manager.mk_ite(le, x, y))
        }
        Some(TermKind::BagDifferenceSubtract(a, c)) => {
            let (x, y) = (ca(a, manager), ca(c, manager));
            let diff = manager.mk_sub(x, y);
            let pos = manager.mk_gt(x, y);
            CountDef::Defined(manager.mk_ite(pos, diff, zero))
        }
        Some(TermKind::BagDifferenceRemove(a, c)) => {
            let (x, y) = (ca(a, manager), ca(c, manager));
            let y_pos = manager.mk_gt(y, zero);
            CountDef::Defined(manager.mk_ite(y_pos, zero, x))
        }
        Some(TermKind::BagSetof(s)) => {
            let x = ca(s, manager);
            let one = manager.mk_int(1);
            let pos = manager.mk_gt(x, zero);
            CountDef::Defined(manager.mk_ite(pos, one, zero))
        }
        // `count` is a function of the bag *value*, and an ite picks a
        // value: `count(e, ite(c, a, b)) = ite(c, count(e, a), count(e, b))`.
        // Both branches are surveyed bags (the walk collects every
        // bag-sorted subterm), so their counts carry their own identities.
        Some(TermKind::Ite(c, a, b)) => {
            let (x, y) = (ca(a, manager), ca(b, manager));
            CountDef::Defined(manager.mk_ite(c, x, y))
        }
        // An opaque bag (variable, application, select): its counts are
        // free integers — exactly the interface the arithmetic solver
        // needs. (An application's or select's value may be *determined*
        // by other axioms — an asserted equality, the array theory's
        // select-over-store — and then the pair-congruence pass below
        // ties the counts across the equal spellings; an equality nobody
        // relates leaves them free, which is sound: the model may pick
        // any bag with those counts.)
        Some(TermKind::Var(_) | TermKind::Apply { .. } | TermKind::Select(_, _)) => {
            CountDef::Opaque
        }
        // Anything else — a datatype `match` yielding a bag, a future
        // constructor — is honestly refused: `incomplete`, so a `Sat`
        // resting on it degrades to `Unknown` instead of trusting free
        // counts on a bag whose value the term already determines.
        _ => CountDef::Unsupported,
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
                    // An ite bag's support is the union of its branches'
                    // (the condition is `Bool`-sorted and contributes
                    // none) — without this arm the branches' makes were
                    // invisible to the element list and every count
                    // identity over the ite was stated against an
                    // incomplete universe.
                    TermKind::Ite(_, a, c) => {
                        stack.push(*a);
                        stack.push(*c);
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
        let mut opaque = false;
        for &e in elems {
            let c = count_term(e, b, manager);
            match count_definition(e, b, zero, manager) {
                CountDef::Defined(def) => {
                    let eq = manager.mk_eq(c, def);
                    out.axioms.push(eq);
                }
                CountDef::Opaque => {
                    opaque = true;
                    // A multiplicity is nonnegative even for an opaque
                    // bag. Without this axiom a negative count satisfied
                    // `|b| = Σ + slack` and `count(1,b) = -3` answered
                    // `sat` (CVC5: `unsat`; found by differential testing
                    // on the model slice).
                    let ge = manager.mk_ge(c, zero);
                    out.axioms.push(ge);
                }
                CountDef::Unsupported => {
                    // A determined-but-unhandled shape: refuse honestly.
                    // The nonneg axiom stays — multiplicities are always
                    // nonnegative — but a `Sat` resting on this
                    // reduction degrades to `Unknown`.
                    opaque = true;
                    out.incomplete = true;
                    let ge = manager.mk_ge(c, zero);
                    out.axioms.push(ge);
                }
            }
        }
        let _ = opaque;
    }

    // ---- count congruence ----
    // `bag.count` is a function of the element: two elements the formula
    // (or the arithmetic model) makes equal have equal counts. The
    // purified arithmetic encoding gives each `bag.count` term its own
    // integer column with no congruence tie — an UF application would
    // get this from the theory combination layer (verified: the same
    // shape through `declare-fun` refutes fine), the count term does
    // not, and `¬((1:3) ⊑ b)` beside `count(1,b) ≥ 5` answered `sat`
    // (CVC5: `unsat`; fuzz-found). The fix is the set theory's
    // membership-congruence pattern: one implication per element pair per
    // bag. Constant pairs fold their equality to `false` in the builder
    // and cost nothing.
    for &(b, es) in &s.bags {
        let Some(elems) = by_sort.get(&es) else {
            continue;
        };
        for (i, &e1) in elems.iter().enumerate() {
            for &e2 in elems.iter().skip(i + 1) {
                let same = manager.mk_eq(e1, e2);
                let (c1, c2) = (count_term(e1, b, manager), count_term(e2, b, manager));
                let agree = manager.mk_eq(c1, c2);
                out.axioms.push(manager.mk_implies(same, agree));
            }
        }
    }

    // ---- bag-pair count and cardinality congruence ----
    // `bag.count` and `bag.card` are functions of the bag **value**, so
    // equal bags have equal counts and sizes — across *derived*
    // equalities too, not just the `Eq` atoms the formula happens to
    // contain (the extensionality pass below covers only the surveyed
    // atoms). The purified encoding gives each `count`/`card` term its
    // own integer column with no tie, so a congruence the EUF layer
    // derives — `f x = f 0` from `x = 0`, `select(A, i) = v` from the
    // array theory's select-over-store — never reached the columns, and
    //     x = 0 ∧ count(1, f x) = 2 ∧ count(1, f 0) = 5
    // answered `sat` (CVC5: `unsat`; differential probe). The axiom is
    // stated over every surveyed bag pair, the same shape as the
    // element-pair congruence above and the set theory's membership
    // congruence: the antecedent is the (hash-consed) equality atom,
    // which EUF commits when a derivation exists. `bag.card` rides the
    // same pairs — without it, `x = 0 ∧ |f x| = 2 ∧ |f 0| = 5` had the
    // same hole through the slack columns.
    const MAX_BAG_PAIRS: usize = 128;
    let mut bag_pairs = 0usize;
    'outer: for (i, &(a, esa)) in s.bags.iter().enumerate() {
        for &(b, esb) in s.bags.iter().skip(i + 1) {
            if a == b || esa != esb {
                continue;
            }
            // **Opaque-with-opaque or opaque-with-constructor pairs only** —
            // the set theory's `implicit_pairs` eligibility, for the two
            // reasons it documents there. First, the same measured one:
            // a closed compound's counts are structurally defined from
            // congruent bases, so stating congruence at the compound too is
            // redundant — and not cheap (the union-rearrangement regression
            // went from a second to an unfinishable search before this
            // filter). Second, the feedback loop: the axiom mints a
            // bag-sorted equality *atom*, the next `assert`'s re-survey
            // (the reduction is conjoined onto the assertion, so the axiom
            // set is re-walked) sees that atom as a user equality and
            // mints an extensionality witness for the pair. Constructors
            // and opaque terms are stable under hash-consing, so the pair
            // set — and with it the witness growth — is bounded and
            // one-shot; compounds would mint fresh pairs every pass.
            // The hole the pass exists to close needs exactly this
            // eligibility: `f x = f 0` (opaque×opaque) and
            // `select(A, i) = v` with `v` a make or `∅` (opaque×constructor).
            let eligible = |t: TermId| bag_is_opaque(t, manager) || bag_is_constructor(t, manager);
            if !eligible(a)
                || !eligible(b)
                || (!bag_is_opaque(a, manager) && !bag_is_opaque(b, manager))
            {
                continue;
            }
            if bag_pairs >= MAX_BAG_PAIRS {
                out.incomplete = true;
                break 'outer;
            }
            bag_pairs += 1;
            let same = manager.mk_eq(a, b);
            if let Some(elems) = by_sort.get(&esa) {
                for &e in elems {
                    let (ca, cb) = (count_term(e, a, manager), count_term(e, b, manager));
                    let agree = manager.mk_eq(ca, cb);
                    out.axioms.push(manager.mk_implies(same, agree));
                }
            }
            let (xa, xb) = (manager.mk_bag_card(a), manager.mk_bag_card(b));
            let equal_card = manager.mk_eq(xa, xb);
            out.axioms.push(manager.mk_implies(same, equal_card));
        }
    }

    // ---- subbag cardinality propagation ----
    // `a ⊑ b → |a| ≤ |b|` (pointwise counts order, nonnegative sums).
    // Without it a subbag against a *closed* bag constrained only the
    // known elements, the unknown support kept its slack, and
    // `b ⊑ (1:-1) ⧵ (x:0)` — which is `b ⊑ ∅`, forcing `b = ∅` — sat
    // beside `|b| = 2` (fuzz-found false-`sat`; CVC5: `unsat`). The set
    // theory has always had this rule (`atom → |a| ≤ |b|`).
    for &(atom, a, b) in &s.subbags {
        let ca = manager.mk_bag_card(a);
        let cb = manager.mk_bag_card(b);
        let le = manager.mk_le(ca, cb);
        out.axioms.push(manager.mk_implies(atom, le));
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
        // The counting sum runs over the element list, which may hold
        // two spellings of one value — the extensionality witnesses are
        // variables that usually *equal* a real element (their consistency
        // axioms force exactly that). Summing every spelling counts one
        // cell twice, and a bag pinned to a closed value then forced its
        // slack to absorb the duplicate — pinning the witnesses away from
        // the elements the disequality directions needed (a fuzz-found
        // false-`unsat`). The fix is the set theory's de-duplication
        // guard: a list entry contributes its count only when no *earlier*
        // entry of the same value already contributed. Distinct entries
        // all pass; equal-valued ones collapse to their first
        // representative, which is one cell counted once.
        let deduped: Vec<TermId> = elems
            .iter()
            .enumerate()
            .map(|(i, &e)| {
                let mut guard_parts: Vec<TermId> = Vec::new();
                for &earlier in &elems[..i] {
                    let same = manager.mk_eq(e, earlier);
                    let ce = count_term(earlier, b, manager);
                    let earlier_present = manager.mk_gt(ce, zero);
                    let clash = manager.mk_and([same, earlier_present]);
                    guard_parts.push(manager.mk_not(clash));
                }
                let count = count_term(e, b, manager);
                if guard_parts.is_empty() {
                    count
                } else {
                    let no_clash = manager.mk_and(guard_parts);
                    manager.mk_ite(no_clash, count, zero)
                }
            })
            .collect();
        if bag_is_closed(b, manager) {
            let total = manager.mk_add(deduped);
            out.axioms.push(manager.mk_eq(card, total));
            continue;
        }
        let mut name = format!("@bag_card_slack_{}", b.0);
        for e in elems {
            name.push_str(&format!("_{}", e.0));
        }
        let slack = manager.mk_var(&name, manager.sorts.int_sort);
        let mut sum = deduped;
        sum.push(slack);
        let total = manager.mk_add(sum);
        out.axioms.push(manager.mk_eq(card, total));
        let ge = manager.mk_ge(slack, zero);
        out.axioms.push(ge);
    }

    // ---- cardinality propagation ----
    // The per-element equations constrain the *known* counts; an opaque
    // bag's unknown support is the slack. Two aggregate rules let the
    // arithmetic solver see through the slack — both are theorems, and
    // without the first, `b = ∅ ∧ |b| = 1` answered `sat` (a fuzz-found
    // false-`sat`; CVC5: `unsat`; the set theory has always had this
    // rule, `equality ⇒ equal cardinality`, which is why the same shape
    // over sets refuted):
    //
    // * `a = b → |a| = |b|` — equal bags have equal sizes, so a bag
    //   pinned to `∅` (or to any closed compound, whose size folds) has
    //   its slack forced through its own cardinality equation.
    // * the operator bounds: `|a ⊎ b| = |a| + |b|` exactly (the sum of
    //   the sums), and `|x ⊙ y| ≤ |x| + |y|`-style upper bounds for the
    //   other four operators and `|setof b| ≤ |b|` (squashing removes
    //   copies, never adds) — every bound is `Σ min(count,1)-shaped`,
    //   i.e. pointwise ≤ the operand sums.
    if std::env::var_os("NIXIE_NO_BAG_EQCARD").is_none() {
        for &(atom, a, b) in &s.bag_equalities {
            let ca = manager.mk_bag_card(a);
            let cb = manager.mk_bag_card(b);
            let same = manager.mk_eq(ca, cb);
            out.axioms.push(manager.mk_implies(atom, same));
        }
    }
    for &(b, _) in &s.bags {
        if std::env::var_os("NIXIE_NO_BAG_BOUNDS").is_none() {
            let Some(kind) = manager.get(b).map(|d| d.kind.clone()) else {
                continue;
            };
            match kind {
                TermKind::BagUnionDisjoint(x, y) => {
                    let (cx, cy, cb) = (
                        manager.mk_bag_card(x),
                        manager.mk_bag_card(y),
                        manager.mk_bag_card(b),
                    );
                    let total = manager.mk_add([cx, cy]);
                    out.axioms.push(manager.mk_eq(cb, total));
                }
                TermKind::BagUnionMax(x, y) => {
                    let (cx, cy, cb) = (
                        manager.mk_bag_card(x),
                        manager.mk_bag_card(y),
                        manager.mk_bag_card(b),
                    );
                    let sum = manager.mk_add([cx, cy]);
                    out.axioms.push(manager.mk_le(cb, sum));
                }
                TermKind::BagInterMin(x, y) => {
                    let (cx, cy, cb) = (
                        manager.mk_bag_card(x),
                        manager.mk_bag_card(y),
                        manager.mk_bag_card(b),
                    );
                    out.axioms.push(manager.mk_le(cb, cx));
                    out.axioms.push(manager.mk_le(cb, cy));
                }
                TermKind::BagDifferenceSubtract(x, _) | TermKind::BagDifferenceRemove(x, _) => {
                    let (cx, cb) = (manager.mk_bag_card(x), manager.mk_bag_card(b));
                    out.axioms.push(manager.mk_le(cb, cx));
                }
                TermKind::BagSetof(x) => {
                    let (cx, cb) = (manager.mk_bag_card(x), manager.mk_bag_card(b));
                    out.axioms.push(manager.mk_le(cb, cx));
                }
                // Cardinality is a function of the bag value, and an ite
                // picks a value: `|ite(c, a, b)| = ite(c, |a|, |b|)`, exact
                // for opaque operands too. Without it the ite's own slack
                // absorbed whatever the branches' cardinalities forbade —
                // `|A| = 5 ∧ b = ite(c, A, ∅) ∧ c ∧ |b| = 6`-shapes with
                // the counts otherwise pinned — a false-`sat` family the
                // count identities alone do not close (they tie the sums,
                // not the slack, to the branches).
                TermKind::Ite(c, x, y) => {
                    let (cx, cy, cb) = (
                        manager.mk_bag_card(x),
                        manager.mk_bag_card(y),
                        manager.mk_bag_card(b),
                    );
                    let picked = manager.mk_ite(c, cx, cy);
                    out.axioms.push(manager.mk_eq(cb, picked));
                }
                _ => {}
            }
        }
    }

    if out.axioms.len() > 20_000 {
        out.incomplete = true;
    }

    let mut seen: FxHashSet<TermId> = FxHashSet::default();
    out.axioms.retain(|a| seen.insert(*a));
    if std::env::var_os("NIXIE_DEBUG_BAGS").is_some() {
        let printer = nixie_core::smtlib::Printer::new(manager);
        for a in &out.axioms {
            eprintln!("BAGAXIOM {}", printer.print_term(*a));
        }
    }
    Reduction {
        axioms: out.axioms,
        incomplete: out.incomplete,
    }
}
