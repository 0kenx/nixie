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
//! fold(f, t, ∅)          = t
//! fold(f, t, (y:n))      = f(y, f(y, … f(y, t) …))   (n applications)
//! fold(f, t, ite(c,a,b)) = ite(c, fold(f,t,a), fold(f,t,b))
//! ```
//!
//! `bag.fold` (`f : (-> T1 T2 T2)`, element first) unrolls a ground
//! multiset (`∅`, `(bag y n)` with numeral `n`, `⊎`, under ites) into its
//! finite application chain; a multiset with several element spellings
//! needs the exchange law `f(e1, f(e2, a)) = f(e2, f(e1, a))` proved by
//! AC-canonicalization first (CVC5's skolem reduction answers opaque
//! domains through a bounded quantifier this eager reduction cannot
//! compile; a fold it cannot pin stays free — sound for `unsat` — and the
//! model pass certifies or degrades the `sat` side; see `extract_bag_model`).
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
use nixie_core::interner::Spur;
use nixie_core::{SortId, TermId, TermKind, TermManager};

/// A `define-fun` recorded for the bag fun operators (`bag.map`,
/// `bag.filter`, `bag.fold`): the bound parameter variables in declaration
/// order plus the body, so the reduction can inline the body per
/// element/accumulator exactly as the parser substitutes at call sites.
/// The parser's arity checks guarantee `bag.map`/`filter` only ever see a
/// one-parameter def and `bag.fold` a two-parameter one; the appliers
/// nevertheless fall back to an `Apply` on an arity mismatch rather than
/// silently mis-substituting.
#[derive(Clone, Debug)]
pub(crate) struct BagFunDef {
    /// The definition's parameter variables, in declaration order.
    pub params: Vec<TermId>,
    /// The definition's body.
    pub body: TermId,
}

/// The result of reducing a formula's bag constraints.
#[derive(Default)]
pub(crate) struct Reduction {
    /// Formulas to assert alongside the original.
    pub axioms: Vec<TermId>,
    /// Whether a construct outside this reduction was seen, so the caller
    /// must keep the honesty gate raised.
    pub incomplete: bool,
    /// Fold terms this pass could not pin to an unrolled chain, with the
    /// reason. The caller records them: they stay free (sound for `unsat`,
    /// since asserting nothing only weakens the constraints) and the
    /// *model* pass certifies any `sat` resting on them — synthesizing a
    /// domain-declined fold's faithful value from its bag's assembled
    /// cells and degrading on contradiction, while an order-sensitive
    /// fold (no proved exchange law over several element spellings)
    /// degrades unconditionally — exhibiting one enumeration order would
    /// disagree with the reference's fixed order half the time. See
    /// `extract_bag_model`.
    pub declined_folds: Vec<(TermId, FoldDecline)>,
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
    /// `bag.choose` terms: `(choose, bag)`.
    chooses: Vec<(TermId, TermId)>,
    /// `bag.map` terms: `(term, func, ret, domain bag)`.
    maps: Vec<(TermId, Spur, SortId, TermId)>,
    /// `bag.filter` terms: `(term, pred, bag)`.
    filters: Vec<(TermId, Spur, TermId)>,
    /// `bag.fold` terms: `(term, func, init, bag)`.
    folds: Vec<(TermId, Spur, TermId, TermId)>,
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
        chooses: Vec::new(),
        maps: Vec::new(),
        filters: Vec::new(),
        folds: Vec::new(),
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
            TermKind::BagChoose(b) => out.chooses.push((t, *b)),
            TermKind::BagMap { func, ret, bag } => {
                out.maps.push((t, *func, *ret, *bag));
            }
            TermKind::BagFilter { pred, bag } => out.filters.push((t, *pred, *bag)),
            TermKind::BagFold { func, init, bag } => {
                out.folds.push((t, *func, *init, *bag));
            }
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
            // A map of a closed bag is closed: its support is exactly
            // the images of the domain's makes, and every image is in
            // the codomain element list (the image-collection step adds
            // them). A filter's support is a subset of the domain's.
            Some(TermKind::BagMap { bag: a, .. }) | Some(TermKind::BagFilter { bag: a, .. }) => {
                stack.push(a);
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

/// The function application `f(x)` of a `bag.map`/`bag.filter` operand:
/// a `define-fun`'s body **inlined** — matching the parser's call-site
/// substitution, so the reduction's images and the user's `(f x)` spellings
/// are the same terms — folded ground; a `declare-fun` symbol becomes an
/// ordinary `Apply` the EUF layer owns.
fn bag_apply_fun(
    func: Spur,
    x: TermId,
    ret: SortId,
    fun_defs: &FxHashMap<Spur, BagFunDef>,
    manager: &mut TermManager,
) -> TermId {
    if let Some(def) = fun_defs.get(&func)
        && def.params.len() == 1
    {
        let mut subst: FxHashMap<TermId, TermId> = FxHashMap::default();
        subst.insert(def.params[0], x);
        let sub = manager.substitute(def.body, &subst);
        return manager.simplify(sub);
    }
    let name = manager.resolve_str(func).to_string();
    manager.mk_apply(&name, [x], ret)
}

/// The binary application `f(e, acc)` of a `bag.fold` operand — the same
/// inlining discipline as [`bag_apply_fun`], with the element bound to the
/// first parameter and the accumulator to the second (CVC5's argument
/// order). An arity mismatch (impossible through the parser's checks, but
/// never silently mis-substituted) falls back to an `Apply`.
fn bag_apply_fun2(
    func: Spur,
    e: TermId,
    acc: TermId,
    ret: SortId,
    fun_defs: &FxHashMap<Spur, BagFunDef>,
    manager: &mut TermManager,
) -> TermId {
    if let Some(def) = fun_defs.get(&func)
        && def.params.len() == 2
    {
        let mut subst: FxHashMap<TermId, TermId> = FxHashMap::default();
        subst.insert(def.params[0], e);
        subst.insert(def.params[1], acc);
        let sub = manager.substitute(def.body, &subst);
        return manager.simplify(sub);
    }
    let name = manager.resolve_str(func).to_string();
    manager.mk_apply(&name, [e, acc], ret)
}

/// AC-canonical form for the exchange check: flatten nested operands of
/// the associative-commutative families a combining function is likely to
/// build through (`+`, `*`, `and`, `or`) and sort them by `TermId`;
/// everything else stays structural. Flattening and permuting AC operands
/// preserve the value, so **equal canonical forms are a proof of semantic
/// equality** — the check never asserts the canonical form itself, so a
/// missed simplification only declines, never a wrong accept. Iterative
/// post-order with a per-call memo.
fn ac_canonical(
    t: TermId,
    memo: &mut FxHashMap<TermId, TermId>,
    manager: &mut TermManager,
) -> TermId {
    if let Some(&v) = memo.get(&t) {
        return v;
    }
    // Post-order: canonicalize children, then rebuild.
    let mut stack: Vec<TermId> = vec![t];
    while let Some(cur) = stack.pop() {
        if memo.contains_key(&cur) {
            continue;
        }
        let Some(data) = manager.get(cur) else {
            return cur;
        };
        let kind = data.kind.clone();
        let is_ac = matches!(
            kind,
            TermKind::Add(_) | TermKind::Mul(_) | TermKind::And(_) | TermKind::Or(_)
        );
        let children: Vec<TermId> = nixie_core::ast::traversal::get_children(&kind).to_vec();
        if children.is_empty()
            || memo.contains_key(&children[0]) && children.iter().all(|c| memo.contains_key(c))
        {
            // Ready to combine (also covers leaves).
            let rebuilt = if is_ac {
                // Flatten: pull the same-family children's operands in.
                let mut flat: Vec<TermId> = Vec::new();
                let mut all_flat = true;
                for &c in &children {
                    if let Some(cd) = manager.get(c)
                        && core::mem::discriminant(&cd.kind) == core::mem::discriminant(&kind)
                    {
                        match &cd.kind {
                            TermKind::Add(args)
                            | TermKind::Mul(args)
                            | TermKind::And(args)
                            | TermKind::Or(args) => flat.extend(args.iter().copied()),
                            _ => unreachable!("discriminant-checked above"),
                        }
                    } else {
                        all_flat = false;
                        flat.push(memo.get(&c).copied().unwrap_or(c));
                    }
                }
                let _ = all_flat;
                flat.sort_by_key(|&a| a.0);
                match &kind {
                    TermKind::Add(_) => manager.mk_add(flat),
                    TermKind::Mul(_) => manager.mk_mul(flat),
                    TermKind::And(_) => manager.mk_and(flat),
                    TermKind::Or(_) => manager.mk_or(flat),
                    _ => unreachable!("is_ac-checked above"),
                }
            } else {
                // Structural rebuild through the substitution-safe builders
                // is unnecessary here: a non-AC node's identity is its kind
                // and children, so re-interning the same kind canon-children
                // happens via `substitute`-free path — simply return the
                // node when its children are unchanged, else rebuild by
                // substitution (the memo maps child → canon child).
                let changed = children.iter().any(|&c| memo.get(&c) != Some(&c));
                if changed {
                    let subst: FxHashMap<TermId, TermId> = children
                        .iter()
                        .filter_map(|&c| memo.get(&c).map(|&v| (c, v)))
                        .collect();
                    manager.substitute(cur, &subst)
                } else {
                    cur
                }
            };
            memo.insert(cur, rebuilt);
        } else {
            stack.push(cur);
            for &c in children.iter().rev() {
                if !memo.contains_key(&c) {
                    stack.push(c);
                }
            }
        }
    }
    memo.get(&t).copied().unwrap_or(t)
}

/// Whether a fold's combining function provably satisfies the **exchange
/// law** `f(e1, f(e2, a)) = f(e2, f(e1, a))` — the exact property that
/// makes a fold over a multiset independent of the enumeration order
/// (adjacent transpositions generate every permutation, and the law holds
/// for arbitrary `a`, so it applies at every nesting depth). Proved the
/// only sound way available here: both sides built over fresh variables
/// and compared after AC-canonicalization — an equality the canonicalizer
/// proves is a semantic equality (flatten+sort preserve values), so an
/// accepted fold is order-insensitive for *every* instantiation. A
/// `declare-fun` symbol has no body and never passes; the caller then
/// declines unless the multiset has a single element spelling (all orders
/// give the same chain).
fn fold_fun_exchange_law(
    func: Spur,
    elem_sort: SortId,
    acc_sort: SortId,
    fun_defs: &FxHashMap<Spur, BagFunDef>,
    manager: &mut TermManager,
) -> bool {
    let Some(def) = fun_defs.get(&func) else {
        return false;
    };
    if def.params.len() != 2 {
        return false;
    }
    let e1 = manager.mk_var("@fold_xchg_e1", elem_sort);
    let e2 = manager.mk_var("@fold_xchg_e2", elem_sort);
    let a = manager.mk_var("@fold_xchg_a", acc_sort);
    let app = |e: TermId, acc: TermId, manager: &mut TermManager| {
        let mut subst: FxHashMap<TermId, TermId> = FxHashMap::default();
        subst.insert(def.params[0], e);
        subst.insert(def.params[1], acc);
        let sub = manager.substitute(def.body, &subst);
        manager.simplify(sub)
    };
    let lhs = app(e1, app(e2, a, manager), manager);
    let rhs = app(e2, app(e1, a, manager), manager);
    let mut memo: FxHashMap<TermId, TermId> = FxHashMap::default();
    let clhs = ac_canonical(lhs, &mut memo, manager);
    let crhs = ac_canonical(rhs, &mut memo, manager);
    clhs == crhs
}

/// Budget on the unrolled application chain: every copy contributes one
/// `f` application, and a `(bag y n)` with a large numeral is a real
/// computation the eager reduction must not explode into. Beyond the
/// budget the fold is declined (honest `incomplete`), like an oversized
/// element list.
const MAX_FOLD_APPLICATIONS: u64 = 64;

/// The faithful value of a declined fold in a finished model: fold the
/// *bag's assembled value* (the `bag.union_disjoint` of `(bag v n)` cells
/// the model pass installed) exactly as the semantics say — `f(v, ·)`
/// applied `n` times per cell, cells in the assembled order, starting from
/// the initial value (itself resolved through the model first). The chain
/// is built with the same inlining applier as the reduction and folded
/// ground; the result is a **value term** (no variable or application
/// anywhere) or `None` — a chain that did not fold (a `declare-fun`
//  combinator, an unresolved accumulator) cannot certify a model.
pub(crate) fn fold_faithful_value(
    func: Spur,
    init: TermId,
    bag: TermId,
    ret: SortId,
    model: &super::types::Model,
    fun_defs: &FxHashMap<Spur, BagFunDef>,
    manager: &mut TermManager,
) -> Option<TermId> {
    let value = model.get(bag)?;
    // Resolve the initial accumulator to a value first: a free `init`
    // variable's model entry (or the arithmetic word for an Int one).
    let init_value = match manager.get(init).map(|d| &d.kind) {
        Some(TermKind::IntConst(_)) => Some(init),
        _ => model.get(init).filter(|&v| v != init),
    };
    let mut acc = init_value?;
    // Walk the assembled cells: `a ⊎ (bag v n)` right-associatively, the
    // shape the model pass assembles.
    let mut applications: u64 = 0;
    let mut stack: Vec<TermId> = vec![value];
    while let Some(t) = stack.pop() {
        match manager.get(t).map(|d| d.kind.clone()) {
            Some(TermKind::BagEmpty(_)) => {}
            Some(TermKind::BagMake(v, n)) => {
                let Some(TermKind::IntConst(k)) = manager.get(n).map(|d| &d.kind) else {
                    return None;
                };
                let copies = num_traits::ToPrimitive::to_u64(k)?;
                applications = applications.checked_add(copies)?;
                if applications > MAX_FOLD_APPLICATIONS {
                    return None;
                }
                for _ in 0..copies {
                    acc = bag_apply_fun2(func, v, acc, ret, fun_defs, manager);
                }
            }
            Some(TermKind::BagUnionDisjoint(a, c)) => {
                // Right operand folds second, matching the assembled
                // left-to-right cell order.
                stack.push(a);
                stack.push(c);
            }
            _ => return None,
        }
    }
    // A `Var`/`Apply` anywhere in the chain means the value did not fold.
    let mut seen: FxHashSet<TermId> = FxHashSet::default();
    let mut walk: Vec<TermId> = vec![acc];
    while let Some(t) = walk.pop() {
        if !seen.insert(t) {
            continue;
        }
        let data = manager.get(t)?;
        match &data.kind {
            TermKind::Var(_) | TermKind::Apply { .. } => return None,
            TermKind::IntConst(_)
            | TermKind::RealConst(_)
            | TermKind::StringLit(_)
            | TermKind::BitVecConst { .. }
            | TermKind::FfConst { .. }
            | TermKind::FpLit { .. }
            | TermKind::True
            | TermKind::False => {}
            _ => {
                walk.extend(nixie_core::ast::traversal::get_children(&data.kind));
            }
        }
    }
    Some(acc)
}

/// The outcome of trying to define a fold term.
enum FoldDef {
    /// `fold(f, t, b) = chain`, the unrolled application chain.
    Defined(TermId),
    /// A shape this reduction cannot pin. The two reasons matter to the
    /// model pass: an **unrollable** domain (opaque bag, symbolic
    /// multiplicity, budget) still admits a faithful model value folded
    /// from the assembled cells, while an **order-sensitive** fold (a
    /// multi-element multiset under a function whose exchange law could
    /// not be proved) has *no* order-independent value at all — CVC5's
    /// rewriter answers these through one fixed internal order, and
    /// exhibiting any particular order here would disagree with it half
    /// the time. An order-sensitive fold therefore degrades unconditionally.
    Declined(FoldDecline),
}

/// Why a fold could not be unrolled.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub(crate) enum FoldDecline {
    /// The value depends on the enumeration order (no proved exchange
    /// law over a multiset with several element spellings).
    OrderSensitive,
    /// The domain could not be unrolled (opaque node, symbolic or
    /// oversized multiplicity, an operator the multiset walk refuses).
    Unrollable,
}

/// The ground multiset of a bag: `(element spelling, copies)` pairs, in
/// structural left-to-right order. Syntactically equal elements merge by
/// adding copies (a `⊎` of two `(bag x n)` spellings is `x` taken `n+m`
/// times); distinct spellings of one value stay separate entries, which
/// is exactly right for a fold — each *copy* contributes one application,
/// whatever its spelling. Multiplicities must be nonnegative numerals
/// (`(bag y n)` with symbolic `n` cannot be unrolled), and a negative or
/// zero numeral contributes nothing (matching the count identity's
/// `ite(e = y ∧ n ≥ 1, n, 0)`). Iterative: the compound DAG is
/// user-shaped, the same discipline as [`bag_is_closed`].
fn bag_ground_multiset(
    b: TermId,
    out: &mut Vec<(TermId, u64)>,
    budget: &mut u64,
    manager: &TermManager,
) -> bool {
    let mut stack: Vec<TermId> = vec![b];
    while let Some(t) = stack.pop() {
        match manager.get(t).map(|d| d.kind.clone()) {
            Some(TermKind::BagEmpty(_)) => {}
            Some(TermKind::BagMake(y, n)) => {
                let Some(TermKind::IntConst(k)) = manager.get(n).map(|d| &d.kind) else {
                    return false;
                };
                let Some(copies) = num_traits::ToPrimitive::to_u64(k) else {
                    return false;
                };
                if copies == 0 {
                    continue;
                }
                if copies > *budget {
                    return false;
                }
                *budget -= copies;
                match out.iter_mut().find(|(e, _)| *e == y) {
                    Some((_, m)) => *m += copies,
                    None => out.push((y, copies)),
                }
            }
            // Left-to-right order: the right operand is pushed first so
            // the left pops (and unrolls) first.
            Some(TermKind::BagUnionDisjoint(a, c)) => {
                stack.push(c);
                stack.push(a);
            }
            // Anything else — an opaque node, an operator whose pointwise
            // geometry needs element *values* to merge (union_max, inter,
            // differences), a map/filter image, a nested ite — is
            // honestly refused.
            _ => return false,
        }
    }
    true
}

/// Define a fold by unrolling. `fold(f, t, ite(c, a, b))` is
/// `ite(c, fold(f, t, a), fold(f, t, b))` — exact, the same branch-picking
/// identity the count and cardinality rules take — and a non-ite bag's
/// ground multiset unrolls into the finite chain
/// `f(e, f(e, … f(e, t) …))` in structural order. A multiset with two or
/// more distinct element spellings needs the exchange law proved first
/// (see [`fold_fun_exchange_law`]); without it the fold's value depends on
/// the enumeration order, which no eager ground encoding may guess —
/// CVC5's own rewriter commits to one order for these shapes, but its
/// reduction semantics leaves the order existential, and the honest
/// answer here is `Declined`. Iterative bottom-up: the ite tree is walked
/// with an explicit stack and rebuilt from the leaves' unrolled values,
/// the same no-native-recursion discipline as the rest of the file.
fn fold_definition(
    func: Spur,
    init: TermId,
    bag: TermId,
    ret: SortId,
    fun_defs: &FxHashMap<Spur, BagFunDef>,
    manager: &mut TermManager,
) -> FoldDef {
    // Unroll one ite-free bag (`None` + the reason when it must decline).
    let unroll_leaf = |bag: TermId, manager: &mut TermManager| -> Result<TermId, FoldDecline> {
        let mut items: Vec<(TermId, u64)> = Vec::new();
        let mut budget = MAX_FOLD_APPLICATIONS;
        if !bag_ground_multiset(bag, &mut items, &mut budget, manager) {
            return Err(FoldDecline::Unrollable);
        }
        let distinct = items
            .iter()
            .map(|(e, _)| *e)
            .collect::<FxHashSet<_>>()
            .len();
        if distinct >= 2
            && !fold_fun_exchange_law(
                func,
                bag_element_of(bag, manager).unwrap_or(ret),
                ret,
                fun_defs,
                manager,
            )
        {
            // The value would depend on the enumeration order: refuse
            // to exhibit one (CVC5 answers through a fixed internal
            // order; matching it is not possible, so the honest answer
            // is a degraded `Unknown`, never a picked-side verdict).
            return Err(FoldDecline::OrderSensitive);
        }
        let mut acc = init;
        for &(e, copies) in &items {
            for _ in 0..copies {
                acc = bag_apply_fun2(func, e, acc, ret, fun_defs, manager);
            }
        }
        Ok(manager.simplify(acc))
    };
    // Post-order rebuild of the ite tree: each node's value is assembled
    // once both children have theirs (the re-push discipline).
    let mut vals: FxHashMap<TermId, TermId> = FxHashMap::default();
    let mut stack: Vec<TermId> = vec![bag];
    while let Some(t) = stack.pop() {
        if vals.contains_key(&t) {
            continue;
        }
        if let Some(TermKind::Ite(c, a, b)) = manager.get(t).map(|d| d.kind.clone()) {
            match (vals.get(&a), vals.get(&b)) {
                (Some(x), Some(y)) => {
                    let picked = manager.mk_ite(c, *x, *y);
                    vals.insert(t, picked);
                }
                _ => {
                    stack.push(t);
                    stack.push(b);
                    stack.push(a);
                }
            }
        } else {
            match unroll_leaf(t, manager) {
                Ok(v) => {
                    vals.insert(t, v);
                }
                // An ite branch that declines carries its reason up: an
                // order-sensitive branch makes the whole fold
                // order-sensitive (some branch's value depends on the
                // order, so the ite does too).
                Err(reason) => return FoldDef::Declined(reason),
            }
        }
    }
    match vals.get(&bag) {
        Some(&v) => FoldDef::Defined(v),
        // The bag itself was missing (an unknown term): the conservative
        // domain refusal.
        None => FoldDef::Declined(FoldDecline::Unrollable),
    }
}

fn count_definition(
    e: TermId,
    b: TermId,
    zero: TermId,
    by_sort: &FxHashMap<SortId, Vec<TermId>>,
    fun_defs: &FxHashMap<Spur, BagFunDef>,
    extra_axioms: &mut Vec<TermId>,
    manager: &mut TermManager,
) -> CountDef {
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
        // `count(y, map(f, b)) = Σ_x ite(f(x) = y, count(x, b), 0)` over
        // the *distinct-valued* domain elements — the de-duplication guard
        // is the cardinality sum's (two spellings of one value must
        // contribute once). Over a **closed** domain bag this is exact
        // (its support is its makes, all collected); over an opaque one
        // an unknown element may map to `y`, so the identity carries a
        // nonnegative slack — without it the encoding claimed the unknown
        // support contributes nothing and `count(5, map(f, b)) = 1` with
        // no known preimage answered `unsat` where the truth is `sat`
        // — a false *unsat*, the worst class.
        Some(TermKind::BagMap { func, ret, bag: d }) => {
            let Some(des) = bag_element_of(d, manager) else {
                return CountDef::Unsupported;
            };
            let Some(domain) = by_sort.get(&des) else {
                return CountDef::Unsupported;
            };
            let mut parts: Vec<TermId> = Vec::with_capacity(domain.len());
            for (i, &x) in domain.iter().enumerate() {
                let fx = bag_apply_fun(func, x, ret, fun_defs, manager);
                let same = manager.mk_eq(fx, e);
                let cx = count_term(x, d, manager);
                let cx_pos = manager.mk_gt(cx, zero);
                let hit = manager.mk_and([same, cx_pos]);
                let term = manager.mk_ite(hit, cx, zero);
                // The guard: no *earlier* domain element of the same value
                // already contributed (its count agrees by element
                // congruence, so the first spelling is the representative).
                let mut guards: Vec<TermId> = Vec::new();
                for &earlier in &domain[..i] {
                    let dup = manager.mk_eq(x, earlier);
                    let ce = count_term(earlier, d, manager);
                    let present = manager.mk_gt(ce, zero);
                    let clash = manager.mk_and([dup, present]);
                    guards.push(manager.mk_not(clash));
                }
                let part = if guards.is_empty() {
                    term
                } else {
                    let no_clash = manager.mk_and(guards);
                    manager.mk_ite(no_clash, term, zero)
                };
                parts.push(part);
            }
            let sum = if parts.is_empty() {
                zero
            } else {
                manager.mk_add(parts)
            };
            if bag_is_closed(d, manager) {
                CountDef::Defined(sum)
            } else {
                let mut name = format!("@bag_map_slack_{}_{}", b.0, e.0);
                for &x in domain {
                    name.push_str(&format!("_{}", x.0));
                }
                let slack = manager.mk_var(&name, manager.sorts.int_sort);
                let ge = manager.mk_ge(slack, zero);
                extra_axioms.push(ge);
                CountDef::Defined(manager.mk_add([sum, slack]))
            }
        }
        // `count(x, filter(p, b)) = ite(p(x), count(x, b), 0)` — exact per
        // element: filter only removes, so the known elements' counts are
        // determined regardless of the domain's unknown support (which the
        // cardinality slack absorbs, with `|filter| <= |b|` below).
        Some(TermKind::BagFilter { pred, bag: d }) => {
            let px = bag_apply_fun(pred, e, manager.sorts.bool_sort, fun_defs, manager);
            let cd = count_term(e, d, manager);
            CountDef::Defined(manager.mk_ite(px, cd, zero))
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
///
/// `user_eq_atoms` are the bag-sorted equality atoms the *user* wrote;
/// `minted_eq_atoms` (persisted by the caller across asserts) are the ones
/// this reduction minted on an earlier pass. A minted atom is re-surveyed
/// by the next assert's walk (the axioms are conjoined onto the assertion),
/// and without the distinction it would be treated as a user equality:
/// an extensionality witness per minted atom, each joining the element
/// list, until the quadratic passes around it ballooned — three-assert
/// fuzz shapes went from instant to unfinishable. Minted atoms get their
/// congruence from the pair pass that minted them; user atoms get the
/// full extensionality treatment (forward implications and witness).
pub(crate) fn reduce(
    roots: &[TermId],
    user_eq_atoms: &FxHashSet<TermId>,
    minted_eq_atoms: &mut FxHashSet<TermId>,
    fun_defs: &FxHashMap<Spur, BagFunDef>,
    manager: &mut TermManager,
) -> Reduction {
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
                    // A map's/filter's support lives in its domain bag's
                    // (the *images* are collected by the dedicated pass
                    // below, not by this walk — they are not makes).
                    TermKind::BagMap { bag, .. } | TermKind::BagFilter { bag, .. } => {
                        stack.push(*bag);
                    }
                    _ => {}
                }
            }
        }
    }
    let zero = manager.mk_int(0);

    // ---- the map images join the codomain element list ----
    // `count(y, map(f, b))` is stated over the codomain's element list, and
    // the image bag's support is exactly the images of the domain's
    // elements — `f(x)` for every known `x` (an inlined `define-fun` body
    // folded ground, or an `Apply` the EUF layer owns). Without this the
    // list for `(Bag T2)` could be empty and the identities stated
    // nothing — the exact vacuity the support walk exists to prevent.
    for &(_, func, ret, d) in &s.maps {
        let Some(des) = bag_element_of(d, manager) else {
            continue;
        };
        let Some(domain) = by_sort.get(&des).cloned() else {
            continue;
        };
        for x in domain {
            let image = bag_apply_fun(func, x, ret, fun_defs, manager);
            let list = by_sort.entry(ret).or_default();
            if !list.contains(&image) {
                list.push(image);
            }
        }
    }

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
    for &(atom, a, b) in &s.bag_equalities {
        // A reduction-minted atom (pair congruence, choose emptiness) gets
        // no witness: the pass that minted it states its congruence
        // directly, and a witness per minted atom is exactly the
        // element-list balloon the `minted_eq_atoms` registry exists to
        // stop.
        if !user_eq_atoms.contains(&atom) && minted_eq_atoms.contains(&atom) {
            continue;
        }
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

    // The **choose elements** join the list for the same reason: the
    // choose axiom below mints `count(choose(b), b)`, and the identity
    // loop must state that count (and the counts over every compound of
    // the sort) for the element the formula now depends on. Without the
    // entry, `count(choose(b), (bag 1 3)) = ite(choose(b) = 1 ∧ 3 ≥ 1, 3, 0)`
    // was never stated and a choose pinned off the support answered
    // `sat` beside a closed bag.
    for &(choose, b) in &s.chooses {
        let Some(es) = bag_element_of(b, manager) else {
            continue;
        };
        if !by_sort.entry(es).or_default().contains(&choose) {
            by_sort.entry(es).or_default().push(choose);
        }
    }

    // ---- bag.fold ----
    // Each fold is pinned to its unrolled application chain when its
    // domain bag is a ground multiset (`∅`/`(bag y n)` with numeral
    // `n`/`⊎`, under ites) and — when the multiset has two or more
    // distinct element spellings — the combining function provably
    // satisfies the exchange law. Along every surveyed bag-equality
    // atom `(a = b)` the two folds are tied (`atom → fold(a) = fold(b)`),
    // so a fold over an opaque bag pinned to a closed compound by
    // extensionality takes the closed value: the tie is guarded by the
    // atom, hence valid whatever its truth, and the minted fold terms
    // (stable under hash-consing) join the unroll work-list. Anything
    // the work-list cannot pin raises the honesty gate: the fold term
    // stays free, so a `Sat` resting on it degrades to `Unknown`, while
    // every *other* axiom stays valid and any `Unsat` remains sound
    // (asserting nothing about the fold only weakened the constraints).
    let mut fold_work: Vec<(TermId, Spur, TermId, TermId)> = s.folds.clone();
    for &(atom, a, b) in &s.bag_equalities {
        for &(_, func, init, bag) in &s.folds {
            if bag != a && bag != b {
                continue;
            }
            let name = manager.resolve_str(func).to_string();
            let fa = manager.mk_bag_fold(&name, init, a);
            let fb = manager.mk_bag_fold(&name, init, b);
            let agree = manager.mk_eq(fa, fb);
            out.axioms.push(manager.mk_implies(atom, agree));
            fold_work.push((fa, func, init, a));
            fold_work.push((fb, func, init, b));
        }
    }
    for &(term, func, init, bag) in &fold_work {
        let ret = manager
            .get(term)
            .map(|d| d.sort)
            .unwrap_or(manager.sorts.int_sort);
        match fold_definition(func, init, bag, ret, fun_defs, manager) {
            FoldDef::Defined(chain) => {
                let eq = manager.mk_eq(term, chain);
                out.axioms.push(eq);
            }
            FoldDef::Declined(reason) => {
                // Not `incomplete`: a free fold keeps every `unsat` sound
                // (the constraint set only got weaker) and the model pass
                // certifies the `sat` side — folding each declined bag's
                // assembled value and degrading on contradiction, or
                // degrading an order-sensitive fold outright.
                out.declined_folds.push((term, reason));
            }
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
            let mut extra_here: Vec<TermId> = Vec::new();
            let def = count_definition(e, b, zero, &by_sort, fun_defs, &mut extra_here, manager);
            out.axioms.append(&mut extra_here);
            match def {
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
            if !eligible(a) || !eligible(b) {
                continue;
            }
            if bag_pairs >= MAX_BAG_PAIRS {
                out.incomplete = true;
                break 'outer;
            }
            bag_pairs += 1;
            let same = manager.mk_eq(a, b);
            minted_eq_atoms.insert(same);
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
        // Minted, non-user: the pair pass owns this atom's congruence.
        if !user_eq_atoms.contains(&atom) && minted_eq_atoms.contains(&atom) {
            continue;
        }
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

    // ---- choose ----
    // CVC5's `BAG_CHOOSE` elimination (`theory_bags.cpp`,
    // `expandChooseOperator`): the skolem `k` carries
    // `A = ∅ ∨ count(k, A) ≥ 1`. Two shapes, by whether the formula
    // already cardinalizes the bag:
    //
    // * **with a `bag.card` term present** (surveyed, so its equation
    //   `|b| = Σ + slack` is stated and the model pass verifies it):
    //   `count(choose(b), b) ≥ 1 ↔ |b| ≥ 1` — the set theory's
    //   `SET_CHOOSE` shape. This is what makes
    //   `|b| ≥ 1 ∧ count(choose(b), b) = 0` refute at the arithmetic
    //   layer, through the card the formula itself owns.
    // * **without one**: CVC5's disjunction over the emptiness
    //   *equality atom*, never a minted `bag.card` — a card term minted
    //   here would join the assertion's conjoined axioms, the model
    //   pass would survey it, and its barely-constrained slack column
    //   would roll back perfectly good bag values (found on
    //   `count(3,b) = 2 ∧ choose(b) = 3`, which printed `b = ∅`).
    //   Because the atom is minted *after* the survey, the
    //   extensionality pass has not seen the pair — so the forward
    //   direction is stated here directly: `b = ∅ → count(e, b) = 0`
    //   for every known element (the choose included), which is what
    //   keeps a single-assert script's disjunction from vacuously
    //   committing `b = ∅` beside a nonzero count.
    for &(choose, b) in &s.chooses {
        let Some(es) = bag_element_of(b, manager) else {
            continue;
        };
        let c = count_term(choose, b, manager);
        let one = manager.mk_int(1);
        let count_ge = manager.mk_ge(c, one);
        if s.cards.iter().any(|&(_, bb)| bb == b) {
            let card = manager.mk_bag_card(b);
            let nonempty = manager.mk_ge(card, one);
            out.axioms.push(manager.mk_eq(count_ge, nonempty));
            continue;
        }
        let bag_sort = manager.sorts.bag(es);
        let empty = manager.mk_bag_empty_at(bag_sort);
        let is_empty = manager.mk_eq(b, empty);
        minted_eq_atoms.insert(is_empty);
        out.axioms.push(manager.mk_or([is_empty, count_ge]));
        let zero = manager.mk_int(0);
        if let Some(elems) = by_sort.get(&es) {
            for &e in elems {
                let ce = count_term(e, b, manager);
                let zero_count = manager.mk_eq(ce, zero);
                out.axioms.push(manager.mk_implies(is_empty, zero_count));
            }
        }
    }
    // `choose` is a function symbol: equal bags give equal elements. EUF
    // would supply this if the choose term were an ordinary application
    // (CVC5's skolem is `uf(A)` for exactly that reason); here the
    // equality atoms are booleanized, so the congruence is stated over
    // the choose pairs the survey found — the set theory's discipline,
    // budget included. Without it, `a = b ∧ |a| ≥ 1 ∧ choose(a) ≠ choose(b)`
    // answered `Sat` there, and the bag shape is identical.
    {
        const MAX_CHOOSE_PAIRS: usize = 128;
        let mut choose_pairs = 0usize;
        'choose: for (i, &(ua, ta)) in s.chooses.iter().enumerate() {
            for &(ub, tb) in s.chooses.iter().skip(i + 1) {
                if ta == tb || bag_element_of(ta, manager) != bag_element_of(tb, manager) {
                    continue;
                }
                if choose_pairs >= MAX_CHOOSE_PAIRS {
                    out.incomplete = true;
                    break 'choose;
                }
                choose_pairs += 1;
                let same = manager.mk_eq(ta, tb);
                minted_eq_atoms.insert(same);
                let agree = manager.mk_eq(ua, ub);
                out.axioms.push(manager.mk_implies(same, agree));
            }
        }
        // `choose(ite c a b) = ite c (choose a) (choose b)`: with `c` true
        // the ite *is* `a`, so the two chooses must agree — but the pair
        // rule above conditions on an equality atom nobody asserts. The
        // set theory's choose-over-ite rule, same shape. Minting the
        // branch chooses is sound: the choose axiom above is valid for
        // every bag, and hash-consing keeps the minted terms stable
        // across the per-assert re-runs.
        for &(u, t) in &s.chooses {
            if let Some(TermKind::Ite(c, a, b)) = manager.get(t).map(|d| d.kind.clone()) {
                let ca = manager.mk_bag_choose(a);
                let cb = manager.mk_bag_choose(b);
                let picked = manager.mk_ite(c, ca, cb);
                out.axioms.push(manager.mk_eq(u, picked));
            }
        }
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
            if !user_eq_atoms.contains(&atom) && minted_eq_atoms.contains(&atom) {
                continue;
            }
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
                // `|map(f, b)| = |b|` exactly: `f` is total, so every one
                // of the `|b|` copies maps to exactly one copy — collisions
                // merge multiplicities, the sum is preserved. This is what
                // ties the per-element image slacks to the domain's.
                TermKind::BagMap { bag: x, .. } => {
                    let (cx, cb) = (manager.mk_bag_card(x), manager.mk_bag_card(b));
                    out.axioms.push(manager.mk_eq(cb, cx));
                }
                // `|filter(p, b)| <= |b|`: filtering only removes.
                TermKind::BagFilter { bag: x, .. } => {
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
        declined_folds: out.declined_folds,
    }
}
