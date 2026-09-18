//! Bag model synthesis: count-driven values and the count readback.
//!
//! [`Solver::extract_bag_model`] runs at model-build time, right after the
//! set pass: by then the arithmetic solver has valued every `bag.count`
//! term the reduction's axioms constrained (they are ordinary integer
//! columns), and a bag's value is *fully determined* by those counts — no
//! mints, no pools, no guesses, unlike the set synthesis. For each bag
//! term whose per-element counts all resolve, the value is assembled as
//! the canonical `bag.union_disjoint` of `(bag e n)` terms (positive
//! multiplicities only), so a printed model re-reads as itself; the count
//! terms themselves get model entries, which is what makes
//! `(get-value ((bag.count 1 b)))` answer with a number instead of
//! echoing.
//!
//! # Soundness posture
//!
//! The assembled value is correct by construction *relative to the
//! arithmetic model's counts*. The one independent commitment to verify is
//! cardinality: where the formula constrains `bag.card`, the assembled
//! value's size (the sum of its multiplicities) must equal the arithmetic
//! solver's word for it — a mismatch means the reduction's axioms and the
//! arithmetic model disagree, and the bag's entries roll back (the honest
//! echo) rather than publish a value that falsifies a constraint.
//! Multiplicities are nonnegative by the reduction's axiom; a resolved
//! count below zero cannot occur in a consistent model, and is declined.

use crate::prelude::*;
use nixie_core::sort::SortId;
use nixie_core::{TermId, TermKind, TermManager};
use nixie_theories::arithmetic::ArithSolver;

use super::Solver;
use super::purify_arith::PurifyState;
use super::types::Model;

impl Solver {
    /// Synthesize bag values from the arithmetic counts, and install the
    /// count readbacks. Runs after [`Self::extract_set_model`]; gated on
    /// the same honesty flag (an incomplete bag reduction leaves every
    /// bag printing the `(as bag.empty …)` default).
    pub(super) fn extract_bag_model(&mut self, model: &mut Model, manager: &mut TermManager) {
        if self.set_terms_unconstrained {
            // Same honesty gate as the set synthesis: the bag reduction
            // raised `incomplete`, so a `Sat` was already degraded and no
            // bag value here can claim faithfulness.
            return;
        }
        let survey = bag_model_survey(&self.assertions, manager);
        if survey.bags.is_empty() {
            return;
        }

        // Ground element lists per sort: the support walk of every bag
        // term (the makes inside compounds) plus every element a
        // count/member atom names. Mirrors the reduction's collection so
        // the two see the same element universe.
        let mut by_sort: FxHashMap<SortId, Vec<TermId>> = FxHashMap::default();
        for &(e, es) in &survey.elements {
            if !by_sort.entry(es).or_default().contains(&e) {
                by_sort.entry(es).or_default().push(e);
            }
        }
        for &(b, es) in &survey.bags {
            collect_bag_support(b, es, &mut by_sort, manager);
        }
        // The map images join the codomain lists — the same collection the
        // reduction performs, so the model's element universe matches the
        // identities' and every count readback the reduction constrained
        // resolves here.
        for &(_, func, ret, d) in &survey.maps {
            let Some(des) = bag_element_of(d, manager) else {
                continue;
            };
            let Some(domain) = by_sort.get(&des).cloned() else {
                continue;
            };
            for x in domain {
                let image = if let Some(&(param, body)) = self.bag_fun_defs.get(&func) {
                    {
                        let mut subst: FxHashMap<TermId, TermId> = FxHashMap::default();
                        subst.insert(param, x);
                        let sub = manager.substitute(body, &subst);
                        manager.simplify(sub)
                    }
                } else {
                    let name = manager.resolve_str(func).to_string();
                    manager.mk_apply(&name, [x], ret)
                };
                let list = by_sort.entry(ret).or_default();
                if !list.contains(&image) {
                    list.push(image);
                }
            }
        }

        let int_entry = |t: TermId, manager: &TermManager| -> Option<i64> {
            match manager.get(t).map(|d| &d.kind) {
                Some(TermKind::IntConst(n)) => num_traits::ToPrimitive::to_i64(n),
                _ => None,
            }
        };
        // The count's value, CVC5's resolution order adapted from the set
        // cardinality readback: the tableau, the model entry the arith
        // pass recorded, then the purification proxy's.
        let count_value = |c: TermId,
                           model: &Model,
                           arith: &ArithSolver,
                           purify: &PurifyState,
                           manager: &TermManager|
         -> Option<i64> {
            // A count over a closed base folds in the builder to a plain
            // constant (`count(2, (2:5))` is `ite(2=2 ∧ 5≥1, 5, 0)` → `5`)
            // — the constant IS the value.
            if let Some(TermKind::IntConst(n)) = manager.get(c).map(|d| &d.kind) {
                return num_traits::ToPrimitive::to_i64(n);
            }
            let mut v: Option<i64> = arith.value(c).map_or_else(
                || model.get(c).and_then(|t| int_entry(t, manager)),
                |r| Some(r.to_integer()),
            );
            if v.is_none()
                && let Some(proxy) = purify.proxy_of(c)
            {
                v = arith.value(proxy).map_or_else(
                    || model.get(proxy).and_then(|t| int_entry(t, manager)),
                    |r| Some(r.to_integer()),
                );
            }
            v
        };

        // ---- value the choose elements ----
        // A choose's value must satisfy its count constraints over every
        // bag, and the one the reduction's axiom pins is its own:
        //     count(choose(b), b) = n
        // so `choose(b)`'s value is a cell of `b` whose multiplicity is
        // exactly `n` (any such cell — the choose axioms only demand
        // membership and congruence, and class-equal bags share cells, so
        // congruent chooses agree on the deterministic first match). For
        // `n = 0` (an empty bag, or the element simply absent) the value
        // must *avoid* the cells. This runs before assembly because the
        // grouping keys on resolved element values: a choose without an
        // entry would decline every bag it counts over.
        //
        // The provisional cells come from the non-choose elements only
        // (their values never depend on a choose, so there is no cycle);
        // the assembly loop below then re-groups with the chooses present
        // and its disagreement check validates the pick.
        let mut valued_chooses: Vec<(TermId, TermId, i64)> = Vec::new();
        for &(choose, b) in &survey.chooses {
            if model.get(choose).is_some() {
                continue;
            }
            let Some(es) = bag_element_of(b, manager) else {
                continue;
            };
            let Some(elems) = by_sort.get(&es) else {
                continue;
            };
            // Provisional cells of `b`, grouped by resolved value.
            let mut cells: Vec<(TermId, i64)> = Vec::new();
            let mut trusted = true;
            for &e in elems {
                if survey.chooses.iter().any(|&(c, _)| c == e) {
                    continue; // chooses resolved below, not here
                }
                let c = manager.mk_bag_count(e, b);
                let Some(n) = count_value(c, model, &self.arith, &self.arith_purify, manager)
                else {
                    trusted = false;
                    break;
                };
                if n <= 0 {
                    continue;
                }
                let Some(v) = self.element_value_term(e, model, manager) else {
                    trusted = false;
                    break;
                };
                match cells.iter_mut().find(|(cv, _)| *cv == v) {
                    Some((_, m)) if *m != n => trusted = false,
                    Some(_) => {}
                    None => cells.push((v, n)),
                }
                if !trusted {
                    break;
                }
            }
            if !trusted {
                continue;
            }
            cells.sort_by_key(|&(v, _)| v.0);
            let c = manager.mk_bag_count(choose, b);
            let Some(n) = count_value(c, model, &self.arith, &self.arith_purify, manager) else {
                continue;
            };
            // **Committed equalities come first.** The SAT layer may have
            // committed `choose(b) = e` (a user assertion) or
            // `choose(b) ≠ e` for a known element; a pick that ignores
            // them publishes a value falsifying an atom the search already
            // decided — the set model's choose pass reads the same
            // commitment (`committed_bool_model`). A committed-true pick
            // must still be a cell (the axioms force the counts to agree;
            // if they did not, the verification below rolls it back).
            let mut value = None;
            let mut avoid: FxHashSet<TermId> = FxHashSet::default();
            for &e in elems {
                let same = manager.mk_eq(choose, e);
                match self.committed_bool_model(same, model, manager) {
                    Some(true) => {
                        if let Some(v) = self.element_value_term(e, model, manager) {
                            value = Some(v);
                        }
                        break;
                    }
                    Some(false) => {
                        avoid.insert(e);
                    }
                    None => {}
                }
            }
            let value = value.or_else(|| {
                if n > 0 {
                    // A member: the first cell whose multiplicity is exactly
                    // `n` (count(choose(b), b) is the multiplicity of
                    // choose(b)'s value, so the pick must match it), avoiding
                    // committed-disequal elements.
                    cells
                        .iter()
                        .find(|&&(v, m)| m == n && !avoid.contains(&v))
                        .map(|&(v, _)| v)
                } else {
                    // Not a member: a fresh value of the sort that is no
                    // cell's — `0` when free, else the smallest nonnegative
                    // integer no cell holds. Non-`Int` element sorts decline
                    // (the honest echo) rather than guess a string/BV that
                    // might collide with a cell.
                    if es == manager.sorts.int_sort {
                        let mut candidate = 0i64;
                        while cells
                            .iter()
                            .any(|&(v, _)| int_cell_value(v, manager) == Some(candidate))
                        {
                            candidate += 1;
                        }
                        Some(manager.mk_int(num_bigint::BigInt::from(candidate)))
                    } else {
                        None
                    }
                }
            });
            let Some(v) = value else {
                // No consistent cell (or an unvalued sort): leave the
                // choose unvalued — the assembly's disagreement check
                // will decline the bag if that mattered.
                continue;
            };
            model.set(choose, v);
            valued_chooses.push((choose, b, n));
            let list = by_sort.entry(es).or_default();
            if !list.contains(&choose) {
                list.push(choose);
            }
        }

        // ---- assemble and install ----
        let mut installed_bags: Vec<TermId> = Vec::new();
        for &(b, es) in &survey.bags {
            let Some(elems) = by_sort.get(&es) else {
                continue;
            };
            // Resolve every (element, count) pair; any unresolvable one
            // declines the term (the honest default), never a guess.
            // Elements are then **grouped by their resolved values**: the
            // reduction's `@bag_ext_*` witnesses are ordinary elements the
            // arithmetic model values (often equal to a real element —
            // that is what their consistency axioms force), and two
            // elements of one value are one bag cell whose counts must
            // agree. Printing the skolem's spelling instead of its value,
            // or emitting the cell twice, would publish a value the
            // printed form does not re-read as.
            let mut counts_by_value: FxHashMap<TermId, i64> = FxHashMap::default();
            let mut resolved_all = true;
            for &e in elems {
                let c = manager.mk_bag_count(e, b);
                let Some(n) = count_value(c, model, &self.arith, &self.arith_purify, manager)
                else {
                    resolved_all = false;
                    break;
                };
                if n < 0 {
                    // A consistent model cannot assign a negative
                    // multiplicity (the reduction axioms forbid it);
                    // seeing one means the counts and the constraints
                    // diverged — decline.
                    resolved_all = false;
                    break;
                }
                if n > 0 {
                    let Some(v) = self.element_value_term(e, model, manager) else {
                        resolved_all = false;
                        break;
                    };
                    match counts_by_value.get(&v) {
                        Some(&m) if m != n => {
                            // Two spellings of one value disagreeing on
                            // the count: an inconsistent model — decline.
                            resolved_all = false;
                            break;
                        }
                        Some(_) => {}
                        None => {
                            counts_by_value.insert(v, n);
                        }
                    }
                }
                // The readback: the count term prints as its number.
                let n_term = manager.mk_int(num_bigint::BigInt::from(n));
                model.set(c, n_term);
            }
            if !resolved_all {
                continue;
            }
            let mut cells: Vec<(TermId, i64)> = counts_by_value.into_iter().collect();
            cells.sort_by_key(|&(v, _)| v.0);
            let bag_sort = manager.sorts.bag(es);
            let mut acc = manager.mk_bag_empty_at(bag_sort);
            for &(v, n) in &cells {
                let n_term = manager.mk_int(num_bigint::BigInt::from(n));
                let make = manager.mk_bag_make(v, n_term);
                acc = manager.mk_bag_union_disjoint(acc, make);
            }
            model.set(b, acc);
            installed_bags.push(b);
        }

        // ---- verify the cardinality commitments ----
        // Where the formula constrains `bag.card`, the assembled size (the
        // sum of the multiplicities) must match the arithmetic solver's
        // word. A mismatch rolls the *bag* entries of that sort back; the
        // count readbacks stay (they are the arithmetic solver's own
        // values, correct or not on their own terms).
        for &(card, b) in &survey.cards {
            if !installed_bags.contains(&b) {
                continue;
            }
            let Some(want) = count_value(card, model, &self.arith, &self.arith_purify, manager)
            else {
                continue;
            };
            // The verified size is the *installed value's* — the sum of
            // the cells actually published, which the assembly already
            // de-duplicated by element value (the raw per-element sum
            // would count a witness spelling twice — exactly the
            // double-count the assembly's grouping exists to avoid).
            let Some(es) = bag_element_of(b, manager) else {
                continue;
            };
            let mut assembled: i64 = 0;
            let Some(value) = model.get(b) else {
                continue;
            };
            let mut cur = value;
            loop {
                match manager.get(cur).map(|d| d.kind.clone()) {
                    Some(TermKind::BagEmpty(_)) => break,
                    Some(TermKind::BagUnionDisjoint(a, make)) => {
                        let Some(TermKind::BagMake(_, n)) =
                            manager.get(make).map(|d| d.kind.clone())
                        else {
                            break;
                        };
                        if let Some(TermKind::IntConst(v)) = manager.get(n).map(|d| &d.kind) {
                            assembled += num_traits::ToPrimitive::to_i64(v).unwrap_or(0);
                        }
                        cur = a;
                    }
                    Some(TermKind::BagMake(_, n)) => {
                        if let Some(TermKind::IntConst(v)) = manager.get(n).map(|d| &d.kind) {
                            assembled += num_traits::ToPrimitive::to_i64(v).unwrap_or(0);
                        }
                        break;
                    }
                    _ => break,
                }
            }
            if assembled != want {
                for &t in &installed_bags {
                    let same_sort = bag_element_of(t, manager) == Some(es);
                    if same_sort {
                        model.remove(t);
                    }
                }
                installed_bags.retain(|&t| bag_element_of(t, manager) != Some(es));
                // The choose entries of the rolled-back sort reference
                // those bag values; they go with them.
                for &(choose, cb, _) in &valued_chooses {
                    if bag_element_of(cb, manager) == Some(es) {
                        model.remove(choose);
                    }
                }
                continue;
            }
            // Verified: the card term prints as the assembled size (the
            // value the published bag actually has, which the check just
            // reconciled with the arithmetic solver's word).
            let n_term = manager.mk_int(num_bigint::BigInt::from(assembled));
            model.set(card, n_term);
        }

        // ---- verify the choose commitments ----
        // A valued choose's multiplicity among the *installed* cells of its
        // bag must equal the arithmetic count the pick was made from — the
        // same reconciliation the cardinality check performs, per element.
        // A mismatch means the counts and the published value disagree;
        // both roll back (the honest echo), never a falsifying value.
        for &(choose, b, n) in &valued_chooses {
            if !installed_bags.contains(&b) {
                continue;
            }
            let Some(value) = model.get(choose) else {
                continue;
            };
            let Some(es) = bag_element_of(b, manager) else {
                continue;
            };
            let Some(bag_value) = model.get(b) else {
                continue;
            };
            let mut found: Option<i64> = None;
            let mut cur = bag_value;
            loop {
                match manager.get(cur).map(|d| d.kind.clone()) {
                    Some(TermKind::BagEmpty(_)) => break,
                    Some(TermKind::BagUnionDisjoint(a, make)) => {
                        if let Some(TermKind::BagMake(e, m)) =
                            manager.get(make).map(|d| d.kind.clone())
                        {
                            let same_value = e == value
                                || (int_cell_value(e, manager).is_some()
                                    && int_cell_value(e, manager)
                                        == int_cell_value(value, manager));
                            if same_value
                                && let Some(TermKind::IntConst(k)) = manager.get(m).map(|d| &d.kind)
                            {
                                found = num_traits::ToPrimitive::to_i64(k);
                            }
                        }
                        cur = a;
                    }
                    Some(TermKind::BagMake(e, m)) => {
                        let same_value = e == value
                            || (int_cell_value(e, manager).is_some()
                                && int_cell_value(e, manager) == int_cell_value(value, manager));
                        if same_value
                            && let Some(TermKind::IntConst(k)) = manager.get(m).map(|d| &d.kind)
                        {
                            found = num_traits::ToPrimitive::to_i64(k);
                        }
                        break;
                    }
                    _ => break,
                }
            }
            let ok = match found {
                Some(m) => m == n,
                // `n = 0`: the value must appear in no cell, which the walk
                // just confirmed.
                None => n == 0,
            };
            if !ok {
                for &t in &installed_bags {
                    if bag_element_of(t, manager) == Some(es) {
                        model.remove(t);
                    }
                }
                installed_bags.retain(|&t| bag_element_of(t, manager) != Some(es));
                for &(choose2, cb2, _) in &valued_chooses {
                    if bag_element_of(cb2, manager) == Some(es) {
                        model.remove(choose2);
                    }
                }
            }
        }
    }
}

/// What the bag model pass needs from the assertions.
struct BagModelSurvey {
    /// Every bag-sorted term with its element sort.
    bags: Vec<(TermId, SortId)>,
    /// Elements named by count/member atoms, with their sorts.
    elements: Vec<(TermId, SortId)>,
    /// `bag.card` terms over bags.
    cards: Vec<(TermId, TermId)>,
    /// `bag.choose` terms: `(choose, bag)`.
    chooses: Vec<(TermId, TermId)>,
    /// `bag.map` terms: `(term, func, ret, domain bag)`.
    maps: Vec<(TermId, nixie_core::interner::Spur, SortId, TermId)>,
}

fn bag_model_survey(roots: &[TermId], manager: &TermManager) -> BagModelSurvey {
    let mut out = BagModelSurvey {
        bags: Vec::new(),
        elements: Vec::new(),
        cards: Vec::new(),
        chooses: Vec::new(),
        maps: Vec::new(),
    };
    let bag_es = |sort: SortId| -> Option<SortId> {
        manager.sorts.get(sort).and_then(|s| match &s.kind {
            nixie_core::SortKind::Bag(e) => Some(*e),
            _ => None,
        })
    };
    let mut seen: FxHashSet<TermId> = FxHashSet::default();
    let mut stack: Vec<TermId> = roots.to_vec();
    while let Some(t) = stack.pop() {
        if !seen.insert(t) {
            continue;
        }
        let Some(data) = manager.get(t) else { continue };
        if let Some(es) = bag_es(data.sort)
            && !out.bags.iter().any(|&(b, _)| b == t)
        {
            out.bags.push((t, es));
        }
        match &data.kind {
            TermKind::BagCount(e, b) | TermKind::BagMember(e, b) => {
                if let Some(es) = manager.get(*b).map(|d| d.sort).and_then(bag_es) {
                    out.elements.push((*e, es));
                }
            }
            TermKind::BagCard(b) => out.cards.push((t, *b)),
            TermKind::BagChoose(b) => out.chooses.push((t, *b)),
            TermKind::BagMap { func, ret, bag } => out.maps.push((t, *func, *ret, *bag)),
            _ => {}
        }
        stack.extend(nixie_core::ast::traversal::get_children(&data.kind));
    }
    out
}

/// An element's resolved value: a term (itself when ground, or the
/// model's entry) or an exact integer the caller materializes.
enum ElementValue {
    /// A printable term as-is.
    Term(TermId),
    /// An exact integer (numeric leaves the tableau valued).
    Int(i64),
}

/// An element's **value**: itself when ground, the arithmetic solver's
/// number for a numeric leaf (the `@bag_ext_*` witnesses are Int
/// variables the tableau values), the model's entry for anything else.
/// `None` declines.
fn element_value_term_of(
    e: TermId,
    model: &Model,
    arith: &ArithSolver,
    purify: &PurifyState,
    manager: &TermManager,
) -> Option<ElementValue> {
    match manager.get(e).map(|d| d.kind.clone()) {
        // Ground values are their own spelling.
        Some(
            TermKind::IntConst(_)
            | TermKind::RealConst(_)
            | TermKind::StringLit(_)
            | TermKind::BitVecConst { .. }
            | TermKind::DtConstructor { .. },
        ) => Some(ElementValue::Term(e)),
        // A numeric leaf (variable, application): the tableau's value,
        // with the purification-proxy fallback. An exact rational with
        // denominator 1 narrows to the integer term.
        Some(_)
            if {
                let sort = manager.get(e).map(|d| d.sort)?;
                sort == manager.sorts.int_sort || sort == manager.sorts.real_sort
            } =>
        {
            // The value as an exact integer; the term is built by the
            // caller (which holds the manager mutably) from the returned
            // number.
            let r = arith
                .value(e)
                .or_else(|| purify.proxy_of(e).and_then(|p| arith.value(p)))?;
            let int = r.to_integer();
            Some(ElementValue::Int(int))
        }
        _ => model.get(e).filter(|&v| v != e).map(ElementValue::Term),
    }
}

impl Solver {
    /// The instance wrapper (borrows `self` for the arithmetic state),
    /// materializing the integer case into a term.
    fn element_value_term(
        &self,
        e: TermId,
        model: &Model,
        manager: &mut TermManager,
    ) -> Option<TermId> {
        match element_value_term_of(e, model, &self.arith, &self.arith_purify, manager)? {
            ElementValue::Term(t) => Some(t),
            ElementValue::Int(n) => Some(manager.mk_int(num_bigint::BigInt::from(n))),
        }
    }
}

/// An `IntConst` cell value's integer, for fresh-value scans.
fn int_cell_value(v: TermId, manager: &TermManager) -> Option<i64> {
    match manager.get(v).map(|d| &d.kind) {
        Some(TermKind::IntConst(k)) => num_traits::ToPrimitive::to_i64(k),
        _ => None,
    }
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

/// Push every `bag.make` element inside `b`'s compound DAG into the
/// per-sort list (the support walk the reduction also does).
fn collect_bag_support(
    b: TermId,
    es: SortId,
    by_sort: &mut FxHashMap<SortId, Vec<TermId>>,
    manager: &TermManager,
) {
    let mut stack = vec![b];
    let mut seen: FxHashSet<TermId> = FxHashSet::default();
    while let Some(t) = stack.pop() {
        if !seen.insert(t) {
            continue;
        }
        match manager.get(t).map(|d| d.kind.clone()) {
            Some(TermKind::BagMake(y, _)) => {
                if !by_sort.entry(es).or_default().contains(&y) {
                    by_sort.entry(es).or_default().push(y);
                }
            }
            Some(TermKind::BagUnionMax(a, c))
            | Some(TermKind::BagUnionDisjoint(a, c))
            | Some(TermKind::BagInterMin(a, c))
            | Some(TermKind::BagDifferenceSubtract(a, c))
            | Some(TermKind::BagDifferenceRemove(a, c)) => {
                stack.push(a);
                stack.push(c);
            }
            Some(TermKind::BagSetof(a)) => stack.push(a),
            // An ite bag's support is the union of its branches' (the
            // `Bool` condition contributes none) — mirrors the reduction's
            // support walk so the two see the same element universe. A
            // map's/filter's support lives in its domain bag; the *images*
            // are collected by the dedicated pass in `extract_bag_model`.
            Some(TermKind::Ite(_, a, c)) => {
                stack.push(a);
                stack.push(c);
            }
            Some(TermKind::BagMap { bag, .. }) | Some(TermKind::BagFilter { bag, .. }) => {
                stack.push(bag);
            }
            _ => {}
        }
    }
}
