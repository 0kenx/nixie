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
            let Some(es) = bag_element_of(b, manager) else {
                continue;
            };
            let Some(elems) = by_sort.get(&es) else {
                continue;
            };
            let assembled: i64 = elems
                .iter()
                .filter_map(|&e| {
                    count_value(
                        manager.mk_bag_count(e, b),
                        model,
                        &self.arith,
                        &self.arith_purify,
                        manager,
                    )
                })
                .sum();
            if assembled != want {
                for &t in &installed_bags {
                    let same_sort = bag_element_of(t, manager) == Some(es);
                    if same_sort {
                        model.remove(t);
                    }
                }
                installed_bags.retain(|&t| bag_element_of(t, manager) != Some(es));
                continue;
            }
            // Verified: the card term prints as the assembled size (the
            // value the published bag actually has, which the check just
            // reconciled with the arithmetic solver's word).
            let n_term = manager.mk_int(num_bigint::BigInt::from(assembled));
            model.set(card, n_term);
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
}

fn bag_model_survey(roots: &[TermId], manager: &TermManager) -> BagModelSurvey {
    let mut out = BagModelSurvey {
        bags: Vec::new(),
        elements: Vec::new(),
        cards: Vec::new(),
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
            _ => {}
        }
    }
}
