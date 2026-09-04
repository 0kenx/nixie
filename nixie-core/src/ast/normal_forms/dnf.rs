//! Disjunctive Normal Form (DNF) conversion.
//!
//! Split out of `ast/normal_forms.rs`; see that module's doc comment for the
//! general iterative-conversion rationale. This is CNF's exact mirror image
//! (distribute `And` over `Or` instead of `Or` over `And`); see
//! `cnf::distribute_or_over_and`'s doc comment for the exponential-blowup /
//! now-real-memoization notes that apply equally to
//! [`distribute_and_over_or`].

use super::super::{TermId, TermKind, TermManager};
use super::{DistributeStep, is_literal};
#[allow(unused_imports)]
use crate::prelude::*;
use smallvec::SmallVec;

/// Convert a boolean formula to Disjunctive Normal Form (DNF)
///
/// DNF is a disjunction of conjunctions, where each conjunction is a conjunction of literals.
/// For example: (a ∧ b) ∨ (¬c ∧ d) ∨ e
///
/// # Algorithm
/// 1. Eliminate implications
/// 2. Push negations inward
/// 3. Distribute AND over OR
///
/// See `cnf::to_cnf`'s doc comment and the parent module's doc comment: this
/// is DNF's mirror image (distribute `And` over `Or` instead of `Or` over
/// `And`), and shares the same exponential-blowup and
/// now-real-memoization properties.
pub fn to_dnf(term_id: TermId, manager: &mut TermManager) -> TermId {
    let mut cache: FxHashMap<(TermId, bool), TermId> = FxHashMap::default();
    let mut pair_cache: FxHashMap<(TermId, TermId), TermId> = FxHashMap::default();
    run_to_dnf(term_id, false, manager, &mut cache, &mut pair_cache)
}

/// Mirrors `cnf::CnfStep`; see that type's doc comment. The one structural
/// difference is `CombineImplies`, because CNF and DNF disagree on *which*
/// polarity of `Implies` needs distribution (see `run_dnf_step`).
enum DnfStep {
    Expand(TermId, bool),
    Alias {
        id: TermId,
        negate: bool,
        from: (TermId, bool),
    },
    CombineImplies {
        id: TermId,
        negate: bool,
        lhs: TermId,
        rhs: TermId,
    },
    CombineAndOr {
        id: TermId,
        negate: bool,
        is_and: bool,
        children: SmallVec<[TermId; 4]>,
    },
}

fn run_to_dnf(
    term_id: TermId,
    negate: bool,
    manager: &mut TermManager,
    cache: &mut FxHashMap<(TermId, bool), TermId>,
    pair_cache: &mut FxHashMap<(TermId, TermId), TermId>,
) -> TermId {
    if let Some(&result) = cache.get(&(term_id, negate)) {
        return result;
    }

    let mut work: Vec<DnfStep> = vec![DnfStep::Expand(term_id, negate)];
    while let Some(step) = work.pop() {
        run_dnf_step(step, manager, cache, pair_cache, &mut work);
    }

    cache.get(&(term_id, negate)).copied().unwrap_or(term_id)
}

#[allow(clippy::too_many_lines)]
fn run_dnf_step(
    step: DnfStep,
    manager: &mut TermManager,
    cache: &mut FxHashMap<(TermId, bool), TermId>,
    pair_cache: &mut FxHashMap<(TermId, TermId), TermId>,
    work: &mut Vec<DnfStep>,
) {
    match step {
        DnfStep::Expand(id, negate) => {
            if cache.contains_key(&(id, negate)) {
                return;
            }
            let kind = manager.get(id).map(|t| t.kind.clone());

            if !negate {
                match kind {
                    None
                    | Some(
                        TermKind::True
                        | TermKind::False
                        | TermKind::Var(_)
                        | TermKind::IntConst(_)
                        | TermKind::RealConst(_)
                        | TermKind::BitVecConst { .. },
                    ) => {
                        cache.insert((id, false), id);
                    }
                    Some(TermKind::Implies(lhs, rhs)) => {
                        work.push(DnfStep::CombineImplies {
                            id,
                            negate: false,
                            lhs,
                            rhs,
                        });
                        if !cache.contains_key(&(rhs, false)) {
                            work.push(DnfStep::Expand(rhs, false));
                        }
                        if !cache.contains_key(&(lhs, true)) {
                            work.push(DnfStep::Expand(lhs, true));
                        }
                    }
                    Some(TermKind::Not(arg)) => {
                        work.push(DnfStep::Alias {
                            id,
                            negate: false,
                            from: (arg, true),
                        });
                        if !cache.contains_key(&(arg, true)) {
                            work.push(DnfStep::Expand(arg, true));
                        }
                    }
                    Some(TermKind::And(args) | TermKind::Or(args)) => {
                        let is_and =
                            matches!(manager.get(id).map(|t| &t.kind), Some(TermKind::And(_)));
                        let children: SmallVec<[TermId; 4]> = args.iter().copied().collect();
                        work.push(DnfStep::CombineAndOr {
                            id,
                            negate: false,
                            is_and,
                            children: children.clone(),
                        });
                        for &a in children.iter().rev() {
                            if !cache.contains_key(&(a, false)) {
                                work.push(DnfStep::Expand(a, false));
                            }
                        }
                    }
                    Some(_) => {
                        cache.insert((id, false), id);
                    }
                }
            } else {
                match kind {
                    Some(TermKind::True) => {
                        let f = manager.mk_false();
                        cache.insert((id, true), f);
                    }
                    Some(TermKind::False) => {
                        let t = manager.mk_true();
                        cache.insert((id, true), t);
                    }
                    Some(TermKind::Not(inner)) => {
                        work.push(DnfStep::Alias {
                            id,
                            negate: true,
                            from: (inner, false),
                        });
                        if !cache.contains_key(&(inner, false)) {
                            work.push(DnfStep::Expand(inner, false));
                        }
                    }
                    Some(TermKind::And(args) | TermKind::Or(args)) => {
                        let is_and =
                            matches!(manager.get(id).map(|t| &t.kind), Some(TermKind::And(_)));
                        let children: SmallVec<[TermId; 4]> = args.iter().copied().collect();
                        work.push(DnfStep::CombineAndOr {
                            id,
                            negate: true,
                            is_and,
                            children: children.clone(),
                        });
                        for &a in children.iter().rev() {
                            if !cache.contains_key(&(a, true)) {
                                work.push(DnfStep::Expand(a, true));
                            }
                        }
                    }
                    Some(TermKind::Implies(lhs, rhs)) => {
                        work.push(DnfStep::CombineImplies {
                            id,
                            negate: true,
                            lhs,
                            rhs,
                        });
                        if !cache.contains_key(&(rhs, true)) {
                            work.push(DnfStep::Expand(rhs, true));
                        }
                        if !cache.contains_key(&(lhs, false)) {
                            work.push(DnfStep::Expand(lhs, false));
                        }
                    }
                    None | Some(_) => {
                        let result = manager.mk_not(id);
                        cache.insert((id, true), result);
                    }
                }
            }
        }

        DnfStep::Alias { id, negate, from } => {
            let result = cache.get(&from).copied().unwrap_or(id);
            cache.insert((id, negate), result);
        }

        DnfStep::CombineImplies {
            id,
            negate,
            lhs,
            rhs,
        } => {
            let result = if negate {
                // not(a -> b) = a and not(b): a conjunction, so DNF must
                // distribute over it (mirrors the retired to_dnf_not's
                // `distribute_and_over_or_multi(...)`).
                let lhs_dnf = cache.get(&(lhs, false)).copied().unwrap_or(lhs);
                let not_rhs_dnf = cache.get(&(rhs, true)).copied().unwrap_or(rhs);
                distribute_and_over_or_multi(
                    [lhs_dnf, not_rhs_dnf].into_iter().collect(),
                    manager,
                    pair_cache,
                )
            } else {
                // a -> b = not(a) or b: already the OR-of-ANDs shape DNF
                // wants, so no distribution needed (mirrors the retired
                // to_dnf_cached's plain `manager.mk_or(...)`).
                let not_lhs_dnf = cache.get(&(lhs, true)).copied().unwrap_or(lhs);
                let rhs_dnf = cache.get(&(rhs, false)).copied().unwrap_or(rhs);
                manager.mk_or([not_lhs_dnf, rhs_dnf])
            };
            let _ = id;
            cache.insert((id, negate), result);
        }

        DnfStep::CombineAndOr {
            id,
            negate,
            is_and,
            children,
        } => {
            let resolved: SmallVec<[TermId; 4]> = children
                .iter()
                .map(|&c| cache.get(&(c, negate)).copied().unwrap_or(c))
                .collect();
            let result = match (is_and, negate) {
                // And, plain: a conjunction of (possibly disjunctive)
                // DNF'd operands -- must distribute to restore DNF's
                // invariant ("OR of ANDs").
                (true, false) => distribute_and_over_or_multi(resolved, manager, pair_cache),
                // Or, plain: already OR-of-(DNF'd operands) -- no
                // distribution needed.
                (false, false) => manager.mk_or(resolved),
                // not(And): De Morgan gives a disjunction -- already
                // DNF-shaped.
                (true, true) => manager.mk_or(resolved),
                // not(Or): De Morgan gives a conjunction -- must distribute.
                (false, true) => distribute_and_over_or_multi(resolved, manager, pair_cache),
            };
            cache.insert((id, negate), result);
        }
    }
}

/// Distribute AND over OR: (a ∧ b) where a or b might be disjunctions
///
/// If a = (a1 ∨ a2), then (a ∧ b) = (a1 ∧ b) ∨ (a2 ∧ b)
///
/// See `cnf::distribute_or_over_and`'s doc comment: this is its exact mirror
/// image (DNF instead of CNF), including the newly-real `cache`.
fn distribute_and_over_or(
    lhs: TermId,
    rhs: TermId,
    manager: &mut TermManager,
    cache: &mut FxHashMap<(TermId, TermId), TermId>,
) -> TermId {
    if let Some(&result) = cache.get(&(lhs, rhs)) {
        return result;
    }

    let mut work: Vec<DistributeStep> = vec![DistributeStep::Expand(lhs, rhs)];
    while let Some(step) = work.pop() {
        run_dnf_distribute_step(step, manager, cache, &mut work);
    }

    cache
        .get(&(lhs, rhs))
        .copied()
        .unwrap_or_else(|| manager.mk_and([lhs, rhs]))
}

fn run_dnf_distribute_step(
    step: DistributeStep,
    manager: &mut TermManager,
    cache: &mut FxHashMap<(TermId, TermId), TermId>,
    work: &mut Vec<DistributeStep>,
) {
    match step {
        DistributeStep::Expand(lhs, rhs) => {
            if cache.contains_key(&(lhs, rhs)) {
                return;
            }
            let lhs_kind = manager.get(lhs).map(|t| t.kind.clone());
            let rhs_kind = manager.get(rhs).map(|t| t.kind.clone());

            match (lhs_kind, rhs_kind) {
                (Some(TermKind::Or(lhs_args)), _) => {
                    let pairs: SmallVec<[(TermId, TermId); 4]> =
                        lhs_args.iter().map(|&a| (a, rhs)).collect();
                    work.push(DistributeStep::Combine(lhs, rhs, pairs.clone()));
                    for &pair in pairs.iter().rev() {
                        if !cache.contains_key(&pair) {
                            work.push(DistributeStep::Expand(pair.0, pair.1));
                        }
                    }
                }
                (_, Some(TermKind::Or(rhs_args))) => {
                    let pairs: SmallVec<[(TermId, TermId); 4]> =
                        rhs_args.iter().map(|&b| (lhs, b)).collect();
                    work.push(DistributeStep::Combine(lhs, rhs, pairs.clone()));
                    for &pair in pairs.iter().rev() {
                        if !cache.contains_key(&pair) {
                            work.push(DistributeStep::Expand(pair.0, pair.1));
                        }
                    }
                }
                _ => {
                    let result = manager.mk_and([lhs, rhs]);
                    cache.insert((lhs, rhs), result);
                }
            }
        }
        DistributeStep::Combine(lhs, rhs, pairs) => {
            let terms: SmallVec<[TermId; 4]> = pairs
                .iter()
                .map(|pair| {
                    cache
                        .get(pair)
                        .copied()
                        .unwrap_or_else(|| manager.mk_and([pair.0, pair.1]))
                })
                .collect();
            let result = manager.mk_or(terms);
            cache.insert((lhs, rhs), result);
        }
    }
}

/// Distribute AND over OR for multiple conjuncts.
///
/// Already iterative in the original; see `cnf::distribute_or_over_and_multi`.
fn distribute_and_over_or_multi(
    args: SmallVec<[TermId; 4]>,
    manager: &mut TermManager,
    cache: &mut FxHashMap<(TermId, TermId), TermId>,
) -> TermId {
    if args.is_empty() {
        return manager.mk_true();
    }

    if args.len() == 1 {
        return args[0];
    }

    let mut result = args[0];
    for &arg in &args[1..] {
        result = distribute_and_over_or(result, arg, manager, cache);
    }
    result
}

// ========  ========
// DNF shape checks
//
// Not converted: switches to a strictly shallower function at every level
// (is_dnf -> is_term_conjunction -> is_literal), so native call depth is
// bounded by a small constant regardless of the input term's own depth. See
// the parent module's doc comment.
// ========  ========

/// Check if a term is in DNF form
#[must_use]
pub fn is_dnf(term_id: TermId, manager: &TermManager) -> bool {
    match manager.get(term_id).map(|t| &t.kind) {
        None | Some(TermKind::True | TermKind::False | TermKind::Var(_)) => true,

        Some(TermKind::Not(arg)) => {
            // Negation of a literal is OK
            matches!(manager.get(*arg).map(|t| &t.kind), Some(TermKind::Var(_)))
        }

        Some(TermKind::Or(args)) => {
            // OR of terms - each term must be a conjunction of literals
            args.iter().all(|&a| is_term_conjunction(a, manager))
        }

        _ => is_term_conjunction(term_id, manager),
    }
}

/// Check if a term is a conjunction of literals
fn is_term_conjunction(term_id: TermId, manager: &TermManager) -> bool {
    match manager.get(term_id).map(|t| &t.kind) {
        None | Some(TermKind::True | TermKind::False | TermKind::Var(_)) => true,

        Some(TermKind::Not(arg)) => {
            matches!(manager.get(*arg).map(|t| &t.kind), Some(TermKind::Var(_)))
        }

        Some(TermKind::And(args)) => args.iter().all(|&a| is_literal(a, manager)),

        _ => false,
    }
}
