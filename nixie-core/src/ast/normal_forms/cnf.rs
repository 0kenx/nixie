//! Conjunctive Normal Form (CNF) conversion.
//!
//! Split out of `ast/normal_forms.rs`; see that module's doc comment for the
//! general iterative-conversion rationale and the exponential-blowup /
//! now-real-memoization notes that apply to [`distribute_or_over_and`].

use super::super::{TermId, TermKind, TermManager};
use super::{DistributeStep, is_literal};
#[allow(unused_imports)]
use crate::prelude::*;
use smallvec::SmallVec;

/// Convert a boolean formula to Conjunctive Normal Form (CNF)
///
/// CNF is a conjunction of clauses, where each clause is a disjunction of literals.
/// For example: (a ∨ b) ∧ (¬c ∨ d) ∧ e
///
/// # Algorithm
/// 1. Eliminate implications: (a → b) becomes (¬a ∨ b)
/// 2. Push negations inward (De Morgan's laws)
/// 3. Distribute OR over AND
///
/// See the module doc comment for why this can blow up exponentially in the
/// worst case (an inherent property of naive, non-Tseitin CNF distribution),
/// and for the iterative conversion this function is now part of.
pub fn to_cnf(term_id: TermId, manager: &mut TermManager) -> TermId {
    let mut cache: FxHashMap<(TermId, bool), TermId> = FxHashMap::default();
    let mut pair_cache: FxHashMap<(TermId, TermId), TermId> = FxHashMap::default();
    run_to_cnf(term_id, false, manager, &mut cache, &mut pair_cache)
}

/// One pending step of the iterative CNF walk. `negate = false` computes
/// what the retired recursive `to_cnf_cached` computed; `negate = true`
/// computes what the retired recursive `to_cnf_not` computed (`to_cnf` of
/// `Not(id)`, without ever constructing that `Not` term) -- both are unified
/// into one `(TermId, bool)`-keyed walk, mirroring `to_nnf_cached`'s
/// existing `(TermId, bool)` cache shape elsewhere in this file.
enum CnfStep {
    /// Resolve `(id, negate)`'s CNF value, scheduling whatever combine step
    /// and children are needed. A no-op if already cached.
    Expand(TermId, bool),
    /// Copy an already-resolved `(from.0, from.1)` result to also be
    /// `(id, negate)`'s result -- used for double-negation and the
    /// `Not(arg)` cases, which are pure aliases with no rebuilding.
    Alias {
        id: TermId,
        negate: bool,
        from: (TermId, bool),
    },
    /// Combine an `Implies(lhs, rhs)` node. Which combinator applies
    /// depends on `negate` (see `to_cnf`'s module-level algorithm comment
    /// and this step's handling in `run_cnf_step`): distribution is only
    /// needed on the side whose natural shape is a disjunction, since CNF's
    /// invariant is "AND of ORs".
    CombineImplies {
        id: TermId,
        negate: bool,
        lhs: TermId,
        rhs: TermId,
    },
    /// Combine an `And`/`Or` node's already-resolved children (`is_and`
    /// records which). Mirrors `to_cnf_cached`'s `And`/`Or` arms
    /// (`negate = false`) and `to_cnf_not`'s De Morgan `And`/`Or` arms
    /// (`negate = true`).
    CombineAndOr {
        id: TermId,
        negate: bool,
        is_and: bool,
        children: SmallVec<[TermId; 4]>,
    },
}

/// Iterative driver shared by [`to_cnf`] (`negate = false`) and what the
/// retired recursive `to_cnf_not` computed (`negate = true`).
fn run_to_cnf(
    term_id: TermId,
    negate: bool,
    manager: &mut TermManager,
    cache: &mut FxHashMap<(TermId, bool), TermId>,
    pair_cache: &mut FxHashMap<(TermId, TermId), TermId>,
) -> TermId {
    if let Some(&result) = cache.get(&(term_id, negate)) {
        return result;
    }

    let mut work: Vec<CnfStep> = vec![CnfStep::Expand(term_id, negate)];
    while let Some(step) = work.pop() {
        run_cnf_step(step, manager, cache, pair_cache, &mut work);
    }

    cache.get(&(term_id, negate)).copied().unwrap_or(term_id)
}

/// Dispatch one [`CnfStep`].
#[allow(clippy::too_many_lines)]
fn run_cnf_step(
    step: CnfStep,
    manager: &mut TermManager,
    cache: &mut FxHashMap<(TermId, bool), TermId>,
    pair_cache: &mut FxHashMap<(TermId, TermId), TermId>,
    work: &mut Vec<CnfStep>,
) {
    match step {
        CnfStep::Expand(id, negate) => {
            if cache.contains_key(&(id, negate)) {
                return;
            }
            let kind = manager.get(id).map(|t| t.kind.clone());

            if !negate {
                // ======== to_cnf_cached (plain) ========
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
                        work.push(CnfStep::CombineImplies {
                            id,
                            negate: false,
                            lhs,
                            rhs,
                        });
                        if !cache.contains_key(&(rhs, false)) {
                            work.push(CnfStep::Expand(rhs, false));
                        }
                        if !cache.contains_key(&(lhs, true)) {
                            work.push(CnfStep::Expand(lhs, true));
                        }
                    }
                    Some(TermKind::Not(arg)) => {
                        work.push(CnfStep::Alias {
                            id,
                            negate: false,
                            from: (arg, true),
                        });
                        if !cache.contains_key(&(arg, true)) {
                            work.push(CnfStep::Expand(arg, true));
                        }
                    }
                    Some(TermKind::And(args) | TermKind::Or(args)) => {
                        let is_and =
                            matches!(manager.get(id).map(|t| &t.kind), Some(TermKind::And(_)));
                        let children: SmallVec<[TermId; 4]> = args.iter().copied().collect();
                        work.push(CnfStep::CombineAndOr {
                            id,
                            negate: false,
                            is_and,
                            children: children.clone(),
                        });
                        for &a in children.iter().rev() {
                            if !cache.contains_key(&(a, false)) {
                                work.push(CnfStep::Expand(a, false));
                            }
                        }
                    }
                    // "For other terms, return as-is."
                    Some(_) => {
                        cache.insert((id, false), id);
                    }
                }
            } else {
                // ======== to_cnf_not (CNF of Not(id)) ========
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
                        // Double negation: to_cnf(Not(Not(inner))) = to_cnf(inner).
                        work.push(CnfStep::Alias {
                            id,
                            negate: true,
                            from: (inner, false),
                        });
                        if !cache.contains_key(&(inner, false)) {
                            work.push(CnfStep::Expand(inner, false));
                        }
                    }
                    Some(TermKind::And(args) | TermKind::Or(args)) => {
                        let is_and =
                            matches!(manager.get(id).map(|t| &t.kind), Some(TermKind::And(_)));
                        let children: SmallVec<[TermId; 4]> = args.iter().copied().collect();
                        work.push(CnfStep::CombineAndOr {
                            id,
                            negate: true,
                            is_and,
                            children: children.clone(),
                        });
                        for &a in children.iter().rev() {
                            if !cache.contains_key(&(a, true)) {
                                work.push(CnfStep::Expand(a, true));
                            }
                        }
                    }
                    Some(TermKind::Implies(lhs, rhs)) => {
                        // not(a -> b) = a and not(b)
                        work.push(CnfStep::CombineImplies {
                            id,
                            negate: true,
                            lhs,
                            rhs,
                        });
                        if !cache.contains_key(&(rhs, true)) {
                            work.push(CnfStep::Expand(rhs, true));
                        }
                        if !cache.contains_key(&(lhs, false)) {
                            work.push(CnfStep::Expand(lhs, false));
                        }
                    }
                    // "For other terms, just negate."
                    None | Some(_) => {
                        let result = manager.mk_not(id);
                        cache.insert((id, true), result);
                    }
                }
            }
        }

        CnfStep::Alias { id, negate, from } => {
            let result = cache.get(&from).copied().unwrap_or(id);
            cache.insert((id, negate), result);
        }

        CnfStep::CombineImplies {
            id,
            negate,
            lhs,
            rhs,
        } => {
            let result = if negate {
                // not(a -> b) = a and not(b): already the AND-of-ORs shape
                // CNF wants, so no distribution needed (mirrors the
                // retired to_cnf_not's plain `manager.mk_and(...)`).
                let lhs_cnf = cache.get(&(lhs, false)).copied().unwrap_or(lhs);
                let not_rhs_cnf = cache.get(&(rhs, true)).copied().unwrap_or(rhs);
                manager.mk_and([lhs_cnf, not_rhs_cnf])
            } else {
                // a -> b = not(a) or b: a disjunction, so CNF must
                // distribute over it (mirrors the retired to_cnf_cached's
                // `distribute_or_over_and(...)`).
                let not_lhs_cnf = cache.get(&(lhs, true)).copied().unwrap_or(lhs);
                let rhs_cnf = cache.get(&(rhs, false)).copied().unwrap_or(rhs);
                distribute_or_over_and(not_lhs_cnf, rhs_cnf, manager, pair_cache)
            };
            let _ = id;
            cache.insert((id, negate), result);
        }

        CnfStep::CombineAndOr {
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
                // And, plain: already AND-of-(CNF'd operands) -- CNF'd
                // operands are themselves AND-of-ORs or ORs, and mk_and
                // over a mix thereof stays a conjunction, matching CNF's
                // invariant, so no distribution is needed.
                (true, false) => manager.mk_and(resolved),
                // Or, plain: a disjunction of (possibly conjunctive) CNF'd
                // operands -- must distribute to restore CNF's invariant.
                (false, false) => distribute_or_over_and_multi(resolved, manager, pair_cache),
                // not(And): De Morgan gives a disjunction -- must distribute.
                (true, true) => distribute_or_over_and_multi(resolved, manager, pair_cache),
                // not(Or): De Morgan gives a conjunction -- already CNF-shaped.
                (false, true) => manager.mk_and(resolved),
            };
            cache.insert((id, negate), result);
        }
    }
}

/// Distribute OR over AND: (a ∨ b) where a or b might be conjunctions
///
/// If a = (a1 ∧ a2), then (a ∨ b) = (a1 ∨ b) ∧ (a2 ∨ b)
///
/// Uses an explicit heap stack rather than native recursion (the previous
/// recursive version's own depth was bounded only by how deeply nested the
/// `And` structures it distributes over are -- themselves already-CNF'd
/// results, whose nesting is not bounded by the *original* input term's
/// depth alone). `cache` memoizes `(lhs, rhs)` pairs already distributed:
/// the previous version took an identically-shaped `_cache` parameter that
/// was declared but never read (no memoization at all), so the same pair
/// reached via two different callers recomputed its distribution from
/// scratch every time; this is a pure function of `(lhs, rhs)` (only
/// reachable via `manager.get`, `mk_and`/`mk_or`, all deterministic
/// hash-consing operations), so memoizing cannot change the result, only
/// avoid redundant recomputation. See the module doc comment for why this
/// does not, and cannot, bound the worst-case *output size*.
fn distribute_or_over_and(
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
        run_distribute_step(step, manager, cache, &mut work);
    }

    cache
        .get(&(lhs, rhs))
        .copied()
        .unwrap_or_else(|| manager.mk_or([lhs, rhs]))
}

fn run_distribute_step(
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
                (Some(TermKind::And(lhs_args)), _) => {
                    let pairs: SmallVec<[(TermId, TermId); 4]> =
                        lhs_args.iter().map(|&a| (a, rhs)).collect();
                    work.push(DistributeStep::Combine(lhs, rhs, pairs.clone()));
                    for &pair in pairs.iter().rev() {
                        if !cache.contains_key(&pair) {
                            work.push(DistributeStep::Expand(pair.0, pair.1));
                        }
                    }
                }
                (_, Some(TermKind::And(rhs_args))) => {
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
                    let result = manager.mk_or([lhs, rhs]);
                    cache.insert((lhs, rhs), result);
                }
            }
        }
        DistributeStep::Combine(lhs, rhs, pairs) => {
            let clauses: SmallVec<[TermId; 4]> = pairs
                .iter()
                .map(|pair| {
                    cache
                        .get(pair)
                        .copied()
                        .unwrap_or_else(|| manager.mk_or([pair.0, pair.1]))
                })
                .collect();
            let result = manager.mk_and(clauses);
            cache.insert((lhs, rhs), result);
        }
    }
}

/// Distribute OR over AND for multiple disjuncts.
///
/// Already iterative in the original (a plain fold over
/// [`distribute_or_over_and`], never recursive itself), so this needed no
/// conversion -- kept as-is beyond threading the now-real `cache`.
fn distribute_or_over_and_multi(
    args: SmallVec<[TermId; 4]>,
    manager: &mut TermManager,
    cache: &mut FxHashMap<(TermId, TermId), TermId>,
) -> TermId {
    if args.is_empty() {
        return manager.mk_false();
    }

    if args.len() == 1 {
        return args[0];
    }

    let mut result = args[0];
    for &arg in &args[1..] {
        result = distribute_or_over_and(result, arg, manager, cache);
    }
    result
}

// ========  ========
// CNF shape checks and clause extraction
//
// Not converted: each of these switches to a strictly shallower function at
// every level (is_cnf -> is_clause -> is_literal; extract_cnf_clauses ->
// extract_clause_literals), so native call depth is bounded by a small
// constant regardless of the input term's own depth. See the module doc
// comment.
// ========  ========

/// Check if a term is in CNF form
#[must_use]
pub fn is_cnf(term_id: TermId, manager: &TermManager) -> bool {
    match manager.get(term_id).map(|t| &t.kind) {
        None | Some(TermKind::True | TermKind::False | TermKind::Var(_)) => true,

        Some(TermKind::Not(arg)) => {
            // Negation of a literal is OK
            matches!(manager.get(*arg).map(|t| &t.kind), Some(TermKind::Var(_)))
        }

        Some(TermKind::And(args)) => {
            // AND of clauses - each clause must be a disjunction of literals
            args.iter().all(|&a| is_clause(a, manager))
        }

        _ => is_clause(term_id, manager),
    }
}

/// Check if a term is a clause (disjunction of literals)
fn is_clause(term_id: TermId, manager: &TermManager) -> bool {
    match manager.get(term_id).map(|t| &t.kind) {
        None | Some(TermKind::True | TermKind::False | TermKind::Var(_)) => true,

        Some(TermKind::Not(arg)) => {
            // Negation of a literal
            matches!(manager.get(*arg).map(|t| &t.kind), Some(TermKind::Var(_)))
        }

        Some(TermKind::Or(args)) => {
            // OR of literals
            args.iter().all(|&a| is_literal(a, manager))
        }

        _ => false,
    }
}

/// Extract clauses from a CNF formula
///
/// Returns a vector of clauses, where each clause is a vector of literals
#[must_use]
pub fn extract_cnf_clauses(term_id: TermId, manager: &TermManager) -> Vec<Vec<TermId>> {
    let mut clauses = Vec::new();

    match manager.get(term_id).map(|t| &t.kind) {
        Some(TermKind::And(args)) => {
            for &arg in args {
                clauses.push(extract_clause_literals(arg, manager));
            }
        }
        _ => {
            clauses.push(extract_clause_literals(term_id, manager));
        }
    }

    clauses
}

/// Extract literals from a clause (disjunction)
fn extract_clause_literals(term_id: TermId, manager: &TermManager) -> Vec<TermId> {
    match manager.get(term_id).map(|t| &t.kind) {
        Some(TermKind::Or(args)) => args.iter().copied().collect(),
        _ => vec![term_id],
    }
}
