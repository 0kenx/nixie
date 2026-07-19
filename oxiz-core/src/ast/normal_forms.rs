//! Normal form conversions for boolean formulas
//!
//! This module provides utilities for converting boolean formulas to various
//! normal forms such as CNF (Conjunctive Normal Form), DNF (Disjunctive Normal Form),
//! and NNF (Negation Normal Form). Also includes Skolemization for quantifier elimination.

use super::{TermId, TermKind, TermManager};
use crate::interner::Spur;
#[allow(unused_imports)]
use crate::prelude::*;
use crate::sort::SortId;
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
pub fn to_cnf(term_id: TermId, manager: &mut TermManager) -> TermId {
    let mut cache = crate::prelude::FxHashMap::default();
    to_cnf_cached(term_id, manager, &mut cache)
}

fn to_cnf_cached(
    term_id: TermId,
    manager: &mut TermManager,
    cache: &mut crate::prelude::FxHashMap<TermId, TermId>,
) -> TermId {
    if let Some(&result) = cache.get(&term_id) {
        return result;
    }

    let result = match manager.get(term_id).map(|t| t.kind.clone()) {
        None
        | Some(
            TermKind::True
            | TermKind::False
            | TermKind::Var(_)
            | TermKind::IntConst(_)
            | TermKind::RealConst(_)
            | TermKind::BitVecConst { .. },
        ) => term_id,

        // Eliminate implication: (a → b) = (¬a ∨ b)
        Some(TermKind::Implies(lhs, rhs)) => {
            let not_lhs = manager.mk_not(lhs);
            let not_lhs_cnf = to_cnf_cached(not_lhs, manager, cache);
            let rhs_cnf = to_cnf_cached(rhs, manager, cache);
            distribute_or_over_and(not_lhs_cnf, rhs_cnf, manager, cache)
        }

        // Push negation inward
        Some(TermKind::Not(arg)) => to_cnf_not(arg, manager, cache),

        // Convert children and combine
        Some(TermKind::And(args)) => {
            let cnf_args: SmallVec<[TermId; 4]> = args
                .iter()
                .map(|&a| to_cnf_cached(a, manager, cache))
                .collect();
            manager.mk_and(cnf_args)
        }

        Some(TermKind::Or(args)) => {
            let cnf_args: SmallVec<[TermId; 4]> = args
                .iter()
                .map(|&a| to_cnf_cached(a, manager, cache))
                .collect();
            // Distribute OR over AND
            distribute_or_over_and_multi(cnf_args, manager, cache)
        }

        // For other terms, return as-is
        Some(_) => term_id,
    };

    cache.insert(term_id, result);
    result
}

/// Convert ¬term to CNF
fn to_cnf_not(
    term_id: TermId,
    manager: &mut TermManager,
    cache: &mut crate::prelude::FxHashMap<TermId, TermId>,
) -> TermId {
    match manager.get(term_id).map(|t| t.kind.clone()) {
        Some(TermKind::True) => manager.mk_false(),
        Some(TermKind::False) => manager.mk_true(),

        // Double negation: ¬¬a = a
        Some(TermKind::Not(inner)) => to_cnf_cached(inner, manager, cache),

        // De Morgan: ¬(a ∧ b) = ¬a ∨ ¬b
        Some(TermKind::And(args)) => {
            let negated_args: SmallVec<[TermId; 4]> = args
                .iter()
                .map(|&a| {
                    let not_a = manager.mk_not(a);
                    to_cnf_cached(not_a, manager, cache)
                })
                .collect();
            distribute_or_over_and_multi(negated_args, manager, cache)
        }

        // De Morgan: ¬(a ∨ b) = ¬a ∧ ¬b
        Some(TermKind::Or(args)) => {
            let negated_args: SmallVec<[TermId; 4]> = args
                .iter()
                .map(|&a| {
                    let not_a = manager.mk_not(a);
                    to_cnf_cached(not_a, manager, cache)
                })
                .collect();
            manager.mk_and(negated_args)
        }

        // ¬(a → b) = ¬(¬a ∨ b) = a ∧ ¬b
        Some(TermKind::Implies(lhs, rhs)) => {
            let lhs_cnf = to_cnf_cached(lhs, manager, cache);
            let not_rhs = manager.mk_not(rhs);
            let not_rhs_cnf = to_cnf_cached(not_rhs, manager, cache);
            manager.mk_and([lhs_cnf, not_rhs_cnf])
        }

        // For other terms, just negate
        _ => manager.mk_not(term_id),
    }
}

/// Distribute OR over AND: (a ∨ b) where a or b might be conjunctions
///
/// If a = (a1 ∧ a2), then (a ∨ b) = (a1 ∨ b) ∧ (a2 ∨ b)
fn distribute_or_over_and(
    lhs: TermId,
    rhs: TermId,
    manager: &mut TermManager,
    _cache: &mut crate::prelude::FxHashMap<TermId, TermId>,
) -> TermId {
    let lhs_kind = manager.get(lhs).map(|t| t.kind.clone());
    let rhs_kind = manager.get(rhs).map(|t| t.kind.clone());

    match (lhs_kind, rhs_kind) {
        // (a1 ∧ a2 ∧ ...) ∨ b = (a1 ∨ b) ∧ (a2 ∨ b) ∧ ...
        (Some(TermKind::And(lhs_args)), _) => {
            let clauses: SmallVec<[TermId; 4]> = lhs_args
                .iter()
                .map(|&a| distribute_or_over_and(a, rhs, manager, _cache))
                .collect();
            manager.mk_and(clauses)
        }

        // a ∨ (b1 ∧ b2 ∧ ...) = (a ∨ b1) ∧ (a ∨ b2) ∧ ...
        (_, Some(TermKind::And(rhs_args))) => {
            let clauses: SmallVec<[TermId; 4]> = rhs_args
                .iter()
                .map(|&b| distribute_or_over_and(lhs, b, manager, _cache))
                .collect();
            manager.mk_and(clauses)
        }

        // a ∨ b (no distribution needed)
        _ => manager.mk_or([lhs, rhs]),
    }
}

/// Distribute OR over AND for multiple disjuncts
fn distribute_or_over_and_multi(
    args: SmallVec<[TermId; 4]>,
    manager: &mut TermManager,
    cache: &mut crate::prelude::FxHashMap<TermId, TermId>,
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

/// Convert a boolean formula to Disjunctive Normal Form (DNF)
///
/// DNF is a disjunction of conjunctions, where each conjunction is a conjunction of literals.
/// For example: (a ∧ b) ∨ (¬c ∧ d) ∨ e
///
/// # Algorithm
/// 1. Eliminate implications
/// 2. Push negations inward
/// 3. Distribute AND over OR
pub fn to_dnf(term_id: TermId, manager: &mut TermManager) -> TermId {
    let mut cache = crate::prelude::FxHashMap::default();
    to_dnf_cached(term_id, manager, &mut cache)
}

fn to_dnf_cached(
    term_id: TermId,
    manager: &mut TermManager,
    cache: &mut crate::prelude::FxHashMap<TermId, TermId>,
) -> TermId {
    if let Some(&result) = cache.get(&term_id) {
        return result;
    }

    let result = match manager.get(term_id).map(|t| t.kind.clone()) {
        None
        | Some(
            TermKind::True
            | TermKind::False
            | TermKind::Var(_)
            | TermKind::IntConst(_)
            | TermKind::RealConst(_)
            | TermKind::BitVecConst { .. },
        ) => term_id,

        // Eliminate implication: (a → b) = (¬a ∨ b)
        Some(TermKind::Implies(lhs, rhs)) => {
            let not_lhs = manager.mk_not(lhs);
            let not_lhs_dnf = to_dnf_cached(not_lhs, manager, cache);
            let rhs_dnf = to_dnf_cached(rhs, manager, cache);
            manager.mk_or([not_lhs_dnf, rhs_dnf])
        }

        // Push negation inward
        Some(TermKind::Not(arg)) => to_dnf_not(arg, manager, cache),

        // Convert children and combine
        Some(TermKind::Or(args)) => {
            let dnf_args: SmallVec<[TermId; 4]> = args
                .iter()
                .map(|&a| to_dnf_cached(a, manager, cache))
                .collect();
            manager.mk_or(dnf_args)
        }

        Some(TermKind::And(args)) => {
            let dnf_args: SmallVec<[TermId; 4]> = args
                .iter()
                .map(|&a| to_dnf_cached(a, manager, cache))
                .collect();
            // Distribute AND over OR
            distribute_and_over_or_multi(dnf_args, manager, cache)
        }

        // For other terms, return as-is
        Some(_) => term_id,
    };

    cache.insert(term_id, result);
    result
}

/// Convert ¬term to DNF
fn to_dnf_not(
    term_id: TermId,
    manager: &mut TermManager,
    cache: &mut crate::prelude::FxHashMap<TermId, TermId>,
) -> TermId {
    match manager.get(term_id).map(|t| t.kind.clone()) {
        Some(TermKind::True) => manager.mk_false(),
        Some(TermKind::False) => manager.mk_true(),

        // Double negation: ¬¬a = a
        Some(TermKind::Not(inner)) => to_dnf_cached(inner, manager, cache),

        // De Morgan: ¬(a ∧ b) = ¬a ∨ ¬b
        Some(TermKind::And(args)) => {
            let negated_args: SmallVec<[TermId; 4]> = args
                .iter()
                .map(|&a| {
                    let not_a = manager.mk_not(a);
                    to_dnf_cached(not_a, manager, cache)
                })
                .collect();
            manager.mk_or(negated_args)
        }

        // De Morgan: ¬(a ∨ b) = ¬a ∧ ¬b
        Some(TermKind::Or(args)) => {
            let negated_args: SmallVec<[TermId; 4]> = args
                .iter()
                .map(|&a| {
                    let not_a = manager.mk_not(a);
                    to_dnf_cached(not_a, manager, cache)
                })
                .collect();
            distribute_and_over_or_multi(negated_args, manager, cache)
        }

        // ¬(a → b) = a ∧ ¬b
        Some(TermKind::Implies(lhs, rhs)) => {
            let lhs_dnf = to_dnf_cached(lhs, manager, cache);
            let not_rhs = manager.mk_not(rhs);
            let not_rhs_dnf = to_dnf_cached(not_rhs, manager, cache);
            distribute_and_over_or_multi(
                SmallVec::from_vec(vec![lhs_dnf, not_rhs_dnf]),
                manager,
                cache,
            )
        }

        // For other terms, just negate
        _ => manager.mk_not(term_id),
    }
}

/// Distribute AND over OR: (a ∧ b) where a or b might be disjunctions
///
/// If a = (a1 ∨ a2), then (a ∧ b) = (a1 ∧ b) ∨ (a2 ∧ b)
fn distribute_and_over_or(
    lhs: TermId,
    rhs: TermId,
    manager: &mut TermManager,
    _cache: &mut crate::prelude::FxHashMap<TermId, TermId>,
) -> TermId {
    let lhs_kind = manager.get(lhs).map(|t| t.kind.clone());
    let rhs_kind = manager.get(rhs).map(|t| t.kind.clone());

    match (lhs_kind, rhs_kind) {
        // (a1 ∨ a2 ∨ ...) ∧ b = (a1 ∧ b) ∨ (a2 ∧ b) ∨ ...
        (Some(TermKind::Or(lhs_args)), _) => {
            let terms: SmallVec<[TermId; 4]> = lhs_args
                .iter()
                .map(|&a| distribute_and_over_or(a, rhs, manager, _cache))
                .collect();
            manager.mk_or(terms)
        }

        // a ∧ (b1 ∨ b2 ∨ ...) = (a ∧ b1) ∨ (a ∧ b2) ∨ ...
        (_, Some(TermKind::Or(rhs_args))) => {
            let terms: SmallVec<[TermId; 4]> = rhs_args
                .iter()
                .map(|&b| distribute_and_over_or(lhs, b, manager, _cache))
                .collect();
            manager.mk_or(terms)
        }

        // a ∧ b (no distribution needed)
        _ => manager.mk_and([lhs, rhs]),
    }
}

/// Distribute AND over OR for multiple conjuncts
fn distribute_and_over_or_multi(
    args: SmallVec<[TermId; 4]>,
    manager: &mut TermManager,
    cache: &mut crate::prelude::FxHashMap<TermId, TermId>,
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

/// Check if a term is a literal (variable or negated variable)
fn is_literal(term_id: TermId, manager: &TermManager) -> bool {
    match manager.get(term_id).map(|t| &t.kind) {
        Some(TermKind::Var(_)) | Some(TermKind::True) | Some(TermKind::False) => true,

        Some(TermKind::Not(arg)) => {
            matches!(manager.get(*arg).map(|t| &t.kind), Some(TermKind::Var(_)))
        }

        _ => false,
    }
}

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

/// Simplify a boolean formula by eliminating redundant terms
pub fn simplify_boolean(term_id: TermId, manager: &mut TermManager) -> TermId {
    match manager.get(term_id).map(|t| t.kind.clone()) {
        None
        | Some(
            TermKind::True
            | TermKind::False
            | TermKind::Var(_)
            | TermKind::IntConst(_)
            | TermKind::RealConst(_)
            | TermKind::BitVecConst { .. },
        ) => term_id,

        Some(TermKind::Not(arg)) => {
            let simplified = simplify_boolean(arg, manager);
            manager.mk_not(simplified)
        }

        Some(TermKind::And(args)) => {
            let simplified: SmallVec<[TermId; 4]> =
                args.iter().map(|&a| simplify_boolean(a, manager)).collect();
            // Remove duplicates
            let unique: FxHashSet<TermId> = simplified.iter().copied().collect();
            manager.mk_and(unique)
        }

        Some(TermKind::Or(args)) => {
            let simplified: SmallVec<[TermId; 4]> =
                args.iter().map(|&a| simplify_boolean(a, manager)).collect();
            // Remove duplicates
            let unique: FxHashSet<TermId> = simplified.iter().copied().collect();
            manager.mk_or(unique)
        }

        _ => term_id,
    }
}

/// Convert a boolean formula to Negation Normal Form (NNF)
///
/// NNF is a formula where negations only appear directly on variables.
/// This is achieved by:
/// 1. Eliminating implications: (a → b) becomes (¬a ∨ b)
/// 2. Pushing negations inward using De Morgan's laws
///
/// NNF is simpler than CNF/DNF as it doesn't require distribution.
pub fn to_nnf(term_id: TermId, manager: &mut TermManager) -> TermId {
    let mut cache = FxHashMap::default();
    to_nnf_cached(term_id, manager, &mut cache, false)
}

fn to_nnf_cached(
    term_id: TermId,
    manager: &mut TermManager,
    cache: &mut FxHashMap<(TermId, bool), TermId>,
    negate: bool,
) -> TermId {
    if let Some(&result) = cache.get(&(term_id, negate)) {
        return result;
    }

    let result = match manager.get(term_id).map(|t| t.kind.clone()) {
        None => term_id,

        Some(TermKind::True) => {
            if negate {
                manager.mk_false()
            } else {
                manager.mk_true()
            }
        }

        Some(TermKind::False) => {
            if negate {
                manager.mk_true()
            } else {
                manager.mk_false()
            }
        }

        Some(TermKind::Var(_)) => {
            if negate {
                manager.mk_not(term_id)
            } else {
                term_id
            }
        }

        // Double negation
        Some(TermKind::Not(arg)) => to_nnf_cached(arg, manager, cache, !negate),

        // De Morgan's laws when negating
        Some(TermKind::And(args)) => {
            let nnf_args: SmallVec<[TermId; 4]> = args
                .iter()
                .map(|&a| to_nnf_cached(a, manager, cache, negate))
                .collect();

            if negate {
                // ¬(a ∧ b) = ¬a ∨ ¬b
                manager.mk_or(nnf_args)
            } else {
                manager.mk_and(nnf_args)
            }
        }

        Some(TermKind::Or(args)) => {
            let nnf_args: SmallVec<[TermId; 4]> = args
                .iter()
                .map(|&a| to_nnf_cached(a, manager, cache, negate))
                .collect();

            if negate {
                // ¬(a ∨ b) = ¬a ∧ ¬b
                manager.mk_and(nnf_args)
            } else {
                manager.mk_or(nnf_args)
            }
        }

        // Eliminate implication: (a → b) = (¬a ∨ b)
        Some(TermKind::Implies(lhs, rhs)) => {
            let lhs_nnf = to_nnf_cached(lhs, manager, cache, !negate);
            let rhs_nnf = to_nnf_cached(rhs, manager, cache, negate);

            if negate {
                // ¬(a → b) = a ∧ ¬b
                manager.mk_and([lhs_nnf, rhs_nnf])
            } else {
                // (a → b) = ¬a ∨ b
                manager.mk_or([lhs_nnf, rhs_nnf])
            }
        }

        // XOR
        Some(TermKind::Xor(lhs, rhs)) => {
            // a ⊕ b = (a ∨ b) ∧ (¬a ∨ ¬b)
            let lhs_nnf = to_nnf_cached(lhs, manager, cache, false);
            let rhs_nnf = to_nnf_cached(rhs, manager, cache, false);
            let not_lhs_nnf = to_nnf_cached(lhs, manager, cache, true);
            let not_rhs_nnf = to_nnf_cached(rhs, manager, cache, true);

            let clause1 = manager.mk_or([lhs_nnf, rhs_nnf]);
            let clause2 = manager.mk_or([not_lhs_nnf, not_rhs_nnf]);

            let result = manager.mk_and([clause1, clause2]);

            if negate {
                to_nnf_cached(result, manager, cache, true)
            } else {
                result
            }
        }

        // Quantifiers
        Some(TermKind::Forall {
            vars,
            body,
            patterns,
        }) => {
            let body_nnf = to_nnf_cached(body, manager, cache, negate);

            // Resolve strings first to avoid borrowing issues
            let var_names: Vec<_> = vars
                .iter()
                .map(|(s, sort)| (manager.resolve_str(*s).to_string(), *sort))
                .collect();

            if negate {
                // ¬∀x. P(x) = ∃x. ¬P(x)
                manager.mk_exists_with_patterns(
                    var_names.iter().map(|(s, sort)| (s.as_str(), *sort)),
                    body_nnf,
                    patterns,
                )
            } else {
                manager.mk_forall_with_patterns(
                    var_names.iter().map(|(s, sort)| (s.as_str(), *sort)),
                    body_nnf,
                    patterns,
                )
            }
        }

        Some(TermKind::Exists {
            vars,
            body,
            patterns,
        }) => {
            let body_nnf = to_nnf_cached(body, manager, cache, negate);

            // Resolve strings first to avoid borrowing issues
            let var_names: Vec<_> = vars
                .iter()
                .map(|(s, sort)| (manager.resolve_str(*s).to_string(), *sort))
                .collect();

            if negate {
                // ¬∃x. P(x) = ∀x. ¬P(x)
                manager.mk_forall_with_patterns(
                    var_names.iter().map(|(s, sort)| (s.as_str(), *sort)),
                    body_nnf,
                    patterns,
                )
            } else {
                manager.mk_exists_with_patterns(
                    var_names.iter().map(|(s, sort)| (s.as_str(), *sort)),
                    body_nnf,
                    patterns,
                )
            }
        }

        // For other terms, just apply negation if needed
        _ => {
            if negate {
                manager.mk_not(term_id)
            } else {
                term_id
            }
        }
    };

    cache.insert((term_id, negate), result);
    result
}

/// Check if a term is in NNF (Negation Normal Form)
#[must_use]
pub fn is_nnf(term_id: TermId, manager: &TermManager) -> bool {
    is_nnf_impl(term_id, manager, &mut FxHashSet::default())
}

fn is_nnf_impl(term_id: TermId, manager: &TermManager, visited: &mut FxHashSet<TermId>) -> bool {
    if !visited.insert(term_id) {
        return true;
    }

    match manager.get(term_id).map(|t| &t.kind) {
        None | Some(TermKind::True | TermKind::False | TermKind::Var(_)) => true,

        // Negation is only allowed on variables
        Some(TermKind::Not(arg)) => {
            matches!(manager.get(*arg).map(|t| &t.kind), Some(TermKind::Var(_)))
        }

        // Implications not allowed in NNF
        Some(TermKind::Implies(_, _)) => false,

        Some(TermKind::And(args) | TermKind::Or(args)) => {
            args.iter().all(|&a| is_nnf_impl(a, manager, visited))
        }

        Some(TermKind::Forall { body, .. } | TermKind::Exists { body, .. }) => {
            is_nnf_impl(*body, manager, visited)
        }

        // Other terms are considered okay
        _ => true,
    }
}

/// Skolemize a formula by eliminating existential quantifiers.
///
/// Skolemization replaces existentially quantified variables with fresh
/// function symbols (Skolem functions) closed over the enclosing universally
/// quantified variables, preserving equisatisfiability. For example:
/// - `∃x. P(x)` becomes `P(sk!0)`
/// - `∀y. ∃x. P(x, y)` becomes `∀y. P(sk!0(y), y)`
///
/// This mirrors the polarity-aware Skolemization tactic in
/// [`crate::tactic::quantifier::SkolemizationTactic`]. Two correctness
/// requirements are handled:
///
/// 1. **Polarity.** Only *effectively existential* quantifiers are
///    Skolemized: an `Exists` at positive polarity, or a `Forall` at
///    negative polarity (since `¬∀x.φ ≡ ∃x.¬φ`). Effectively *universal*
///    quantifiers keep their binder, and their bound variables become
///    arguments of any inner Skolem functions. Ignoring polarity would turn
///    `¬(∃x.P(x))` into `¬P(sk!0)`, flipping UNSAT into SAT.
/// 2. **Real argument sorts.** Skolem function arguments use the actual
///    sorts of the governing universal variables, not a fixed sort.
///
/// Skolemization only descends through Boolean structure (`Not`, `And`,
/// `Or`, `Implies`, `Ite` branches, and quantifiers). Sub-formulas at
/// genuinely mixed polarity (an `Ite` condition, a Boolean equality) are
/// left untouched rather than Skolemized unsoundly.
///
/// For a single formula this is sufficient. To Skolemize *several*
/// assertions belonging to the same goal, use [`skolemize_with_counter`]
/// with one shared counter across all calls: resetting the counter per
/// assertion would let distinct existentials collide on the same Skolem
/// symbol (e.g. `{∃x.P(x), ∃x.¬P(x)}` collapsing to `{P(sk!0), ¬P(sk!0)}`,
/// flipping SAT into UNSAT).
pub fn skolemize(term_id: TermId, manager: &mut TermManager) -> TermId {
    let mut counter = 0;
    skolemize_with_counter(term_id, manager, &mut counter)
}

/// Skolemize a formula, threading an external fresh-name counter.
///
/// See [`skolemize`] for the algorithm. Use this entry point instead of
/// [`skolemize`] when Skolemizing multiple assertions of the same goal:
/// pass the same `counter` to every call so that Skolem symbols never
/// collide across assertions.
pub fn skolemize_with_counter(
    term_id: TermId,
    manager: &mut TermManager,
    counter: &mut usize,
) -> TermId {
    let governing: Vec<(Spur, SortId)> = Vec::new();
    skolemize_polar(term_id, manager, true, &governing, counter)
}

/// Polarity-aware Skolemization.
///
/// `positive` is the polarity of `term_id` in the enclosing formula
/// (top-level formulas start positive). `governing` lists the
/// effectively-universal variables currently in scope, with their real
/// sorts, used as Skolem-function arguments.
fn skolemize_polar(
    term_id: TermId,
    manager: &mut TermManager,
    positive: bool,
    governing: &[(Spur, SortId)],
    counter: &mut usize,
) -> TermId {
    let kind = match manager.get(term_id) {
        Some(t) => t.kind.clone(),
        None => return term_id,
    };

    match kind {
        TermKind::Not(arg) => {
            let sk = skolemize_polar(arg, manager, !positive, governing, counter);
            manager.mk_not(sk)
        }

        TermKind::And(args) => {
            let new_args: SmallVec<[TermId; 4]> = args
                .iter()
                .map(|&a| skolemize_polar(a, manager, positive, governing, counter))
                .collect();
            manager.mk_and(new_args)
        }

        TermKind::Or(args) => {
            let new_args: SmallVec<[TermId; 4]> = args
                .iter()
                .map(|&a| skolemize_polar(a, manager, positive, governing, counter))
                .collect();
            manager.mk_or(new_args)
        }

        TermKind::Implies(lhs, rhs) => {
            // Antecedent is at flipped polarity, consequent keeps polarity.
            let sk_lhs = skolemize_polar(lhs, manager, !positive, governing, counter);
            let sk_rhs = skolemize_polar(rhs, manager, positive, governing, counter);
            manager.mk_implies(sk_lhs, sk_rhs)
        }

        TermKind::Ite(cond, then_br, else_br) => {
            // `cond` occurs at mixed polarity (both c and ¬c); leave it
            // untouched. Both branches preserve the ambient polarity.
            let sk_then = skolemize_polar(then_br, manager, positive, governing, counter);
            let sk_else = skolemize_polar(else_br, manager, positive, governing, counter);
            manager.mk_ite(cond, sk_then, sk_else)
        }

        TermKind::Forall {
            vars,
            body,
            patterns,
        } => {
            if positive {
                // Effectively universal: keep binder, extend governing set.
                skolemize_universal(
                    &vars, body, &patterns, true, positive, manager, governing, counter,
                )
            } else {
                // ¬∀x.φ ≡ ∃x.¬φ: effectively existential, Skolemize it.
                skolemize_existential(&vars, body, positive, manager, governing, counter)
            }
        }

        TermKind::Exists {
            vars,
            body,
            patterns,
        } => {
            if positive {
                // Effectively existential: Skolemize.
                skolemize_existential(&vars, body, positive, manager, governing, counter)
            } else {
                // ¬∃x.φ ≡ ∀x.¬φ: effectively universal, keep binder.
                skolemize_universal(
                    &vars, body, &patterns, false, positive, manager, governing, counter,
                )
            }
        }

        // Atoms and mixed-polarity contexts (Boolean equalities, arithmetic,
        // uninterpreted applications, …) are left unchanged: they cannot be
        // Skolemized soundly without polarity information we do not have
        // here, and leaving them intact keeps the result equisatisfiable.
        _ => term_id,
    }
}

/// Skolemize an effectively-existential quantifier: replace each bound
/// variable with a fresh Skolem term over the governing universals, drop
/// the binder, and recurse into the substituted body.
fn skolemize_existential(
    vars: &[(Spur, SortId)],
    body: TermId,
    positive: bool,
    manager: &mut TermManager,
    governing: &[(Spur, SortId)],
    counter: &mut usize,
) -> TermId {
    let mut subst = FxHashMap::default();
    for &(var_name, var_sort) in vars {
        let var_name_str = manager.resolve_str(var_name).to_string();
        let var_id = manager.mk_var(&var_name_str, var_sort);
        let skolem_term = make_skolem_term(var_sort, manager, governing, counter);
        subst.insert(var_id, skolem_term);
    }

    // Substitution is capture-avoiding, so Skolem terms (closed over the
    // governing universals) cannot be captured by inner binders.
    let substituted = manager.substitute(body, &subst);
    skolemize_polar(substituted, manager, positive, governing, counter)
}

/// Handle an effectively-universal quantifier: keep the binder, add its
/// variables to the governing set, and recurse into the body.
#[allow(clippy::too_many_arguments)]
fn skolemize_universal(
    vars: &[(Spur, SortId)],
    body: TermId,
    patterns: &[SmallVec<[TermId; 2]>],
    is_forall: bool,
    positive: bool,
    manager: &mut TermManager,
    governing: &[(Spur, SortId)],
    counter: &mut usize,
) -> TermId {
    let mut gov = governing.to_vec();
    gov.extend(vars.iter().copied());
    let sk_body = skolemize_polar(body, manager, positive, &gov, counter);

    let var_names: Vec<_> = vars
        .iter()
        .map(|(n, s)| (manager.resolve_str(*n).to_string(), *s))
        .collect();
    let var_strs: Vec<_> = var_names
        .iter()
        .map(|(name, sort)| (name.as_str(), *sort))
        .collect();
    let patterns_owned: SmallVec<[SmallVec<[TermId; 2]>; 2]> = patterns.iter().cloned().collect();
    if is_forall {
        manager.mk_forall_with_patterns(var_strs, sk_body, patterns_owned)
    } else {
        manager.mk_exists_with_patterns(var_strs, sk_body, patterns_owned)
    }
}

/// Build the Skolem term for a variable of sort `var_sort`: a fresh
/// constant when no universals govern it, otherwise a fresh function
/// applied to the governing universal variables (using their real sorts).
fn make_skolem_term(
    var_sort: SortId,
    manager: &mut TermManager,
    governing: &[(Spur, SortId)],
    counter: &mut usize,
) -> TermId {
    let skolem_name = format!("sk!{}", *counter);
    *counter += 1;

    if governing.is_empty() {
        manager.mk_var(&skolem_name, var_sort)
    } else {
        let gov_names: Vec<_> = governing
            .iter()
            .map(|(n, s)| (manager.resolve_str(*n).to_string(), *s))
            .collect();
        let arg_ids: SmallVec<[TermId; 4]> = gov_names
            .iter()
            .map(|(name, sort)| manager.mk_var(name, *sort))
            .collect();
        manager.mk_apply(&skolem_name, arg_ids, var_sort)
    }
}

/// Eliminate universal quantifiers by replacing them with fresh variables
///
/// This is useful for converting formulas to quantifier-free form when
/// combined with Skolemization. The formula should have existential
/// quantifiers eliminated first (via Skolemization).
pub fn eliminate_universal_quantifiers(term_id: TermId, manager: &mut TermManager) -> TermId {
    let mut counter = 0;
    eliminate_universal_impl(term_id, manager, &mut counter)
}

fn eliminate_universal_impl(
    term_id: TermId,
    manager: &mut TermManager,
    counter: &mut usize,
) -> TermId {
    match manager.get(term_id).map(|t| t.kind.clone()) {
        None
        | Some(
            TermKind::True
            | TermKind::False
            | TermKind::Var(_)
            | TermKind::IntConst(_)
            | TermKind::RealConst(_)
            | TermKind::BitVecConst { .. },
        ) => term_id,

        Some(TermKind::Not(arg)) => {
            let new_arg = eliminate_universal_impl(arg, manager, counter);
            manager.mk_not(new_arg)
        }

        Some(TermKind::And(args)) => {
            let new_args: SmallVec<[TermId; 4]> = args
                .iter()
                .map(|&a| eliminate_universal_impl(a, manager, counter))
                .collect();
            manager.mk_and(new_args)
        }

        Some(TermKind::Or(args)) => {
            let new_args: SmallVec<[TermId; 4]> = args
                .iter()
                .map(|&a| eliminate_universal_impl(a, manager, counter))
                .collect();
            manager.mk_or(new_args)
        }

        Some(TermKind::Forall { vars, body, .. }) => {
            // Replace quantified vars with fresh constants
            let mut subst = FxHashMap::default();

            for (var_name, var_sort) in &vars {
                let fresh_name = format!("u_{}", counter);
                *counter += 1;

                // Resolve string first to avoid borrowing issues
                let var_name_str = manager.resolve_str(*var_name).to_string();

                let var_id = manager.mk_var(&var_name_str, *var_sort);
                let fresh_var = manager.mk_var(&fresh_name, *var_sort);

                subst.insert(var_id, fresh_var);
            }

            let substituted = manager.substitute(body, &subst);
            eliminate_universal_impl(substituted, manager, counter)
        }

        _ => term_id,
    }
}
