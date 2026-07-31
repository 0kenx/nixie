//! Boolean simplification and Negation Normal Form (NNF) conversion.
//!
//! Split out of `ast/normal_forms.rs`; see that module's doc comment for the
//! general iterative-conversion rationale.

use super::super::{TermId, TermKind, TermManager};
use crate::interner::Spur;
#[allow(unused_imports)]
use crate::prelude::*;
use crate::sort::SortId;
use smallvec::SmallVec;

// ===========================================================================
// Boolean simplification
// ===========================================================================

/// Simplify a boolean formula by eliminating redundant terms.
///
/// Uses an explicit heap stack rather than native recursion (see the parent
/// module's doc comment). The original had no memoization at all; `cache`
/// (keyed by plain `TermId`, since this pass carries no polarity/negation
/// state) is added as a direct byproduct of converting to a post-order walk
/// -- safe because `manager.get`/`mk_not`/`mk_and`/`mk_or` are deterministic
/// hash-consing operations, so memoizing cannot change any result, only
/// avoid recomputing an identical shared subterm reached from two parents.
pub fn simplify_boolean(term_id: TermId, manager: &mut TermManager) -> TermId {
    let mut cache: FxHashMap<TermId, TermId> = FxHashMap::default();
    if let Some(&result) = cache.get(&term_id) {
        return result;
    }

    let mut stack: Vec<(TermId, bool)> = vec![(term_id, false)];
    while let Some((current, expanded)) = stack.pop() {
        if cache.contains_key(&current) {
            continue;
        }
        if expanded {
            let result = combine_simplify_boolean(current, manager, &cache);
            cache.insert(current, result);
        } else {
            let children = simplify_boolean_children(current, manager);
            stack.push((current, true));
            for &child in children.iter().rev() {
                if !cache.contains_key(&child) {
                    stack.push((child, false));
                }
            }
        }
    }

    cache.get(&term_id).copied().unwrap_or(term_id)
}

/// Children `simplify_boolean` recurses into for `id`, or none for a leaf
/// or any kind it does not touch (matching the original's implicit `_ =>
/// term_id` catch-all, which never visited such a node's children).
fn simplify_boolean_children(id: TermId, manager: &TermManager) -> SmallVec<[TermId; 4]> {
    match manager.get(id).map(|t| &t.kind) {
        Some(TermKind::Not(arg)) => [*arg].into_iter().collect(),
        Some(TermKind::And(args) | TermKind::Or(args)) => args.iter().copied().collect(),
        _ => SmallVec::new(),
    }
}

/// Rebuild `id` from its already-simplified children.
fn combine_simplify_boolean(
    id: TermId,
    manager: &mut TermManager,
    cache: &FxHashMap<TermId, TermId>,
) -> TermId {
    let sub = |t: TermId| cache.get(&t).copied().unwrap_or(t);
    match manager.get(id).map(|t| t.kind.clone()) {
        None
        | Some(
            TermKind::True
            | TermKind::False
            | TermKind::Var(_)
            | TermKind::IntConst(_)
            | TermKind::RealConst(_)
            | TermKind::BitVecConst { .. },
        ) => id,

        Some(TermKind::Not(arg)) => {
            let simplified = sub(arg);
            manager.mk_not(simplified)
        }

        Some(TermKind::And(args)) => {
            let simplified: SmallVec<[TermId; 4]> = args.iter().map(|&a| sub(a)).collect();
            // Remove duplicates -- matches the original exactly, including
            // its loss of argument order once collected into a hash set.
            let unique: FxHashSet<TermId> = simplified.iter().copied().collect();
            manager.mk_and(unique)
        }

        Some(TermKind::Or(args)) => {
            let simplified: SmallVec<[TermId; 4]> = args.iter().map(|&a| sub(a)).collect();
            let unique: FxHashSet<TermId> = simplified.iter().copied().collect();
            manager.mk_or(unique)
        }

        _ => id,
    }
}

// ===========================================================================
// NNF
// ===========================================================================

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
    run_to_nnf(term_id, manager, &mut cache, false)
}

/// One pending step of the iterative NNF walk, using an explicit heap stack
/// rather than native recursion (see the parent module's doc comment).
enum NnfStep {
    Expand(TermId, bool),
    Alias {
        id: TermId,
        negate: bool,
        from: (TermId, bool),
    },
    CombineAndOr {
        id: TermId,
        negate: bool,
        is_and: bool,
        children: SmallVec<[TermId; 4]>,
    },
    CombineImplies {
        id: TermId,
        negate: bool,
        lhs: TermId,
        rhs: TermId,
    },
    /// After the four sub-computations `to_nnf(lhs,false)`,
    /// `to_nnf(rhs,false)`, `to_nnf(lhs,true)`, `to_nnf(rhs,true)` are all
    /// resolved, build `and(or(lhs_nnf,rhs_nnf), or(not_lhs_nnf,
    /// not_rhs_nnf))`. If `negate` is false that built term *is* the
    /// answer; if `negate` is true the original recursively re-entered
    /// `to_nnf_cached(result, cache, true)` on it (to push the outer
    /// negation through the freshly built structure), so this schedules
    /// exactly that as a follow-up `Expand` and defers to
    /// [`NnfStep::CombineXorFinal`] to read its result back.
    CombineXorBuilt {
        id: TermId,
        negate: bool,
        lhs: TermId,
        rhs: TermId,
    },
    CombineXorFinal {
        id: TermId,
        negate: bool,
        built: TermId,
    },
    CombineQuantifier {
        id: TermId,
        negate: bool,
        is_forall: bool,
        vars: SmallVec<[(Spur, SortId); 2]>,
        patterns: SmallVec<[SmallVec<[TermId; 2]>; 2]>,
        body: TermId,
    },
}

fn run_to_nnf(
    term_id: TermId,
    manager: &mut TermManager,
    cache: &mut FxHashMap<(TermId, bool), TermId>,
    negate: bool,
) -> TermId {
    if let Some(&result) = cache.get(&(term_id, negate)) {
        return result;
    }

    let mut work: Vec<NnfStep> = vec![NnfStep::Expand(term_id, negate)];
    while let Some(step) = work.pop() {
        run_nnf_step(step, manager, cache, &mut work);
    }

    cache.get(&(term_id, negate)).copied().unwrap_or(term_id)
}

#[allow(clippy::too_many_lines)]
fn run_nnf_step(
    step: NnfStep,
    manager: &mut TermManager,
    cache: &mut FxHashMap<(TermId, bool), TermId>,
    work: &mut Vec<NnfStep>,
) {
    match step {
        NnfStep::Expand(id, negate) => {
            if cache.contains_key(&(id, negate)) {
                return;
            }
            match manager.get(id).map(|t| t.kind.clone()) {
                None => {
                    cache.insert((id, negate), id);
                }
                Some(TermKind::True) => {
                    let result = if negate {
                        manager.mk_false()
                    } else {
                        manager.mk_true()
                    };
                    cache.insert((id, negate), result);
                }
                Some(TermKind::False) => {
                    let result = if negate {
                        manager.mk_true()
                    } else {
                        manager.mk_false()
                    };
                    cache.insert((id, negate), result);
                }
                Some(TermKind::Var(_)) => {
                    let result = if negate { manager.mk_not(id) } else { id };
                    cache.insert((id, negate), result);
                }
                Some(TermKind::Not(arg)) => {
                    work.push(NnfStep::Alias {
                        id,
                        negate,
                        from: (arg, !negate),
                    });
                    if !cache.contains_key(&(arg, !negate)) {
                        work.push(NnfStep::Expand(arg, !negate));
                    }
                }
                Some(TermKind::And(args) | TermKind::Or(args)) => {
                    let is_and = matches!(manager.get(id).map(|t| &t.kind), Some(TermKind::And(_)));
                    let children: SmallVec<[TermId; 4]> = args.iter().copied().collect();
                    work.push(NnfStep::CombineAndOr {
                        id,
                        negate,
                        is_and,
                        children: children.clone(),
                    });
                    for &a in children.iter().rev() {
                        if !cache.contains_key(&(a, negate)) {
                            work.push(NnfStep::Expand(a, negate));
                        }
                    }
                }
                Some(TermKind::Implies(lhs, rhs)) => {
                    work.push(NnfStep::CombineImplies {
                        id,
                        negate,
                        lhs,
                        rhs,
                    });
                    if !cache.contains_key(&(rhs, negate)) {
                        work.push(NnfStep::Expand(rhs, negate));
                    }
                    if !cache.contains_key(&(lhs, !negate)) {
                        work.push(NnfStep::Expand(lhs, !negate));
                    }
                }
                Some(TermKind::Xor(lhs, rhs)) => {
                    work.push(NnfStep::CombineXorBuilt {
                        id,
                        negate,
                        lhs,
                        rhs,
                    });
                    for &(t, n) in &[(lhs, false), (rhs, false), (lhs, true), (rhs, true)] {
                        if !cache.contains_key(&(t, n)) {
                            work.push(NnfStep::Expand(t, n));
                        }
                    }
                }
                Some(TermKind::Forall {
                    vars,
                    body,
                    patterns,
                }) => {
                    work.push(NnfStep::CombineQuantifier {
                        id,
                        negate,
                        is_forall: true,
                        vars,
                        patterns,
                        body,
                    });
                    if !cache.contains_key(&(body, negate)) {
                        work.push(NnfStep::Expand(body, negate));
                    }
                }
                Some(TermKind::Exists {
                    vars,
                    body,
                    patterns,
                }) => {
                    work.push(NnfStep::CombineQuantifier {
                        id,
                        negate,
                        is_forall: false,
                        vars,
                        patterns,
                        body,
                    });
                    if !cache.contains_key(&(body, negate)) {
                        work.push(NnfStep::Expand(body, negate));
                    }
                }
                Some(_) => {
                    let result = if negate { manager.mk_not(id) } else { id };
                    cache.insert((id, negate), result);
                }
            }
        }

        NnfStep::Alias { id, negate, from } => {
            let result = cache.get(&from).copied().unwrap_or(id);
            cache.insert((id, negate), result);
        }

        NnfStep::CombineAndOr {
            id,
            negate,
            is_and,
            children,
        } => {
            let nnf_args: SmallVec<[TermId; 4]> = children
                .iter()
                .map(|&c| cache.get(&(c, negate)).copied().unwrap_or(c))
                .collect();
            // De Morgan's laws when negating (see the original's `And`/`Or`
            // arms): negating flips which combinator is used.
            let result = match (is_and, negate) {
                (true, false) => manager.mk_and(nnf_args),
                (true, true) => manager.mk_or(nnf_args),
                (false, false) => manager.mk_or(nnf_args),
                (false, true) => manager.mk_and(nnf_args),
            };
            cache.insert((id, negate), result);
        }

        NnfStep::CombineImplies {
            id,
            negate,
            lhs,
            rhs,
        } => {
            let lhs_nnf = cache.get(&(lhs, !negate)).copied().unwrap_or(lhs);
            let rhs_nnf = cache.get(&(rhs, negate)).copied().unwrap_or(rhs);
            let result = if negate {
                // not(a -> b) = a and not(b)
                manager.mk_and([lhs_nnf, rhs_nnf])
            } else {
                // a -> b = not(a) or b
                manager.mk_or([lhs_nnf, rhs_nnf])
            };
            cache.insert((id, negate), result);
        }

        NnfStep::CombineXorBuilt {
            id,
            negate,
            lhs,
            rhs,
        } => {
            // a xor b = (a or b) and (not(a) or not(b))
            let lhs_nnf = cache.get(&(lhs, false)).copied().unwrap_or(lhs);
            let rhs_nnf = cache.get(&(rhs, false)).copied().unwrap_or(rhs);
            let not_lhs_nnf = cache.get(&(lhs, true)).copied().unwrap_or(lhs);
            let not_rhs_nnf = cache.get(&(rhs, true)).copied().unwrap_or(rhs);
            let clause1 = manager.mk_or([lhs_nnf, rhs_nnf]);
            let clause2 = manager.mk_or([not_lhs_nnf, not_rhs_nnf]);
            let built = manager.mk_and([clause1, clause2]);

            if negate {
                work.push(NnfStep::CombineXorFinal { id, negate, built });
                if !cache.contains_key(&(built, true)) {
                    work.push(NnfStep::Expand(built, true));
                }
            } else {
                cache.insert((id, negate), built);
            }
        }

        NnfStep::CombineXorFinal { id, negate, built } => {
            let result = cache.get(&(built, true)).copied().unwrap_or(built);
            cache.insert((id, negate), result);
        }

        NnfStep::CombineQuantifier {
            id,
            negate,
            is_forall,
            vars,
            patterns,
            body,
        } => {
            let body_nnf = cache.get(&(body, negate)).copied().unwrap_or(body);
            let var_names: Vec<(String, SortId)> = vars
                .iter()
                .map(|(s, sort)| (manager.resolve_str(*s).to_string(), *sort))
                .collect();
            let names_iter = var_names.iter().map(|(s, sort)| (s.as_str(), *sort));

            // Original: Forall negated -> exists; Forall plain -> forall;
            // Exists negated -> forall; Exists plain -> exists.
            let result = match (is_forall, negate) {
                (true, true) => manager.mk_exists_with_patterns(names_iter, body_nnf, patterns),
                (true, false) => manager.mk_forall_with_patterns(names_iter, body_nnf, patterns),
                (false, true) => manager.mk_forall_with_patterns(names_iter, body_nnf, patterns),
                (false, false) => manager.mk_exists_with_patterns(names_iter, body_nnf, patterns),
            };
            cache.insert((id, negate), result);
        }
    }
}

/// Check if a term is in NNF (Negation Normal Form)
#[must_use]
pub fn is_nnf(term_id: TermId, manager: &TermManager) -> bool {
    is_nnf_impl(term_id, manager, &mut FxHashSet::default())
}

/// Uses an explicit heap stack rather than native recursion (see the parent
/// module's doc comment). `visited` memoizes globally (unconditionally,
/// unlike `TermManager::free_vars`'s binder-scope-sensitive memo): whether a
/// subterm is itself in NNF never depends on where it is reached from, so
/// this is always sound.
fn is_nnf_impl(term_id: TermId, manager: &TermManager, visited: &mut FxHashSet<TermId>) -> bool {
    let mut stack: Vec<TermId> = vec![term_id];
    while let Some(id) = stack.pop() {
        if !visited.insert(id) {
            continue;
        }
        match manager.get(id).map(|t| &t.kind) {
            None | Some(TermKind::True | TermKind::False | TermKind::Var(_)) => {}

            // Negation is only allowed on variables.
            Some(TermKind::Not(arg))
                if !matches!(manager.get(*arg).map(|t| &t.kind), Some(TermKind::Var(_))) =>
            {
                return false;
            }
            Some(TermKind::Not(_)) => {}

            // Implications are not allowed in NNF: `to_nnf` rewrites
            // `a -> b` to `¬a ∨ b`.
            Some(TermKind::Implies(_, _)) => return false,

            // Neither is exclusive-or. `to_nnf`'s `Xor` arm expands
            // `a xor b` into `(a ∧ ¬b) ∨ (¬a ∧ b)`, so a term containing an
            // `Xor` node is *not* a fixed point of `to_nnf` and reporting it
            // as NNF is a wrong answer, not a conservative one. This used to
            // fall into the catch-all below and answer `true`, which is what
            // makes a caller that guards `to_nnf` behind `if !is_nnf(t)` skip
            // the conversion it needed.
            Some(TermKind::Xor(_, _)) => return false,

            Some(TermKind::And(args) | TermKind::Or(args)) => {
                for &a in args {
                    stack.push(a);
                }
            }

            Some(TermKind::Forall { body, .. } | TermKind::Exists { body, .. }) => {
                stack.push(*body);
            }

            // Everything else is an *atom* for NNF purposes -- exactly the
            // kinds `to_nnf`'s own `Some(_)` arm treats as atomic (arithmetic
            // and BV relations, `Eq`, `Ite`, `Apply`, `Select`, the string
            // and floating-point predicates, ...). NNF constrains only the
            // Boolean skeleton, so an atom is always in NNF regardless of its
            // internals, and this catch-all is a genuine leaf classification
            // rather than a dropped case: every Boolean connective
            // (`Not`/`And`/`Or`/`Implies`/`Xor`) and both binders are matched
            // explicitly above.
            _ => {}
        }
    }
    true
}
