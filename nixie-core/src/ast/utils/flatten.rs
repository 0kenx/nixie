//! Flattening nested associative operations (`and`/`or`/`+`/`*`).
//!
//! [`flatten_associative`] rebuilds a term bottom-up, exactly like
//! [`super::hash::structural_hash`]'s walk, but it needs `&mut TermManager`
//! (to call the `mk_*` constructors) and produces a *new* [`TermId`] rather
//! than a plain value, so it is closer in shape to `term_complexity`: a
//! two-phase (`expand`, then `combine`) post-order walk with a real
//! `TermId -> TermId` cache, driven by an explicit stack instead of the
//! native call stack.
//!
//! ## The flattening rule is preserved exactly, including its limits
//!
//! The original only ever rewrites nine kinds: `And`/`Or`/`Add`/`Mul` (which
//! get flattened -- a nested node of the *same* kind has its arguments
//! spliced into the parent) and `Not`/`Implies`/`Xor`/`Eq`/`Ite` (whose
//! children are recursively flattened, but the node itself is rebuilt as-is,
//! never spliced). Every other kind -- every bitvector/FP/string operator,
//! `Apply`, `Forall`/`Exists`/`Let`/`Match`, datatype constructors, and so on
//! -- is returned completely unchanged, **without even being inspected for a
//! nested associative op somewhere inside it**. So e.g. `(f (and (and a b)
//! c))` leaves the inner `and` un-flattened, because `Apply` isn't one of the
//! nine rewritten kinds and the walk never looks past it. This is a
//! pre-existing limitation of the original recursive function, reproduced
//! here exactly rather than "fixed" as a side effect of the iterative
//! conversion.

use crate::ast::{TermId, TermKind, TermManager};
#[allow(unused_imports)]
use crate::prelude::*;
use smallvec::{SmallVec, smallvec};

/// Flatten nested associative operations
///
/// This function flattens nested associative operations (And, Or, Add, Mul) into
/// single n-ary operations. For example:
/// - `(and (and a b) c)` becomes `(and a b c)`
/// - `(+ (+ x 1) (+ 2 3))` becomes `(+ x 1 2 3)`
///
/// This is useful for:
/// - Term normalization
/// - Reducing tree depth
/// - Improving pattern matching
/// - More efficient subsequent operations
#[must_use]
pub fn flatten_associative(term_id: TermId, manager: &mut TermManager) -> TermId {
    let mut cache: FxHashMap<TermId, TermId> = FxHashMap::default();
    let mut stack: Vec<(TermId, bool)> = vec![(term_id, false)];

    while let Some((id, expanded)) = stack.pop() {
        if cache.contains_key(&id) {
            continue;
        }

        // Clone the kind (as the original did) to avoid holding a borrow of
        // `manager` across the `mk_*` calls in `rebuild_flattened`.
        let Some(kind) = manager.get(id).map(|t| t.kind.clone()) else {
            cache.insert(id, id);
            continue;
        };

        let Some(pending) = flatten_pending_children(&kind) else {
            // Every other kind is returned unchanged -- matches the
            // original's `_ => term_id` catch-all exactly, including not
            // recursing into it at all.
            cache.insert(id, id);
            continue;
        };

        if !expanded {
            stack.push((id, true));
            for &child in &pending {
                if !cache.contains_key(&child) {
                    stack.push((child, false));
                }
            }
            continue;
        }

        // Every child in `pending` was pushed, and popped, before `id`
        // itself is re-popped with `expanded = true` (a LIFO stack fully
        // drains a subtree before returning to its parent), so `cache` holds
        // a flattened form for each of them already.
        let result = rebuild_flattened(&kind, manager, &cache).unwrap_or(id);
        cache.insert(id, result);
    }

    cache.get(&term_id).copied().unwrap_or(term_id)
}

/// The children that must be flattened before `kind` can be rebuilt, or
/// `None` if `kind` is not one of the nine kinds this function rewrites (in
/// which case the term is returned unchanged without being expanded at all).
fn flatten_pending_children(kind: &TermKind) -> Option<SmallVec<[TermId; 4]>> {
    Some(match kind {
        TermKind::And(args) | TermKind::Or(args) | TermKind::Add(args) | TermKind::Mul(args) => {
            args.iter().copied().collect()
        }
        TermKind::Not(a) => smallvec![*a],
        TermKind::Implies(a, b) | TermKind::Xor(a, b) | TermKind::Eq(a, b) => {
            smallvec![*a, *b]
        }
        TermKind::Ite(c, t, e) => smallvec![*c, *t, *e],
        _ => return None,
    })
}

/// Rebuild `kind` from its already-flattened children in `cache`, splicing
/// same-kind nested `And`/`Or`/`Add`/`Mul` children in rather than nesting
/// them. Returns `None` for any kind `flatten_pending_children` would not
/// have expanded, so the caller can fall back to "unchanged" -- the same
/// fallback the original's `_ => term_id` catch-all produces.
fn rebuild_flattened(
    kind: &TermKind,
    manager: &mut TermManager,
    cache: &FxHashMap<TermId, TermId>,
) -> Option<TermId> {
    let get = |c: TermId| cache.get(&c).copied().unwrap_or(c);

    Some(match kind {
        TermKind::And(args) => {
            let mut flattened: SmallVec<[TermId; 4]> = SmallVec::new();
            for &arg in args.iter() {
                let flat_arg = get(arg);
                match manager.get(flat_arg) {
                    Some(child_term) => match &child_term.kind {
                        TermKind::And(child_args) => flattened.extend(child_args.iter().copied()),
                        _ => flattened.push(flat_arg),
                    },
                    None => flattened.push(flat_arg),
                }
            }
            manager.mk_and(flattened)
        }

        TermKind::Or(args) => {
            let mut flattened: SmallVec<[TermId; 4]> = SmallVec::new();
            for &arg in args.iter() {
                let flat_arg = get(arg);
                match manager.get(flat_arg) {
                    Some(child_term) => match &child_term.kind {
                        TermKind::Or(child_args) => flattened.extend(child_args.iter().copied()),
                        _ => flattened.push(flat_arg),
                    },
                    None => flattened.push(flat_arg),
                }
            }
            manager.mk_or(flattened)
        }

        TermKind::Add(args) => {
            let mut flattened: SmallVec<[TermId; 4]> = SmallVec::new();
            for &arg in args.iter() {
                let flat_arg = get(arg);
                match manager.get(flat_arg) {
                    Some(child_term) => match &child_term.kind {
                        TermKind::Add(child_args) => flattened.extend(child_args.iter().copied()),
                        _ => flattened.push(flat_arg),
                    },
                    None => flattened.push(flat_arg),
                }
            }
            manager.mk_add(flattened)
        }

        TermKind::Mul(args) => {
            let mut flattened: SmallVec<[TermId; 4]> = SmallVec::new();
            for &arg in args.iter() {
                let flat_arg = get(arg);
                match manager.get(flat_arg) {
                    Some(child_term) => match &child_term.kind {
                        TermKind::Mul(child_args) => flattened.extend(child_args.iter().copied()),
                        _ => flattened.push(flat_arg),
                    },
                    None => flattened.push(flat_arg),
                }
            }
            manager.mk_mul(flattened)
        }

        // For other operations, recursively flatten children but don't flatten the operation itself
        TermKind::Not(a) => {
            let flat_a = get(*a);
            manager.mk_not(flat_a)
        }

        TermKind::Implies(a, b) => {
            let flat_a = get(*a);
            let flat_b = get(*b);
            manager.mk_implies(flat_a, flat_b)
        }

        TermKind::Xor(a, b) => {
            let flat_a = get(*a);
            let flat_b = get(*b);
            manager.mk_xor(flat_a, flat_b)
        }

        TermKind::Eq(a, b) => {
            let flat_a = get(*a);
            let flat_b = get(*b);
            manager.mk_eq(flat_a, flat_b)
        }

        TermKind::Ite(c, t, e) => {
            let flat_c = get(*c);
            let flat_t = get(*t);
            let flat_e = get(*e);
            manager.mk_ite(flat_c, flat_t, flat_e)
        }

        _ => return None,
    })
}
