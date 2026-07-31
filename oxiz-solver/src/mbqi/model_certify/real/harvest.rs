//! Eligibility scan for the real fragment.
//!
//! One iterative pass decides whether a goal is something the piecewise-affine
//! engine can interpret *totally* — and collects, while it is there, the
//! symbols that need an interpretation and the rational literals worth trying
//! as defaults.
//!
//! The scan is the real engine's soundness gate.  It refuses a goal the moment
//! it meets anything the engine would have to guess at: an integer-sorted
//! symbol (whose values are not rationals), a function of arity other than one,
//! a quantifier over more than one variable or over a non-real one, integer
//! division, or any operator outside the affine vocabulary.

use oxiz_core::ast::{TermId, TermKind, TermManager};
use oxiz_core::interner::Spur;

#[allow(unused_imports)]
use crate::prelude::*;

use super::super::value::{ValueSort, rational_literal, value_sort};
use super::affine::Rat;
use super::eval::operands;

/// Cap on the number of distinct terms one scan visits.
const MAX_NODES: usize = 100_000;

/// Everything the real interpretation builder needs, read off the goal.
#[derive(Debug, Default)]
pub(crate) struct RealHarvest {
    /// Unary uninterpreted functions with the sort of their result.
    pub(crate) funcs: FxHashMap<Spur, ValueSort>,
    /// Free constants with their sort.
    pub(crate) consts: FxHashMap<Spur, ValueSort>,
    /// Names bound by some quantifier.
    pub(crate) bound_names: FxHashSet<Spur>,
    /// Rational literals occurring in the goal.
    pub(crate) literals: Vec<Rat>,
    /// Whether a quantifier occurs at all.
    pub(crate) has_quantifier: bool,
}

/// Scan `assertions`, or decline when the goal leaves the real fragment.
pub(crate) fn harvest(assertions: &[TermId], manager: &TermManager) -> Option<RealHarvest> {
    let mut out = RealHarvest::default();
    let mut stack: Vec<TermId> = assertions.iter().rev().copied().collect();
    let mut visited: FxHashSet<TermId> = FxHashSet::default();

    while let Some(current) = stack.pop() {
        if !visited.insert(current) {
            continue;
        }
        if visited.len() > MAX_NODES {
            return None;
        }
        let node = manager.get(current)?;
        match &node.kind {
            TermKind::True | TermKind::False => {}
            TermKind::IntConst(_) | TermKind::RealConst(_) => {
                out.literals.push(rational_literal(current, manager)?);
            }
            TermKind::Var(name) => {
                let sort = value_sort(node.sort, manager)?;
                // An integer-sorted symbol would have to be given an integer
                // value; the affine defaults this engine searches are rational,
                // so interpreting one could invent a non-integer "integer".
                if sort == ValueSort::Int {
                    return None;
                }
                out.consts.insert(*name, sort);
            }
            TermKind::Apply { func, args } => {
                let result = value_sort(node.sort, manager)?;
                if result == ValueSort::Int {
                    return None;
                }
                let [arg] = args.as_slice() else {
                    return None;
                };
                let arg_sort = manager.get(*arg)?.sort;
                if value_sort(arg_sort, manager)? != ValueSort::Real {
                    return None;
                }
                out.funcs.insert(*func, result);
                stack.push(*arg);
            }
            TermKind::Forall { vars, body, .. } | TermKind::Exists { vars, body, .. } => {
                out.has_quantifier = true;
                let &(name, sort) = match vars.as_slice() {
                    [single] => single,
                    _ => return None,
                };
                if value_sort(sort, manager)? != ValueSort::Real {
                    return None;
                }
                out.bound_names.insert(name);
                stack.push(*body);
            }
            // Integer division and modulo have SMT-LIB corner cases that exact
            // rational arithmetic does not reproduce.
            TermKind::Mod(_, _) => return None,
            TermKind::Div(_, _) if node.sort == manager.sorts.int_sort => return None,
            other => {
                // Rejecting unknown sorts here is what keeps bit-vectors,
                // arrays, strings and datatypes out of the fragment; integer
                // *arithmetic* over literals stays exact under rationals, and
                // the only integer-specific operators (`div`, `mod`) are
                // refused above.
                value_sort(node.sort, manager)?;
                let children = operands(other)?;
                stack.extend(children.iter().rev().copied());
            }
        }
    }

    // Names a quantifier binds are not free constants; a name used both ways
    // simply loses its constant entry, and the evaluator then declines the
    // free occurrence rather than reading the bound variable's value.
    for name in &out.bound_names {
        out.consts.remove(name);
    }

    Some(out)
}
