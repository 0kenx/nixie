//! Symbol / constant harvesting and the fragment eligibility test.
//!
//! Two passes over the assertion set:
//!
//! * [`harvest`] collects everything the certifier needs to *build* a candidate
//!   interpretation – the applied function symbols with their result sorts, the
//!   free constants, the integer literals, and the names some quantifier binds.
//! * [`region_stable`] decides whether the goal is inside the fragment the
//!   finite check is complete for.  This is the certifier's soundness gate:
//!   `false` here means the exhaustive domain of [`super::eval`] would not be
//!   exhaustive after all, and the whole certification declines.

use nixie_core::ast::{TermId, TermKind, TermManager};
use nixie_core::interner::Spur;
use num_bigint::BigInt;
use smallvec::SmallVec;

#[allow(unused_imports)]
use crate::prelude::*;

use super::value::{CertValue, ValueSort, literal_value, value_sort};

/// Everything the interpretation builder needs, read off the assertion set.
#[derive(Debug, Default)]
pub(crate) struct Harvest {
    /// Every uninterpreted function symbol applied anywhere, with the sort of
    /// its result.
    pub(crate) applied: FxHashMap<Spur, ValueSort>,
    /// Every name some quantifier binds.
    pub(crate) bound_names: FxHashSet<Spur>,
    /// Every integer literal that occurs in the assertions.
    pub(crate) int_consts: Vec<BigInt>,
    /// Whether a quantifier occurs at all (nothing to certify otherwise).
    pub(crate) has_quantifier: bool,
}

/// Cap on the number of distinct terms one harvest pass visits.
///
/// Bounds the certifier's cost on a huge goal.  Exceeding it declines, which
/// costs completeness only.
const MAX_HARVEST_NODES: usize = 100_000;

/// Collect the applied symbols, bound names and integer literals of
/// `assertions`, or `None` when some sub-term is outside the certifier's
/// vocabulary.
///
/// Iterative with an explicit heap stack: assertion shape is user input, and a
/// native recursion would trade a stack overflow for the depth guard this walk
/// does not need.  Returning `None` on an unknown `TermKind` is the honest
/// answer – a symbol the certifier cannot interpret cannot be part of a model
/// it claims to have verified.
pub(crate) fn harvest(assertions: &[TermId], manager: &TermManager) -> Option<Harvest> {
    let mut out = Harvest::default();
    let mut stack: Vec<TermId> = assertions.iter().rev().copied().collect();
    let mut visited: FxHashSet<TermId> = FxHashSet::default();

    while let Some(current) = stack.pop() {
        if !visited.insert(current) {
            continue;
        }
        if visited.len() > MAX_HARVEST_NODES {
            return None;
        }
        let node = manager.get(current)?;
        let sort = node.sort;
        match &node.kind {
            TermKind::True | TermKind::False | TermKind::Var(_) => {}
            TermKind::IntConst(n) => out.int_consts.push(n.clone()),
            TermKind::Apply { func, args } => {
                out.applied.insert(*func, value_sort(sort, manager)?);
                stack.extend(args.iter().rev().copied());
            }
            TermKind::Forall { vars, body, .. } | TermKind::Exists { vars, body, .. } => {
                out.has_quantifier = true;
                for &(name, var_sort) in vars.iter() {
                    // A bound variable of a sort the certifier cannot
                    // enumerate makes the whole check impossible.
                    value_sort(var_sort, manager)?;
                    out.bound_names.insert(name);
                }
                stack.push(*body);
            }
            other => {
                let children = supported_children(other)?;
                stack.extend(children.iter().rev().copied());
            }
        }
    }

    Some(out)
}

/// The operand list of a supported non-leaf, non-`Apply`, non-quantifier node,
/// in left-to-right order, or `None` when the certifier does not interpret the
/// operator.
pub(crate) fn supported_children(kind: &TermKind) -> Option<SmallVec<[TermId; 4]>> {
    let out: SmallVec<[TermId; 4]> = match kind {
        TermKind::Not(a) | TermKind::Neg(a) => SmallVec::from_slice(&[*a]),
        TermKind::And(args) | TermKind::Or(args) | TermKind::Add(args) | TermKind::Mul(args) => {
            args.iter().copied().collect()
        }
        TermKind::Distinct(args) => args.iter().copied().collect(),
        TermKind::Xor(l, r)
        | TermKind::Implies(l, r)
        | TermKind::Eq(l, r)
        | TermKind::Sub(l, r)
        | TermKind::Lt(l, r)
        | TermKind::Le(l, r)
        | TermKind::Gt(l, r)
        | TermKind::Ge(l, r) => SmallVec::from_slice(&[*l, *r]),
        TermKind::Ite(c, t, e) => SmallVec::from_slice(&[*c, *t, *e]),
        // Everything else – `Div`/`Mod` (whose SMT-LIB corner cases the
        // certifier does not reproduce), reals, bit-vectors, arrays, strings,
        // floating point, datatypes – is outside the vocabulary.
        _ => return None,
    };
    Some(out)
}

/// The position a sub-term is visited in, which decides whether a bound
/// variable may appear there.
#[derive(Clone, Copy, PartialEq, Eq, Hash)]
enum Position {
    /// Anywhere a bound variable's *own value* would flow into the result:
    /// arithmetic, an `ite` branch, a boolean connective.  A bound variable
    /// here breaks region stability and is rejected.
    Value,
    /// A direct argument of an uninterpreted function.  A bound variable here
    /// is the essentially-uninterpreted position: outside the pinned tuples
    /// the function is constant, so the variable's exact value is invisible.
    FuncArg,
    /// An operand of a comparison / `distinct` whose *other* operands are all
    /// region-stable.  A bound variable here is visible only through its order
    /// relative to critical values, which the enumeration domain covers.
    Comparand,
}

/// Whether every occurrence of every bound variable in `assertions` sits in a
/// position the finite enumeration of [`super::eval`] is *complete* for.
///
/// # The region argument
///
/// Fix an interpretation in which every function is a finite pin table plus a
/// default, and let `C` be the critical set: every integer literal of the goal,
/// every pinned argument and result, every constant's value, every default, and
/// the values already assigned to enclosing bound variables.  `C` cuts the
/// integers into finitely many *regions*: the singletons `{c}` for `c ∈ C` and
/// the open gaps between (and beyond) them.
///
/// If every occurrence of a bound variable `v` is either
///
/// * a direct argument of an uninterpreted function, or
/// * an operand of a comparison whose other operands are region-stable – an
///   integer literal, a constant, a function application, or another bound
///   variable –
///
/// then the truth of the body depends on `v` only through `v`'s region:
///
/// * every application mentioning a `v` drawn from a gap misses the pin table
///   (pinned arguments are all in `C`), so it returns the default, identically
///   for every point of that gap – and so does every application built on top
///   of it, because function results are in `C` too;
/// * every comparison compares `v` against a value in `C` (a literal, a
///   constant, or a function result) or against another bound variable, whose
///   own value is added to `C` before *its* domain is built.
///
/// So checking one representative per region decides the quantifier over the
/// whole of `Int`.  When this function answers `false`, that reasoning does not
/// apply and the certifier must not claim a verdict.
pub(crate) fn region_stable(
    assertions: &[TermId],
    bound_names: &FxHashSet<Spur>,
    manager: &TermManager,
) -> bool {
    let mut stack: Vec<(TermId, Position)> = assertions
        .iter()
        .rev()
        .map(|&t| (t, Position::Value))
        .collect();
    let mut visited: FxHashSet<(TermId, Position)> = FxHashSet::default();

    while let Some((current, position)) = stack.pop() {
        if !visited.insert((current, position)) {
            continue;
        }
        if visited.len() > MAX_HARVEST_NODES {
            return false;
        }
        let Some(node) = manager.get(current) else {
            return false;
        };
        match &node.kind {
            TermKind::Var(name) => {
                // A `Bool` variable is enumerated over its *entire* domain
                // ({false, true}), so it stays complete in any position; an
                // `Int` variable outside a function argument or a comparison
                // would leak its exact value into the result.
                if bound_names.contains(name)
                    && position == Position::Value
                    && node.sort != manager.sorts.bool_sort
                {
                    return false;
                }
            }
            TermKind::True | TermKind::False | TermKind::IntConst(_) => {}
            TermKind::Apply { args, .. } => {
                for &arg in args.iter() {
                    stack.push((arg, Position::FuncArg));
                }
            }
            TermKind::Forall { body, .. } | TermKind::Exists { body, .. } => {
                stack.push((*body, Position::Value));
            }
            TermKind::Eq(l, r)
            | TermKind::Lt(l, r)
            | TermKind::Le(l, r)
            | TermKind::Gt(l, r)
            | TermKind::Ge(l, r) => {
                if !comparison_ok(&[*l, *r], bound_names, manager) {
                    return false;
                }
                stack.push((*l, Position::Comparand));
                stack.push((*r, Position::Comparand));
            }
            TermKind::Distinct(args) => {
                if !comparison_ok(args, bound_names, manager) {
                    return false;
                }
                for &arg in args.iter() {
                    stack.push((arg, Position::Comparand));
                }
            }
            other => {
                let Some(children) = supported_children(other) else {
                    return false;
                };
                for &child in children.iter() {
                    stack.push((child, Position::Value));
                }
            }
        }
    }
    true
}

/// Whether a comparison over `operands` keeps its bound variables region-stable.
///
/// A bound-variable operand is admissible only when *every other* operand is
/// region-stable on its own: a literal, a free constant, a function
/// application, or another bound variable.  An arithmetic operand (`y + 1`)
/// is not – its value moves with the variable it mentions, so two points of
/// one region could compare differently.
fn comparison_ok(
    operands: &[TermId],
    bound_names: &FxHashSet<Spur>,
    manager: &TermManager,
) -> bool {
    let has_bound_operand = operands
        .iter()
        .any(|&t| is_bound_var(t, bound_names, manager));
    if !has_bound_operand {
        return true;
    }
    operands
        .iter()
        .all(|&t| is_region_stable_operand(t, bound_names, manager))
}

/// Whether `term` is a `Var` naming a quantifier-bound variable.
fn is_bound_var(term: TermId, bound_names: &FxHashSet<Spur>, manager: &TermManager) -> bool {
    matches!(manager.get(term).map(|t| &t.kind), Some(TermKind::Var(n)) if bound_names.contains(n))
}

/// Whether `term`'s value under any candidate interpretation is guaranteed to
/// lie in the critical set (a literal, a constant, a function result) or to be
/// a bound variable whose own enumeration is region-aware.
fn is_region_stable_operand(
    term: TermId,
    bound_names: &FxHashSet<Spur>,
    manager: &TermManager,
) -> bool {
    match manager.get(term).map(|t| &t.kind) {
        Some(TermKind::IntConst(_) | TermKind::True | TermKind::False) => true,
        // A free constant's value and every function result are added to the
        // critical set when the interpretation is built; a bound variable's
        // value is added before any *inner* variable's domain is built.
        Some(TermKind::Var(_) | TermKind::Apply { .. }) => true,
        _ => {
            let _ = bound_names;
            false
        }
    }
}

/// Read the pin table and constant assignments out of a ground model.
///
/// A model entry `f(3, 4) := 7` becomes a pin; `c := 5` becomes a constant's
/// value.  Entries whose key or value is not fully literal (`f(x, sk(x)) := 1`)
/// are skipped – the resulting interpretation is verified against every
/// assertion afterwards, so a missing pin costs completeness, never soundness.
pub(crate) fn read_model(
    assignments: &FxHashMap<TermId, TermId>,
    bound_names: &FxHashSet<Spur>,
    manager: &TermManager,
) -> ModelFacts {
    let mut facts = ModelFacts::default();

    for (&key, &value) in assignments {
        let Some(result) = literal_value(value, manager) else {
            continue;
        };
        match manager.get(key).map(|t| &t.kind) {
            Some(TermKind::Apply { func, args }) => {
                let mut tuple: Vec<CertValue> = Vec::with_capacity(args.len());
                let mut concrete = true;
                for &arg in args.iter() {
                    match literal_value(arg, manager) {
                        Some(v) => tuple.push(v),
                        None => {
                            concrete = false;
                            break;
                        }
                    }
                }
                if concrete {
                    facts
                        .pins
                        .entry(*func)
                        .or_default()
                        .insert(tuple, result.clone());
                }
            }
            Some(TermKind::Var(name)) if !bound_names.contains(name) => {
                facts.consts.insert(*name, result.clone());
            }
            _ => {}
        }
    }

    facts
}

/// The pins and constant values read off a ground model.
#[derive(Debug, Default)]
pub(crate) struct ModelFacts {
    /// Pinned argument tuples per function symbol.
    pub(crate) pins: FxHashMap<Spur, FxHashMap<Vec<CertValue>, CertValue>>,
    /// Values of free constants.
    pub(crate) consts: FxHashMap<Spur, CertValue>,
}
