//! Simple per-term metrics: groundness, complexity, size/depth statistics,
//! and predicate-based search.
//!
//! `find_terms`, `count_operations`, `max_term_id` and
//! `collect_unique_subterms` were already iterative (a `VecDeque`-driven BFS
//! with a `visited` set, never a recursive call) before this conversion pass;
//! they are unchanged here beyond moving into this file and switching to
//! absolute `crate::ast::...` paths now that they are one module level
//! deeper. `is_ground` and `term_complexity` are the two that actually
//! recursed and are rewritten below.

use crate::ast::{TermId, TermKind, TermManager};
#[allow(unused_imports)]
use crate::prelude::*;
use smallvec::SmallVec;

/// Find all terms matching a predicate
pub fn find_terms<F>(term_id: TermId, manager: &TermManager, predicate: F) -> Vec<TermId>
where
    F: Fn(TermId, &TermManager) -> bool,
{
    let mut result = Vec::new();
    let mut visited = FxHashSet::default();
    let mut queue = VecDeque::new();
    queue.push_back(term_id);

    while let Some(current) = queue.pop_front() {
        if !visited.insert(current) {
            continue;
        }

        if predicate(current, manager) {
            result.push(current);
        }

        if let Some(term) = manager.get(current) {
            let children = crate::ast::traversal::get_children(&term.kind);
            queue.extend(children);
        }
    }

    result
}

/// Count the number of operations of a specific kind in a term
pub fn count_operations<F>(term_id: TermId, manager: &TermManager, predicate: F) -> usize
where
    F: Fn(&TermKind) -> bool,
{
    let mut count = 0;
    let mut visited = FxHashSet::default();
    let mut queue = VecDeque::new();
    queue.push_back(term_id);

    while let Some(current) = queue.pop_front() {
        if !visited.insert(current) {
            continue;
        }

        if let Some(term) = manager.get(current) {
            if predicate(&term.kind) {
                count += 1;
            }

            let children = crate::ast::traversal::get_children(&term.kind);
            queue.extend(children);
        }
    }

    count
}

/// Get the maximum term ID used (for statistics)
#[must_use]
pub fn max_term_id(term_id: TermId, manager: &TermManager) -> u32 {
    let mut max_id = term_id.0;
    let mut visited = FxHashSet::default();
    let mut queue = VecDeque::new();
    queue.push_back(term_id);

    while let Some(current) = queue.pop_front() {
        if !visited.insert(current) {
            continue;
        }

        max_id = max_id.max(current.0);

        if let Some(term) = manager.get(current) {
            let children = crate::ast::traversal::get_children(&term.kind);
            queue.extend(children);
        }
    }

    max_id
}

/// Collect all unique subterms (deduplicated by ID)
#[must_use]
pub fn collect_unique_subterms(term_id: TermId, manager: &TermManager) -> FxHashSet<TermId> {
    let mut result = FxHashSet::default();
    let mut queue = VecDeque::new();
    queue.push_back(term_id);

    while let Some(current) = queue.pop_front() {
        if !result.insert(current) {
            continue;
        }

        if let Some(term) = manager.get(current) {
            let children = crate::ast::traversal::get_children(&term.kind);
            queue.extend(children);
        }
    }

    result
}

/// Check if a term is ground (contains no variables)
///
/// # Why this can be a flat, single-phase walk
///
/// The original recursive form combines every compound kind's children with
/// `&&`/`.all()` (never `||`), and forces `false` unconditionally -- without
/// even inspecting `body` -- for `Forall`/`Exists`. By structural induction
/// over that definition: `is_ground(t)` is `true` exactly when *no* node
/// reachable from `t` (via [`crate::ast::traversal::get_children`], `t`
/// itself included) is a `Var`, `Forall`, or `Exists`. That means groundness
/// can be decided by a single walk that returns `false` the instant it meets
/// a `Var`/`Forall`/`Exists`, without ever needing to combine children's
/// results afterward -- unlike `term_complexity` below, there is no numeric
/// formula here that depends on a child's *specific* value, only a yes/no
/// search. This also reproduces the original's refusal to descend into a
/// quantifier's body: the `Forall`/`Exists` arm returns immediately rather
/// than falling into the generic `get_children` extension.
#[must_use]
pub fn is_ground(term_id: TermId, manager: &TermManager) -> bool {
    let mut visited: FxHashSet<TermId> = FxHashSet::default();
    let mut stack: Vec<TermId> = vec![term_id];

    while let Some(id) = stack.pop() {
        if !visited.insert(id) {
            continue;
        }

        let Some(term) = manager.get(id) else {
            continue;
        };

        match &term.kind {
            TermKind::Var(_) => return false,
            TermKind::Forall { .. } | TermKind::Exists { .. } => return false,
            _ => stack.extend(crate::ast::traversal::get_children(&term.kind)),
        }
    }

    true
}

/// Get term complexity (weighted sum of operations)
///
/// Different operations have different complexity weights:
/// - Constants and variables: 1
/// - Unary operations: 2
/// - Binary operations: 3
/// - N-ary operations: N + 1
/// - Quantifiers: 10 * body_complexity
///
/// Unlike `is_ground`, this is a genuine numeric fold (a parent's complexity
/// is an arithmetic function of its children's exact values, e.g. `10 *
/// body_complexity`), so it needs a real memoized combine step rather than a
/// yes/no search. The iterative version below is a standard two-phase
/// (`expand`, then `combine`) post-order walk driven by an explicit stack:
/// each id is pushed once as `(id, false)` ("not yet expanded") and, if not
/// already cached, re-pushed as `(id, true)` *underneath* its children before
/// they are pushed on top. Because a LIFO stack fully drains everything
/// pushed on top of a frame before returning to it, every child is
/// guaranteed to be in `cache` by the time `(id, true)` is popped.
#[must_use]
pub fn term_complexity(term_id: TermId, manager: &TermManager) -> usize {
    let mut cache: FxHashMap<TermId, usize> = FxHashMap::default();
    let mut stack: Vec<(TermId, bool)> = vec![(term_id, false)];

    while let Some((id, expanded)) = stack.pop() {
        if cache.contains_key(&id) {
            continue;
        }

        if !expanded {
            stack.push((id, true));
            for child in complexity_children(id, manager) {
                if !cache.contains_key(&child) {
                    stack.push((child, false));
                }
            }
            continue;
        }

        let complexity = combine_complexity(id, manager, &cache);
        cache.insert(id, complexity);
    }

    cache.get(&term_id).copied().unwrap_or(1)
}

/// Children whose complexity must be known before `id`'s own complexity can
/// be combined. This is exactly [`crate::ast::traversal::get_children`] --
/// unlike `is_ground`, `term_complexity` *does* need a `Forall`/`Exists`'s
/// `body` (just combined with a `10 *` multiplier instead of the generic
/// `N + 1`), and every other kind's children match `get_children`
/// one-for-one too, so no separate child-enumeration logic is needed here.
fn complexity_children(id: TermId, manager: &TermManager) -> SmallVec<[TermId; 4]> {
    manager
        .get(id)
        .map(|t| crate::ast::traversal::get_children(&t.kind))
        .unwrap_or_default()
}

/// Combine `id`'s already-cached children into `id`'s own complexity,
/// mirroring the original recursive match arm-for-arm.
fn combine_complexity(
    id: TermId,
    manager: &TermManager,
    cache: &FxHashMap<TermId, usize>,
) -> usize {
    // Every child of `id` was pushed, and popped, before `id` itself is
    // re-popped with `expanded = true` (a LIFO stack fully drains a subtree
    // before returning to its parent), so every lookup below is guaranteed to
    // hit; `unwrap_or(1)` is a defensive fallback matching this crate's "no
    // unwrap()" policy, not a case this can actually reach.
    let get = |c: TermId| cache.get(&c).copied().unwrap_or(1);

    match manager.get(id).map(|t| &t.kind) {
        None
        | Some(
            TermKind::True
            | TermKind::False
            | TermKind::IntConst(_)
            | TermKind::RealConst(_)
            | TermKind::BitVecConst { .. }
            | TermKind::StringLit(_)
            | TermKind::Var(_),
        ) => 1,

        Some(
            TermKind::Not(a)
            | TermKind::Neg(a)
            | TermKind::BvNot(a)
            | TermKind::StrLen(a)
            | TermKind::StrToInt(a)
            | TermKind::IntToStr(a)
            | TermKind::StrToCode(a)
            | TermKind::StrFromCode(a),
        ) => 2 + get(*a),

        Some(TermKind::BvExtract { arg, .. }) => 2 + get(*arg),

        Some(
            TermKind::And(args)
            | TermKind::Or(args)
            | TermKind::Add(args)
            | TermKind::Mul(args)
            | TermKind::Distinct(args),
        ) => args.len() + 1 + args.iter().map(|&a| get(a)).sum::<usize>(),

        Some(
            TermKind::Implies(a, b)
            | TermKind::Xor(a, b)
            | TermKind::Eq(a, b)
            | TermKind::Sub(a, b)
            | TermKind::Div(a, b)
            | TermKind::Mod(a, b)
            | TermKind::Lt(a, b)
            | TermKind::Le(a, b)
            | TermKind::Gt(a, b)
            | TermKind::Ge(a, b)
            | TermKind::Select(a, b)
            | TermKind::BvConcat(a, b)
            | TermKind::BvAnd(a, b)
            | TermKind::BvOr(a, b)
            | TermKind::BvXor(a, b)
            | TermKind::BvAdd(a, b)
            | TermKind::BvSub(a, b)
            | TermKind::BvMul(a, b)
            | TermKind::BvUdiv(a, b)
            | TermKind::BvSdiv(a, b)
            | TermKind::BvUrem(a, b)
            | TermKind::BvSrem(a, b)
            | TermKind::BvShl(a, b)
            | TermKind::BvLshr(a, b)
            | TermKind::BvAshr(a, b)
            | TermKind::BvUlt(a, b)
            | TermKind::BvUle(a, b)
            | TermKind::BvSlt(a, b)
            | TermKind::BvSle(a, b)
            | TermKind::StrConcat(a, b)
            | TermKind::StrAt(a, b)
            | TermKind::StrContains(a, b)
            | TermKind::StrPrefixOf(a, b)
            | TermKind::StrSuffixOf(a, b)
            | TermKind::StrInRe(a, b)
            | TermKind::StrLt(a, b)
            | TermKind::StrLe(a, b),
        ) => 3 + get(*a) + get(*b),

        Some(
            TermKind::Ite(c, t, e)
            | TermKind::Store(c, t, e)
            | TermKind::StrSubstr(c, t, e)
            | TermKind::StrIndexOf(c, t, e)
            | TermKind::StrReplace(c, t, e)
            | TermKind::StrReplaceAll(c, t, e)
            | TermKind::StrReplaceRe(c, t, e)
            | TermKind::StrReplaceReAll(c, t, e),
        ) => 4 + get(*c) + get(*t) + get(*e),

        Some(TermKind::Apply { args, .. }) => {
            args.len() + 1 + args.iter().map(|&a| get(a)).sum::<usize>()
        }

        Some(TermKind::Forall { body, .. } | TermKind::Exists { body, .. }) => 10 * get(*body),

        Some(TermKind::Let { bindings, body }) => {
            bindings.len() + bindings.iter().map(|(_, t)| get(*t)).sum::<usize>() + get(*body)
        }

        // Floating-point literals have complexity 1
        Some(
            TermKind::FpLit { .. }
            | TermKind::FpPlusInfinity { .. }
            | TermKind::FpMinusInfinity { .. }
            | TermKind::FpPlusZero { .. }
            | TermKind::FpMinusZero { .. }
            | TermKind::FpNaN { .. },
        ) => 1,

        // Unary FP operations
        Some(
            TermKind::FpAbs(a)
            | TermKind::FpNeg(a)
            | TermKind::FpSqrt(_, a)
            | TermKind::FpRoundToIntegral(_, a)
            | TermKind::FpIsNormal(a)
            | TermKind::FpIsSubnormal(a)
            | TermKind::FpIsZero(a)
            | TermKind::FpIsInfinite(a)
            | TermKind::FpIsNaN(a)
            | TermKind::FpIsNegative(a)
            | TermKind::FpIsPositive(a)
            | TermKind::FpToReal(a)
            | TermKind::FpToFp { arg: a, .. }
            | TermKind::FpToSBV { arg: a, .. }
            | TermKind::FpToUBV { arg: a, .. }
            | TermKind::RealToFp { arg: a, .. }
            | TermKind::SBVToFp { arg: a, .. }
            | TermKind::UBVToFp { arg: a, .. },
        ) => 2 + get(*a),

        // Binary FP operations
        Some(
            TermKind::FpAdd(_, a, b)
            | TermKind::FpSub(_, a, b)
            | TermKind::FpMul(_, a, b)
            | TermKind::FpDiv(_, a, b)
            | TermKind::FpRem(a, b)
            | TermKind::FpMin(a, b)
            | TermKind::FpMax(a, b)
            | TermKind::FpLeq(a, b)
            | TermKind::FpLt(a, b)
            | TermKind::FpGeq(a, b)
            | TermKind::FpGt(a, b)
            | TermKind::FpEq(a, b),
        ) => 3 + get(*a) + get(*b),

        // Ternary FP operations (FMA)
        Some(TermKind::FpFma(_, a, b, c)) => 4 + get(*a) + get(*b) + get(*c),

        // Algebraic datatypes
        Some(TermKind::DtConstructor { args, .. }) => {
            2 + args.iter().map(|&a| get(a)).sum::<usize>()
        }
        Some(TermKind::DtTester { arg, .. } | TermKind::DtSelector { arg, .. }) => 2 + get(*arg),

        // Match expressions
        Some(TermKind::Match { scrutinee, cases }) => {
            5 + get(*scrutinee) + cases.iter().map(|c| get(c.body)).sum::<usize>()
        }
    }
}

/// Collect statistics about a term
#[derive(Debug, Clone, Default)]
pub struct TermStatistics {
    /// Total number of unique subterms
    pub unique_subterms: usize,
    /// Total number of nodes (counting sharing)
    pub total_nodes: usize,
    /// Maximum depth
    pub depth: usize,
    /// Number of variables
    pub num_variables: usize,
    /// Number of constants
    pub num_constants: usize,
    /// Number of function applications
    pub num_applications: usize,
    /// Complexity score
    pub complexity: usize,
}

/// Compute detailed statistics for a term
///
/// Every walk reachable from here is iterative. `manager.term_depth()` (used
/// for the `depth` field) lives in `ast::manager::query::size_depth`; it was
/// once a native recursion, and this comment used to record that as a residual
/// gap, but it now drives an explicit `Vec<(TermId, bool)>` stack of its own,
/// so a long unshared chain no longer risks the native stack.
#[must_use]
pub fn compute_statistics(term_id: TermId, manager: &TermManager) -> TermStatistics {
    let unique = collect_unique_subterms(term_id, manager);
    let depth = manager.term_depth(term_id);
    let complexity = term_complexity(term_id, manager);

    let mut num_variables = 0;
    let mut num_constants = 0;
    let mut num_applications = 0;
    let mut total_nodes = 0;

    let mut visited = FxHashSet::default();
    let mut queue = VecDeque::new();
    queue.push_back(term_id);

    while let Some(current) = queue.pop_front() {
        if !visited.insert(current) {
            continue;
        }

        total_nodes += 1;

        if let Some(term) = manager.get(current) {
            match &term.kind {
                TermKind::Var(_) => num_variables += 1,
                TermKind::True
                | TermKind::False
                | TermKind::IntConst(_)
                | TermKind::RealConst(_)
                | TermKind::BitVecConst { .. } => num_constants += 1,
                TermKind::Apply { .. } => num_applications += 1,
                _ => {}
            }

            let children = crate::ast::traversal::get_children(&term.kind);
            queue.extend(children);
        }
    }

    TermStatistics {
        unique_subterms: unique.len(),
        total_nodes,
        depth,
        num_variables,
        num_constants,
        num_applications,
        complexity,
    }
}
