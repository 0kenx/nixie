//! DAG traversal utilities for terms
//!
//! This module provides efficient traversal mechanisms for term DAGs,
//! including visitors, iterators, and utility functions for collecting
//! subterms, free variables, and other structural information.

use super::{TermId, TermKind, TermManager};
#[allow(unused_imports)]
use crate::prelude::*;
use smallvec::SmallVec;

/// Visitor trait for traversing term DAGs
pub trait TermVisitor {
    /// Visit a term (pre-order)
    fn visit_pre(&mut self, term_id: TermId, manager: &TermManager) -> VisitorAction {
        let _ = (term_id, manager);
        VisitorAction::Continue
    }

    /// Visit a term (post-order, after visiting children)
    fn visit_post(&mut self, term_id: TermId, manager: &TermManager) {
        let _ = (term_id, manager);
    }
}

/// Action to take after visiting a term
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum VisitorAction {
    /// Continue traversing children
    Continue,
    /// Skip children of this term
    SkipChildren,
    /// Stop traversal completely
    Stop,
}

/// Traverse a term DAG with a visitor
pub fn traverse<V: TermVisitor>(
    term_id: TermId,
    manager: &TermManager,
    visitor: &mut V,
) -> Result<(), TraversalError> {
    let mut visited = FxHashSet::default();
    let mut stack = vec![(term_id, false)]; // (term_id, post_visit)

    while let Some((current_id, is_post)) = stack.pop() {
        if is_post {
            visitor.visit_post(current_id, manager);
            continue;
        }

        // Pre-visit
        let action = visitor.visit_pre(current_id, manager);

        match action {
            VisitorAction::Stop => return Ok(()),
            VisitorAction::SkipChildren => continue,
            VisitorAction::Continue => {}
        }

        // Avoid revisiting (DAG not tree)
        if !visited.insert(current_id) {
            continue;
        }

        // Schedule post-visit
        stack.push((current_id, true));

        // Push children for pre-visit
        if let Some(term) = manager.get(current_id) {
            let children = get_children(&term.kind);
            for &child in children.iter().rev() {
                stack.push((child, false));
            }
        }
    }

    Ok(())
}

/// Traversal error
#[derive(Debug, Clone, thiserror::Error)]
pub enum TraversalError {
    /// Term not found
    #[error("Term not found: {0:?}")]
    TermNotFound(TermId),
}

/// Get immediate children of a term
#[must_use]
pub fn get_children(kind: &TermKind) -> SmallVec<[TermId; 4]> {
    let mut children = SmallVec::new();

    match kind {
        // Nullary
        TermKind::True
        | TermKind::False
        | TermKind::IntConst(_)
        | TermKind::RealConst(_)
        | TermKind::BitVecConst { .. }
        | TermKind::StringLit(_)
        | TermKind::Var(_) => {}

        // Unary
        TermKind::Not(a)
        | TermKind::Neg(a)
        | TermKind::BvNot(a)
        | TermKind::StrLen(a)
        | TermKind::StrToInt(a)
        | TermKind::IntToStr(a)
        | TermKind::StrToCode(a)
        | TermKind::StrFromCode(a) => {
            children.push(*a);
        }

        TermKind::BvExtract { arg, .. } => {
            children.push(*arg);
        }

        // Binary
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
        | TermKind::StrConcat(a, b)
        | TermKind::StrAt(a, b)
        | TermKind::StrContains(a, b)
        | TermKind::StrPrefixOf(a, b)
        | TermKind::StrSuffixOf(a, b)
        | TermKind::StrInRe(a, b)
        | TermKind::StrLt(a, b)
        | TermKind::StrLe(a, b)
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
        | TermKind::BvSle(a, b) => {
            children.push(*a);
            children.push(*b);
        }

        // Ternary
        TermKind::Ite(c, t, e)
        | TermKind::Store(c, t, e)
        | TermKind::StrSubstr(c, t, e)
        | TermKind::StrIndexOf(c, t, e)
        | TermKind::StrReplace(c, t, e)
        | TermKind::StrReplaceAll(c, t, e)
        | TermKind::StrReplaceRe(c, t, e)
        | TermKind::StrReplaceReAll(c, t, e) => {
            children.push(*c);
            children.push(*t);
            children.push(*e);
        }

        // N-ary
        TermKind::And(args)
        | TermKind::Or(args)
        | TermKind::Add(args)
        | TermKind::Mul(args)
        | TermKind::Distinct(args) => {
            children.extend(args.iter().copied());
        }

        // Function application
        TermKind::Apply { args, .. } => {
            children.extend(args.iter().copied());
        }

        // Algebraic datatypes
        TermKind::DtConstructor { args, .. } => {
            children.extend(args.iter().copied());
        }
        TermKind::DtTester { arg, .. } | TermKind::DtSelector { arg, .. } => {
            children.push(*arg);
        }

        // Quantifiers
        TermKind::Forall { body, .. } | TermKind::Exists { body, .. } => {
            children.push(*body);
        }

        // Let bindings
        TermKind::Let { bindings, body } => {
            for (_, value) in bindings {
                children.push(*value);
            }
            children.push(*body);
        }

        // Floating-point literals have no children
        TermKind::FpLit { .. }
        | TermKind::FpPlusInfinity { .. }
        | TermKind::FpMinusInfinity { .. }
        | TermKind::FpPlusZero { .. }
        | TermKind::FpMinusZero { .. }
        | TermKind::FpNaN { .. } => {}

        // Unary FP operations
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
        | TermKind::UBVToFp { arg: a, .. } => {
            children.push(*a);
        }

        // Binary FP operations
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
        | TermKind::FpEq(a, b) => {
            children.push(*a);
            children.push(*b);
        }

        // Ternary FP operations
        TermKind::FpFma(_, a, b, c) => {
            children.push(*a);
            children.push(*b);
            children.push(*c);
        }

        // Match expression
        TermKind::Match { scrutinee, cases } => {
            children.push(*scrutinee);
            for case in cases {
                children.push(case.body);
            }
        }
    }

    children
}

/// Collect all subterms (including the term itself) in post-order
#[must_use]
pub fn collect_subterms(term_id: TermId, manager: &TermManager) -> Vec<TermId> {
    struct Collector {
        subterms: Vec<TermId>,
        visited: FxHashSet<TermId>,
    }

    impl TermVisitor for Collector {
        fn visit_post(&mut self, term_id: TermId, _manager: &TermManager) {
            if self.visited.insert(term_id) {
                self.subterms.push(term_id);
            }
        }
    }

    let mut collector = Collector {
        subterms: Vec::new(),
        visited: FxHashSet::default(),
    };

    let _ = traverse(term_id, manager, &mut collector);
    collector.subterms
}

/// Collect all free variables in a term.
///
/// Delegates to [`TermManager::free_vars`], which does the actual
/// (name, sort)-aware, capture-scope-correct walk with an explicit heap
/// stack. This function used to carry its own independent implementation
/// built directly on [`traverse`]'s generic, globally-memoized visitor,
/// but that turned out to have two correctness bugs:
///
/// * Shadowing was tracked by variable *name* alone, ignoring sort, so a
///   bound `x: Bool` in an enclosing scope could incorrectly shadow an
///   unrelated, differently-sorted free `x: Int`.
/// * `traverse`'s visited set is global and unconditional: once a shared
///   subterm (structural sharing under hash-consing) was walked once
///   *while under a binder* that happened to shadow one of its
///   variables, revisiting that exact subterm later from an unshadowed
///   position would be skipped as "already visited", silently dropping a
///   genuinely free occurrence.
///
/// Both bugs matter here specifically: this function is called by
/// `TermManager::prepare_binder_subst` (capture-avoiding substitution's
/// name-avoidance computation) and by `nixie-solver`'s MBQI instantiation
/// checking, which rejects a grounding substitution if a bound variable
/// it meant to eliminate is still reported free in the result -- an
/// under-reported free-variable set there would let a not-fully-grounded
/// lemma silently pass. Rather than fix this independent implementation
/// in place and risk it diverging from `TermManager::free_vars` again
/// later (this crate has hit that exact hazard before with this same
/// module's [`map_terms`] and its retired `transform_children`), this now
/// simply reuses the one, already-hardened implementation.
///
/// # Trigger patterns are *not* included
///
/// Like [`get_children`] (and therefore like every generic walk in this
/// module), this ignores a `Forall`/`Exists` node's `patterns` field, so a
/// variable occurring only inside an SMT-LIB `:pattern` / trigger
/// annotation is not reported. Callers whose result drives a decision
/// about variable *names* -- capture avoidance, fresh-name choice,
/// groundedness of an instantiation -- must use
/// [`collect_free_vars_including_patterns`] instead, because a name that
/// is invisible here can still be captured. That includes
/// `TermManager::prepare_binder_subst` and `nixie-solver`'s MBQI grounding
/// guard, both of which have been switched over.
#[must_use]
pub fn collect_free_vars(term_id: TermId, manager: &TermManager) -> FxHashSet<TermId> {
    manager.free_vars(term_id).into_iter().collect()
}

/// Collect all free variables in a term, including occurrences that appear
/// only inside `Forall`/`Exists` trigger patterns.
///
/// Delegates to [`TermManager::free_vars_including_patterns`]; see
/// [`collect_free_vars`] for the non-pattern-aware variant and for why
/// both exist.
///
/// Use this one whenever the answer decides something about variable
/// *names*: over-reporting a free variable merely makes substitution pick
/// a different fresh name, whereas under-reporting silently captures a
/// live occurrence.
#[must_use]
pub fn collect_free_vars_including_patterns(
    term_id: TermId,
    manager: &TermManager,
) -> FxHashSet<TermId> {
    manager
        .free_vars_including_patterns(term_id)
        .into_iter()
        .collect()
}

/// Count the number of nodes in the term DAG
#[must_use]
pub fn count_nodes(term_id: TermId, manager: &TermManager) -> usize {
    collect_subterms(term_id, manager).len()
}

/// Compute the depth (height) of a term
#[must_use]
pub fn compute_depth(term_id: TermId, manager: &TermManager) -> usize {
    struct DepthCalculator {
        depths: crate::prelude::FxHashMap<TermId, usize>,
    }

    impl TermVisitor for DepthCalculator {
        fn visit_post(&mut self, term_id: TermId, manager: &TermManager) {
            if let Some(term) = manager.get(term_id) {
                let children = get_children(&term.kind);
                let max_child_depth = children
                    .iter()
                    .filter_map(|&child| self.depths.get(&child))
                    .max()
                    .unwrap_or(&0);
                self.depths.insert(term_id, max_child_depth + 1);
            }
        }
    }

    let mut calculator = DepthCalculator {
        depths: crate::prelude::FxHashMap::default(),
    };

    let _ = traverse(term_id, manager, &mut calculator);
    calculator.depths.get(&term_id).copied().unwrap_or(0)
}

/// Check if a term contains a specific subterm
#[must_use]
pub fn contains_term(haystack: TermId, needle: TermId, manager: &TermManager) -> bool {
    struct ContainsChecker {
        needle: TermId,
        found: bool,
    }

    impl TermVisitor for ContainsChecker {
        fn visit_pre(&mut self, term_id: TermId, _manager: &TermManager) -> VisitorAction {
            if term_id == self.needle {
                self.found = true;
                VisitorAction::Stop
            } else {
                VisitorAction::Continue
            }
        }
    }

    let mut checker = ContainsChecker {
        needle,
        found: false,
    };

    let _ = traverse(haystack, manager, &mut checker);
    checker.found
}

/// Map a function over all subterms (bottom-up).
///
/// `f` is offered every subterm (post-order, each visited once); returning
/// `Some(new_id)` replaces that subterm everywhere it occurs, `None` leaves
/// it as-is (its own children may still have been replaced).
///
/// This delegates the actual rebuild to `TermManager::substitute` -- the
/// single exhaustive, capture-avoiding implementation of "rebuild a term
/// given a subterm replacement map" in `TermManager::substitute`.
/// Previously this function carried its own parallel match over every
/// `TermKind` variant (`transform_children`); keeping two such matches in
/// sync is a soundness hazard (a variant added to one and missed in the
/// other silently drops rewrites), and the duplicate additionally lacked
/// `substitute`'s capture-avoidance for `Forall`/`Exists`/`Let`/`Match`
/// binders, so replacing a subterm that happens to share a hash-consed
/// `Var` id with some binder's bound variable name could have captured it.
pub fn map_terms<F>(term_id: TermId, manager: &mut TermManager, mut f: F) -> TermId
where
    F: FnMut(TermId, &TermManager) -> Option<TermId>,
{
    use crate::prelude::FxHashMap;

    let subterms = collect_subterms(term_id, manager);
    let mut direct: FxHashMap<TermId, TermId> = FxHashMap::default();
    for &subterm_id in &subterms {
        if let Some(new_id) = f(subterm_id, manager) {
            direct.insert(subterm_id, new_id);
        }
    }

    if direct.is_empty() {
        return term_id;
    }

    manager.substitute(term_id, &direct)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::ast::TermManager;

    #[test]
    fn test_collect_subterms() {
        let mut manager = TermManager::new();

        // (+ 1 2)
        let one = manager.mk_int(1);
        let two = manager.mk_int(2);
        let sum = manager.mk_add([one, two]);

        let subterms = collect_subterms(sum, &manager);
        // Should contain: 1, 2, (+ 1 2)
        assert_eq!(subterms.len(), 3);
        assert!(subterms.contains(&one));
        assert!(subterms.contains(&two));
        assert!(subterms.contains(&sum));
    }

    #[test]
    fn test_collect_free_vars() {
        let mut manager = TermManager::new();

        // (+ x y)
        let x = manager.mk_var("x", manager.sorts.int_sort);
        let y = manager.mk_var("y", manager.sorts.int_sort);
        let sum = manager.mk_add([x, y]);

        let free_vars = collect_free_vars(sum, &manager);
        assert_eq!(free_vars.len(), 2);
        assert!(free_vars.contains(&x));
        assert!(free_vars.contains(&y));
    }

    #[test]
    fn test_compute_depth() {
        let mut manager = TermManager::new();

        // (+ (+ 1 2) 3)
        let one = manager.mk_int(1);
        let two = manager.mk_int(2);
        let three = manager.mk_int(3);
        let inner_sum = manager.mk_add([one, two]);
        let outer_sum = manager.mk_add([inner_sum, three]);

        assert_eq!(compute_depth(one, &manager), 1);
        assert_eq!(compute_depth(inner_sum, &manager), 2);
        assert_eq!(compute_depth(outer_sum, &manager), 3);
    }

    #[test]
    fn test_contains_term() {
        let mut manager = TermManager::new();

        let one = manager.mk_int(1);
        let two = manager.mk_int(2);
        let three = manager.mk_int(3);
        let sum = manager.mk_add([one, two]);

        assert!(contains_term(sum, one, &manager));
        assert!(contains_term(sum, two, &manager));
        assert!(!contains_term(sum, three, &manager));
    }

    #[test]
    fn test_count_nodes() {
        let mut manager = TermManager::new();

        // (+ 1 2 3)
        let one = manager.mk_int(1);
        let two = manager.mk_int(2);
        let three = manager.mk_int(3);
        let sum = manager.mk_add([one, two, three]);

        // Should count: 1, 2, 3, (+ 1 2 3) = 4 nodes
        assert_eq!(count_nodes(sum, &manager), 4);
    }

    #[test]
    fn test_map_terms_basic_substitution() {
        let mut manager = TermManager::new();
        let x = manager.mk_var("x", manager.sorts.int_sort);
        let y = manager.mk_var("y", manager.sorts.int_sort);
        let one = manager.mk_int(1);
        let expr = manager.mk_add([x, one]);

        let result = map_terms(
            expr,
            &mut manager,
            |id, _mgr| {
                if id == x { Some(y) } else { None }
            },
        );

        let expected = manager.mk_add([y, one]);
        assert_eq!(result, expected);
    }

    #[test]
    fn test_map_terms_does_not_capture_bound_variable() {
        // Regression: map_terms used to rebuild children via a flat, private
        // TermId -> TermId cache (`transform_children`) with no binder-scope
        // awareness. Since bound and free occurrences of a same-named
        // variable share one hash-consed `TermId`, replacing the free
        // occurrence of `x` used to also silently rewrite the *bound* `x`
        // inside `forall ((x Int)) ...`, capturing it. map_terms now
        // delegates to `TermManager::substitute`, the shared exhaustive,
        // capture-avoiding implementation, which must leave the bound
        // occurrence untouched.
        let mut manager = TermManager::new();
        let int_sort = manager.sorts.int_sort;
        let bool_sort = manager.sorts.bool_sort;

        let x = manager.mk_var("x", int_sort);
        let y = manager.mk_var("y", int_sort);
        // Outer: P(x) -- free occurrence of x.
        let p_outer = manager.mk_apply("P", [x], bool_sort);
        // Inner: forall x. Q(x) -- x is bound here, shadowing the outer x.
        let q_inner = manager.mk_apply("Q", [x], bool_sort);
        let forall = manager.mk_forall([("x", int_sort)], q_inner);
        let term = manager.mk_and([p_outer, forall]);

        // Replace every occurrence of the `x` TermId with `y`.
        let result = map_terms(
            term,
            &mut manager,
            |id, _mgr| {
                if id == x { Some(y) } else { None }
            },
        );

        // The free occurrence must be rewritten: P(x) -> P(y).
        let p_outer_new = manager.mk_apply("P", [y], bool_sort);
        // The bound occurrence must NOT be captured: the forall body must
        // stay Q(x), not become Q(y).
        let q_inner_same = manager.mk_apply("Q", [x], bool_sort);
        let forall_same = manager.mk_forall([("x", int_sort)], q_inner_same);
        let expected = manager.mk_and([p_outer_new, forall_same]);

        assert_eq!(result, expected);
    }

    #[test]
    fn test_visitor_pattern() {
        struct CountVisitor {
            count: usize,
        }

        impl TermVisitor for CountVisitor {
            fn visit_pre(&mut self, _term_id: TermId, _manager: &TermManager) -> VisitorAction {
                self.count += 1;
                VisitorAction::Continue
            }
        }

        let mut manager = TermManager::new();
        let one = manager.mk_int(1);
        let two = manager.mk_int(2);
        let sum = manager.mk_add([one, two]);

        let mut visitor = CountVisitor { count: 0 };
        traverse(sum, &manager, &mut visitor).expect("test operation should succeed");

        // Should visit each node once (due to visited set)
        assert_eq!(visitor.count, 3);
    }
}
