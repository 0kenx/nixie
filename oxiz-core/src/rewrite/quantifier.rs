//! Quantifier Term Rewriter
//!
//! This module provides rewriting rules for quantified formulas:
//! - Trivial quantifier simplification
//! - Unused variable elimination
//!
//! # Theory Background
//!
//! Quantifier rewriting is crucial for:
//! - Reducing quantifier scope
//! - Eliminating quantifiers when possible
//! - Normalizing quantified formulas
//! - Preparing for quantifier instantiation

use super::{RewriteContext, RewriteResult, Rewriter};
use crate::SortId;
use crate::ast::{TermId, TermKind, TermManager};
use crate::interner::Spur;
#[allow(unused_imports)]
use crate::prelude::*;
use smallvec::SmallVec;

/// Instantiation pattern type alias
pub type InstPattern = SmallVec<[SmallVec<[TermId; 2]>; 2]>;

/// Quantifier rewriter
#[derive(Debug, Clone)]
pub struct QuantifierRewriter {
    /// Enable unused variable elimination
    pub elim_unused_vars: bool,
    /// Enable trivial quantifier elimination
    pub elim_trivial: bool,
}

impl Default for QuantifierRewriter {
    fn default() -> Self {
        Self::new()
    }
}

impl QuantifierRewriter {
    /// Create a new quantifier rewriter
    pub fn new() -> Self {
        Self {
            elim_unused_vars: true,
            elim_trivial: true,
        }
    }

    /// Create with all optimizations enabled
    pub fn aggressive() -> Self {
        Self {
            elim_unused_vars: true,
            elim_trivial: true,
        }
    }

    /// Names occurring free in `term`, excluding anything in `bound`.
    ///
    /// Delegates to [`TermManager::free_vars_including_patterns`], the
    /// pattern-aware free-variable query. This module used to carry a third,
    /// independent free-variable walk (after `TermManager::free_vars` and
    /// `ast::traversal::collect_free_vars`, which already delegates to it),
    /// and that walk under-reported in three separate ways -- each of which
    /// makes `elim_unused_forall`/`elim_unused_exists` drop a binder for a
    /// variable that *is* used, turning a bound occurrence into a free one:
    ///
    /// * it ignored `Forall`/`Exists` `patterns`, so a variable used only in
    ///   a trigger looked unused;
    /// * it bailed out silently past a fixed recursion depth
    ///   (`max_depth`, since removed), so a deep body looked variable-free;
    /// * its final `_ => {}` arm silently dropped every kind it did not
    ///   enumerate -- `Let`, `Match`, all bit-vector, string and
    ///   floating-point operators, datatype constructors/selectors/testers --
    ///   so a variable used only under any of those looked unused.
    ///
    /// The shared implementation has none of those: it is iterative (no depth
    /// cap), enumerates leaves and binders explicitly and routes everything
    /// else through `get_children`, and is `(name, sort)`-aware.
    fn collect_free_vars(
        &self,
        term: TermId,
        bound: &FxHashSet<Spur>,
        manager: &TermManager,
    ) -> FxHashSet<Spur> {
        let mut free = FxHashSet::default();
        for var in manager.free_vars_including_patterns(term) {
            if let Some(TermKind::Var(name)) = manager.get(var).map(|t| &t.kind)
                && !bound.contains(name)
            {
                free.insert(*name);
            }
        }
        free
    }

    /// Names a quantifier's binder list may *not* drop: those occurring in
    /// its body, plus those occurring in its own trigger patterns.
    ///
    /// The patterns are siblings of the body, not subterms of it, so no walk
    /// of the body alone can see them. Eliminating a variable that a retained
    /// trigger still mentions would leave that trigger referring to a
    /// now-unbound name -- a dangling free variable manufactured out of a
    /// closed formula. Keeping the binder instead preserves the formula
    /// exactly (an unused-but-bound variable is semantically harmless).
    fn used_names(
        &self,
        body: TermId,
        patterns: &InstPattern,
        manager: &TermManager,
    ) -> FxHashSet<Spur> {
        let bound = FxHashSet::default();
        let mut used = self.collect_free_vars(body, &bound, manager);
        for pattern in patterns {
            for &trigger in pattern {
                used.extend(self.collect_free_vars(trigger, &bound, manager));
            }
        }
        used
    }

    /// Helper to create forall term from Spur-based vars
    fn create_forall(
        vars: &[(Spur, SortId)],
        body: TermId,
        patterns: &InstPattern,
        manager: &mut TermManager,
    ) -> TermId {
        // Convert Spur to String first to avoid borrowing issues
        let var_strs: Vec<(String, SortId)> = vars
            .iter()
            .map(|(spur, sort)| (manager.resolve_str(*spur).to_string(), *sort))
            .collect();

        // Now create the forall with string references
        let var_refs: Vec<(&str, SortId)> = var_strs
            .iter()
            .map(|(s, sort)| (s.as_str(), *sort))
            .collect();

        manager.mk_forall_with_patterns(var_refs, body, patterns.clone())
    }

    /// Helper to create exists term from Spur-based vars
    fn create_exists(
        vars: &[(Spur, SortId)],
        body: TermId,
        patterns: &InstPattern,
        manager: &mut TermManager,
    ) -> TermId {
        // Convert Spur to String first to avoid borrowing issues
        let var_strs: Vec<(String, SortId)> = vars
            .iter()
            .map(|(spur, sort)| (manager.resolve_str(*spur).to_string(), *sort))
            .collect();

        // Now create the exists with string references
        let var_refs: Vec<(&str, SortId)> = var_strs
            .iter()
            .map(|(s, sort)| (s.as_str(), *sort))
            .collect();

        manager.mk_exists_with_patterns(var_refs, body, patterns.clone())
    }

    /// Rewrite universal quantifier
    fn rewrite_forall(
        &mut self,
        vars: &SmallVec<[(Spur, SortId); 2]>,
        body: TermId,
        patterns: &InstPattern,
        ctx: &mut RewriteContext,
        manager: &mut TermManager,
    ) -> RewriteResult {
        // Empty quantifier: ∀. φ → φ
        if vars.is_empty() {
            ctx.stats_mut().record_rule("quant_empty_forall");
            return RewriteResult::Rewritten(body);
        }

        // Check for trivial cases in body
        if let Some(t) = manager.get(body).cloned() {
            match &t.kind {
                // ∀x. true → true
                TermKind::True => {
                    ctx.stats_mut().record_rule("quant_forall_true");
                    return RewriteResult::Rewritten(manager.mk_true());
                }
                // ∀x. false → false
                TermKind::False => {
                    ctx.stats_mut().record_rule("quant_forall_false");
                    return RewriteResult::Rewritten(manager.mk_false());
                }
                _ => {}
            }
        }

        // Eliminate unused variables
        if self.elim_unused_vars
            && let Some(result) = self.elim_unused_forall(vars, body, patterns, ctx, manager)
        {
            return result;
        }

        let vars_vec: Vec<(Spur, SortId)> = vars.iter().cloned().collect();
        RewriteResult::Unchanged(Self::create_forall(&vars_vec, body, patterns, manager))
    }

    /// Eliminate unused variables from forall
    fn elim_unused_forall(
        &mut self,
        vars: &SmallVec<[(Spur, SortId); 2]>,
        body: TermId,
        patterns: &InstPattern,
        ctx: &mut RewriteContext,
        manager: &mut TermManager,
    ) -> Option<RewriteResult> {
        let free = self.used_names(body, patterns, manager);

        let used_vars: Vec<(Spur, SortId)> = vars
            .iter()
            .filter(|(name, _)| free.contains(name))
            .cloned()
            .collect();

        if used_vars.len() < vars.len() {
            ctx.stats_mut().record_rule("quant_elim_unused");
            if used_vars.is_empty() {
                return Some(RewriteResult::Rewritten(body));
            }
            return Some(RewriteResult::Rewritten(Self::create_forall(
                &used_vars, body, patterns, manager,
            )));
        }
        None
    }

    /// Rewrite existential quantifier
    fn rewrite_exists(
        &mut self,
        vars: &SmallVec<[(Spur, SortId); 2]>,
        body: TermId,
        patterns: &InstPattern,
        ctx: &mut RewriteContext,
        manager: &mut TermManager,
    ) -> RewriteResult {
        // Empty quantifier: ∃. φ → φ
        if vars.is_empty() {
            ctx.stats_mut().record_rule("quant_empty_exists");
            return RewriteResult::Rewritten(body);
        }

        // Check for trivial cases
        if let Some(t) = manager.get(body).cloned() {
            match &t.kind {
                // ∃x. true → true
                TermKind::True => {
                    ctx.stats_mut().record_rule("quant_exists_true");
                    return RewriteResult::Rewritten(manager.mk_true());
                }
                // ∃x. false → false
                TermKind::False => {
                    ctx.stats_mut().record_rule("quant_exists_false");
                    return RewriteResult::Rewritten(manager.mk_false());
                }
                _ => {}
            }
        }

        // Eliminate unused variables
        if self.elim_unused_vars
            && let Some(result) = self.elim_unused_exists(vars, body, patterns, ctx, manager)
        {
            return result;
        }

        let vars_vec: Vec<(Spur, SortId)> = vars.iter().cloned().collect();
        RewriteResult::Unchanged(Self::create_exists(&vars_vec, body, patterns, manager))
    }

    /// Eliminate unused variables from exists
    fn elim_unused_exists(
        &mut self,
        vars: &SmallVec<[(Spur, SortId); 2]>,
        body: TermId,
        patterns: &InstPattern,
        ctx: &mut RewriteContext,
        manager: &mut TermManager,
    ) -> Option<RewriteResult> {
        let free = self.used_names(body, patterns, manager);

        let used_vars: Vec<(Spur, SortId)> = vars
            .iter()
            .filter(|(name, _)| free.contains(name))
            .cloned()
            .collect();

        if used_vars.len() < vars.len() {
            ctx.stats_mut().record_rule("quant_elim_unused");
            if used_vars.is_empty() {
                return Some(RewriteResult::Rewritten(body));
            }
            return Some(RewriteResult::Rewritten(Self::create_exists(
                &used_vars, body, patterns, manager,
            )));
        }
        None
    }
}

impl Rewriter for QuantifierRewriter {
    fn rewrite(
        &mut self,
        term: TermId,
        ctx: &mut RewriteContext,
        manager: &mut TermManager,
    ) -> RewriteResult {
        let Some(t) = manager.get(term).cloned() else {
            return RewriteResult::Unchanged(term);
        };

        match &t.kind {
            TermKind::Forall {
                vars,
                body,
                patterns,
            } => self.rewrite_forall(vars, *body, patterns, ctx, manager),
            TermKind::Exists {
                vars,
                body,
                patterns,
            } => self.rewrite_exists(vars, *body, patterns, ctx, manager),
            _ => RewriteResult::Unchanged(term),
        }
    }

    fn name(&self) -> &str {
        "QuantifierRewriter"
    }

    fn can_handle(&self, term: TermId, manager: &TermManager) -> bool {
        let Some(t) = manager.get(term) else {
            return false;
        };

        matches!(t.kind, TermKind::Forall { .. } | TermKind::Exists { .. })
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn setup() -> (TermManager, RewriteContext, QuantifierRewriter) {
        (
            TermManager::new(),
            RewriteContext::new(),
            QuantifierRewriter::new(),
        )
    }

    #[test]
    fn test_forall_true() {
        let (mut manager, mut ctx, mut rewriter) = setup();

        let int_sort = manager.sorts.int_sort;
        let body = manager.mk_true();
        let forall = manager.mk_forall([("x", int_sort)], body);

        let result = rewriter.rewrite(forall, &mut ctx, &mut manager);
        assert!(result.was_rewritten());

        let t = manager.get(result.term()).expect("term");
        assert!(matches!(t.kind, TermKind::True));
    }

    #[test]
    fn test_exists_false() {
        let (mut manager, mut ctx, mut rewriter) = setup();

        let int_sort = manager.sorts.int_sort;
        let body = manager.mk_false();
        let exists = manager.mk_exists([("x", int_sort)], body);

        let result = rewriter.rewrite(exists, &mut ctx, &mut manager);
        assert!(result.was_rewritten());

        let t = manager.get(result.term()).expect("term");
        assert!(matches!(t.kind, TermKind::False));
    }

    #[test]
    fn test_elim_unused_forall() {
        let (mut manager, mut ctx, mut rewriter) = setup();

        let int_sort = manager.sorts.int_sort;
        let y_spur = manager.intern_str("y");

        // ∀x, y. y > 0 → ∀y. y > 0 (x is unused)
        let y_var = manager.mk_var("y", int_sort);
        let zero = manager.mk_int(0);
        let body = manager.mk_gt(y_var, zero);
        let forall = manager.mk_forall([("x", int_sort), ("y", int_sort)], body);

        let result = rewriter.rewrite(forall, &mut ctx, &mut manager);
        assert!(result.was_rewritten());

        let t = manager.get(result.term()).expect("term");
        if let TermKind::Forall { vars, .. } = &t.kind {
            assert_eq!(vars.len(), 1);
            assert_eq!(vars[0].0, y_spur);
        } else {
            panic!("Expected Forall term");
        }
    }

    #[test]
    fn test_elim_unused_exists() {
        let (mut manager, mut ctx, mut rewriter) = setup();

        let int_sort = manager.sorts.int_sort;
        let y_spur = manager.intern_str("y");

        // ∃x, y. y > 0 → ∃y. y > 0 (x is unused)
        let y_var = manager.mk_var("y", int_sort);
        let zero = manager.mk_int(0);
        let body = manager.mk_gt(y_var, zero);
        let exists = manager.mk_exists([("x", int_sort), ("y", int_sort)], body);

        let result = rewriter.rewrite(exists, &mut ctx, &mut manager);
        assert!(result.was_rewritten());

        let t = manager.get(result.term()).expect("term");
        if let TermKind::Exists { vars, .. } = &t.kind {
            assert_eq!(vars.len(), 1);
            assert_eq!(vars[0].0, y_spur);
        } else {
            panic!("Expected Exists term");
        }
    }

    #[test]
    fn test_empty_forall() {
        let (mut manager, mut ctx, mut rewriter) = setup();

        let body = manager.mk_true();
        // Use empty array for vars
        let forall = manager.mk_forall(core::iter::empty::<(&str, SortId)>(), body);

        let result = rewriter.rewrite(forall, &mut ctx, &mut manager);
        // Empty forall returns body directly, which is already true
        // The result should be the body itself
        assert_eq!(result.term(), body);
    }

    #[test]
    fn test_collect_free_vars() {
        let (mut manager, _ctx, rewriter) = setup();

        let int_sort = manager.sorts.int_sort;
        let x_var = manager.mk_var("x", int_sort);
        let y_var = manager.mk_var("y", int_sort);
        let expr = manager.mk_add(vec![x_var, y_var]);

        let bound = FxHashSet::default();
        let free = rewriter.collect_free_vars(expr, &bound, &manager);

        let x = manager.intern_str("x");
        let y = manager.intern_str("y");
        assert!(free.contains(&x));
        assert!(free.contains(&y));
    }

    /// Regression: unused-variable elimination used a free-variable walk
    /// that ignored the quantifier's own trigger patterns, so a variable
    /// referenced *only* by a trigger looked unused and its binder was
    /// dropped -- leaving the retained trigger mentioning a name nothing
    /// binds any more.
    #[test]
    fn elim_unused_keeps_variable_used_only_in_a_trigger() {
        let (mut manager, mut ctx, mut rewriter) = setup();

        let int_sort = manager.sorts.int_sort;
        let y_var = manager.mk_var("y", int_sort);
        let x_var = manager.mk_var("x", int_sort);
        let zero = manager.mk_int(0);
        let body = manager.mk_gt(y_var, zero);
        let trigger = manager.mk_apply("f", [x_var], int_sort);

        // (forall ((x Int) (y Int)) (! (> y 0) :pattern ((f x))))
        let forall = manager.mk_forall_with_patterns(
            [("x", int_sort), ("y", int_sort)],
            body,
            [vec![trigger]],
        );

        let result = rewriter.rewrite(forall, &mut ctx, &mut manager);
        let t = manager.get(result.term()).expect("term");
        let TermKind::Forall { vars, .. } = &t.kind else {
            panic!("Expected Forall term, got {:?}", t.kind);
        };
        assert_eq!(
            vars.len(),
            2,
            "x is referenced by the trigger, so its binder must be kept"
        );
    }
}
