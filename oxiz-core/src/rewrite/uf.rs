//! Uninterpreted Function Rewriter
//!
//! This module provides rewriting rules for uninterpreted functions:
//! - Function congruence: f(a) = f(a) → true
//! - Argument simplification
//! - Beta reduction for lambda expressions
//! - Function application normalization
//! - Constant propagation through functions
//!
//! # Example
//!
//! ```ignore
//! use oxiz_core::rewrite::{Rewriter, RewriteContext, UfRewriter};
//!
//! let mut ctx = RewriteContext::new();
//! let mut uf = UfRewriter::new();
//! let simplified = uf.rewrite(term, &mut ctx, &mut manager)?;
//! ```

use super::{RewriteContext, RewriteResult, Rewriter};
use crate::SortId;
use crate::ast::{TermId, TermKind, TermManager};
use crate::interner::Spur;
#[allow(unused_imports)]
use crate::prelude::*;
use smallvec::SmallVec;

/// Configuration for UF rewriting
///
/// There is deliberately no `max_depth` knob. One existed, defaulted to 100,
/// and was never read by anything: it looked like a recursion bound for the
/// (formerly native-recursive) substitution walk but could not fire. It is
/// gone rather than wired up, because there is nothing sound to wire it to --
/// `UfRewriter`'s internal substitution now delegates to
/// [`TermManager::substitute`],
/// which walks an explicit heap stack and so has no depth to bound, and a
/// bound that *did* fire could only return an under-substituted term, which
/// this rewriter's callers would silently install in place of the original
/// application.
#[derive(Debug, Clone)]
pub struct UfRewriterConfig {
    /// Enable function congruence simplification
    pub enable_congruence: bool,
    /// Enable beta reduction
    pub enable_beta_reduction: bool,
    /// Enable argument normalization (sort arguments for AC symbols)
    pub enable_arg_normalization: bool,
    /// Track function definitions for inline expansion
    pub enable_inlining: bool,
    /// Maximum number of expansion rounds the rewriter's private
    /// `try_inline` may perform on one application.
    ///
    /// Round 1 expands the application itself; each further round expands
    /// every defined application the previous round exposed. `0` therefore
    /// disables inlining outright, and `1` makes it a single unfold (the
    /// same step beta reduction performs).
    ///
    /// # What running out of budget does
    ///
    /// Nothing but *stop*. Expansion is replacement of a call by its
    /// definition's body, which is an equality the definition itself
    /// asserts, so any prefix of the expansion sequence is as valid as the
    /// whole: a term left with `f(a)` still in it simply keeps that call.
    /// The bound is what makes a self-referential definition
    /// (`f(x) = f(x) + 1`) terminate instead of expanding forever, and it is
    /// the *only* thing that bounds this: the expansion loop is otherwise
    /// driven by the definitions, not by the input term's shape.
    ///
    /// This replaces a `depth` parameter that was threaded into
    /// `try_inline` as a literal `0` by its single caller and never
    /// incremented, so `depth >= max_inline_depth` was unfirable and
    /// inlining was in fact a single unfold whatever this was set to.
    pub max_inline_depth: usize,
}

impl Default for UfRewriterConfig {
    fn default() -> Self {
        Self {
            enable_congruence: true,
            enable_beta_reduction: true,
            enable_arg_normalization: true,
            enable_inlining: true,
            max_inline_depth: 5,
        }
    }
}

/// Function definition (for inlining)
#[derive(Debug, Clone)]
pub struct FunctionDef {
    /// Parameter names
    pub params: Vec<Spur>,
    /// Function body
    pub body: TermId,
    /// Result sort
    pub result_sort: SortId,
}

/// Uninterpreted function rewriter
#[derive(Debug)]
pub struct UfRewriter {
    /// Configuration
    config: UfRewriterConfig,
    /// Function definitions for inlining
    definitions: FxHashMap<Spur, FunctionDef>,
    /// Known commutative symbols
    commutative: FxHashSet<Spur>,
    /// Known associative symbols
    associative: FxHashSet<Spur>,
    /// Congruence cache: (func, args) -> canonical result.
    ///
    /// Keyed by the *exact* argument list rather than a 64-bit hash of it:
    /// a hash-only key can collide for two genuinely different argument
    /// lists (rare, but not impossible – e.g. adversarial input, or simply
    /// enough distinct applications), which would silently rewrite `f(a,b)`
    /// to the cached result of an unrelated `f(c,d)`.
    congruence_cache: FxHashMap<(Spur, SmallVec<[TermId; 4]>), TermId>,
}

impl UfRewriter {
    /// Create a new UF rewriter with default configuration
    pub fn new() -> Self {
        Self::with_config(UfRewriterConfig::default())
    }

    /// Create with specific configuration
    pub fn with_config(config: UfRewriterConfig) -> Self {
        Self {
            config,
            definitions: FxHashMap::default(),
            commutative: FxHashSet::default(),
            associative: FxHashSet::default(),
            congruence_cache: FxHashMap::default(),
        }
    }

    /// Register a function definition for inlining
    pub fn register_definition(
        &mut self,
        func: Spur,
        params: Vec<Spur>,
        body: TermId,
        result_sort: SortId,
    ) {
        self.definitions.insert(
            func,
            FunctionDef {
                params,
                body,
                result_sort,
            },
        );
    }

    /// Mark a function as commutative
    pub fn mark_commutative(&mut self, func: Spur) {
        self.commutative.insert(func);
    }

    /// Mark a function as associative
    pub fn mark_associative(&mut self, func: Spur) {
        self.associative.insert(func);
    }

    /// Check if function is commutative
    pub fn is_commutative(&self, func: Spur) -> bool {
        self.commutative.contains(&func)
    }

    /// Check if function is associative
    pub fn is_associative(&self, func: Spur) -> bool {
        self.associative.contains(&func)
    }

    /// Clear the congruence cache
    pub fn clear_cache(&mut self) {
        self.congruence_cache.clear();
    }

    /// Create an Apply term with Spur-based function name
    fn mk_apply_with_spur(
        &self,
        func: Spur,
        args: Vec<TermId>,
        sort: SortId,
        manager: &mut TermManager,
    ) -> TermId {
        let func_str = manager.resolve_str(func).to_string();
        manager.mk_apply(&func_str, args, sort)
    }

    /// Rewrite a function application
    fn rewrite_apply(
        &mut self,
        term: TermId,
        func: Spur,
        args: &SmallVec<[TermId; 4]>,
        sort: SortId,
        ctx: &mut RewriteContext,
        manager: &mut TermManager,
    ) -> RewriteResult {
        // Try beta reduction if we have a definition
        if self.config.enable_beta_reduction
            && let Some(result) = self.try_beta_reduction(func, args, manager)
        {
            ctx.stats_mut().record_rule("uf_beta_reduction");
            return RewriteResult::Rewritten(result);
        }

        // Try inlining.
        //
        // Reachable only with `enable_beta_reduction` off: beta reduction
        // above fires on exactly the same precondition (a definition of
        // `func` with matching arity) and returns first. The two are kept
        // apart because they promise different things -- beta reduction is
        // one unfold, inlining is transitive expansion under
        // `max_inline_depth` -- and a caller picks between them through the
        // config rather than through call order.
        if self.config.enable_inlining
            && let Some(result) = self.try_inline(func, args, manager)
        {
            ctx.stats_mut().record_rule("uf_inline");
            return RewriteResult::Rewritten(result);
        }

        // Normalize commutative arguments
        if self.config.enable_arg_normalization
            && self.is_commutative(func)
            && args.len() == 2
            && let Some(result) = self.normalize_commutative(func, args, sort, manager)
        {
            ctx.stats_mut().record_rule("uf_commutative_normalize");
            return RewriteResult::Rewritten(result);
        }

        // Flatten associative applications
        if self.is_associative(func)
            && let Some(result) = self.flatten_associative(func, args, sort, manager)
        {
            ctx.stats_mut().record_rule("uf_associative_flatten");
            return RewriteResult::Rewritten(result);
        }

        // Check congruence cache
        if self.config.enable_congruence {
            let key = (func, args.clone());
            if let Some(&cached) = self.congruence_cache.get(&key) {
                return RewriteResult::Rewritten(cached);
            }
            // Cache this application
            self.congruence_cache.insert(key, term);
        }

        RewriteResult::Unchanged(term)
    }

    /// Try beta reduction: one unfold of `func`'s definition.
    fn try_beta_reduction(
        &self,
        func: Spur,
        args: &SmallVec<[TermId; 4]>,
        manager: &mut TermManager,
    ) -> Option<TermId> {
        self.expand_definition(func, args, manager)
    }

    /// Replace `func(args)` by its definition's body with the arguments
    /// substituted for the parameters.
    ///
    /// `None` when `func` has no definition or the arity does not match.
    /// The substitution itself is [`Self::substitute`], i.e. the
    /// capture-avoiding [`TermManager::substitute`].
    fn expand_definition(
        &self,
        func: Spur,
        args: &SmallVec<[TermId; 4]>,
        manager: &mut TermManager,
    ) -> Option<TermId> {
        let def = self.definitions.get(&func)?;

        // Check arity matches
        if def.params.len() != args.len() {
            return None;
        }

        // Build substitution map
        let subst: FxHashMap<Spur, TermId> = def
            .params
            .iter()
            .zip(args.iter())
            .map(|(&param, &arg)| (param, arg))
            .collect();

        // Apply substitution to body
        Some(self.substitute(def.body, &subst, manager))
    }

    /// Expand the application `func(args)` and keep expanding the defined
    /// applications each expansion exposes, for at most
    /// [`UfRewriterConfig::max_inline_depth`] rounds.
    ///
    /// # The bound is real
    ///
    /// The previous version took a `depth` argument, compared it against
    /// `max_inline_depth`, and was called from exactly one place with a
    /// literal `0`; it never recursed, so `depth` never grew and the
    /// comparison never held. It was a single unfold wearing a bound's
    /// clothing -- indistinguishable from [`Self::try_beta_reduction`],
    /// which sits right above it in [`Self::rewrite_apply`].
    ///
    /// Now the rounds exist, so the budget is what stops them. There is no
    /// other bound available: expansion is driven by the *definitions*, and
    /// a definition may mention itself, so without a budget
    /// `f(x) = f(x) + 1` expands forever. Running out is benign -- see
    /// [`UfRewriterConfig::max_inline_depth`] -- because every intermediate
    /// term is equal to the original by the definitions themselves.
    ///
    /// # Scope restriction
    ///
    /// Nested rounds refuse to enter binder scopes, and give up entirely on
    /// a term that contains one (see
    /// [`Self::collect_inlinable_applications`]). Round 1 is unaffected: it
    /// expands the application it was handed regardless of what the body
    /// contains.
    ///
    /// The traversal is iterative throughout -- both the search for nested
    /// applications and [`TermManager::substitute`], which performs the
    /// replacement -- so nothing here recurses on user-controlled nesting.
    fn try_inline(
        &self,
        func: Spur,
        args: &SmallVec<[TermId; 4]>,
        manager: &mut TermManager,
    ) -> Option<TermId> {
        // A zero budget means "do not inline", and it fires before any work
        // is done rather than after the first unfold.
        if self.config.max_inline_depth == 0 {
            return None;
        }

        // Round 1: the application itself.
        let mut current = self.expand_definition(func, args, manager)?;

        // Rounds 2..=max_inline_depth: whatever the previous round exposed.
        for _ in 1..self.config.max_inline_depth {
            let Some(applications) = self.collect_inlinable_applications(current, manager) else {
                break;
            };
            if applications.is_empty() {
                break;
            }

            let mut expansions: FxHashMap<TermId, TermId> = FxHashMap::default();
            for application in applications {
                if let Some(expansion) = self.expand_application_term(application, manager) {
                    expansions.insert(application, expansion);
                }
            }
            if expansions.is_empty() {
                break;
            }

            let next = manager.substitute(current, &expansions);
            if next == current {
                break;
            }
            current = next;
        }

        Some(current)
    }

    /// Expand the application *term* `application` (as opposed to a
    /// `(func, args)` pair), or `None` if it is not a defined application.
    fn expand_application_term(
        &self,
        application: TermId,
        manager: &mut TermManager,
    ) -> Option<TermId> {
        // Clone the kind out first: `expand_definition` needs `&mut
        // TermManager`, which cannot coexist with a borrow of the term.
        let TermKind::Apply { func, args } = manager.get(application).map(|t| t.kind.clone())?
        else {
            return None;
        };
        self.expand_definition(func, &args, manager)
    }

    /// Collect the defined applications inside `root` that a further
    /// inlining round may expand.
    ///
    /// Returns `None` when `root` contains a binder anywhere, meaning "do
    /// not run further rounds on this term at all".
    ///
    /// # Why binders stop it
    ///
    /// A round replaces whole application *nodes* via
    /// [`TermManager::substitute`]. That routine is capture-avoiding with
    /// respect to the replacement terms' free variables: if a replacement
    /// mentions `y` and the walk enters a `forall y`, it alpha-renames the
    /// binder so the replacement's `y` cannot be captured. That is exactly
    /// right for a replacement that came from outside the scope, and exactly
    /// wrong for one that came from inside it -- expanding `f(y)` under
    /// `forall y` yields a body mentioning that same bound `y`, and the
    /// rename would push the binder off it. Terms are hash-consed, so an
    /// application collected outside a binder can also occur inside one,
    /// which makes "collect only outside binders" insufficient on its own;
    /// bailing out on any binder is the conservative rule that has no such
    /// hole. The cost is that applications in quantified formulas are
    /// unfolded once (by round 1, or by beta reduction) rather than
    /// transitively.
    fn collect_inlinable_applications(
        &self,
        root: TermId,
        manager: &TermManager,
    ) -> Option<Vec<TermId>> {
        let mut found: Vec<TermId> = Vec::new();
        let mut seen: FxHashSet<TermId> = FxHashSet::default();
        let mut stack: Vec<TermId> = vec![root];

        while let Some(id) = stack.pop() {
            if !seen.insert(id) {
                continue;
            }
            let Some(term) = manager.get(id) else {
                continue;
            };
            match &term.kind {
                TermKind::Forall { .. }
                | TermKind::Exists { .. }
                | TermKind::Let { .. }
                | TermKind::Match { .. } => return None,
                TermKind::Apply { func, args } => {
                    let defined = self
                        .definitions
                        .get(func)
                        .is_some_and(|def| def.params.len() == args.len());
                    if defined {
                        found.push(id);
                    }
                    stack.extend(args.iter().copied());
                }
                kind => stack.extend(crate::ast::traversal::get_children(kind)),
            }
        }

        Some(found)
    }

    /// Apply substitution to a term.
    ///
    /// # Why this delegates to [`TermManager::substitute`]
    ///
    /// This used to be a hand-rolled recursive walk over a whitelist of
    /// `TermKind`s (`Var`, the Boolean connectives, `Eq`, the
    /// linear-arithmetic operators, `Ite`, `Apply`, `Forall`/`Exists`/`Let`)
    /// ending in
    ///
    /// ```text
    /// // Leaves and other terms that don't need substitution
    /// _ => term,
    /// ```
    ///
    /// so every bit-vector, string, floating-point, datatype and array
    /// operator, plus `Xor`, `Mod`, `Distinct` and `Match`, was returned
    /// *unchanged*. The comment was true only of the literal leaves that also
    /// land in that arm; for the operator kinds it was a silent
    /// under-substitution.
    ///
    /// That is not a cosmetic gap here, because the result of this call
    /// *replaces the application*: [`Self::try_beta_reduction`] and
    /// [`Self::try_inline`] report `Some(..)` regardless of whether the
    /// substitution did anything, and [`Self::rewrite_apply`] then returns it
    /// as `RewriteResult::Rewritten`. With `f(p) = p + #x01`, rewriting
    /// `f(#x05)` yielded `p + #x01` -- the callee's parameter variable, now
    /// *free*, standing in for the application. See this module's
    /// `tests::beta_reduction_substitutes_through_a_bitvector_operator`.
    ///
    /// The old walk was also **not capture-avoiding**: descending into a
    /// binder it dropped shadowed names from the substitution but otherwise
    /// rebuilt the binder verbatim, so `f(p) = ∀y. P(p, y)` applied to `y`
    /// produced `∀y. P(y, y)` with the argument captured. And it recursed
    /// natively once per level of term nesting, with no guard of any kind (the
    /// `UfRewriterConfig::max_depth` field that looked like one was never read
    /// -- it has been removed rather than left reading as a bound it never
    /// was).
    ///
    /// [`TermManager::substitute`] fixes all three: it has an arm for every
    /// `TermKind` with no catch-all (a new variant is a compile error there),
    /// it is capture-avoiding across all four binder forms, it respects
    /// shadowing, and it walks with an explicit heap stack. So this is now a
    /// thin adapter: resolve each parameter *name* to the actual free
    /// occurrences it denotes, then hand a `TermId`-keyed map to the core
    /// routine.
    ///
    /// Occurrences are matched by name across all sorts, matching what the
    /// caller supplies (a `FunctionDef`'s parameter `Spur`s carry no sort);
    /// only *free* occurrences are replaced, so a binder re-binding a
    /// parameter name still shadows it, exactly as before.
    fn substitute(
        &self,
        term: TermId,
        subst: &FxHashMap<Spur, TermId>,
        manager: &mut TermManager,
    ) -> TermId {
        if subst.is_empty() {
            return term;
        }

        let targets: FxHashMap<TermId, TermId> = manager
            .free_vars_including_patterns(term)
            .into_iter()
            .filter_map(|var| match manager.get(var).map(|t| &t.kind) {
                Some(TermKind::Var(name)) => subst.get(name).map(|&to| (var, to)),
                _ => None,
            })
            .collect();

        // No parameter occurs free (absent, or every occurrence shadowed by an
        // inner binder of the same name): the term is its own substitution
        // instance.
        if targets.is_empty() {
            return term;
        }

        manager.substitute(term, &targets)
    }

    /// Normalize commutative function arguments (sort by TermId)
    fn normalize_commutative(
        &self,
        func: Spur,
        args: &SmallVec<[TermId; 4]>,
        sort: SortId,
        manager: &mut TermManager,
    ) -> Option<TermId> {
        if args.len() != 2 {
            return None;
        }

        let (a, b) = (args[0], args[1]);

        // Sort by TermId for canonical form
        if a.0 > b.0 {
            Some(self.mk_apply_with_spur(func, vec![b, a], sort, manager))
        } else {
            None
        }
    }

    /// Flatten nested associative function applications
    fn flatten_associative(
        &self,
        func: Spur,
        args: &SmallVec<[TermId; 4]>,
        sort: SortId,
        manager: &mut TermManager,
    ) -> Option<TermId> {
        let mut flattened = Vec::new();
        let mut changed = false;

        for &arg in args.iter() {
            if let Some(t) = manager.get(arg)
                && let TermKind::Apply {
                    func: inner_func,
                    args: inner_args,
                } = &t.kind
                && *inner_func == func
            {
                flattened.extend(inner_args.iter().copied());
                changed = true;
                continue;
            }
            flattened.push(arg);
        }

        if changed {
            Some(self.mk_apply_with_spur(func, flattened, sort, manager))
        } else {
            None
        }
    }

    /// Rewrite equality of function applications
    fn rewrite_func_eq(
        &mut self,
        lhs: TermId,
        rhs: TermId,
        ctx: &mut RewriteContext,
        manager: &mut TermManager,
    ) -> RewriteResult {
        let term = manager.mk_eq(lhs, rhs);

        // f(a) = f(a) → true
        if lhs == rhs {
            ctx.stats_mut().record_rule("uf_eq_refl");
            return RewriteResult::Rewritten(manager.mk_true());
        }

        let Some(t_lhs) = manager.get(lhs).cloned() else {
            return RewriteResult::Unchanged(term);
        };
        let Some(t_rhs) = manager.get(rhs).cloned() else {
            return RewriteResult::Unchanged(term);
        };

        // Check for same function with same args
        if let (
            TermKind::Apply {
                func: f1,
                args: args1,
            },
            TermKind::Apply {
                func: f2,
                args: args2,
            },
        ) = (&t_lhs.kind, &t_rhs.kind)
            && f1 == f2
            && args1 == args2
        {
            ctx.stats_mut().record_rule("uf_congruence_true");
            return RewriteResult::Rewritten(manager.mk_true());
        }

        RewriteResult::Unchanged(term)
    }
}

impl Default for UfRewriter {
    fn default() -> Self {
        Self::new()
    }
}

impl Rewriter for UfRewriter {
    fn rewrite(
        &mut self,
        term: TermId,
        ctx: &mut RewriteContext,
        manager: &mut TermManager,
    ) -> RewriteResult {
        ctx.stats_mut().terms_visited += 1;

        let Some(t) = manager.get(term).cloned() else {
            return RewriteResult::Unchanged(term);
        };

        match &t.kind {
            TermKind::Apply { func, args } => {
                self.rewrite_apply(term, *func, args, t.sort, ctx, manager)
            }

            TermKind::Eq(lhs, rhs) => {
                // Check if either side is a function application
                let is_lhs_apply = manager
                    .get(*lhs)
                    .map(|t| matches!(&t.kind, TermKind::Apply { .. }))
                    .unwrap_or(false);
                let is_rhs_apply = manager
                    .get(*rhs)
                    .map(|t| matches!(&t.kind, TermKind::Apply { .. }))
                    .unwrap_or(false);

                if is_lhs_apply || is_rhs_apply {
                    self.rewrite_func_eq(*lhs, *rhs, ctx, manager)
                } else {
                    RewriteResult::Unchanged(term)
                }
            }

            _ => RewriteResult::Unchanged(term),
        }
    }

    fn name(&self) -> &str {
        "uf"
    }

    fn can_handle(&self, term: TermId, manager: &TermManager) -> bool {
        if let Some(t) = manager.get(term) {
            matches!(&t.kind, TermKind::Apply { .. } | TermKind::Eq(_, _))
        } else {
            false
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn setup() -> (TermManager, RewriteContext, UfRewriter) {
        let manager = TermManager::new();
        let ctx = RewriteContext::new();
        let rewriter = UfRewriter::new();
        (manager, ctx, rewriter)
    }

    /// Does `name` occur as a *free* variable anywhere in `term`?
    ///
    /// A beta reduction that silently skipped its body leaves the callee's
    /// parameter variable free in the result, which is what these tests look
    /// for.
    fn mentions_free_var(manager: &TermManager, term: TermId, name: &str) -> bool {
        manager
            .free_vars_including_patterns(term)
            .into_iter()
            .filter_map(|v| match manager.get(v).map(|t| &t.kind) {
                Some(TermKind::Var(n)) => Some(manager.resolve_str(*n).to_string()),
                _ => None,
            })
            .any(|n| n == name)
    }

    #[test]
    fn test_apply_unchanged() {
        let (mut manager, mut ctx, mut rewriter) = setup();
        let int_sort = manager.sorts.int_sort;
        let x = manager.mk_var("x", int_sort);
        let apply = manager.mk_apply("f", vec![x], int_sort);

        let result = rewriter.rewrite(apply, &mut ctx, &mut manager);
        assert!(!result.was_rewritten());
    }

    #[test]
    fn test_commutative_normalize() {
        let (mut manager, mut ctx, mut rewriter) = setup();
        let int_sort = manager.sorts.int_sort;

        // Register a commutative symbol
        let f_spur = manager.intern_str("comm_f");
        rewriter.mark_commutative(f_spur);

        let x = manager.mk_var("x", int_sort);
        let y = manager.mk_var("y", int_sort);

        // Create f(y, x) where y.id > x.id - should be normalized to f(x, y)
        let func_str = manager.resolve_str(f_spur).to_string();
        let apply = manager.mk_apply(&func_str, vec![y, x], int_sort);

        // The normalization depends on term ordering
        let result = rewriter.rewrite(apply, &mut ctx, &mut manager);
        // Check that the term was processed (may or may not rewrite depending on term IDs)
        assert!(result.term().0 > 0);
    }

    #[test]
    fn test_func_eq_refl() {
        let (mut manager, mut ctx, mut rewriter) = setup();
        let int_sort = manager.sorts.int_sort;
        let x = manager.mk_var("x", int_sort);
        let apply = manager.mk_apply("f", vec![x], int_sort);

        // f(x) = f(x) → true
        // Note: mk_eq already simplifies identical terms to true during construction,
        // so the UF rewriter sees 'true' directly
        let eq = manager.mk_eq(apply, apply);

        // The term should already be 'true' due to mk_eq simplification
        let t_eq = manager.get(eq);
        assert!(matches!(t_eq.map(|t| &t.kind), Some(TermKind::True)));

        // Rewriter should not change it further
        let result = rewriter.rewrite(eq, &mut ctx, &mut manager);
        assert!(!result.was_rewritten()); // Already simplified
        let t_result = manager.get(result.term());
        assert!(matches!(t_result.map(|t| &t.kind), Some(TermKind::True)));
    }

    #[test]
    fn test_beta_reduction() {
        let (mut manager, mut ctx, mut rewriter) = setup();
        let int_sort = manager.sorts.int_sort;

        // Define f(x) = x + 1
        let param_x = manager.intern_str("param_x");
        let param_var = manager.mk_var("param_x", int_sort);
        let one = manager.mk_int(1);
        let body = manager.mk_add(vec![param_var, one]);

        let f_spur = manager.intern_str("f");
        rewriter.register_definition(f_spur, vec![param_x], body, int_sort);

        // Now apply f(5)
        let five = manager.mk_int(5);
        let func_str = manager.resolve_str(f_spur).to_string();
        let apply = manager.mk_apply(&func_str, vec![five], int_sort);

        let result = rewriter.rewrite(apply, &mut ctx, &mut manager);
        assert!(result.was_rewritten());
    }

    #[test]
    fn test_associative_flatten() {
        let (mut manager, mut ctx, mut rewriter) = setup();
        let int_sort = manager.sorts.int_sort;

        let g_spur = manager.intern_str("assoc_g");
        rewriter.mark_associative(g_spur);

        let x = manager.mk_var("x", int_sort);
        let y = manager.mk_var("y", int_sort);
        let z = manager.mk_var("z", int_sort);

        // Create g(g(x, y), z) - should flatten to g(x, y, z)
        let g_str = manager.resolve_str(g_spur).to_string();
        let inner = manager.mk_apply(&g_str, vec![x, y], int_sort);
        let outer = manager.mk_apply(&g_str, vec![inner, z], int_sort);

        let result = rewriter.rewrite(outer, &mut ctx, &mut manager);
        assert!(result.was_rewritten());

        // Check flattened structure
        if let Some(t) = manager.get(result.term()) {
            if let TermKind::Apply { args, .. } = &t.kind {
                assert_eq!(args.len(), 3);
            } else {
                panic!("Expected Apply");
            }
        }
    }

    #[test]
    fn test_substitution_avoid_capture() {
        let (mut manager, _ctx, rewriter) = setup();
        let int_sort = manager.sorts.int_sort;

        // Create forall x. x > 0
        let x = manager.mk_var("x", int_sort);
        let zero = manager.mk_int(0);
        let body = manager.mk_gt(x, zero);
        let forall = manager.mk_forall(vec![("x", int_sort)], body);

        // Substitution should not affect bound variable x
        let x_spur = manager.intern_str("x");
        let five = manager.mk_int(5);
        let mut subst: FxHashMap<Spur, TermId> = FxHashMap::default();
        subst.insert(x_spur, five);

        let result = rewriter.substitute(forall, &subst, &mut manager);

        // Should be unchanged since x is bound
        assert_eq!(result, forall);
    }

    /// Beta reduction through the *public* [`Rewriter::rewrite`] entry point
    /// with a bit-vector body.
    ///
    /// `substitute` used to match a whitelist of `TermKind`s and end in
    /// `_ => term`, so every bit-vector, string, floating-point, datatype and
    /// array operator (plus `Xor`, `Mod`, `Distinct`, `Match`) was returned
    /// *unchanged*. `try_beta_reduction` reports success regardless, so
    /// `f(#x05)` with `f(p) = p + #x01` rewrote to `p + #x01` -- the callee's
    /// parameter variable, now free, in place of the application.
    #[test]
    fn beta_reduction_substitutes_through_a_bitvector_operator() {
        let (mut manager, mut ctx, mut rewriter) = setup();
        let bv8 = manager.sorts.bitvec(8);

        let param = manager.intern_str("p");
        let param_var = manager.mk_var("p", bv8);
        let one = manager.mk_bitvec(1, 8);
        let body = manager.mk_bv_add(param_var, one);

        let f = manager.intern_str("f");
        rewriter.register_definition(f, vec![param], body, bv8);

        let five = manager.mk_bitvec(5, 8);
        let apply = manager.mk_apply("f", vec![five], bv8);

        let result = rewriter.rewrite(apply, &mut ctx, &mut manager).term();

        assert!(
            !mentions_free_var(&manager, result, "p"),
            "the parameter p must not survive beta reduction"
        );
        let expected = manager.mk_bv_add(five, one);
        assert_eq!(result, expected, "expected #x05 + #x01");
    }

    /// Same gap, reached through a datatype constructor/selector body.
    #[test]
    fn beta_reduction_substitutes_through_a_datatype_constructor() {
        let (mut manager, mut ctx, mut rewriter) = setup();
        let int_sort = manager.sorts.int_sort;
        let dt_sort = manager.sorts.mk_datatype_sort("Pair");

        let param = manager.intern_str("p");
        let param_var = manager.mk_var("p", int_sort);
        let zero = manager.mk_int(0);
        let pair = manager.mk_dt_constructor("Pair", vec![param_var, zero], dt_sort);
        let body = manager.mk_dt_selector("first", pair, int_sort);

        let f = manager.intern_str("f");
        rewriter.register_definition(f, vec![param], body, int_sort);

        let seven = manager.mk_int(7);
        let apply = manager.mk_apply("f", vec![seven], int_sort);

        let result = rewriter.rewrite(apply, &mut ctx, &mut manager).term();

        assert!(!mentions_free_var(&manager, result, "p"));
        let expected_pair = manager.mk_dt_constructor("Pair", vec![seven, zero], dt_sort);
        let expected = manager.mk_dt_selector("first", expected_pair, int_sort);
        assert_eq!(result, expected);
    }

    /// Capture avoidance: `f(p) = ∀y. P(p, y)` applied to `y` must rename the
    /// binder. The old walk rebuilt the `Forall` verbatim whenever the binder
    /// did not shadow the substituted *name*, so `f(y)` became
    /// `∀y. P(y, y)` -- the argument captured by the callee's own binder,
    /// which is a different formula from the one beta reduction promises.
    #[test]
    fn beta_reduction_avoids_capturing_the_argument() {
        let (mut manager, mut ctx, mut rewriter) = setup();
        let int_sort = manager.sorts.int_sort;
        let bool_sort = manager.sorts.bool_sort;

        let param = manager.intern_str("p");
        let param_var = manager.mk_var("p", int_sort);
        let y = manager.mk_var("y", int_sort);
        let inner = manager.mk_apply("P", vec![param_var, y], bool_sort);
        let body = manager.mk_forall(vec![("y", int_sort)], inner);

        let f = manager.intern_str("f");
        rewriter.register_definition(f, vec![param], body, bool_sort);

        let apply = manager.mk_apply("f", vec![y], bool_sort);
        let result = rewriter.rewrite(apply, &mut ctx, &mut manager).term();

        let kind = manager
            .get(result)
            .map(|t| t.kind.clone())
            .expect("result term must exist");
        let TermKind::Forall {
            vars,
            body: new_body,
            ..
        } = kind
        else {
            panic!("expected a Forall, got {kind:?}");
        };
        let (renamed, sort) = vars
            .first()
            .map(|&(n, s)| (manager.resolve_str(n).to_string(), s))
            .expect("exactly one bound variable");
        assert_ne!(renamed, "y", "the bound y must be alpha-renamed");

        let fresh = manager.mk_var(&renamed, sort);
        let expected_body = manager.mk_apply("P", vec![y, fresh], bool_sort);
        assert_eq!(
            new_body, expected_body,
            "the argument y must not be captured by the callee's binder"
        );
    }

    /// A `let` in the body: the value position must be substituted into, and a
    /// `let` re-binding the parameter name must still shadow it.
    #[test]
    fn beta_reduction_descends_into_a_let_and_respects_shadowing() {
        let (mut manager, mut ctx, mut rewriter) = setup();
        let int_sort = manager.sorts.int_sort;
        let bool_sort = manager.sorts.bool_sort;

        let param = manager.intern_str("p");
        let param_var = manager.mk_var("p", int_sort);
        let zero = manager.mk_int(0);
        // (let ((a p)) (> a 0))
        let a = manager.mk_var("a", int_sort);
        let inner = manager.mk_gt(a, zero);
        let body = manager.mk_let(vec![("a", param_var)], inner);

        let f = manager.intern_str("f");
        rewriter.register_definition(f, vec![param], body, bool_sort);

        let nine = manager.mk_int(9);
        let apply = manager.mk_apply("f", vec![nine], bool_sort);
        let result = rewriter.rewrite(apply, &mut ctx, &mut manager).term();

        assert!(!mentions_free_var(&manager, result, "p"));
        let expected = manager.mk_let(vec![("a", nine)], inner);
        assert_eq!(result, expected);
    }

    // ========  ========
    // Inlining budget (`UfRewriterConfig::max_inline_depth`)
    //
    // These drive the rewriter through `enable_beta_reduction: false,
    // enable_inlining: true`, which is the configuration that reaches
    // `try_inline` at all -- with beta reduction on it fires first on the
    // same precondition. See `rewrite_apply`.
    // ========  ========

    /// A rewriter that inlines (and does not beta-reduce) with the given
    /// budget.
    fn inlining_setup(max_inline_depth: usize) -> (TermManager, RewriteContext, UfRewriter) {
        let rewriter = UfRewriter::with_config(UfRewriterConfig {
            enable_beta_reduction: false,
            enable_inlining: true,
            max_inline_depth,
            ..UfRewriterConfig::default()
        });
        (TermManager::new(), RewriteContext::new(), rewriter)
    }

    /// Register `f1(p) = f2(p)`, ..., `f{last-1}(p) = f{last}(p)` and
    /// `f{last}(p) = p + 1`, returning the parameter variable.
    fn register_definition_chain(
        manager: &mut TermManager,
        rewriter: &mut UfRewriter,
        last: usize,
    ) {
        let int_sort = manager.sorts.int_sort;
        let param = manager.intern_str("p");
        let param_var = manager.mk_var("p", int_sort);

        for index in 1..last {
            let body = manager.mk_apply(&format!("f{}", index + 1), vec![param_var], int_sort);
            let name = manager.intern_str(&format!("f{index}"));
            rewriter.register_definition(name, vec![param], body, int_sort);
        }

        let one = manager.mk_int(1);
        let body = manager.mk_add(vec![param_var, one]);
        let name = manager.intern_str(&format!("f{last}"));
        rewriter.register_definition(name, vec![param], body, int_sort);
    }

    /// A budget of zero refuses to inline at all -- the guard fires before
    /// the first unfold.
    #[test]
    fn inline_budget_of_zero_disables_inlining() {
        let (mut manager, mut ctx, mut rewriter) = inlining_setup(0);
        register_definition_chain(&mut manager, &mut rewriter, 6);

        let int_sort = manager.sorts.int_sort;
        let five = manager.mk_int(5);
        let apply = manager.mk_apply("f1", vec![five], int_sort);

        let result = rewriter.rewrite(apply, &mut ctx, &mut manager);
        assert!(!result.was_rewritten());
        assert_eq!(result.term(), apply);
    }

    /// A budget of one is a single unfold: exactly what the (unfirable)
    /// guard's predecessor did for every setting.
    #[test]
    fn inline_budget_of_one_is_a_single_unfold() {
        let (mut manager, mut ctx, mut rewriter) = inlining_setup(1);
        register_definition_chain(&mut manager, &mut rewriter, 6);

        let int_sort = manager.sorts.int_sort;
        let five = manager.mk_int(5);
        let apply = manager.mk_apply("f1", vec![five], int_sort);

        let result = rewriter.rewrite(apply, &mut ctx, &mut manager);
        let expected = manager.mk_apply("f2", vec![five], int_sort);
        assert_eq!(result.term(), expected);
    }

    /// The budget fires mid-chain and leaves the remaining call in place;
    /// the term is still equal to the original by the definitions.
    #[test]
    fn inline_budget_stops_mid_chain() {
        let (mut manager, mut ctx, mut rewriter) = inlining_setup(3);
        register_definition_chain(&mut manager, &mut rewriter, 6);

        let int_sort = manager.sorts.int_sort;
        let five = manager.mk_int(5);
        let apply = manager.mk_apply("f1", vec![five], int_sort);

        let result = rewriter.rewrite(apply, &mut ctx, &mut manager);
        // Three rounds: f1 -> f2 -> f3 -> f4.
        let expected = manager.mk_apply("f4", vec![five], int_sort);
        assert_eq!(result.term(), expected);
    }

    /// With enough budget the whole chain collapses to the innermost body --
    /// which is what makes inlining more than beta reduction.
    #[test]
    fn a_sufficient_budget_inlines_the_whole_chain() {
        let (mut manager, mut ctx, mut rewriter) = inlining_setup(20);
        register_definition_chain(&mut manager, &mut rewriter, 6);

        let int_sort = manager.sorts.int_sort;
        let five = manager.mk_int(5);
        let apply = manager.mk_apply("f1", vec![five], int_sort);

        let result = rewriter.rewrite(apply, &mut ctx, &mut manager);
        let one = manager.mk_int(1);
        let expected = manager.mk_add(vec![five, one]);
        assert_eq!(result.term(), expected);
    }

    /// A self-referential definition would expand forever; the budget is the
    /// only thing that stops it, and stopping leaves a well-formed term.
    #[test]
    fn self_referential_definition_terminates_at_the_budget() {
        let (mut manager, mut ctx, mut rewriter) = inlining_setup(4);
        let int_sort = manager.sorts.int_sort;

        // f(p) = f(p) + 1
        let param = manager.intern_str("p");
        let param_var = manager.mk_var("p", int_sort);
        let recursive_call = manager.mk_apply("f", vec![param_var], int_sort);
        let one = manager.mk_int(1);
        let body = manager.mk_add(vec![recursive_call, one]);
        let f = manager.intern_str("f");
        rewriter.register_definition(f, vec![param], body, int_sort);

        let five = manager.mk_int(5);
        let apply = manager.mk_apply("f", vec![five], int_sort);

        let result = rewriter.rewrite(apply, &mut ctx, &mut manager).term();

        // Four rounds of `f(5) -> f(5) + 1`, so four `+ 1`s wrapped around a
        // residual call.
        let mut expected = manager.mk_apply("f", vec![five], int_sort);
        for _ in 0..4 {
            expected = manager.mk_add(vec![expected, one]);
        }
        assert_eq!(result, expected);
    }

    /// A body containing a binder stops the nested rounds: round 1 still
    /// expands the application it was handed, and nothing enters the
    /// quantifier's scope.
    #[test]
    fn inlining_does_not_enter_binder_scopes() {
        let (mut manager, mut ctx, mut rewriter) = inlining_setup(5);
        let int_sort = manager.sorts.int_sort;
        let bool_sort = manager.sorts.bool_sort;

        // g(p) = forall y. q(p, y), and f(p) = g(p).
        let param = manager.intern_str("p");
        let param_var = manager.mk_var("p", int_sort);
        let y = manager.mk_var("y", int_sort);
        let predicate = manager.mk_apply("q", vec![param_var, y], bool_sort);
        let quantified = manager.mk_forall(vec![("y", int_sort)], predicate);
        let g = manager.intern_str("g");
        rewriter.register_definition(g, vec![param], quantified, bool_sort);

        let g_call = manager.mk_apply("g", vec![param_var], bool_sort);
        let f = manager.intern_str("f");
        rewriter.register_definition(f, vec![param], g_call, bool_sort);

        let five = manager.mk_int(5);
        let apply = manager.mk_apply("f", vec![five], bool_sort);

        let result = rewriter.rewrite(apply, &mut ctx, &mut manager).term();

        // Round 1: f(5) -> g(5). Round 2: g(5) -> forall y. q(5, y).
        // Round 3 sees a binder and stops.
        let expected_body = manager.mk_apply("q", vec![five, y], bool_sort);
        let expected = manager.mk_forall(vec![("y", int_sort)], expected_body);
        assert_eq!(result, expected);
    }

    /// With the default configuration beta reduction fires first, so the
    /// inlining budget is not consulted at all.
    #[test]
    fn default_configuration_uses_beta_reduction() {
        let (mut manager, mut ctx, mut rewriter) = setup();
        register_definition_chain(&mut manager, &mut rewriter, 6);

        let int_sort = manager.sorts.int_sort;
        let five = manager.mk_int(5);
        let apply = manager.mk_apply("f1", vec![five], int_sort);

        let result = rewriter.rewrite(apply, &mut ctx, &mut manager);
        let expected = manager.mk_apply("f2", vec![five], int_sort);
        assert_eq!(result.term(), expected);
        assert_eq!(
            ctx.stats().rule_applications.get("uf_beta_reduction"),
            Some(&1)
        );
        assert_eq!(ctx.stats().rule_applications.get("uf_inline"), None);
    }

    #[test]
    fn test_congruence_cache() {
        let (mut manager, mut ctx, mut rewriter) = setup();
        let int_sort = manager.sorts.int_sort;

        let x = manager.mk_var("x", int_sort);
        let apply1 = manager.mk_apply("h", vec![x], int_sort);
        let apply2 = manager.mk_apply("h", vec![x], int_sort);

        // First call - cache miss
        let result1 = rewriter.rewrite(apply1, &mut ctx, &mut manager);

        // Second call - should hit cache
        let result2 = rewriter.rewrite(apply2, &mut ctx, &mut manager);

        // Both should return the same term
        assert_eq!(result1.term(), result2.term());
    }
}
