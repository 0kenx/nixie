//! Term query, analysis, substitution and simplification for TermManager.
//!
//! Split into submodules so each stays well under the workspace's
//! line-count ceiling (see `size_depth`, `substitute`, `simplify`; this
//! root file keeps only the free-variable query, which was not part of
//! that split):
//!
//! * [`size_depth`] -- [`TermManager::term_size`] / [`TermManager::term_depth`].
//! * [`substitute`] -- [`TermManager::substitute`], capture-avoiding.
//! * [`simplify`] -- [`TermManager::simplify`], bottom-up rewriting.
//!
//! `substitute` and `simplify` used to share a recursion-depth cap
//! (`MAX_QUERY_RECURSION_DEPTH`) that bailed out by returning a
//! pathologically deep term unchanged rather than overflowing the native
//! call stack. Both were converted to use an explicit heap stack instead
//! (see `substitute`'s module doc comment for why the cap was unsound for
//! `substitute` specifically), which removed the need for that cap
//! entirely; it no longer exists.
//!
//! [`TermManager::free_vars`] (this file) had no cap at all -- it was
//! plain native recursion with no depth guard whatsoever, worse than what
//! `substitute`/`simplify` had before their conversion. It is converted
//! the same way: an explicit `Vec`-backed work stack ([`FreeVarStep`])
//! replaces the native call stack, so there is no depth at which it
//! crashes.
//!
//! # A second `collect_free_vars`, and why it now delegates here
//!
//! [`crate::ast::traversal`] has its own free function of the same name,
//! `collect_free_vars`, previously built directly on that module's
//! generic post-order `traverse` visitor. It is the one actually imported
//! by [`substitute`]'s `prepare_binder_subst` (to compute which names a
//! fresh binder variable must avoid) and by `oxiz-solver`'s MBQI
//! instantiation checking (`oxiz_solver::mbqi::{sat_certify,
//! integration}`), which rejects a grounding substitution outright if a
//! bound variable it meant to eliminate is still reported free in the
//! result -- a soundness-relevant use, not just a utility.
//!
//! That generic-traversal implementation turned out to have two
//! correctness bugs, both fixed by making it delegate to
//! [`TermManager::free_vars`] instead of walking independently:
//!
//! * It tracked shadowing by variable *name* alone, ignoring sort, so a
//!   bound `x: Bool` in an enclosing scope could incorrectly shadow an
//!   unrelated, differently-sorted free `x: Int`.
//! * The generic `traverse` helper's visited set is global and
//!   unconditional: once a shared subterm (structural sharing under
//!   hash-consing) was walked once *while under a binder* that happened
//!   to shadow one of its variables, revisiting that exact subterm later
//!   from an unshadowed position would be skipped as "already visited",
//!   silently dropping a genuinely free occurrence. See this file's
//!   `free_vars_binder_tests::shared_subterm_free_outside_a_shadowing_binder_is_still_reported`
//!   for the scenario this breaks -- `free_vars` itself avoids it via the
//!   conditional memoization described on [`FreeVarStep`].
//!
//! Both bugs matter most for the MBQI safety check: an under-reported
//! free-variable set there means the "residual bound variable" guard can
//! silently pass a not-fully-grounded lemma. Rather than fix the second
//! implementation in place and risk the two diverging again later (this
//! crate has hit that exact hazard before with `ast::traversal::
//! map_terms`'s retired `transform_children`, see that function's doc
//! comment), `ast::traversal::collect_free_vars` now simply calls
//! [`TermManager::free_vars`] and collects the result into a set.
//!
//! `Match` case bindings are also now treated as a fourth binder form
//! here, alongside `Forall`/`Exists`/`Let`: the previous implementation
//! had no `Match` arm at all, so a case's pattern-bound names fell
//! through to the generic `get_children`-based catch-all and were never
//! shadowed -- a latent unsoundness for exactly the same MBQI check,
//! since a datatype match wrapping a quantifier body would have leaked
//! the case's bound names as spuriously "free".
//!
//! # Why there are *two* free-variable queries
//!
//! [`TermManager::free_vars`] deliberately does **not** look inside a
//! `Forall`/`Exists` node's `patterns` field (its SMT-LIB `:pattern` /
//! trigger annotations), because that is what every generic walk in the
//! workspace does: [`crate::ast::traversal::get_children`] does not
//! report pattern subterms either, so simplification, hashing,
//! size/depth accounting, printing and rewriting all agree that a
//! quantifier's only child is its body. Widening that notion globally
//! would change all of those behaviours at once.
//!
//! But triggers *are* term positions, and a variable occurring only in a
//! trigger is a genuine occurrence. Two callers depend on that:
//!
//! * `substitute`'s `TermManager::prepare_binder_subst`, which uses
//!   the free-variable set as its capture-avoidance name-clash detector:
//!   a name invisible to it can be handed out as a "fresh" binder name
//!   even though it still occurs live in a pattern, capturing it.
//! * `oxiz-solver`'s MBQI grounding guard
//!   (`oxiz_solver::mbqi::{sat_certify, integration}`), which rejects a
//!   grounding substitution whose target variable is still reported free
//!   in the result. Under-reporting there passes a not-fully-grounded
//!   lemma.
//!
//! Those callers use [`TermManager::free_vars_including_patterns`]
//! (surfaced to other crates as
//! [`crate::ast::traversal::collect_free_vars_including_patterns`]),
//! which is identical except that a quantifier's pattern terms are
//! walked *inside* that quantifier's own scope -- a trigger normally
//! mentions the bound variables, and those occurrences are bound, not
//! free.
//!
//! Rule of thumb for new callers: if the answer feeds a decision about
//! *names* (freshness, capture, groundedness), use the pattern-aware
//! variant; over-reporting a free variable only makes substitution pick
//! a different fresh name, whereas under-reporting captures. If the
//! answer must agree with `get_children`-based structural walks, use
//! [`TermManager::free_vars`].

use super::super::term::{TermId, TermKind};
use super::super::traversal::get_children;
use crate::interner::Spur;
#[allow(unused_imports)]
use crate::prelude::*;
use crate::sort::SortId;
use smallvec::SmallVec;

use super::TermManager;

mod simplify;
mod size_depth;
mod substitute;

#[cfg(test)]
mod tests;

/// One pending step of the iterative free-variable walk driven by
/// [`TermManager::free_vars`].
///
/// Entering a binder's scope, walking within it, and leaving the scope
/// again are three separate steps here (rather than three phases of one
/// recursive call), so that the "leave scope" cleanup still happens at
/// exactly the right point -- after that binder's body/case is fully
/// walked, but before its enclosing scope is touched again.
enum FreeVarStep {
    /// Visit `id`: if it is an unbound `Var`, record it; otherwise
    /// inspect its structure and push whatever further steps are needed.
    Visit(TermId),
    /// Bring `names` into scope (increment their reference counts in
    /// `bound`); run before visiting a binder's body/case.
    Enter(SmallVec<[(Spur, SortId); 2]>),
    /// Remove `names` from scope (decrement/remove their reference counts
    /// in `bound`); run after a binder's body/case has been fully
    /// visited -- mirrors the original recursive version's post-call
    /// cleanup loop.
    Exit(SmallVec<[(Spur, SortId); 2]>),
}

/// Whether a free-variable walk descends into `Forall`/`Exists`
/// `patterns` (trigger) subterms.
///
/// Two variants exist deliberately; see this module's "Why there are
/// *two* free-variable queries" section for the full rationale and for
/// which one a new caller should pick.
#[derive(Clone, Copy, PartialEq, Eq)]
enum PatternPolicy {
    /// Skip pattern subterms, matching what
    /// [`get_children`] reports as a quantifier's children (its body
    /// alone). Backs [`TermManager::free_vars`].
    Skip,
    /// Walk pattern subterms inside the owning quantifier's own scope,
    /// so that a trigger's references to the bound variables are treated
    /// as bound and anything else it mentions is reported free. Backs
    /// [`TermManager::free_vars_including_patterns`].
    Include,
}

impl TermManager {
    /// Collect all free variables in a term, **ignoring** `Forall`/
    /// `Exists` trigger patterns.
    ///
    /// A `Var(name)` occurrence at sort `s` that lies inside the body of a
    /// `Forall`/`Exists`/`Let` binding `(name, s)`, or inside a `Match`
    /// case that pattern-binds `(name, s)`, is *bound*, not free -- per
    /// standard first-order-logic scoping it must not be reported. See
    /// this module's private `FreeVarStep` enum and `run_free_var_step`
    /// method for how the bound-name environment is threaded through the
    /// traversal, which uses an explicit heap stack rather than native
    /// recursion so that no input depth can overflow the call stack.
    ///
    /// A variable occurring *only* inside a quantifier's `patterns`
    /// (SMT-LIB `:pattern` / trigger annotation) is **not** reported,
    /// because pattern subterms are not [`get_children`] children and
    /// this query is the one that must agree with every generic,
    /// `get_children`-driven structural walk in the workspace. Callers
    /// reasoning about *names* -- capture avoidance, freshness,
    /// groundedness -- must use
    /// [`TermManager::free_vars_including_patterns`] instead.
    #[must_use]
    pub fn free_vars(&self, id: TermId) -> Vec<TermId> {
        self.free_vars_with(id, PatternPolicy::Skip)
    }

    /// Collect all free variables in a term, **including** occurrences
    /// that appear only inside `Forall`/`Exists` trigger patterns.
    ///
    /// Identical to [`TermManager::free_vars`] except that each
    /// quantifier's `patterns` terms are also walked, within that
    /// quantifier's own scope: a trigger typically mentions the bound
    /// variables, and those occurrences are bound rather than free.
    ///
    /// This is the variant required wherever the result drives a
    /// decision about variable *names* rather than about term structure:
    ///
    /// * capture-avoiding substitution's fresh-name choice (a name that
    ///   still occurs in a pattern is not free for use as a fresh binder
    ///   name -- reusing it captures that occurrence);
    /// * `oxiz-solver`'s MBQI grounding guard, which rejects an
    ///   instantiation whose bound variable survives in the result.
    #[must_use]
    pub fn free_vars_including_patterns(&self, id: TermId) -> Vec<TermId> {
        self.free_vars_with(id, PatternPolicy::Include)
    }

    /// Shared driver for [`TermManager::free_vars`] and
    /// [`TermManager::free_vars_including_patterns`]: one iterative walk
    /// parameterized by whether trigger patterns are in scope.
    fn free_vars_with(&self, id: TermId, patterns: PatternPolicy) -> Vec<TermId> {
        let mut vars = Vec::new();
        let mut visited: FxHashMap<TermId, ()> = FxHashMap::default();
        let mut bound: FxHashMap<(Spur, SortId), u32> = FxHashMap::default();
        let mut work: Vec<FreeVarStep> = vec![FreeVarStep::Visit(id)];
        while let Some(step) = work.pop() {
            self.run_free_var_step(
                step,
                patterns,
                &mut vars,
                &mut visited,
                &mut bound,
                &mut work,
            );
        }
        vars
    }

    /// Dispatch one [`FreeVarStep`], possibly pushing more onto `work`
    /// (and, for binder nodes, an `Enter`/`Exit` pair bracketing the
    /// body/case's own steps).
    ///
    /// `visited` memoizes traversal by `TermId` to avoid re-walking
    /// shared DAG subterms, but that memoization is only sound while no
    /// binder is active: the *same* `TermId` subterm can be reachable
    /// both inside and outside a binder's scope (structural sharing), and
    /// whether a `Var` inside it counts as free depends on which binders
    /// are active at the point of reference. So the memo is
    /// consulted/updated only while `bound` is empty; traversal under any
    /// active binder always re-walks.
    ///
    /// `patterns` is fixed for the whole walk by whichever public entry
    /// point started it, so it never invalidates `visited` (which is
    /// per-call).
    fn run_free_var_step(
        &self,
        step: FreeVarStep,
        patterns: PatternPolicy,
        vars: &mut Vec<TermId>,
        visited: &mut FxHashMap<TermId, ()>,
        bound: &mut FxHashMap<(Spur, SortId), u32>,
        work: &mut Vec<FreeVarStep>,
    ) {
        match step {
            FreeVarStep::Enter(names) => {
                for (name, sort) in names {
                    *bound.entry((name, sort)).or_insert(0) += 1;
                }
            }
            FreeVarStep::Exit(names) => {
                for (name, sort) in names {
                    if let Some(count) = bound.get_mut(&(name, sort)) {
                        *count = count.saturating_sub(1);
                        if *count == 0 {
                            bound.remove(&(name, sort));
                        }
                    }
                }
            }
            FreeVarStep::Visit(id) => {
                let memo_active = bound.is_empty();
                if memo_active {
                    if visited.contains_key(&id) {
                        return;
                    }
                    visited.insert(id, ());
                }

                match self.get(id).map(|t| &t.kind) {
                    None => {}
                    Some(TermKind::Var(name)) => {
                        let is_bound = self
                            .get(id)
                            .is_some_and(|t| bound.get(&(*name, t.sort)).is_some_and(|&n| n > 0));
                        if !is_bound && !vars.contains(&id) {
                            vars.push(id);
                        }
                    }
                    Some(
                        TermKind::True
                        | TermKind::False
                        | TermKind::IntConst(_)
                        | TermKind::RealConst(_)
                        | TermKind::BitVecConst { .. }
                        | TermKind::StringLit(_),
                    ) => {}
                    Some(TermKind::Forall {
                        vars: bound_vars,
                        body,
                        patterns: triggers,
                    })
                    | Some(TermKind::Exists {
                        vars: bound_vars,
                        body,
                        patterns: triggers,
                    }) => {
                        let names: SmallVec<[(Spur, SortId); 2]> =
                            bound_vars.iter().copied().collect();
                        let body = *body;
                        // Trigger terms live in the quantifier's own scope
                        // (a trigger such as `(f x)` refers to the bound
                        // `x`), so they are walked *inside* the
                        // Enter/Exit bracket, exactly like the body -- but
                        // only under `PatternPolicy::Include`. See the
                        // module doc comment for why the default query
                        // skips them.
                        let trigger_terms: SmallVec<[TermId; 4]> = match patterns {
                            PatternPolicy::Skip => SmallVec::new(),
                            PatternPolicy::Include => {
                                triggers.iter().flat_map(|p| p.iter().copied()).collect()
                            }
                        };
                        // Execution order (LIFO, so pushed bottom-to-top):
                        // enter scope, walk body, walk triggers, leave
                        // scope.
                        work.push(FreeVarStep::Exit(names.clone()));
                        for &trigger in trigger_terms.iter().rev() {
                            work.push(FreeVarStep::Visit(trigger));
                        }
                        work.push(FreeVarStep::Visit(body));
                        work.push(FreeVarStep::Enter(names));
                    }
                    Some(TermKind::Let { bindings, body }) => {
                        // The bound value of `(let ((x t)) body)` is
                        // evaluated in the *outer* scope, so each value is
                        // walked before `x` enters `bound`; `x`'s
                        // effective sort is the sort of its value term
                        // `t`.
                        let body = *body;
                        let entered: SmallVec<[(Spur, SortId); 2]> = bindings
                            .iter()
                            .filter_map(|(name, term)| self.get(*term).map(|t| (*name, t.sort)))
                            .collect();
                        work.push(FreeVarStep::Exit(entered.clone()));
                        work.push(FreeVarStep::Visit(body));
                        work.push(FreeVarStep::Enter(entered));
                        // Binding values are walked in array order, each
                        // fully completing before the next starts (so
                        // pushed in reverse to end up on top in order).
                        for &(_, term) in bindings.iter().rev() {
                            work.push(FreeVarStep::Visit(term));
                        }
                    }
                    Some(TermKind::Match { scrutinee, cases }) => {
                        // The scrutinee is evaluated in the outer scope,
                        // like a `Let`'s bound values; each case's pattern
                        // bindings are then in scope only for that case's
                        // own body, mirroring `substitute`'s
                        // `expand_match` (see that module's doc comment).
                        // Cases are walked in array order (each pushed in
                        // reverse so they end up executing in order).
                        let scrutinee = *scrutinee;
                        for case in cases.iter().rev() {
                            let case_body = case.body;
                            let names: SmallVec<[(Spur, SortId); 2]> = case
                                .bindings
                                .iter()
                                .filter_map(|&name| {
                                    self.find_var_sort(case_body, name).map(|sort| (name, sort))
                                })
                                .collect();
                            work.push(FreeVarStep::Exit(names.clone()));
                            work.push(FreeVarStep::Visit(case_body));
                            work.push(FreeVarStep::Enter(names));
                        }
                        work.push(FreeVarStep::Visit(scrutinee));
                    }
                    // Everything else (arithmetic, bit-vector, string,
                    // array, floating-point, uninterpreted-function and
                    // algebraic-datatype operators): no scope change, so
                    // just recurse into every child uniformly via
                    // `get_children`. This is faithful to the original
                    // recursive version's many explicitly-enumerated
                    // "just recurse into every operand" arms (unary,
                    // n-ary, binary, ternary, `Apply`), which -- like
                    // `size_depth`'s conversion already established for
                    // `term_size`/`term_depth` -- summed/recursed over
                    // exactly the same children `get_children` returns
                    // for each of those kinds, plus its final catch-all
                    // (floating-point operations, and datatype
                    // constructors/testers/selectors) which already used
                    // `get_children` directly.
                    Some(_) => {
                        if let Some(term) = self.get(id) {
                            for &child in get_children(&term.kind).iter().rev() {
                                work.push(FreeVarStep::Visit(child));
                            }
                        }
                    }
                }
            }
        }
    }
}
