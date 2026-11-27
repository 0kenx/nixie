//! Pattern (trigger) representation and E-matching.
//!
//! Split out of the former single-file `tactic/quantifier.rs`; see
//! [`super`] for the module layout. Pure code motion, except for the
//! matching core itself:
//!
//! * `backtrack` (private) -- [`BacktrackMatcher`], the explicit-stack
//!   backtracking machine that replaced the mutually recursive
//!   `match_recursive`. See that module's doc comment for why the recursion
//!   had to go (unbounded, user-driven native recursion with only a `bool`
//!   to report through), how the two `Eq` orientations became recorded
//!   alternatives instead of a `4^depth` re-traversal, and why undoing
//!   bindings on backtrack also fixes two wrong-verdict bugs.

use crate::ast::{TermId, TermKind, TermManager};
use crate::interner::Spur;
#[allow(unused_imports)]
use crate::prelude::*;
use crate::sort::SortId;
use smallvec::SmallVec;

use super::ground_terms::GroundTermCollector;
use backtrack::BacktrackMatcher;
use join::for_each_merge;

mod backtrack;
mod join;

#[cfg(test)]
mod tests;

/// A pattern for quantifier instantiation (trigger)
#[derive(Debug, Clone)]
pub struct Pattern {
    /// The quantifier this pattern belongs to
    pub quantifier: TermId,
    /// The trigger terms (multi-pattern)
    pub triggers: SmallVec<[TermId; 2]>,
    /// Bound variable names with their sorts
    pub bound_vars: SmallVec<[(Spur, SortId); 2]>,
    /// Body of the quantifier
    pub body: TermId,
}

/// A binding from bound variables to ground terms
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Binding {
    /// Index of the pattern that produced this binding
    pub pattern_idx: usize,
    /// Substitution from variable names to ground terms
    pub substitution: FxHashMap<Spur, TermId>,
}

/// Pattern matcher for E-matching based quantifier instantiation
#[derive(Debug, Default)]
pub struct PatternMatcher {
    /// Registered patterns
    patterns: Vec<Pattern>,
    /// Already generated bindings (for deduplication)
    generated_bindings: FxHashSet<(usize, Vec<(Spur, TermId)>)>,
}

impl PatternMatcher {
    /// Create a new pattern matcher
    #[must_use]
    pub fn new() -> Self {
        Self::default()
    }

    /// Add a pattern for a quantifier
    pub fn add_pattern(&mut self, quantifier: TermId, manager: &TermManager) {
        if let Some(term) = manager.get(quantifier)
            && let TermKind::Forall {
                vars,
                body,
                patterns,
            } = &term.kind
        {
            if patterns.is_empty() {
                // No explicit patterns - use heuristic trigger inference
                // For now, just use the body as a fallback (not ideal)
                self.patterns.push(Pattern {
                    quantifier,
                    triggers: SmallVec::new(),
                    bound_vars: vars.clone(),
                    body: *body,
                });
            } else {
                // Use explicit patterns
                for pattern in patterns {
                    self.patterns.push(Pattern {
                        quantifier,
                        triggers: pattern.clone(),
                        bound_vars: vars.clone(),
                        body: *body,
                    });
                }
            }
        }
    }

    /// Try to match a ground term against a pattern trigger
    ///
    /// Returns bindings if successful, None otherwise. The bindings are
    /// exactly those made along the successful path: an alternative that was
    /// tried and failed leaves nothing behind (see [`backtrack`]).
    ///
    /// `pub(super)` only so that `super::tests` can keep exercising it
    /// directly: it was a plain private method while the tests lived in the
    /// same file, and widening it to the enclosing `quantifier` module was
    /// the minimum needed to preserve that white-box test unchanged when
    /// the file was split (mirrors `ast::manager::query`'s `pub(super)`
    /// `prepare_binder_subst`/`find_var_sort`). Still unreachable from
    /// outside `crate::tactic::quantifier`.
    pub(super) fn try_match_term(
        &self,
        pattern_term: TermId,
        ground_term: TermId,
        bound_vars: &[(Spur, SortId)],
        manager: &TermManager,
    ) -> Option<FxHashMap<Spur, TermId>> {
        let bound_var_names: FxHashSet<Spur> = bound_vars.iter().map(|(n, _)| *n).collect();
        let mut matcher = BacktrackMatcher::new(&bound_var_names);

        if matcher.run(pattern_term, ground_term, manager) {
            Some(matcher.into_bindings())
        } else {
            None
        }
    }

    /// Match patterns against ground terms and generate bindings.
    pub fn match_against(
        &mut self,
        ground_terms: &GroundTermCollector,
        manager: &TermManager,
    ) -> Vec<Binding> {
        self.match_against_within(ground_terms, manager, usize::MAX)
    }

    /// [`Self::match_against`], stopping once `limit` bindings have been
    /// generated.
    ///
    /// The bindings are the first `limit` of the unlimited list, in its
    /// order, so a caller that would have taken the first `limit` and
    /// dropped the rest sees exactly what it saw – without the rest being
    /// built first.  A multi-trigger's consistent merges are streamed by
    /// the join (`matching::join`), so the stop reaches the cross product:
    /// two triggers over disjoint variables produce a product, and the
    /// tactic's budget is a prefix of it.
    pub fn match_against_within(
        &mut self,
        ground_terms: &GroundTermCollector,
        manager: &TermManager,
        limit: usize,
    ) -> Vec<Binding> {
        let mut new_bindings: Vec<Binding> = Vec::new();

        for pattern_idx in 0..self.patterns.len() {
            if new_bindings.len() >= limit {
                break;
            }
            let Pattern {
                triggers,
                bound_vars,
                ..
            } = &self.patterns[pattern_idx];
            // Skip patterns without triggers (need heuristic inference)
            if triggers.is_empty() {
                continue;
            }

            // For single-trigger patterns
            if triggers.len() == 1 {
                let trigger = triggers[0];

                // Try matching against each ground term
                for &ground_term in ground_terms.all_terms() {
                    if let Some(subst) =
                        self.try_match_term(trigger, ground_term, bound_vars, manager)
                        && push_binding(
                            &mut self.generated_bindings,
                            &mut new_bindings,
                            pattern_idx,
                            bound_vars,
                            subst,
                        )
                        && new_bindings.len() >= limit
                    {
                        break;
                    }
                }
            } else {
                // Multi-trigger: all trigger patterns must match
                // simultaneously.  Each trigger's partial substitutions
                // are collected on their own, then joined on their shared
                // variables (`matching::join`): the consistent merges,
                // streamed in cross-product order.
                let mut per_trigger: Vec<Vec<FxHashMap<Spur, TermId>>> = Vec::new();

                for &trigger in triggers {
                    let mut partial_substs: Vec<FxHashMap<Spur, TermId>> = Vec::new();
                    for &ground_term in ground_terms.all_terms() {
                        if let Some(subst) =
                            self.try_match_term(trigger, ground_term, bound_vars, manager)
                        {
                            partial_substs.push(subst);
                        }
                    }
                    if partial_substs.is_empty() {
                        // No matches for this trigger: no combined match possible.
                        per_trigger.clear();
                        break;
                    }
                    per_trigger.push(partial_substs);
                }

                if per_trigger.is_empty() {
                    continue;
                }

                let generated = &mut self.generated_bindings;
                for_each_merge(&per_trigger, |subst| {
                    push_binding(generated, &mut new_bindings, pattern_idx, bound_vars, subst);
                    new_bindings.len() < limit
                });
            }
        }

        new_bindings
    }
}

/// Record `subst` for pattern `pattern_idx` as a binding if every bound
/// variable is assigned and the pattern has not produced it before; whether
/// one was recorded.  The deduplication key is the sorted substitution, so
/// two matches of the same trigger (or two merges) yielding the same
/// substitution produce one binding.
fn push_binding(
    generated: &mut FxHashSet<(usize, Vec<(Spur, TermId)>)>,
    new_bindings: &mut Vec<Binding>,
    pattern_idx: usize,
    bound_vars: &[(Spur, SortId)],
    subst: FxHashMap<Spur, TermId>,
) -> bool {
    // Check all bound variables are assigned.
    if !bound_vars.iter().all(|(n, _)| subst.contains_key(n)) {
        return false;
    }
    let mut key_vec: Vec<_> = subst.iter().map(|(&k, &v)| (k, v)).collect();
    key_vec.sort_by_key(|(k, _)| k.into_inner());
    if !generated.insert((pattern_idx, key_vec)) {
        return false;
    }
    new_bindings.push(Binding {
        pattern_idx,
        substitution: subst,
    });
    true
}

impl PatternMatcher {
    /// Instantiate a quantifier body with a binding
    pub fn instantiate(&self, binding: &Binding, manager: &mut TermManager) -> Option<TermId> {
        let pattern = self.patterns.get(binding.pattern_idx)?;

        // Build substitution map from Spur to TermId
        let subst: FxHashMap<TermId, TermId> = pattern
            .bound_vars
            .iter()
            .filter_map(|(name, sort)| {
                let var_name = manager.resolve_str(*name).to_string();
                let var_id = manager.mk_var(&var_name, *sort);
                binding.substitution.get(name).map(|&term| (var_id, term))
            })
            .collect();

        Some(manager.substitute(pattern.body, &subst))
    }

    /// Get the number of patterns
    #[must_use]
    pub fn pattern_count(&self) -> usize {
        self.patterns.len()
    }

    /// Get the quantifier for a pattern index
    #[must_use]
    pub fn get_quantifier(&self, pattern_idx: usize) -> Option<TermId> {
        self.patterns.get(pattern_idx).map(|p| p.quantifier)
    }

    /// Clear all patterns and bindings
    pub fn clear(&mut self) {
        self.patterns.clear();
        self.generated_bindings.clear();
    }
}
