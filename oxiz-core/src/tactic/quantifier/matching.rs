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

mod backtrack;

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

    /// Match patterns against ground terms and generate bindings
    pub fn match_against(
        &mut self,
        ground_terms: &GroundTermCollector,
        manager: &TermManager,
    ) -> Vec<Binding> {
        let mut new_bindings = Vec::new();

        for (pattern_idx, pattern) in self.patterns.iter().enumerate() {
            // Skip patterns without triggers (need heuristic inference)
            if pattern.triggers.is_empty() {
                continue;
            }

            // For single-trigger patterns
            if pattern.triggers.len() == 1 {
                let trigger = pattern.triggers[0];

                // Try matching against each ground term
                for &ground_term in ground_terms.all_terms() {
                    if let Some(subst) =
                        self.try_match_term(trigger, ground_term, &pattern.bound_vars, manager)
                    {
                        // Check all bound variables are assigned
                        let all_bound = pattern
                            .bound_vars
                            .iter()
                            .all(|(n, _)| subst.contains_key(n));
                        if all_bound {
                            // Create binding key for deduplication
                            let mut key_vec: Vec<_> = subst.iter().map(|(&k, &v)| (k, v)).collect();
                            key_vec.sort_by_key(|(k, _)| k.into_inner());
                            let key = (pattern_idx, key_vec.clone());

                            if !self.generated_bindings.contains(&key) {
                                self.generated_bindings.insert(key);
                                new_bindings.push(Binding {
                                    pattern_idx,
                                    substitution: subst,
                                });
                            }
                        }
                    }
                }
            } else if pattern.triggers.len() > 1 {
                // Multi-trigger: all trigger patterns must match simultaneously.
                // Compute the cross-product of per-trigger substitutions, keeping
                // only consistent ones (same variable maps to the same term in all).
                let mut per_trigger: Vec<Vec<FxHashMap<Spur, TermId>>> = Vec::new();

                for &trigger in &pattern.triggers {
                    let mut partial_substs: Vec<FxHashMap<Spur, TermId>> = Vec::new();
                    for &ground_term in ground_terms.all_terms() {
                        if let Some(subst) =
                            self.try_match_term(trigger, ground_term, &pattern.bound_vars, manager)
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

                // Cross-product merge: start with first trigger's substitutions.
                let mut combined: Vec<FxHashMap<Spur, TermId>> = per_trigger.remove(0);

                for next_substs in per_trigger {
                    let mut merged: Vec<FxHashMap<Spur, TermId>> = Vec::new();
                    for s1 in &combined {
                        for s2 in &next_substs {
                            // Merge s1 and s2 if consistent (no conflicting bindings).
                            let mut ok = true;
                            for (k, v2) in s2 {
                                if let Some(v1) = s1.get(k)
                                    && v1 != v2
                                {
                                    ok = false;
                                    break;
                                }
                            }
                            if ok {
                                let mut merged_subst = s1.clone();
                                merged_subst.extend(s2.iter().map(|(&k, &v)| (k, v)));
                                merged.push(merged_subst);
                            }
                        }
                    }
                    combined = merged;
                    if combined.is_empty() {
                        break;
                    }
                }

                for subst in combined {
                    // Check all bound variables are assigned.
                    let all_bound = pattern
                        .bound_vars
                        .iter()
                        .all(|(n, _)| subst.contains_key(n));
                    if all_bound {
                        let mut key_vec: Vec<_> = subst.iter().map(|(&k, &v)| (k, v)).collect();
                        key_vec.sort_by_key(|(k, _)| k.into_inner());
                        let key = (pattern_idx, key_vec.clone());

                        if !self.generated_bindings.contains(&key) {
                            self.generated_bindings.insert(key);
                            new_bindings.push(Binding {
                                pattern_idx,
                                substitution: subst,
                            });
                        }
                    }
                }
            }
        }

        new_bindings
    }

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
