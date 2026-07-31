//! Ground-term collection for instantiation candidates.
//!
//! Split out of the former single-file `tactic/quantifier.rs`; see
//! [`super`] for the module layout. Pure code motion.

use crate::ast::traversal::{collect_free_vars_including_patterns, collect_subterms};
use crate::ast::{TermId, TermKind, TermManager};
#[allow(unused_imports)]
use crate::prelude::*;
use crate::sort::SortId;

use crate::tactic::Goal;

/// Collects ground (variable-free) terms by their sort.
///
/// Ground terms are terms that contain no free variables and are not under
/// quantifiers. These terms serve as instantiation candidates for quantified
/// formulas.
#[derive(Debug, Default)]
pub struct GroundTermCollector {
    /// Ground terms indexed by sort
    terms_by_sort: FxHashMap<SortId, Vec<TermId>>,
    /// All collected ground terms (for deduplication)
    all_terms: FxHashSet<TermId>,
}

impl GroundTermCollector {
    /// Create a new ground term collector
    #[must_use]
    pub fn new() -> Self {
        Self::default()
    }

    /// Collect all ground terms from a term
    pub fn collect(&mut self, term_id: TermId, manager: &TermManager) {
        let subterms = collect_subterms(term_id, manager);

        for subterm_id in subterms {
            // Skip if already collected
            if self.all_terms.contains(&subterm_id) {
                continue;
            }

            // Check if the term is ground (no free variables). The
            // pattern-aware query is used deliberately: a subterm whose only
            // variable occurrence sits in a nested quantifier's trigger is
            // not a legal ground instantiation candidate, and treating it as
            // one would feed a non-ground term to E-matching.
            let free_vars = collect_free_vars_including_patterns(subterm_id, manager);
            if free_vars.is_empty() {
                // Get the sort of this term
                if let Some(term) = manager.get(subterm_id) {
                    // Skip boolean constants and quantifiers
                    match &term.kind {
                        TermKind::True
                        | TermKind::False
                        | TermKind::Forall { .. }
                        | TermKind::Exists { .. } => continue,
                        _ => {}
                    }

                    let sort = term.sort;
                    self.all_terms.insert(subterm_id);
                    self.terms_by_sort.entry(sort).or_default().push(subterm_id);
                }
            }
        }
    }

    /// Collect ground terms from a goal (all assertions)
    pub fn collect_from_goal(&mut self, goal: &Goal, manager: &TermManager) {
        for &assertion in &goal.assertions {
            self.collect(assertion, manager);
        }
    }

    /// Get all ground terms of a specific sort
    #[must_use]
    pub fn get_terms(&self, sort: SortId) -> &[TermId] {
        self.terms_by_sort
            .get(&sort)
            .map(Vec::as_slice)
            .unwrap_or(&[])
    }

    /// Get all collected ground terms
    #[must_use]
    pub fn all_terms(&self) -> &FxHashSet<TermId> {
        &self.all_terms
    }

    /// Get the number of ground terms collected
    #[must_use]
    pub fn len(&self) -> usize {
        self.all_terms.len()
    }

    /// Check if no ground terms were collected
    #[must_use]
    pub fn is_empty(&self) -> bool {
        self.all_terms.is_empty()
    }

    /// Get all sorts that have ground terms
    pub fn sorts(&self) -> impl Iterator<Item = &SortId> {
        self.terms_by_sort.keys()
    }

    /// Clear all collected terms
    pub fn clear(&mut self) {
        self.terms_by_sort.clear();
        self.all_terms.clear();
    }
}
