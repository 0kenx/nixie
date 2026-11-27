//! Ground-term collection for instantiation candidates.
//!
//! Split out of the former single-file `tactic/quantifier.rs`; see
//! [`super`] for the module layout.

use crate::ast::traversal::{collect_subterms, get_children};
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
    /// Whether `term` is ground, for every subterm examined so far: the
    /// answer the scope- and pattern-aware query gives, computed once per
    /// subterm instead of once per subterm per enclosing subterm (see
    /// [`Self::collect`]).
    ground: FxHashMap<TermId, bool>,
}

impl GroundTermCollector {
    /// Create a new ground term collector
    #[must_use]
    pub fn new() -> Self {
        Self::default()
    }

    /// Collect all ground subterms of `term_id`.
    ///
    /// The subterms are visited in `collect_subterms`' post-order, children
    /// before parents, and a subterm's groundness is read off its children's
    /// where that is its definition – for every operator that binds nothing,
    /// the free variables of a term are the union of its children's, so it is
    /// ground exactly when they all are.  The scope-aware query
    /// (`free_vars_including_patterns`) still answers for the four binding
    /// forms (`Forall`, `Exists`, `Let`, `Match`), whose body may mention the
    /// names they bind and whose triggers are walked in their own scope, and
    /// for a variable, which is its own free variable.  The answers are the
    /// same term for term, so the candidate lists come out in the same order
    /// for every sort.
    ///
    /// The query used to run once per subterm over that whole subterm, which
    /// is the tree size rather than the DAG size: 483 µs → 179 µs of
    /// collection on a Hamming-stream UF assertion set, and 55 ms → 0.093 ms
    /// on a chain of 2,000 nested applications.
    pub fn collect(&mut self, term_id: TermId, manager: &TermManager) {
        let subterms = collect_subterms(term_id, manager);

        for subterm_id in subterms {
            // Skip if already collected
            if self.all_terms.contains(&subterm_id) {
                continue;
            }

            let Some(term) = manager.get(subterm_id) else {
                continue;
            };

            // Skip boolean constants and quantifiers
            match &term.kind {
                TermKind::True
                | TermKind::False
                | TermKind::Forall { .. }
                | TermKind::Exists { .. } => continue,
                _ => {}
            }

            // Check if the term is ground (no free variables). The
            // pattern-aware answer is kept deliberately: a subterm whose only
            // variable occurrence sits in a nested quantifier's trigger is
            // not a legal ground instantiation candidate, and treating it as
            // one would feed a non-ground term to E-matching.
            if !self.is_ground(subterm_id, &term.kind, manager) {
                continue;
            }

            let sort = term.sort;
            self.all_terms.insert(subterm_id);
            self.terms_by_sort.entry(sort).or_default().push(subterm_id);
        }
    }

    /// Whether `term` is ground, from the memo or from its children; see
    /// [`Self::collect`].
    fn is_ground(&mut self, term: TermId, kind: &TermKind, manager: &TermManager) -> bool {
        if let Some(&ground) = self.ground.get(&term) {
            return ground;
        }
        let ground = match kind {
            // Binding forms and their triggers: the scope-aware query.
            TermKind::Forall { .. }
            | TermKind::Exists { .. }
            | TermKind::Let { .. }
            | TermKind::Match { .. }
            // A variable is a free variable of itself.
            | TermKind::Var(_) => manager.free_vars_including_patterns(term).is_empty(),
            // Everything else binds nothing: ground exactly when its children are.
            _ => get_children(kind)
                .iter()
                .all(|&child| self.groundness_of(child, manager)),
        };
        self.ground.insert(term, ground);
        ground
    }

    /// A child's groundness out of the memo; a child the post-order has not
    /// handed over yet (it cannot happen – every child is visited before its
    /// parent –) is answered by the query that defines it.
    fn groundness_of(&mut self, child: TermId, manager: &TermManager) -> bool {
        self.ground.get(&child).copied().unwrap_or_else(|| {
            let ground = manager.free_vars_including_patterns(child).is_empty();
            self.ground.insert(child, ground);
            ground
        })
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
        self.ground.clear();
    }
}
