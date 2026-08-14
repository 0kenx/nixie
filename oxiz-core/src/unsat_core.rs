//! Unsat core extraction infrastructure
//!
//! This module provides utilities for extracting minimal unsatisfiable cores
//! from a set of assertions. An unsat core is a minimal subset of assertions
//! that is still unsatisfiable.

use crate::ast::{NamedAssertion, TermId};
#[allow(unused_imports)]
use crate::prelude::*;

/// An unsatisfiable core
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct UnsatCore {
    /// The assertions in the unsat core
    assertions: Vec<NamedAssertion>,
}

impl UnsatCore {
    /// Create a new unsat core from a set of assertions
    #[must_use]
    pub fn new(assertions: Vec<NamedAssertion>) -> Self {
        Self { assertions }
    }

    /// Create an empty unsat core
    #[must_use]
    pub fn empty() -> Self {
        Self {
            assertions: Vec::new(),
        }
    }

    /// Get the assertions in the core
    #[must_use]
    pub fn assertions(&self) -> &[NamedAssertion] {
        &self.assertions
    }

    /// Get the term IDs in the core
    #[must_use]
    pub fn term_ids(&self) -> Vec<TermId> {
        self.assertions.iter().map(|a| a.term).collect()
    }

    /// Get the names of assertions in the core
    #[must_use]
    pub fn names(&self) -> Vec<Option<&str>> {
        self.assertions.iter().map(|a| a.name.as_deref()).collect()
    }

    /// Get the number of assertions in the core
    #[must_use]
    pub fn len(&self) -> usize {
        self.assertions.len()
    }

    /// Check if the core is empty
    #[must_use]
    pub fn is_empty(&self) -> bool {
        self.assertions.is_empty()
    }

    /// Add an assertion to the core
    pub fn add(&mut self, assertion: NamedAssertion) {
        self.assertions.push(assertion);
    }

    /// Check if the core contains a specific term
    #[must_use]
    pub fn contains_term(&self, term: TermId) -> bool {
        self.assertions.iter().any(|a| a.term == term)
    }

    /// Check if the core contains an assertion with a specific name
    #[must_use]
    pub fn contains_name(&self, name: &str) -> bool {
        self.assertions
            .iter()
            .any(|a| a.name.as_deref() == Some(name))
    }

    /// Deduplicate the core by removing repeated assertions.
    ///
    /// This does *not* attempt to shrink the core further (that requires a
    /// solver to re-check unsatisfiability after each removal – see
    /// [`Self::minimize_with`]); it only drops assertions that name/term
    /// the exact same [`TermId`] as one already kept.
    pub fn minimize(&mut self) {
        let mut seen = FxHashSet::default();
        self.assertions.retain(|a| seen.insert(a.term));
    }

    /// Minimize the core via deletion-based MUS extraction, using
    /// `is_unsat` to re-check satisfiability after each tentative removal.
    ///
    /// For each assertion (in turn): tentatively remove it, ask `is_unsat`
    /// whether the remaining assertions are still unsatisfiable, and keep
    /// it removed only if so; otherwise restore it. The result is a subset
    /// of the original core that is still reported unsatisfiable by
    /// `is_unsat` and from which no single further assertion can be
    /// dropped without losing unsatisfiability (a "delta-minimal" – though
    /// not necessarily globally minimum-cardinality – unsat core).
    ///
    /// Also deduplicates repeated assertions first (see [`Self::minimize`]),
    /// since a duplicate is trivially redundant regardless of what
    /// `is_unsat` would say.
    pub fn minimize_with(&mut self, is_unsat: impl Fn(&[TermId]) -> bool) {
        self.minimize();

        let mut i = 0;
        while i < self.assertions.len() {
            let removed = self.assertions.remove(i);
            let remaining_terms = self.term_ids();
            if is_unsat(&remaining_terms) {
                // Still unsat without `removed`: drop it for good, don't
                // advance `i` (the next element has shifted into position `i`).
            } else {
                // Needed for unsatisfiability: put it back and move on.
                self.assertions.insert(i, removed);
                i += 1;
            }
        }
    }
}

/// Builder for constructing unsat cores
#[derive(Debug, Clone)]
pub struct UnsatCoreBuilder {
    assertions: Vec<NamedAssertion>,
}

impl UnsatCoreBuilder {
    /// Create a new builder
    #[must_use]
    pub fn new() -> Self {
        Self {
            assertions: Vec::new(),
        }
    }

    /// Add an assertion to the core
    pub fn add(&mut self, assertion: NamedAssertion) -> &mut Self {
        self.assertions.push(assertion);
        self
    }

    /// Add a term without a name
    pub fn add_term(&mut self, term: TermId) -> &mut Self {
        self.assertions.push(NamedAssertion::unnamed(term));
        self
    }

    /// Add a named term
    pub fn add_named(&mut self, term: TermId, name: impl Into<String>) -> &mut Self {
        self.assertions.push(NamedAssertion::named(term, name));
        self
    }

    /// Build the unsat core
    #[must_use]
    pub fn build(self) -> UnsatCore {
        UnsatCore::new(self.assertions)
    }
}

impl Default for UnsatCoreBuilder {
    fn default() -> Self {
        Self::new()
    }
}

impl core::fmt::Display for UnsatCore {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        writeln!(f, "Unsat Core ({} assertions):", self.len())?;
        for (i, assertion) in self.assertions.iter().enumerate() {
            if let Some(name) = &assertion.name {
                writeln!(f, "  {}: {} (term {:?})", i + 1, name, assertion.term)?;
            } else {
                writeln!(f, "  {}: <unnamed> (term {:?})", i + 1, assertion.term)?;
            }
        }
        Ok(())
    }
}

/// Strategy for extracting unsat cores
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum UnsatCoreStrategy {
    /// Return all assertions (no minimization)
    All,
    /// Use deletion-based minimization (remove one at a time)
    Deletion,
    /// Use QuickXplain algorithm for faster minimization
    QuickXplain,
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_empty_core() {
        let core = UnsatCore::empty();
        assert!(core.is_empty());
        assert_eq!(core.len(), 0);
    }

    #[test]
    fn test_create_core() {
        let assertions = vec![
            NamedAssertion::named(TermId(1), "a1"),
            NamedAssertion::named(TermId(2), "a2"),
        ];

        let core = UnsatCore::new(assertions);
        assert_eq!(core.len(), 2);
        assert!(!core.is_empty());
    }

    #[test]
    fn test_term_ids() {
        let core = UnsatCore::new(vec![
            NamedAssertion::unnamed(TermId(1)),
            NamedAssertion::unnamed(TermId(2)),
            NamedAssertion::unnamed(TermId(3)),
        ]);

        let ids = core.term_ids();
        assert_eq!(ids, vec![TermId(1), TermId(2), TermId(3)]);
    }

    #[test]
    fn test_names() {
        let core = UnsatCore::new(vec![
            NamedAssertion::named(TermId(1), "a1"),
            NamedAssertion::unnamed(TermId(2)),
            NamedAssertion::named(TermId(3), "a3"),
        ]);

        let names = core.names();
        assert_eq!(names.len(), 3);
        assert_eq!(names[0], Some("a1"));
        assert_eq!(names[1], None);
        assert_eq!(names[2], Some("a3"));
    }

    #[test]
    fn test_contains_term() {
        let core = UnsatCore::new(vec![
            NamedAssertion::unnamed(TermId(1)),
            NamedAssertion::unnamed(TermId(2)),
        ]);

        assert!(core.contains_term(TermId(1)));
        assert!(core.contains_term(TermId(2)));
        assert!(!core.contains_term(TermId(3)));
    }

    #[test]
    fn test_contains_name() {
        let core = UnsatCore::new(vec![
            NamedAssertion::named(TermId(1), "a1"),
            NamedAssertion::named(TermId(2), "a2"),
        ]);

        assert!(core.contains_name("a1"));
        assert!(core.contains_name("a2"));
        assert!(!core.contains_name("a3"));
    }

    #[test]
    fn test_add() {
        let mut core = UnsatCore::empty();
        assert_eq!(core.len(), 0);

        core.add(NamedAssertion::unnamed(TermId(1)));
        assert_eq!(core.len(), 1);

        core.add(NamedAssertion::named(TermId(2), "a2"));
        assert_eq!(core.len(), 2);
    }

    #[test]
    fn test_minimize() {
        let mut core = UnsatCore::new(vec![
            NamedAssertion::unnamed(TermId(1)),
            NamedAssertion::unnamed(TermId(2)),
            NamedAssertion::unnamed(TermId(1)), // duplicate
        ]);

        assert_eq!(core.len(), 3);
        core.minimize();
        assert_eq!(core.len(), 2);
    }

    #[test]
    fn test_builder() {
        let mut builder = UnsatCoreBuilder::new();
        builder.add_term(TermId(1));
        builder.add_named(TermId(2), "a2");
        builder.add_term(TermId(3));
        let core = builder.build();

        assert_eq!(core.len(), 3);
        assert!(core.contains_term(TermId(1)));
        assert!(core.contains_name("a2"));
    }

    #[test]
    fn test_builder_default() {
        let mut builder = UnsatCoreBuilder::default();
        builder.add_term(TermId(1));
        let core = builder.build();

        assert_eq!(core.len(), 1);
    }

    #[test]
    fn test_display() {
        let core = UnsatCore::new(vec![
            NamedAssertion::named(TermId(1), "assertion_one"),
            NamedAssertion::unnamed(TermId(2)),
        ]);

        let display = format!("{}", core);
        assert!(display.contains("Unsat Core"));
        assert!(display.contains("assertion_one"));
        assert!(display.contains("<unnamed>"));
    }

    #[test]
    fn test_strategy() {
        assert_ne!(UnsatCoreStrategy::All, UnsatCoreStrategy::Deletion);
        assert_eq!(
            UnsatCoreStrategy::QuickXplain,
            UnsatCoreStrategy::QuickXplain
        );
    }
}
