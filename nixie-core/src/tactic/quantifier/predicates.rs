//! Quantifier-presence queries over terms and goals.
//!
//! Split out of the former single-file `tactic/quantifier.rs`; see
//! [`super`] for the module layout. Pure code motion.

use crate::ast::{TermId, TermManager};
#[allow(unused_imports)]
use crate::prelude::*;

use crate::tactic::Goal;

/// Check if a term contains any quantifiers
///
/// Delegates to the manager's memoized walk ([`TermManager::
/// contains_quantifier`]): repeated queries and shared subterms are set
/// lookups instead of re-traversals, which the per-assertion pipeline
/// asks for at several stages.
#[must_use]
pub fn contains_quantifier(term_id: TermId, manager: &TermManager) -> bool {
    manager.contains_quantifier(term_id)
}

/// Check if a goal contains any quantifiers
#[must_use]
pub fn goal_has_quantifiers(goal: &Goal, manager: &TermManager) -> bool {
    goal.assertions
        .iter()
        .any(|&a| contains_quantifier(a, manager))
}
