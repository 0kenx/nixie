//! Quantifier-presence queries over terms and goals.
//!
//! Split out of the former single-file `tactic/quantifier.rs`; see
//! [`super`] for the module layout. Pure code motion.

use crate::ast::traversal::{TermVisitor, VisitorAction, traverse};
use crate::ast::{TermId, TermKind, TermManager};
#[allow(unused_imports)]
use crate::prelude::*;

use crate::tactic::Goal;

/// Check if a term contains any quantifiers
#[must_use]
pub fn contains_quantifier(term_id: TermId, manager: &TermManager) -> bool {
    struct QuantifierChecker {
        found: bool,
    }

    impl TermVisitor for QuantifierChecker {
        fn visit_pre(&mut self, term_id: TermId, manager: &TermManager) -> VisitorAction {
            if let Some(term) = manager.get(term_id)
                && matches!(term.kind, TermKind::Forall { .. } | TermKind::Exists { .. })
            {
                self.found = true;
                return VisitorAction::Stop;
            }
            VisitorAction::Continue
        }
    }

    let mut checker = QuantifierChecker { found: false };
    let _ = traverse(term_id, manager, &mut checker);
    checker.found
}

/// Check if a goal contains any quantifiers
#[must_use]
pub fn goal_has_quantifiers(goal: &Goal, manager: &TermManager) -> bool {
    goal.assertions
        .iter()
        .any(|&a| contains_quantifier(a, manager))
}
