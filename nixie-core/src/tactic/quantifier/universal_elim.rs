//! The universal-elimination tactic.
//!
//! Split out of the former single-file `tactic/quantifier.rs`; see
//! [`super`] for the module layout. Pure code motion.

use crate::ast::TermManager;
use crate::ast::normal_forms::eliminate_universal_quantifiers;
use crate::error::Result;
#[allow(unused_imports)]
use crate::prelude::*;

use crate::tactic::{Goal, TacticResult};

/// Universal elimination tactic
///
/// Eliminates universal quantifiers by replacing bound variables with
/// fresh constants.
#[derive(Debug)]
pub struct UniversalEliminationTactic<'a> {
    manager: &'a mut TermManager,
}

impl<'a> UniversalEliminationTactic<'a> {
    /// Create a new universal elimination tactic
    pub fn new(manager: &'a mut TermManager) -> Self {
        Self { manager }
    }

    /// Apply the tactic to a goal
    pub fn apply_mut(&mut self, goal: &Goal) -> Result<TacticResult> {
        let mut changed = false;
        let mut new_assertions = Vec::with_capacity(goal.assertions.len());

        for &assertion in &goal.assertions {
            let eliminated = eliminate_universal_quantifiers(assertion, self.manager);
            if eliminated != assertion {
                changed = true;
            }
            new_assertions.push(eliminated);
        }

        if !changed {
            return Ok(TacticResult::NotApplicable);
        }

        Ok(TacticResult::SubGoals(vec![Goal {
            assertions: new_assertions,
            precision: goal.precision,
        }]))
    }
}
