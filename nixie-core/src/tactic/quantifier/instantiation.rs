//! The quantifier instantiation tactic.
//!
//! Split out of the former single-file `tactic/quantifier.rs`; see
//! [`super`] for the module layout. Pure code motion.

use crate::ast::{TermId, TermKind, TermManager};
use crate::error::Result;
#[allow(unused_imports)]
use crate::prelude::*;

use super::ground_terms::GroundTermCollector;
use super::matching::PatternMatcher;
use crate::tactic::{Goal, TacticResult};

/// Quantifier instantiation tactic
///
/// This tactic finds quantified formulas (∀x. φ(x)), collects ground terms,
/// matches patterns, and generates instantiation lemmas (φ(t) for ground t).
#[derive(Debug)]
pub struct QuantifierInstantiationTactic<'a> {
    manager: &'a mut TermManager,
    /// Maximum number of instantiations per round
    max_instances: usize,
}

impl<'a> QuantifierInstantiationTactic<'a> {
    /// Create a new quantifier instantiation tactic
    pub fn new(manager: &'a mut TermManager) -> Self {
        Self {
            manager,
            max_instances: 100,
        }
    }

    /// Set the maximum number of instantiations per round
    pub fn with_max_instances(mut self, max: usize) -> Self {
        self.max_instances = max;
        self
    }

    /// Apply the tactic to a goal
    pub fn apply_mut(&mut self, goal: &Goal) -> Result<TacticResult> {
        // Phase 1: Collect quantifiers from goal
        let quantifiers = self.collect_quantifiers(goal);
        if quantifiers.is_empty() {
            return Ok(TacticResult::NotApplicable);
        }

        // Phase 2: Collect ground terms
        let mut ground_collector = GroundTermCollector::new();
        ground_collector.collect_from_goal(goal, self.manager);

        if ground_collector.is_empty() {
            // No ground terms to instantiate with
            return Ok(TacticResult::NotApplicable);
        }

        // Phase 3: Set up pattern matcher
        let mut matcher = PatternMatcher::new();
        for &quant in &quantifiers {
            matcher.add_pattern(quant, self.manager);
        }

        // Phase 4: Match and generate bindings
        let bindings = matcher.match_against(&ground_collector, self.manager);

        if bindings.is_empty() {
            return Ok(TacticResult::NotApplicable);
        }

        // Phase 5: Generate instantiation lemmas
        let mut new_assertions = goal.assertions.clone();
        let mut count = 0;

        for binding in bindings {
            if count >= self.max_instances {
                break;
            }

            if let Some(instance) = matcher.instantiate(&binding, self.manager) {
                // Add the instance as a new assertion.
                //
                // The instantiation lemma is: ∀x.φ(x) → φ(t).  This is only a
                // sound top-level fact when ∀x.φ(x) is *asserted*, i.e. it
                // occurs at positive polarity.  `collect_quantifiers` only
                // gathers positive-polarity universals, so φ(t) is entailed by
                // the goal and may be added safely.
                new_assertions.push(instance);
                count += 1;
            }
        }

        if count == 0 {
            return Ok(TacticResult::NotApplicable);
        }

        Ok(TacticResult::SubGoals(vec![Goal {
            assertions: new_assertions,
            precision: goal.precision,
        }]))
    }

    /// Collect universal quantifiers that occur at **positive polarity** in a
    /// goal.
    ///
    /// Only positive-polarity `Forall` terms are entailed by the goal as
    /// asserted facts, so only those may be instantiated soundly (∀x.φ(x) ⊢
    /// φ(t)).  A `Forall` under a negation, an `Implies` antecedent, or another
    /// mixed-polarity context is *not* asserted – instantiating it as a fact is
    /// unsound (it can turn SAT goals into UNSAT).
    ///
    /// Descent stops at any variable-binding boundary that is not a
    /// positive-polarity universal (i.e. at existentials and at
    /// negative-polarity universals): descending past such a binder would
    /// expose quantifiers whose bodies mention an *existentially* governed
    /// variable, for which φ(t) is not entailed.
    fn collect_quantifiers(&self, goal: &Goal) -> Vec<TermId> {
        let mut quantifiers = Vec::new();
        for &assertion in &goal.assertions {
            self.collect_positive_foralls(assertion, true, &mut quantifiers);
        }
        quantifiers
    }

    /// Recursively collect positive-polarity universal quantifiers.
    /// Collect every universally quantified subformula occurring at positive
    /// polarity.
    ///
    /// Iterative (explicit heap stack over `(term, polarity)` pairs): the
    /// return type is `()`, so a depth cap could only silently drop
    /// quantifiers – costing instantiations without any signal – while the
    /// native recursion it replaces aborted the process outright on a deeply
    /// nested Boolean skeleton.
    ///
    /// `visited` is keyed on `(TermId, polarity)`, which is exactly what the
    /// answer depends on. It stops a shared subformula of the hash-consed DAG
    /// from being re-expanded once per path (previously exponential) and, as
    /// a side effect, keeps each quantifier out of `out` more than once –
    /// duplicates only produced duplicate patterns and duplicate
    /// instantiation lemmas that consumed the caller's `max_instances`
    /// budget.
    fn collect_positive_foralls(&self, term_id: TermId, positive: bool, out: &mut Vec<TermId>) {
        let mut visited: FxHashSet<(TermId, bool)> = FxHashSet::default();
        let mut stack = vec![(term_id, positive)];

        while let Some((id, positive)) = stack.pop() {
            if !visited.insert((id, positive)) {
                continue;
            }
            let kind = match self.manager.get(id) {
                Some(t) => t.kind.clone(),
                None => continue,
            };

            match kind {
                TermKind::Not(arg) => stack.push((arg, !positive)),
                TermKind::And(args) | TermKind::Or(args) => {
                    stack.extend(args.iter().map(|&a| (a, positive)));
                }
                TermKind::Implies(lhs, rhs) => {
                    stack.push((lhs, !positive));
                    stack.push((rhs, positive));
                }
                TermKind::Ite(_, then_br, else_br) => {
                    // The condition occurs at mixed polarity; skip it.  Both
                    // branches preserve the ambient polarity.
                    stack.push((then_br, positive));
                    stack.push((else_br, positive));
                }
                // Negative-polarity forall behaves existentially: do not
                // collect and do not descend (falls through to the catch-all
                // below).
                TermKind::Forall { body, .. } if positive => {
                    out.push(id);
                    // Body of a positive universal is still governed only by
                    // universals, so nested positive foralls remain sound.
                    stack.push((body, positive));
                }
                // Existentials (either polarity) and all other kinds
                // (including boolean equalities, which are mixed-polarity)
                // are not descended.
                _ => {}
            }
        }
    }
}
