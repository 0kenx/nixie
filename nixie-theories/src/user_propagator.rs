//! User Propagator Framework
//!
//! Allows users to integrate custom theory solvers and propagation logic into Nixie.
//!
//! # Overview
//!
//! The user propagator system enables:
//! 1. **Custom Theory Integration**: Define domain-specific reasoning
//! 2. **Event Callbacks**: React to fixed values, equalities, and decisions
//! 3. **Propagation**: Derive and propagate custom consequences
//! 4. **Branching Hints**: Guide the solver's search strategy
//!
//! # Example
//!
//! ```rust,ignore
//! use nixie_theories::user_propagator::*;
//!
//! struct MyTheory {
//!     // Custom state
//! }
//!
//! impl UserPropagator for MyTheory {
//!     fn on_fixed(&mut self, term: TermId, value: TermId, ctx: &mut PropagatorContext) {
//!         // React to term getting a fixed value
//!         // Can propagate consequences via ctx.propagate(...)
//!     }
//!
//!     fn on_equality(&mut self, lhs: TermId, rhs: TermId, ctx: &mut PropagatorContext) {
//!         // React to equality lhs = rhs
//!     }
//!
//!     fn final_check(&mut self, ctx: &mut PropagatorContext) -> PropagatorResult {
//!         // Perform complete theory check
//!         PropagatorResult::Sat
//!     }
//! }
//! ```

#[allow(unused_imports)]
use crate::prelude::*;
use nixie_core::ast::TermId;

/// Result from a propagator operation
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum PropagatorResult {
    /// Satisfiable - no conflicts found
    Sat,
    /// Inconsistent: the conjunction of these true antecedent literals is impossible.
    Unsat(Vec<TermId>),
    /// Unknown - incomplete check
    Unknown,
}

/// Consequence to propagate
#[derive(Debug, Clone)]
pub struct Consequence {
    /// The consequence term to assert as true
    pub term: TermId,
    /// Justification (antecedent literals)
    pub justification: Vec<TermId>,
    /// Optional independently checkable table witness. Its original statement
    /// must be authenticated by the consumer; attaching a certificate alone
    /// does not make an arbitrary user propagator trusted or proof-producing.
    pub table_certificate: Option<crate::cp::table_proof::TableCertificate>,
    /// Optional exactly-one domain witness. Consumers must authenticate
    /// its original statement and check the exact implication before use.
    pub domain_certificate: Option<crate::cp::domain_proof::DomainCertificate>,
    /// Optional graph path/cut/cycle witness. Consumers must authenticate
    /// its original statement and check the exact implication before use;
    /// checking recomputes explicit closures over the immutable
    /// declaration (the propagator stays untrusted).
    pub graph_certificate: Option<crate::graph::proof::GraphCertificate>,
}

impl Consequence {
    /// Create a new consequence
    pub fn new(term: TermId, justification: Vec<TermId>) -> Self {
        Self {
            term,
            justification,
            table_certificate: None,
            domain_certificate: None,
            graph_certificate: None,
        }
    }
}

/// Context provided to user propagators for callbacks
pub struct PropagatorContext<'a> {
    /// Queue of consequences to propagate
    consequences: &'a mut VecDeque<Consequence>,
    /// Undo journal for the consequence queue (see [`UserPropagatorManager`]).
    journal: &'a mut Vec<ConsequenceOp>,
    /// Fixed terms
    fixed_terms: &'a FxHashMap<TermId, TermId>,
    /// Equalities
    equalities: &'a FxHashSet<(TermId, TermId)>,
}

impl<'a> PropagatorContext<'a> {
    /// Create a new propagator context
    pub(crate) fn new(
        consequences: &'a mut VecDeque<Consequence>,
        journal: &'a mut Vec<ConsequenceOp>,
        fixed_terms: &'a FxHashMap<TermId, TermId>,
        equalities: &'a FxHashSet<(TermId, TermId)>,
    ) -> Self {
        Self {
            consequences,
            journal,
            fixed_terms,
            equalities,
        }
    }

    /// Propagate a consequence
    pub fn propagate(&mut self, consequence: Consequence) {
        self.journal.push(ConsequenceOp::Pushed);
        self.consequences.push_back(consequence);
    }

    /// Get the fixed value for a term, if any
    pub fn get_fixed_value(&self, term: TermId) -> Option<TermId> {
        self.fixed_terms.get(&term).copied()
    }

    /// Check if two terms are equal
    pub fn are_equal(&self, lhs: TermId, rhs: TermId) -> bool {
        self.equalities.contains(&(lhs, rhs)) || self.equalities.contains(&(rhs, lhs))
    }
}

/// Trait for user-defined propagators
///
/// Implement this trait to integrate custom theory reasoning into Nixie.
pub trait UserPropagator: Send + Sync {
    /// Called when a term gets a fixed value
    ///
    /// # Arguments
    /// * `term` - The term that got fixed
    /// * `value` - The value assigned to the term
    /// * `ctx` - Context for propagating consequences
    fn on_fixed(&mut self, _term: TermId, _value: TermId, _ctx: &mut PropagatorContext) {
        // Default: do nothing
    }

    /// Called when two terms become equal
    ///
    /// # Arguments
    /// * `lhs` - Left-hand side of equality
    /// * `rhs` - Right-hand side of equality
    /// * `ctx` - Context for propagating consequences
    fn on_equality(&mut self, _lhs: TermId, _rhs: TermId, _ctx: &mut PropagatorContext) {
        // Default: do nothing
    }

    /// Called when two terms become disequal
    ///
    /// # Arguments
    /// * `lhs` - Left-hand side of disequality
    /// * `rhs` - Right-hand side of disequality
    /// * `ctx` - Context for propagating consequences
    fn on_disequality(&mut self, _lhs: TermId, _rhs: TermId, _ctx: &mut PropagatorContext) {
        // Default: do nothing
    }

    /// Called when a new term is created
    ///
    /// Allows the propagator to track or register the term.
    fn on_created(&mut self, _term: TermId) {
        // Default: do nothing
    }

    /// Called during final check (SAT-complete check)
    ///
    /// The propagator should perform a complete satisfiability check.
    fn final_check(&mut self, _ctx: &mut PropagatorContext) -> PropagatorResult {
        PropagatorResult::Unknown
    }

    /// Called before making a branching decision
    ///
    /// Returns `Some((var, phase))` to guide the decision, or `None` to let the solver decide.
    fn decide(&mut self) -> Option<(TermId, bool)> {
        None
    }

    /// Push a new context level
    fn push(&mut self) {
        // Default: do nothing
    }

    /// Pop context levels
    fn pop(&mut self, _levels: usize) {
        // Default: do nothing
    }

    /// Reset the propagator
    fn reset(&mut self) {
        // Default: do nothing
    }
}

/// Statistics for user propagators
#[derive(Debug, Clone, Default)]
pub struct UserPropagatorStats {
    /// Number of fixed callbacks
    pub num_fixed_callbacks: usize,
    /// Number of equality callbacks
    pub num_eq_callbacks: usize,
    /// Number of disequality callbacks
    pub num_diseq_callbacks: usize,
    /// Number of created callbacks
    pub num_created_callbacks: usize,
    /// Number of final checks
    pub num_final_checks: usize,
    /// Number of propagated consequences
    pub num_propagations: usize,
    /// Number of conflicts found
    pub num_conflicts: usize,
}

impl UserPropagatorStats {
    /// Reset all statistics
    pub fn reset(&mut self) {
        *self = Self::default();
    }
}

/// Manager for user propagators
pub struct UserPropagatorManager {
    /// Registered propagators
    propagators: Vec<Box<dyn UserPropagator>>,
    /// Fixed terms (term -> value). FxHash, not std SipHash: every watched
    /// atom of every search event is looked up here, and the SipHash rounds
    /// measured at ~12 % of a graph-corpus solve.
    fixed_terms: FxHashMap<TermId, TermId>,
    /// Known equalities
    equalities: FxHashSet<(TermId, TermId)>,
    /// Pending consequences
    consequences: VecDeque<Consequence>,
    /// Watched terms
    watched_terms: FxHashSet<TermId>,
    /// Statistics
    stats: UserPropagatorStats,
    /// Context stack for push/pop: exact undo journals. Each observable
    /// mutation appends the previous state of the touched entry, so a `pop`
    /// replays backward to the recorded mark. This restores precisely the
    /// same state a full snapshot would (including overwritten fixations
    /// and retracted watches) while costing O(changes) instead of
    /// O(total state) per push — the snapshot design cloned every watched
    /// term per SAT decision level, which dominated solving once models
    /// registered thousands of watches (graph constraints).
    context_stack: Vec<PropagatorMark>,
    /// Journal of fixed-term mutations: `(term, previous value)`.
    fixed_journal: Vec<(TermId, Option<TermId>)>,
    /// Journal of equality insertions (pairs; never overwritten, so a
    /// journal entry only records that the pair must be removed on pop).
    equality_journal: Vec<(TermId, TermId)>,
    /// Journal of watched-term insertions.
    watch_journal: Vec<TermId>,
    /// Journal of consequence-queue mutations, replayed exactly (pushed
    /// entries pop back off; drained entries return to the front).
    consequence_journal: Vec<ConsequenceOp>,
}

/// One mutation of the pending-consequence queue.
pub(crate) enum ConsequenceOp {
    /// `push_back` happened; undo = `pop_back` (the entry itself is not
    /// needed to undo it).
    Pushed,
    /// front-drain happened; undo = `push_front` of the drained entry.
    Drained(Consequence),
}

struct PropagatorMark {
    fixed_journal: usize,
    equality_journal: usize,
    watch_journal: usize,
    consequence_journal: usize,
    propagators: usize,
}

impl UserPropagatorManager {
    /// Create a new user propagator manager
    pub fn new() -> Self {
        Self {
            propagators: Vec::new(),
            fixed_terms: FxHashMap::default(),
            equalities: FxHashSet::default(),
            consequences: VecDeque::new(),
            watched_terms: FxHashSet::default(),
            stats: UserPropagatorStats::default(),
            context_stack: Vec::new(),
            fixed_journal: Vec::new(),
            equality_journal: Vec::new(),
            watch_journal: Vec::new(),
            consequence_journal: Vec::new(),
        }
    }

    /// Register a user propagator
    pub fn register_propagator(&mut self, propagator: Box<dyn UserPropagator>) {
        self.propagators.push(propagator);
    }

    /// Watch a term (trigger callbacks for this term)
    pub fn watch_term(&mut self, term: TermId) {
        if self.watched_terms.insert(term) {
            self.watch_journal.push(term);
        }
    }

    /// Queue a consequence directly (journaled like `PropagatorContext::
    /// propagate`; in-module white-box tests use this to seed the queue).
    #[cfg(test)]
    fn queue_consequence(&mut self, consequence: Consequence) {
        self.consequence_journal.push(ConsequenceOp::Pushed);
        self.consequences.push_back(consequence);
    }

    /// Notify that a term has a fixed value
    pub fn notify_fixed(&mut self, term: TermId, value: TermId) {
        if !self.watched_terms.contains(&term) {
            return;
        }

        let previous = self.fixed_terms.insert(term, value);
        // Idempotent re-fixation needs no undo entry; a real mutation
        // records the overwritten state exactly once.
        if previous != Some(value) {
            self.fixed_journal.push((term, previous));
        }
        self.stats.num_fixed_callbacks = self.stats.num_fixed_callbacks.saturating_add(1);

        let mut ctx = PropagatorContext::new(
            &mut self.consequences,
            &mut self.consequence_journal,
            &self.fixed_terms,
            &self.equalities,
        );

        for prop in &mut self.propagators {
            prop.on_fixed(term, value, &mut ctx);
        }
    }

    /// Notify that two terms are equal
    pub fn notify_equality(&mut self, lhs: TermId, rhs: TermId) {
        if !self.watched_terms.contains(&lhs) && !self.watched_terms.contains(&rhs) {
            return;
        }

        if self.equalities.insert((lhs, rhs)) {
            self.equality_journal.push((lhs, rhs));
        }
        self.stats.num_eq_callbacks = self.stats.num_eq_callbacks.saturating_add(1);

        let mut ctx = PropagatorContext::new(
            &mut self.consequences,
            &mut self.consequence_journal,
            &self.fixed_terms,
            &self.equalities,
        );

        for prop in &mut self.propagators {
            prop.on_equality(lhs, rhs, &mut ctx);
        }
    }

    /// Notify that two terms are disequal
    pub fn notify_disequality(&mut self, lhs: TermId, rhs: TermId) {
        if !self.watched_terms.contains(&lhs) && !self.watched_terms.contains(&rhs) {
            return;
        }

        self.stats.num_diseq_callbacks = self.stats.num_diseq_callbacks.saturating_add(1);

        let mut ctx = PropagatorContext::new(
            &mut self.consequences,
            &mut self.consequence_journal,
            &self.fixed_terms,
            &self.equalities,
        );

        for prop in &mut self.propagators {
            prop.on_disequality(lhs, rhs, &mut ctx);
        }
    }

    /// Notify that a new term was created
    pub fn notify_created(&mut self, term: TermId) {
        self.stats.num_created_callbacks = self.stats.num_created_callbacks.saturating_add(1);

        for prop in &mut self.propagators {
            prop.on_created(term);
        }
    }

    /// Perform final check (complete satisfiability)
    pub fn final_check(&mut self) -> PropagatorResult {
        self.stats.num_final_checks = self.stats.num_final_checks.saturating_add(1);

        let mut ctx = PropagatorContext::new(
            &mut self.consequences,
            &mut self.consequence_journal,
            &self.fixed_terms,
            &self.equalities,
        );

        for prop in &mut self.propagators {
            match prop.final_check(&mut ctx) {
                PropagatorResult::Sat => continue,
                PropagatorResult::Unsat(conflict) => {
                    self.stats.num_conflicts = self.stats.num_conflicts.saturating_add(1);
                    return PropagatorResult::Unsat(conflict);
                }
                PropagatorResult::Unknown => return PropagatorResult::Unknown,
            }
        }

        PropagatorResult::Sat
    }

    /// Get the next branching decision from propagators
    pub fn get_decision(&mut self) -> Option<(TermId, bool)> {
        for prop in &mut self.propagators {
            if let Some(decision) = prop.decide() {
                return Some(decision);
            }
        }
        None
    }

    /// Get pending consequences to propagate
    pub fn get_consequences(&mut self) -> Vec<Consequence> {
        let consequences: Vec<_> = self
            .consequences
            .drain(..)
            .inspect(|c| {
                self.consequence_journal
                    .push(ConsequenceOp::Drained(c.clone()))
            })
            .collect();
        self.stats.num_propagations = self
            .stats
            .num_propagations
            .saturating_add(consequences.len());
        consequences
    }

    /// Check if there are pending consequences
    pub fn has_consequences(&self) -> bool {
        !self.consequences.is_empty()
    }

    /// Push a new context level
    pub fn push(&mut self) {
        self.context_stack.push(PropagatorMark {
            fixed_journal: self.fixed_journal.len(),
            equality_journal: self.equality_journal.len(),
            watch_journal: self.watch_journal.len(),
            consequence_journal: self.consequence_journal.len(),
            propagators: self.propagators.len(),
        });
        for prop in &mut self.propagators {
            prop.push();
        }
    }

    /// Pop context levels
    pub fn pop(&mut self, levels: usize) {
        if levels == 0 {
            return;
        }

        for _ in 0..levels {
            let Some(mark) = self.context_stack.pop() else {
                break;
            };
            self.propagators.truncate(mark.propagators);
            for prop in &mut self.propagators {
                prop.pop(1);
            }
            // Replay the consequence-queue journal backward.
            while self.consequence_journal.len() > mark.consequence_journal {
                match self.consequence_journal.pop() {
                    Some(ConsequenceOp::Pushed) => {
                        self.consequences.pop_back();
                    }
                    Some(ConsequenceOp::Drained(consequence)) => {
                        self.consequences.push_front(consequence);
                    }
                    None => break,
                }
            }
            // Replay the fixed-value journal backward.
            while self.fixed_journal.len() > mark.fixed_journal {
                match self.fixed_journal.pop() {
                    Some((term, Some(previous))) => {
                        self.fixed_terms.insert(term, previous);
                    }
                    Some((term, None)) => {
                        self.fixed_terms.remove(&term);
                    }
                    None => break,
                }
            }
            // Equality and watch insertions are removal-only journals.
            while self.equality_journal.len() > mark.equality_journal {
                match self.equality_journal.pop() {
                    Some(pair) => {
                        self.equalities.remove(&pair);
                    }
                    None => break,
                }
            }
            while self.watch_journal.len() > mark.watch_journal {
                match self.watch_journal.pop() {
                    Some(term) => {
                        self.watched_terms.remove(&term);
                    }
                    None => break,
                }
            }
        }
    }

    /// Current fixed value, scoped with the corresponding notification.
    pub fn get_fixed_value(&self, term: TermId) -> Option<TermId> {
        self.fixed_terms.get(&term).copied()
    }

    /// Reset the manager
    pub fn reset(&mut self) {
        self.fixed_terms.clear();
        self.equalities.clear();
        self.consequences.clear();
        self.watched_terms.clear();
        self.context_stack.clear();
        self.fixed_journal.clear();
        self.equality_journal.clear();
        self.watch_journal.clear();
        self.consequence_journal.clear();
        self.stats.reset();

        for prop in &mut self.propagators {
            prop.reset();
        }
    }

    /// Get statistics
    pub fn stats(&self) -> &UserPropagatorStats {
        &self.stats
    }

    /// Get number of registered propagators
    pub fn num_propagators(&self) -> usize {
        self.propagators.len()
    }
}

impl Default for UserPropagatorManager {
    fn default() -> Self {
        Self::new()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    struct DummyPropagator {
        fixed_count: usize,
        eq_count: usize,
    }

    impl DummyPropagator {
        fn new() -> Self {
            Self {
                fixed_count: 0,
                eq_count: 0,
            }
        }
    }

    impl UserPropagator for DummyPropagator {
        fn on_fixed(&mut self, _term: TermId, _value: TermId, _ctx: &mut PropagatorContext) {
            self.fixed_count = self.fixed_count.saturating_add(1);
        }

        fn on_equality(&mut self, _lhs: TermId, _rhs: TermId, _ctx: &mut PropagatorContext) {
            self.eq_count = self.eq_count.saturating_add(1);
        }

        fn final_check(&mut self, _ctx: &mut PropagatorContext) -> PropagatorResult {
            PropagatorResult::Sat
        }
    }

    #[test]
    fn test_manager_creation() {
        let manager = UserPropagatorManager::new();
        assert_eq!(manager.num_propagators(), 0);
        assert!(!manager.has_consequences());
    }

    #[test]
    fn test_register_propagator() {
        let mut manager = UserPropagatorManager::new();
        manager.register_propagator(Box::new(DummyPropagator::new()));
        assert_eq!(manager.num_propagators(), 1);
    }

    #[test]
    fn test_watch_term() {
        let mut manager = UserPropagatorManager::new();
        let term = TermId::new(1);
        manager.watch_term(term);
        assert!(manager.watched_terms.contains(&term));
    }

    #[test]
    fn test_notify_fixed() {
        let mut manager = UserPropagatorManager::new();
        manager.register_propagator(Box::new(DummyPropagator::new()));

        let term = TermId::new(1);
        let value = TermId::new(2);

        manager.watch_term(term);
        manager.notify_fixed(term, value);

        assert_eq!(manager.stats().num_fixed_callbacks, 1);
        assert_eq!(manager.get_fixed_value(term), Some(value));
    }

    #[test]
    fn test_notify_equality() {
        let mut manager = UserPropagatorManager::new();
        manager.register_propagator(Box::new(DummyPropagator::new()));

        let lhs = TermId::new(1);
        let rhs = TermId::new(2);

        manager.watch_term(lhs);
        manager.notify_equality(lhs, rhs);

        assert_eq!(manager.stats().num_eq_callbacks, 1);
    }

    #[test]
    fn test_final_check() {
        let mut manager = UserPropagatorManager::new();
        manager.register_propagator(Box::new(DummyPropagator::new()));

        let result = manager.final_check();
        assert_eq!(result, PropagatorResult::Sat);
        assert_eq!(manager.stats().num_final_checks, 1);
    }

    #[test]
    fn test_push_pop() {
        let mut manager = UserPropagatorManager::new();
        manager.register_propagator(Box::new(DummyPropagator::new()));

        let term = TermId::new(1);
        let value = TermId::new(2);

        manager.push();
        manager.watch_term(term);
        manager.notify_fixed(term, value);

        assert_eq!(manager.get_fixed_value(term), Some(value));

        manager.pop(1);
        assert_eq!(manager.get_fixed_value(term), None);
        assert!(!manager.watched_terms.contains(&term));
    }

    #[test]
    fn test_consequence_propagation() {
        let mut manager = UserPropagatorManager::new();

        struct PropagatingPropagator;
        impl UserPropagator for PropagatingPropagator {
            fn on_fixed(&mut self, _term: TermId, _value: TermId, ctx: &mut PropagatorContext) {
                let cons = Consequence::new(TermId::new(100), vec![]);
                ctx.propagate(cons);
            }
        }

        manager.register_propagator(Box::new(PropagatingPropagator));
        let term = TermId::new(1);
        manager.watch_term(term);
        manager.notify_fixed(term, TermId::new(2));

        assert!(manager.has_consequences());
        let consequences = manager.get_consequences();
        assert_eq!(consequences.len(), 1);
    }

    #[test]
    fn restores_overwrites_equalities_watches_and_pending_consequences() {
        let mut manager = UserPropagatorManager::new();
        let a = TermId::new(10);
        let b = TermId::new(11);
        let c = TermId::new(12);
        manager.watch_term(a);
        manager.notify_fixed(a, b);
        manager.notify_equality(a, b);
        manager.queue_consequence(Consequence::new(a, vec![]));
        manager.push();
        manager.notify_fixed(a, c);
        manager.notify_equality(a, c);
        manager.watch_term(c);
        manager.notify_fixed(c, b);
        manager.get_consequences();
        manager.queue_consequence(Consequence::new(c, vec![a]));
        manager.push();
        manager.notify_fixed(a, a);
        manager.pop(1);
        assert_eq!(manager.get_fixed_value(a), Some(c));
        manager.pop(1);
        assert_eq!(manager.get_fixed_value(a), Some(b));
        assert_eq!(manager.get_fixed_value(c), None);
        assert_eq!(manager.equalities.len(), 1);
        assert!(manager.equalities.contains(&(a, b)));
        assert!(!manager.watched_terms.contains(&c));
        let consequences = manager.get_consequences();
        assert_eq!(consequences.len(), 1);
        assert_eq!(consequences[0].term, a);
    }
}
