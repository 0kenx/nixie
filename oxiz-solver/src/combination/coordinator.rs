//! Theory Combination Coordinator
//!
//! This module coordinates multiple theory solvers using the Nelson-Oppen method
//! with optimizations:
//! - Lazy vs eager theory combination
//! - Shared term management
//! - Equality sharing between theories
//! - Conflict minimization across theories

#![allow(missing_docs)] // Under development

#[allow(unused_imports)]
use crate::prelude::*;
#[cfg(feature = "std")]
use oxiz_core::TermId as ProofTermId;
#[cfg(feature = "profiling")]
use oxiz_core::profiling::{ProfilingCategory, ScopedTimer};
#[cfg(feature = "std")]
use oxiz_proof::{CombinationStep, CombinationTheoryId, NelsonOppenCertificate, ProofNodeId};

/// Placeholder term identifier
pub type TermId = usize;

/// Theory identifier
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum TheoryId {
    Core,
    Arithmetic,
    BitVector,
    Array,
    Datatype,
    String,
    Uninterpreted,
}

/// Theory interface
pub trait TheorySolver {
    /// Get theory ID
    fn theory_id(&self) -> TheoryId;

    /// Assert a formula
    fn assert_formula(&mut self, formula: TermId) -> Result<(), String>;

    /// Check satisfiability
    fn check_sat(&mut self) -> Result<SatResult, String>;

    /// Get model (if SAT)
    fn get_model(&self) -> Option<FxHashMap<TermId, TermId>>;

    /// Get conflict explanation (if UNSAT)
    fn get_conflict(&self) -> Option<Vec<TermId>>;

    /// Backtrack to a level
    fn backtrack(&mut self, level: usize) -> Result<(), String>;

    /// Get implied equalities
    fn get_implied_equalities(&self) -> Vec<(TermId, TermId)>;

    /// Notify of external equality
    fn notify_equality(&mut self, lhs: TermId, rhs: TermId) -> Result<(), String>;
}

/// Satisfiability result
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum SatResult {
    Sat,
    Unsat,
    Unknown,
}

/// Shared term between theories
#[derive(Debug, Clone)]
pub struct SharedTerm {
    /// The term
    pub term: TermId,
    /// Theories that use this term
    pub theories: FxHashSet<TheoryId>,
    /// Current equivalence class representative
    pub representative: TermId,
}

/// Equality propagation item
#[derive(Debug, Clone)]
pub struct EqualityProp {
    /// Left-hand side
    pub lhs: TermId,
    /// Right-hand side
    pub rhs: TermId,
    /// Source theory
    pub source: TheoryId,
    /// Explanation (justification)
    pub explanation: Vec<TermId>,
}

/// Statistics for theory combination
#[derive(Debug, Clone, Default)]
pub struct CoordinatorStats {
    pub check_sat_calls: u64,
    pub theory_conflicts: u64,
    pub equalities_propagated: u64,
    pub shared_terms_count: usize,
    pub theory_combination_rounds: u64,
}

/// Configuration for theory combination
#[derive(Debug, Clone)]
pub struct CoordinatorConfig {
    /// Use eager theory combination (propagate all equalities immediately)
    pub eager_combination: bool,
    /// Maximum theory combination rounds
    pub max_combination_rounds: usize,
    /// Enable conflict minimization across theories
    pub minimize_conflicts: bool,
    /// Enable theory-combination proof certificates.
    pub proof_mode: bool,
}

impl Default for CoordinatorConfig {
    fn default() -> Self {
        Self {
            eager_combination: false,
            max_combination_rounds: 10,
            minimize_conflicts: true,
            proof_mode: false,
        }
    }
}

/// Theory combination coordinator
pub struct TheoryCoordinator {
    config: CoordinatorConfig,
    stats: CoordinatorStats,
    /// Registered theory solvers
    theories: FxHashMap<TheoryId, Box<dyn TheorySolver>>,
    /// Shared terms between theories
    shared_terms: FxHashMap<TermId, SharedTerm>,
    /// Pending equality propagations
    pending_equalities: VecDeque<EqualityProp>,
    /// Memoized implied equalities by theory and decision level.
    theory_propagation_cache: FxHashMap<(TheoryId, u32), Vec<EqualityProp>>,
    /// Every theory that has asserted a formula built around a given
    /// `TermId`. Used by [`Self::identify_shared_terms`] to detect terms
    /// genuinely shared across two or more theories.
    formula_theories: FxHashMap<TermId, FxHashSet<TheoryId>>,
    /// Equality propagation history for proof certificates.
    propagated_equalities_log: Vec<EqualityProp>,
    /// Last generated theory-combination certificate.
    #[cfg(feature = "std")]
    last_certificate: Option<NelsonOppenCertificate>,
    /// Current decision level
    current_level: usize,
}

impl TheoryCoordinator {
    /// Create a new theory coordinator
    pub fn new(config: CoordinatorConfig) -> Self {
        Self {
            config,
            stats: CoordinatorStats::default(),
            theories: FxHashMap::default(),
            shared_terms: FxHashMap::default(),
            pending_equalities: VecDeque::new(),
            theory_propagation_cache: FxHashMap::default(),
            formula_theories: FxHashMap::default(),
            propagated_equalities_log: Vec::new(),
            #[cfg(feature = "std")]
            last_certificate: None,
            current_level: 0,
        }
    }

    /// Register a theory solver
    pub fn register_theory(&mut self, theory: Box<dyn TheorySolver>) {
        let theory_id = theory.theory_id();
        self.theories.insert(theory_id, theory);
    }

    /// Assert a formula to the appropriate theory
    pub fn assert_formula(&mut self, formula: TermId, theory: TheoryId) -> Result<(), String> {
        if let Some(solver) = self.theories.get_mut(&theory) {
            solver.assert_formula(formula)?;
            self.clear_from_level(self.current_level as u32);

            // Record that `theory` now uses `formula`, so `identify_shared_terms`
            // can tell whether it is also used by any other registered theory.
            self.formula_theories
                .entry(formula)
                .or_default()
                .insert(theory);

            // Identify shared terms
            self.identify_shared_terms(formula)?;
        } else {
            return Err(format!("Theory {:?} not registered", theory));
        }

        Ok(())
    }

    /// Check satisfiability with theory combination
    pub fn check_sat(&mut self) -> Result<SatResult, String> {
        #[cfg(feature = "profiling")]
        let _timer = ScopedTimer::new(ProfilingCategory::TheoryCheck);
        self.stats.check_sat_calls += 1;

        // Phase 1: Check individual theories
        for solver in self.theories.values_mut() {
            let result = solver.check_sat()?;

            match result {
                SatResult::Unsat => {
                    self.stats.theory_conflicts += 1;
                    self.maybe_record_certificate_from_log();
                    return Ok(SatResult::Unsat);
                }
                SatResult::Unknown => {
                    return Ok(SatResult::Unknown);
                }
                SatResult::Sat => {
                    // Continue to next theory
                }
            }
        }

        // Phase 2: Theory combination via equality sharing
        if self.config.eager_combination {
            self.eager_theory_combination()
        } else {
            self.lazy_theory_combination()
        }
    }

    /// Eager theory combination: propagate all equalities immediately
    fn eager_theory_combination(&mut self) -> Result<SatResult, String> {
        let mut iteration = 0;

        loop {
            self.stats.theory_combination_rounds += 1;
            iteration += 1;

            if iteration > self.config.max_combination_rounds {
                return Ok(SatResult::Unknown);
            }

            // Collect implied equalities from all theories
            let mut new_equalities = Vec::new();

            for theory_id in self.theories.keys().copied().collect::<Vec<_>>() {
                let equalities = self.cached_theory_propagation(theory_id)?;

                for eq in equalities {
                    // Only propagate equalities between shared terms
                    if self.is_shared_term(eq.lhs) || self.is_shared_term(eq.rhs) {
                        new_equalities.push(eq);
                    }
                }
            }

            // No new equalities: fixed point reached
            if new_equalities.is_empty() {
                return Ok(SatResult::Sat);
            }

            // Propagate equalities to all theories
            for eq in new_equalities {
                self.propagate_equality(eq)?;
            }

            // Re-check theories for conflicts
            for solver in self.theories.values_mut() {
                match solver.check_sat()? {
                    SatResult::Unsat => {
                        self.stats.theory_conflicts += 1;
                        self.maybe_record_certificate_from_log();
                        return Ok(SatResult::Unsat);
                    }
                    SatResult::Unknown => {
                        return Ok(SatResult::Unknown);
                    }
                    SatResult::Sat => {}
                }
            }
        }
    }

    /// Lazy theory combination: propagate equalities on-demand
    fn lazy_theory_combination(&mut self) -> Result<SatResult, String> {
        // Process pending equalities
        while let Some(eq) = self.pending_equalities.pop_front() {
            self.propagate_equality(eq)?;

            // Check for conflicts after each propagation
            for solver in self.theories.values_mut() {
                match solver.check_sat()? {
                    SatResult::Unsat => {
                        self.stats.theory_conflicts += 1;
                        self.maybe_record_certificate_from_log();
                        return Ok(SatResult::Unsat);
                    }
                    SatResult::Unknown => {
                        return Ok(SatResult::Unknown);
                    }
                    SatResult::Sat => {}
                }
            }
        }

        Ok(SatResult::Sat)
    }

    /// Propagate an equality to all relevant theories
    fn propagate_equality(&mut self, eq: EqualityProp) -> Result<(), String> {
        self.stats.equalities_propagated += 1;
        let logged_eq = eq.clone();

        // Update equivalence classes
        self.merge_equivalence_classes(eq.lhs, eq.rhs)?;

        // Notify all theories that use these terms
        let theories_to_notify = self.get_theories_for_terms(eq.lhs, eq.rhs);

        for theory_id in theories_to_notify {
            if theory_id != eq.source
                && let Some(solver) = self.theories.get_mut(&theory_id)
            {
                solver.notify_equality(eq.lhs, eq.rhs)?;
            }
        }

        self.clear_from_level(self.current_level as u32);
        self.propagated_equalities_log.push(logged_eq);

        Ok(())
    }

    /// Identify shared terms in a formula.
    ///
    /// This module operates on opaque `TermId` handles (a bare `usize`) with
    /// no attached AST, so it cannot literally "traverse the formula" to
    /// find shared sub-terms the way a `TermManager`-backed combination
    /// engine could. What it *can* determine soundly, using only the
    /// bookkeeping this coordinator already owns, is whether `formula`
    /// itself has been asserted under two or more distinct theories -- by
    /// the Nelson-Oppen definition, that makes it an interface/shared term
    /// subject to equality propagation. Callers that need finer-grained
    /// sub-term sharing register it explicitly via [`Self::add_shared_term`].
    fn identify_shared_terms(&mut self, formula: TermId) -> Result<(), String> {
        if let Some(theories) = self.formula_theories.get(&formula)
            && theories.len() > 1
        {
            let owners: Vec<TheoryId> = theories.iter().copied().collect();
            for theory in owners {
                self.add_shared_term(formula, theory);
            }
        }

        self.stats.shared_terms_count = self.shared_terms.len();
        Ok(())
    }

    /// Check if a term is shared between theories
    fn is_shared_term(&self, term: TermId) -> bool {
        self.shared_terms
            .get(&term)
            .is_some_and(|st| st.theories.len() > 1)
    }

    /// Get theories that use given terms
    fn get_theories_for_terms(&self, lhs: TermId, rhs: TermId) -> FxHashSet<TheoryId> {
        let mut theories = FxHashSet::default();

        if let Some(st) = self.shared_terms.get(&lhs) {
            theories.extend(&st.theories);
        }

        if let Some(st) = self.shared_terms.get(&rhs) {
            theories.extend(&st.theories);
        }

        theories
    }

    /// Merge equivalence classes for two terms
    fn merge_equivalence_classes(&mut self, lhs: TermId, rhs: TermId) -> Result<(), String> {
        // Get representatives
        let lhs_rep = self.find_representative(lhs);
        let rhs_rep = self.find_representative(rhs);

        if lhs_rep == rhs_rep {
            return Ok(());
        }

        // Union: make lhs_rep point to rhs_rep
        if let Some(st) = self.shared_terms.get_mut(&lhs_rep) {
            st.representative = rhs_rep;
        }

        Ok(())
    }

    /// Find equivalence class representative
    fn find_representative(&self, term: TermId) -> TermId {
        if let Some(st) = self.shared_terms.get(&term)
            && st.representative != term
        {
            // Path compression would be applied here
            return self.find_representative(st.representative);
        }
        term
    }

    /// Add a shared term
    pub fn add_shared_term(&mut self, term: TermId, theory: TheoryId) {
        self.shared_terms
            .entry(term)
            .or_insert_with(|| SharedTerm {
                term,
                theories: FxHashSet::default(),
                representative: term,
            })
            .theories
            .insert(theory);

        self.stats.shared_terms_count = self.shared_terms.len();
    }

    /// Enqueue an equality for propagation
    pub fn enqueue_equality(&mut self, lhs: TermId, rhs: TermId, source: TheoryId) {
        self.pending_equalities.push_back(EqualityProp {
            lhs,
            rhs,
            source,
            explanation: vec![],
        });
    }

    /// Backtrack all theories to a level
    pub fn backtrack(&mut self, level: usize) -> Result<(), String> {
        self.current_level = level;

        for solver in self.theories.values_mut() {
            solver.backtrack(level)?;
        }

        // Clear pending equalities
        self.pending_equalities.clear();
        self.clear_above_level(level as u32);
        self.propagated_equalities_log.clear();
        #[cfg(feature = "std")]
        {
            self.last_certificate = None;
        }

        Ok(())
    }

    /// Get combined model from all theories
    pub fn get_model(&self) -> Option<FxHashMap<TermId, TermId>> {
        let mut combined_model = FxHashMap::default();

        for solver in self.theories.values() {
            if let Some(model) = solver.get_model() {
                combined_model.extend(model);
            } else {
                return None;
            }
        }

        Some(combined_model)
    }

    /// Get combined conflict explanation
    pub fn get_conflict(&mut self) -> Option<Vec<TermId>> {
        // Collect conflicts from all theories
        let mut combined_conflict = Vec::new();

        for solver in self.theories.values() {
            if let Some(conflict) = solver.get_conflict() {
                combined_conflict.extend(conflict);
            }
        }

        if combined_conflict.is_empty() {
            None
        } else if self.config.minimize_conflicts {
            Some(self.minimize_conflict(combined_conflict))
        } else {
            combined_conflict.sort();
            combined_conflict.dedup();
            Some(combined_conflict)
        }
    }

    /// Minimize a conflict explanation to a locally-minimal unsatisfiable core.
    ///
    /// Deletion-based minimization: a literal is redundant exactly when the
    /// remaining conflict is *still* theory-inconsistent, so we drop each literal
    /// in turn and re-check the combination; a literal whose removal restores
    /// satisfiability is necessary and kept.  The re-check re-asserts a subset
    /// through [`Self::reassert_only`] and consults the same Nelson-Oppen
    /// [`Self::check_sat`] used for the top-level decision, so the result is a
    /// genuine core rather than a mere deduplication.
    ///
    /// When no registered theory can witness inconsistency (e.g. no theories, or
    /// a conflict none of them re-derives), every removal leaves the subset
    /// satisfiable, so the deduplicated conflict is returned unchanged — a sound,
    /// conservative fallback.  The coordinator's full assertion set is restored
    /// before returning so later queries are unaffected.
    fn minimize_conflict(&mut self, conflict: Vec<TermId>) -> Vec<TermId> {
        let mut core = conflict;
        core.sort();
        core.dedup();

        let mut index = 0;
        while index < core.len() {
            let mut trial = core.clone();
            trial.remove(index);
            match self.subset_is_unsat(&trial) {
                Ok(true) => {
                    // core[index] is not needed to derive the conflict.
                    core = trial;
                    // Keep `index`: the next literal shifted into this slot.
                }
                _ => {
                    // Necessary (or the re-check was inconclusive): keep it.
                    index += 1;
                }
            }
        }

        // Leave the theories holding their full asserted set again.
        let _ = self.restore_all_assertions();

        core
    }

    /// Re-assert exactly the formulas in `keep` and report whether the resulting
    /// combination is unsatisfiable.
    fn subset_is_unsat(&mut self, keep: &[TermId]) -> Result<bool, String> {
        let keep_set: FxHashSet<TermId> = keep.iter().copied().collect();
        self.reassert_only(&keep_set)?;
        Ok(self.check_sat()? == SatResult::Unsat)
    }

    /// Reset every theory to its empty base and re-assert only the formulas in
    /// `keep`, each to the theories that originally used it (per
    /// [`Self::formula_theories`]).  `backtrack(0)` is the theory-solver reset
    /// primitive here: it must return the solver to the state with no user
    /// assertions.
    fn reassert_only(&mut self, keep: &FxHashSet<TermId>) -> Result<(), String> {
        for solver in self.theories.values_mut() {
            solver.backtrack(0)?;
        }
        // Snapshot to avoid borrowing `self.formula_theories` and
        // `self.theories` simultaneously.
        let plan: Vec<(TermId, Vec<TheoryId>)> = self
            .formula_theories
            .iter()
            .filter(|(formula, _)| keep.contains(formula))
            .map(|(&formula, theories)| (formula, theories.iter().copied().collect()))
            .collect();
        for (formula, theories) in plan {
            for theory_id in theories {
                if let Some(solver) = self.theories.get_mut(&theory_id) {
                    solver.assert_formula(formula)?;
                }
            }
        }
        Ok(())
    }

    /// Restore every theory's full asserted set (all tracked formulas).
    fn restore_all_assertions(&mut self) -> Result<(), String> {
        let all: FxHashSet<TermId> = self.formula_theories.keys().copied().collect();
        self.reassert_only(&all)
    }

    /// Get statistics
    pub fn stats(&self) -> &CoordinatorStats {
        &self.stats
    }

    /// Get current decision level
    pub fn current_level(&self) -> usize {
        self.current_level
    }

    /// Get the last generated theory-combination proof certificate.
    #[cfg(feature = "std")]
    pub fn proof_certificate(&self) -> Option<&NelsonOppenCertificate> {
        self.last_certificate.as_ref()
    }

    /// Increment decision level
    pub fn increment_level(&mut self) {
        self.current_level += 1;
    }

    fn maybe_record_certificate_from_log(&mut self) {
        #[cfg(feature = "std")]
        {
            if !self.config.proof_mode {
                return;
            }

            self.last_certificate = self.build_certificate_from_log();
        }
    }

    fn cached_theory_propagation(
        &mut self,
        theory_id: TheoryId,
    ) -> Result<Vec<EqualityProp>, String> {
        let level = self.current_level as u32;
        let key = (theory_id, level);

        if let Some(cached) = self.theory_propagation_cache.get(&key) {
            return Ok(cached.clone());
        }

        let solver = self
            .theories
            .get(&theory_id)
            .ok_or_else(|| format!("Theory {:?} not registered", theory_id))?;

        let propagated: Vec<EqualityProp> = solver
            .get_implied_equalities()
            .into_iter()
            .map(|(lhs, rhs)| EqualityProp {
                lhs,
                rhs,
                source: theory_id,
                explanation: vec![],
            })
            .collect();

        self.theory_propagation_cache
            .insert(key, propagated.clone());

        Ok(propagated)
    }

    fn clear_above_level(&mut self, level: u32) {
        self.theory_propagation_cache
            .retain(|(_, cached_level), _| *cached_level <= level);
    }

    fn clear_from_level(&mut self, level: u32) {
        self.theory_propagation_cache
            .retain(|(_, cached_level), _| *cached_level < level);
    }

    #[cfg(feature = "std")]
    fn build_certificate_from_log(&self) -> Option<NelsonOppenCertificate> {
        let last_eq = self.propagated_equalities_log.last()?;
        let mut certificate =
            NelsonOppenCertificate::new(self.to_proof_theory_id(last_eq.source), ProofNodeId(0));

        for eq in &self.propagated_equalities_log {
            let lhs = Self::to_proof_term_id(eq.lhs)?;
            let rhs = Self::to_proof_term_id(eq.rhs)?;
            certificate.add_step(CombinationStep {
                theory: self.to_proof_theory_id(eq.source),
                propagated_equalities: vec![(lhs, rhs)],
                justification: Vec::new(),
            });
        }

        Some(certificate)
    }

    #[cfg(feature = "std")]
    fn to_proof_term_id(term: TermId) -> Option<ProofTermId> {
        let raw = u32::try_from(term).ok()?;
        Some(ProofTermId::new(raw))
    }

    #[cfg(feature = "std")]
    const fn to_proof_theory_id(&self, theory: TheoryId) -> CombinationTheoryId {
        let raw = match theory {
            TheoryId::Core => 0,
            TheoryId::Arithmetic => 1,
            TheoryId::BitVector => 2,
            TheoryId::Array => 3,
            TheoryId::Datatype => 4,
            TheoryId::String => 5,
            TheoryId::Uninterpreted => 6,
        };
        CombinationTheoryId(raw)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    // Mock theory solver for testing
    struct MockTheory {
        id: TheoryId,
        sat_result: SatResult,
        implied_equalities: Vec<(TermId, TermId)>,
    }

    impl TheorySolver for MockTheory {
        fn theory_id(&self) -> TheoryId {
            self.id
        }

        fn assert_formula(&mut self, _formula: TermId) -> Result<(), String> {
            Ok(())
        }

        fn check_sat(&mut self) -> Result<SatResult, String> {
            Ok(self.sat_result)
        }

        fn get_model(&self) -> Option<FxHashMap<TermId, TermId>> {
            Some(FxHashMap::default())
        }

        fn get_conflict(&self) -> Option<Vec<TermId>> {
            None
        }

        fn backtrack(&mut self, _level: usize) -> Result<(), String> {
            Ok(())
        }

        fn get_implied_equalities(&self) -> Vec<(TermId, TermId)> {
            self.implied_equalities.clone()
        }

        fn notify_equality(&mut self, _lhs: TermId, _rhs: TermId) -> Result<(), String> {
            Ok(())
        }
    }

    #[test]
    fn test_coordinator_creation() {
        let config = CoordinatorConfig::default();
        let coordinator = TheoryCoordinator::new(config);
        assert_eq!(coordinator.stats.check_sat_calls, 0);
    }

    #[test]
    fn test_register_theory() {
        let config = CoordinatorConfig::default();
        let mut coordinator = TheoryCoordinator::new(config);

        let mock_theory = MockTheory {
            id: TheoryId::Arithmetic,
            sat_result: SatResult::Sat,
            implied_equalities: Vec::new(),
        };

        coordinator.register_theory(Box::new(mock_theory));
        assert!(coordinator.theories.contains_key(&TheoryId::Arithmetic));
    }

    #[test]
    fn test_check_sat_single_theory() {
        let config = CoordinatorConfig::default();
        let mut coordinator = TheoryCoordinator::new(config);

        let mock_theory = MockTheory {
            id: TheoryId::Arithmetic,
            sat_result: SatResult::Sat,
            implied_equalities: Vec::new(),
        };

        coordinator.register_theory(Box::new(mock_theory));

        let result = coordinator.check_sat();
        assert!(result.is_ok());
        assert_eq!(
            result.expect("test operation should succeed"),
            SatResult::Sat
        );
        assert_eq!(coordinator.stats.check_sat_calls, 1);
    }

    #[test]
    fn test_shared_term_management() {
        let config = CoordinatorConfig::default();
        let mut coordinator = TheoryCoordinator::new(config);

        coordinator.add_shared_term(1, TheoryId::Arithmetic);
        coordinator.add_shared_term(1, TheoryId::BitVector);

        assert!(coordinator.is_shared_term(1));
        assert_eq!(coordinator.stats.shared_terms_count, 1);
    }

    /// Audit regression: `identify_shared_terms` used to be a pure no-op
    /// (it only re-derived `shared_terms_count` from whatever was already
    /// in `shared_terms`, which nothing ever populated automatically).
    /// Asserting the *same* formula id under two different theories must
    /// now be enough, on its own -- with no manual `add_shared_term` call
    /// -- for the coordinator to recognize it as shared.
    #[test]
    fn test_audit_identify_shared_terms_detects_cross_theory_sharing() {
        let config = CoordinatorConfig::default();
        let mut coordinator = TheoryCoordinator::new(config);

        coordinator.register_theory(Box::new(MockTheory {
            id: TheoryId::Arithmetic,
            sat_result: SatResult::Sat,
            implied_equalities: Vec::new(),
        }));
        coordinator.register_theory(Box::new(MockTheory {
            id: TheoryId::BitVector,
            sat_result: SatResult::Sat,
            implied_equalities: Vec::new(),
        }));

        // Not yet shared: only Arithmetic has ever asserted term `7`.
        coordinator
            .assert_formula(7, TheoryId::Arithmetic)
            .expect("assert should succeed");
        assert!(
            !coordinator.is_shared_term(7),
            "a term asserted under only one theory must not be reported as shared"
        );

        // Now BitVector also asserts the very same term id: it must be
        // recognized as shared automatically, purely from bookkeeping
        // `identify_shared_terms` performs internally.
        coordinator
            .assert_formula(7, TheoryId::BitVector)
            .expect("assert should succeed");
        assert!(
            coordinator.is_shared_term(7),
            "a term asserted under two distinct theories must be detected as shared"
        );
        assert_eq!(coordinator.stats.shared_terms_count, 1);

        // A term asserted under a single theory only must still not be
        // reported as shared (no false positives).
        coordinator
            .assert_formula(9, TheoryId::Arithmetic)
            .expect("assert should succeed");
        assert!(!coordinator.is_shared_term(9));
        assert_eq!(coordinator.stats.shared_terms_count, 1);
    }

    #[test]
    fn test_equivalence_classes() {
        let config = CoordinatorConfig::default();
        let mut coordinator = TheoryCoordinator::new(config);

        coordinator.add_shared_term(1, TheoryId::Arithmetic);
        coordinator.add_shared_term(2, TheoryId::Arithmetic);

        coordinator
            .merge_equivalence_classes(1, 2)
            .expect("test operation should succeed");

        let rep1 = coordinator.find_representative(1);
        let rep2 = coordinator.find_representative(2);
        assert_eq!(rep1, rep2);
    }

    #[test]
    fn test_equality_propagation() {
        let config = CoordinatorConfig::default();
        let mut coordinator = TheoryCoordinator::new(config);

        coordinator.enqueue_equality(1, 2, TheoryId::Arithmetic);
        assert_eq!(coordinator.pending_equalities.len(), 1);
    }

    #[test]
    fn test_backtrack() {
        let config = CoordinatorConfig::default();
        let mut coordinator = TheoryCoordinator::new(config);

        let mock_theory = MockTheory {
            id: TheoryId::Arithmetic,
            sat_result: SatResult::Sat,
            implied_equalities: Vec::new(),
        };

        coordinator.register_theory(Box::new(mock_theory));
        coordinator.increment_level();
        coordinator.increment_level();

        assert_eq!(coordinator.current_level(), 2);

        coordinator
            .backtrack(0)
            .expect("test operation should succeed");
        assert_eq!(coordinator.current_level(), 0);
    }

    #[test]
    fn test_get_model() {
        let config = CoordinatorConfig::default();
        let mut coordinator = TheoryCoordinator::new(config);

        let mock_theory = MockTheory {
            id: TheoryId::Arithmetic,
            sat_result: SatResult::Sat,
            implied_equalities: Vec::new(),
        };

        coordinator.register_theory(Box::new(mock_theory));

        let model = coordinator.get_model();
        assert!(model.is_some());
    }

    #[test]
    fn test_conflict_minimization_dedup_fallback() {
        // With no theory able to witness inconsistency, minimization cannot drop
        // any literal (every removal leaves the subset satisfiable), so the
        // conservative result is exactly the deduplicated conflict.
        let mut coordinator = TheoryCoordinator::new(CoordinatorConfig {
            minimize_conflicts: true,
            ..Default::default()
        });

        let conflict = vec![1, 2, 2, 3, 1, 4];
        let minimized = coordinator.minimize_conflict(conflict);

        assert_eq!(minimized, vec![1, 2, 3, 4]);
    }

    /// Theory whose satisfiability depends on the concrete set of formulas
    /// currently asserted to it: it is UNSAT exactly when every formula in
    /// `required` is present.  `backtrack(0)` clears its assertions, matching the
    /// reset contract the coordinator's re-check relies on.
    struct CoreMockTheory {
        id: TheoryId,
        required: Vec<TermId>,
        asserted: FxHashSet<TermId>,
    }

    impl TheorySolver for CoreMockTheory {
        fn theory_id(&self) -> TheoryId {
            self.id
        }
        fn assert_formula(&mut self, formula: TermId) -> Result<(), String> {
            self.asserted.insert(formula);
            Ok(())
        }
        fn check_sat(&mut self) -> Result<SatResult, String> {
            // A theory with no required core imposes no constraint (always SAT);
            // otherwise it is UNSAT exactly when every required formula is present.
            if !self.required.is_empty() && self.required.iter().all(|f| self.asserted.contains(f))
            {
                Ok(SatResult::Unsat)
            } else {
                Ok(SatResult::Sat)
            }
        }
        fn get_model(&self) -> Option<FxHashMap<TermId, TermId>> {
            Some(FxHashMap::default())
        }
        fn get_conflict(&self) -> Option<Vec<TermId>> {
            None
        }
        fn backtrack(&mut self, level: usize) -> Result<(), String> {
            if level == 0 {
                self.asserted.clear();
            }
            Ok(())
        }
        fn get_implied_equalities(&self) -> Vec<(TermId, TermId)> {
            Vec::new()
        }
        fn notify_equality(&mut self, _lhs: TermId, _rhs: TermId) -> Result<(), String> {
            Ok(())
        }
    }

    #[test]
    fn test_conflict_minimization_extracts_minimal_core() {
        // Three registered theories; the genuine inconsistency needs formulas
        // {1, 2, 3} (routed to Arithmetic), while 4 (BitVector) and 5 (Array)
        // are irrelevant padding also reported in the raw conflict.  Genuine
        // deletion-based re-check must peel off 4 and 5 and keep {1, 2, 3}.
        let mut coordinator = TheoryCoordinator::new(CoordinatorConfig {
            minimize_conflicts: true,
            eager_combination: false,
            ..Default::default()
        });

        coordinator.register_theory(Box::new(CoreMockTheory {
            id: TheoryId::Arithmetic,
            required: vec![1, 2, 3],
            asserted: FxHashSet::default(),
        }));
        coordinator.register_theory(Box::new(CoreMockTheory {
            id: TheoryId::BitVector,
            required: Vec::new(),
            asserted: FxHashSet::default(),
        }));
        coordinator.register_theory(Box::new(CoreMockTheory {
            id: TheoryId::Array,
            required: Vec::new(),
            asserted: FxHashSet::default(),
        }));

        coordinator
            .assert_formula(1, TheoryId::Arithmetic)
            .expect("assert 1");
        coordinator
            .assert_formula(2, TheoryId::Arithmetic)
            .expect("assert 2");
        coordinator
            .assert_formula(3, TheoryId::Arithmetic)
            .expect("assert 3");
        coordinator
            .assert_formula(4, TheoryId::BitVector)
            .expect("assert 4");
        coordinator
            .assert_formula(5, TheoryId::Array)
            .expect("assert 5");

        // The full set is genuinely inconsistent.
        assert_eq!(
            coordinator.check_sat().expect("check"),
            SatResult::Unsat,
            "the full assertion set must be UNSAT"
        );

        let minimized = coordinator.minimize_conflict(vec![1, 2, 3, 4, 5]);
        assert_eq!(
            minimized,
            vec![1, 2, 3],
            "minimization must keep exactly the necessary core {{1,2,3}}"
        );

        // After minimization the full assertion set is restored, so the
        // combination is inconsistent again.
        assert_eq!(
            coordinator.check_sat().expect("re-check"),
            SatResult::Unsat,
            "the full assertion set must remain UNSAT after minimization"
        );
    }

    #[test]
    fn test_theory_propagation_cache_clears_on_backtrack() {
        let mut coordinator = TheoryCoordinator::new(CoordinatorConfig::default());
        coordinator.register_theory(Box::new(MockTheory {
            id: TheoryId::Arithmetic,
            sat_result: SatResult::Sat,
            implied_equalities: vec![(1, 2)],
        }));

        assert_eq!(
            coordinator
                .cached_theory_propagation(TheoryId::Arithmetic)
                .expect("initial cache fill should succeed")
                .len(),
            1
        );
        assert_eq!(coordinator.theory_propagation_cache.len(), 1);

        coordinator.increment_level();
        assert_eq!(
            coordinator
                .cached_theory_propagation(TheoryId::Arithmetic)
                .expect("level-one cache fill should succeed")
                .len(),
            1
        );
        assert_eq!(coordinator.theory_propagation_cache.len(), 2);

        coordinator
            .backtrack(0)
            .expect("backtrack should clear higher-level cache entries");
        assert_eq!(coordinator.theory_propagation_cache.len(), 1);
    }
}
