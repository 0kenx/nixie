//! Advanced Nelson-Oppen Theory Combination.
//!
//! This module extends the basic Nelson-Oppen method with advanced techniques:
//! - Non-convex theory handling via model-based case splitting
//! - Delayed equality sharing for efficiency
//! - Optimization for stably-infinite theories
//! - Partition refinement algorithms
//! - Incremental theory combination
//!
//! ## Non-Convex Theories
//!
//! Non-convex theories (like integer arithmetic) require enumeration of
//! all possible equality arrangements. This module implements:
//! - Model-based case splitting
//! - Conflict-driven learning of equality arrangements
//! - Heuristics to minimize case splits
//!
//! ## Delayed Equality Sharing
//!
//! Rather than eagerly propagating all interface equalities, this module:
//! - Maintains a priority queue of pending equalities
//! - Propagates equalities only when necessary
//! - Uses relevancy tracking to avoid irrelevant propagations
//!
//! ## References
//!
//! - Nelson & Oppen: "Simplification by Cooperating Decision Procedures" (1979)
//! - Tinelli & Harandi: "A New Correctness Proof of the Nelson-Oppen Combination" (1996)
//! - Z3's `smt/theory_opt.cpp`, `smt/theory_combination.cpp`

#![allow(missing_docs)]

#[allow(unused_imports)]
use crate::prelude::*;
use core::cmp::Ordering;

/// Term identifier.
pub type TermId = u32;

/// Theory identifier.
pub type TheoryId = u32;

/// Decision level for backtracking.
pub type DecisionLevel = u32;

/// Equality between two terms.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct Equality {
    /// Left-hand side term.
    pub lhs: TermId,
    /// Right-hand side term.
    pub rhs: TermId,
}

impl Equality {
    /// Create a new equality (normalized).
    pub fn new(lhs: TermId, rhs: TermId) -> Self {
        if lhs <= rhs {
            Self { lhs, rhs }
        } else {
            Self { lhs: rhs, rhs: lhs }
        }
    }

    /// Flip the equality.
    pub fn flip(self) -> Self {
        Self::new(self.rhs, self.lhs)
    }
}

/// Disequality between two terms.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct Disequality {
    /// Left-hand side term.
    pub lhs: TermId,
    /// Right-hand side term.
    pub rhs: TermId,
}

impl Disequality {
    /// Create a new disequality (normalized).
    pub fn new(lhs: TermId, rhs: TermId) -> Self {
        if lhs <= rhs {
            Self { lhs, rhs }
        } else {
            Self { lhs: rhs, rhs: lhs }
        }
    }
}

/// Explanation for an equality.
#[derive(Debug, Clone)]
pub enum EqualityExplanation {
    /// Given as input.
    Given,
    /// Asserted by theory.
    TheoryPropagation(TheoryId, Vec<Equality>),
    /// Transitivity chain.
    Transitivity(Vec<Equality>),
    /// Congruence.
    Congruence {
        /// Function applications.
        lhs_app: TermId,
        rhs_app: TermId,
        /// Argument equalities.
        arg_equalities: Vec<Equality>,
    },
}

/// Priority for equality propagation.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct EqualityPriority {
    /// Priority level (higher = more urgent).
    pub level: u32,
    /// Relevancy score.
    pub relevancy: u32,
    /// Decision level where equality was derived.
    pub decision_level: DecisionLevel,
}

impl Ord for EqualityPriority {
    fn cmp(&self, other: &Self) -> Ordering {
        self.level
            .cmp(&other.level)
            .then_with(|| self.relevancy.cmp(&other.relevancy))
            .then_with(|| other.decision_level.cmp(&self.decision_level))
    }
}

impl PartialOrd for EqualityPriority {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

/// Pending equality with priority.
#[derive(Debug, Clone)]
struct PendingEquality {
    /// The equality.
    equality: Equality,
    /// Priority for propagation.
    priority: EqualityPriority,
    /// Explanation.
    explanation: EqualityExplanation,
    /// Source theory.
    source_theory: TheoryId,
}

impl PartialEq for PendingEquality {
    fn eq(&self, other: &Self) -> bool {
        self.priority == other.priority
    }
}

impl Eq for PendingEquality {}

impl Ord for PendingEquality {
    fn cmp(&self, other: &Self) -> Ordering {
        self.priority.cmp(&other.priority)
    }
}

impl PartialOrd for PendingEquality {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

/// Partition of terms for equality arrangement enumeration.
#[derive(Debug, Clone)]
pub struct TermPartition {
    /// Equivalence classes.
    classes: Vec<FxHashSet<TermId>>,
    /// Term to class index.
    term_to_class: FxHashMap<TermId, usize>,
}

impl TermPartition {
    /// Create a new partition with singleton classes.
    pub fn new(terms: &[TermId]) -> Self {
        let classes: Vec<_> = terms
            .iter()
            .map(|&t| {
                let mut set = FxHashSet::default();
                set.insert(t);
                set
            })
            .collect();

        let term_to_class: FxHashMap<_, _> =
            terms.iter().enumerate().map(|(i, &t)| (t, i)).collect();

        Self {
            classes,
            term_to_class,
        }
    }

    /// Merge two classes.
    pub fn merge(&mut self, t1: TermId, t2: TermId) -> Result<(), String> {
        let c1 = *self.term_to_class.get(&t1).ok_or("Term not in partition")?;
        let c2 = *self.term_to_class.get(&t2).ok_or("Term not in partition")?;

        if c1 == c2 {
            return Ok(());
        }

        // Merge smaller into larger
        let (src, dst) = if self.classes[c1].len() < self.classes[c2].len() {
            (c1, c2)
        } else {
            (c2, c1)
        };

        let src_terms: Vec<_> = self.classes[src].iter().copied().collect();
        for term in src_terms {
            self.classes[dst].insert(term);
            self.term_to_class.insert(term, dst);
        }
        self.classes[src].clear();

        Ok(())
    }

    /// Get all non-trivial equalities implied by partition.
    pub fn get_equalities(&self) -> Vec<Equality> {
        let mut equalities = Vec::new();
        for class in &self.classes {
            if class.len() > 1 {
                let terms: Vec<_> = class.iter().copied().collect();
                for i in 0..terms.len() {
                    for j in (i + 1)..terms.len() {
                        equalities.push(Equality::new(terms[i], terms[j]));
                    }
                }
            }
        }
        equalities
    }

    /// Get number of non-empty classes.
    pub fn num_classes(&self) -> usize {
        self.classes.iter().filter(|c| !c.is_empty()).count()
    }

    /// Check if two terms are in the same class.
    pub fn are_equal(&self, t1: TermId, t2: TermId) -> bool {
        if let (Some(&c1), Some(&c2)) = (self.term_to_class.get(&t1), self.term_to_class.get(&t2)) {
            c1 == c2
        } else {
            false
        }
    }
}

/// Theory properties for combination.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct TheoryProperties {
    /// Is the theory convex?
    ///
    /// Convex theories propagate all implied equalities.
    /// Non-convex theories require case splitting.
    pub is_convex: bool,

    /// Is the theory stably infinite?
    ///
    /// Stably infinite theories have infinite models for satisfiable formulas.
    pub is_stably_infinite: bool,

    /// Does the theory support incremental solving?
    pub is_incremental: bool,

    /// Does the theory produce explanations?
    pub has_explanations: bool,

    /// Priority for this theory (higher = more important).
    pub priority: u32,
}

impl Default for TheoryProperties {
    fn default() -> Self {
        Self {
            is_convex: true,
            is_stably_infinite: true,
            is_incremental: true,
            has_explanations: true,
            priority: 100,
        }
    }
}

/// Configuration for advanced Nelson-Oppen.
#[derive(Debug, Clone)]
pub struct AdvancedNelsonOppenConfig {
    /// Enable delayed equality sharing.
    pub delayed_sharing: bool,

    /// Enable model-based theory combination for non-convex theories.
    pub model_based_combination: bool,

    /// Maximum number of case splits for non-convex theories.
    pub max_case_splits: u32,

    /// Enable conflict-driven learning of equality arrangements.
    pub conflict_driven_learning: bool,

    /// Enable relevancy tracking.
    pub relevancy_tracking: bool,

    /// Maximum iterations.
    pub max_iterations: u32,

    /// Propagation batch size.
    pub propagation_batch_size: usize,

    /// Enable incremental mode.
    pub incremental_mode: bool,
}

impl Default for AdvancedNelsonOppenConfig {
    fn default() -> Self {
        Self {
            delayed_sharing: true,
            model_based_combination: true,
            max_case_splits: 100,
            conflict_driven_learning: true,
            relevancy_tracking: true,
            max_iterations: 10000,
            propagation_batch_size: 100,
            incremental_mode: true,
        }
    }
}

/// Statistics for advanced Nelson-Oppen.
#[derive(Debug, Clone, Default)]
pub struct AdvancedNelsonOppenStats {
    /// Total iterations.
    pub iterations: u64,
    /// Equalities propagated.
    pub equalities_propagated: u64,
    /// Delayed equalities.
    pub delayed_equalities: u64,
    /// Case splits performed.
    pub case_splits: u64,
    /// Conflicts found.
    pub conflicts: u64,
    /// Theory calls.
    pub theory_calls: u64,
    /// Backtracking operations.
    pub backtracks: u64,
    /// Learned equality arrangements.
    pub learned_arrangements: u64,
}

/// Result of theory combination.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum CombinationResult {
    /// Satisfiable.
    Sat,
    /// Unsatisfiable with conflict clause.
    Unsat(Vec<Equality>),
    /// Unknown.
    Unknown,
    /// Resource limit exceeded.
    ResourceExceeded,
}

/// Conflict clause from theory combination.
#[derive(Debug, Clone)]
pub struct TheoryConflict {
    /// Theory that detected conflict.
    pub theory: TheoryId,
    /// Conflicting equalities.
    pub equalities: Vec<Equality>,
    /// Explanation.
    pub explanation: Vec<EqualityExplanation>,
}

/// Interface for theory solvers in combination.
pub trait TheorySolver {
    /// Get theory identifier.
    fn theory_id(&self) -> TheoryId;

    /// Get theory properties.
    fn properties(&self) -> TheoryProperties;

    /// Assert equality.
    fn assert_equality(&mut self, eq: Equality, level: DecisionLevel) -> Result<(), String>;

    /// Assert disequality.
    fn assert_disequality(
        &mut self,
        diseq: Disequality,
        level: DecisionLevel,
    ) -> Result<(), String>;

    /// Check satisfiability.
    fn check_satisfiability(&mut self) -> Result<CombinationResult, String>;

    /// Get implied equalities.
    fn get_implied_equalities(&self) -> Vec<(Equality, EqualityExplanation)>;

    /// Backtrack to decision level.
    fn backtrack(&mut self, level: DecisionLevel) -> Result<(), String>;

    /// Get current decision level.
    fn decision_level(&self) -> DecisionLevel;

    /// Reset theory state.
    fn reset(&mut self);
}

/// Advanced Nelson-Oppen combination engine.
pub struct AdvancedNelsonOppen {
    /// Configuration.
    config: AdvancedNelsonOppenConfig,

    /// Statistics.
    stats: AdvancedNelsonOppenStats,

    /// Theory properties.
    theory_properties: FxHashMap<TheoryId, TheoryProperties>,

    /// Shared terms.
    shared_terms: FxHashSet<TermId>,

    /// Asserted equalities at each decision level.
    asserted_equalities: FxHashMap<DecisionLevel, Vec<Equality>>,

    /// Pending equalities priority queue.
    pending_equalities: BinaryHeap<PendingEquality>,

    /// Propagated equalities.
    propagated_equalities: FxHashSet<Equality>,

    /// Current decision level.
    decision_level: DecisionLevel,

    /// Union-find for equality classes.
    union_find: UnionFindWithExplanation,

    /// Learned equality arrangements (conflict clauses).
    learned_arrangements: Vec<Vec<Equality>>,

    /// Relevancy scores for terms.
    relevancy_scores: FxHashMap<TermId, u32>,

    /// Case split stack for non-convex theories.
    case_split_stack: Vec<CaseSplit>,

    /// Conflict clauses.
    conflicts: Vec<TheoryConflict>,
}

/// Union-Find with explanation tracking.
#[derive(Debug, Clone)]
pub struct UnionFindWithExplanation {
    /// Parent pointers.
    pub parent: FxHashMap<TermId, TermId>,
    /// Rank for union-by-rank.
    pub rank: FxHashMap<TermId, usize>,
    /// Explanations for equalities.
    pub explanations: FxHashMap<Equality, EqualityExplanation>,
    /// Decision level where equality was asserted.
    pub decision_levels: FxHashMap<Equality, DecisionLevel>,
}

impl UnionFindWithExplanation {
    /// Create new union-find.
    fn new() -> Self {
        Self {
            parent: FxHashMap::default(),
            rank: FxHashMap::default(),
            explanations: FxHashMap::default(),
            decision_levels: FxHashMap::default(),
        }
    }

    /// Find representative with path compression.
    fn find(&mut self, term: TermId) -> TermId {
        if let Some(&parent) = self.parent.get(&term)
            && parent != term
        {
            let root = self.find(parent);
            self.parent.insert(term, root);
            return root;
        }
        term
    }

    /// Union two terms.
    fn union(
        &mut self,
        lhs: TermId,
        rhs: TermId,
        explanation: EqualityExplanation,
        level: DecisionLevel,
    ) -> bool {
        let lhs_root = self.find(lhs);
        let rhs_root = self.find(rhs);

        if lhs_root == rhs_root {
            return false;
        }

        let lhs_rank = self.rank.get(&lhs_root).copied().unwrap_or(0);
        let rhs_rank = self.rank.get(&rhs_root).copied().unwrap_or(0);

        let (child, parent) = if lhs_rank < rhs_rank {
            (lhs_root, rhs_root)
        } else if lhs_rank > rhs_rank {
            (rhs_root, lhs_root)
        } else {
            self.rank.insert(rhs_root, rhs_rank + 1);
            (lhs_root, rhs_root)
        };

        self.parent.insert(child, parent);

        let eq = Equality::new(lhs, rhs);
        self.explanations.insert(eq, explanation);
        self.decision_levels.insert(eq, level);

        true
    }

    /// Check if two terms are equal.
    fn are_equal(&mut self, lhs: TermId, rhs: TermId) -> bool {
        self.find(lhs) == self.find(rhs)
    }

    /// Get explanation for equality.
    #[allow(dead_code)]
    fn get_explanation(&self, eq: &Equality) -> Option<&EqualityExplanation> {
        self.explanations.get(eq)
    }

    /// Get decision level for equality.
    #[allow(dead_code)]
    fn get_decision_level(&self, eq: &Equality) -> Option<DecisionLevel> {
        self.decision_levels.get(eq).copied()
    }

    /// Backtrack to decision level.
    fn backtrack(&mut self, level: DecisionLevel) {
        // Remove all equalities above this level
        let to_remove: Vec<_> = self
            .decision_levels
            .iter()
            .filter(|(_, l)| **l > level)
            .map(|(eq, _)| *eq)
            .collect();

        for eq in to_remove {
            self.explanations.remove(&eq);
            self.decision_levels.remove(&eq);
        }

        // Rebuild union-find from remaining equalities
        let remaining: Vec<_> = self.explanations.keys().copied().collect();
        self.parent.clear();
        self.rank.clear();

        for eq in remaining {
            if let Some(explanation) = self.explanations.get(&eq).cloned()
                && let Some(&level) = self.decision_levels.get(&eq)
            {
                self.union(eq.lhs, eq.rhs, explanation, level);
            }
        }
    }

    /// Clear all state.
    fn clear(&mut self) {
        self.parent.clear();
        self.rank.clear();
        self.explanations.clear();
        self.decision_levels.clear();
    }
}

/// Case split for non-convex theory combination.
#[derive(Debug, Clone)]
pub struct CaseSplit {
    /// Decision level where split was made.
    pub level: DecisionLevel,
    /// Terms being partitioned.
    pub terms: Vec<TermId>,
    /// Current partition.
    pub partition: TermPartition,
    /// Arrangements tried so far.
    pub tried_arrangements: Vec<Vec<Equality>>,
}

impl AdvancedNelsonOppen {
    /// Create new advanced Nelson-Oppen engine.
    pub fn new() -> Self {
        Self::with_config(AdvancedNelsonOppenConfig::default())
    }

    /// Create with configuration.
    pub fn with_config(config: AdvancedNelsonOppenConfig) -> Self {
        Self {
            config,
            stats: AdvancedNelsonOppenStats::default(),
            theory_properties: FxHashMap::default(),
            shared_terms: FxHashSet::default(),
            asserted_equalities: FxHashMap::default(),
            pending_equalities: BinaryHeap::new(),
            propagated_equalities: FxHashSet::default(),
            decision_level: 0,
            union_find: UnionFindWithExplanation::new(),
            learned_arrangements: Vec::new(),
            relevancy_scores: FxHashMap::default(),
            case_split_stack: Vec::new(),
            conflicts: Vec::new(),
        }
    }

    /// Register a theory with properties.
    pub fn register_theory(&mut self, theory_id: TheoryId, properties: TheoryProperties) {
        self.theory_properties.insert(theory_id, properties);
    }

    /// Register a shared term.
    pub fn add_shared_term(&mut self, term: TermId) {
        self.shared_terms.insert(term);
    }

    /// Get statistics.
    pub fn stats(&self) -> &AdvancedNelsonOppenStats {
        &self.stats
    }

    /// Get current decision level.
    pub fn current_decision_level(&self) -> DecisionLevel {
        self.decision_level
    }

    /// Increment decision level.
    pub fn push_decision_level(&mut self) {
        self.decision_level += 1;
    }

    /// Backtrack to decision level.
    pub fn backtrack(&mut self, level: DecisionLevel) -> Result<(), String> {
        if level > self.decision_level {
            return Err("Cannot backtrack to future level".to_string());
        }

        // Remove asserted equalities above this level
        let levels_to_remove: Vec<_> = self
            .asserted_equalities
            .keys()
            .filter(|&&l| l > level)
            .copied()
            .collect();

        for l in levels_to_remove {
            self.asserted_equalities.remove(&l);
        }

        // Backtrack union-find
        self.union_find.backtrack(level);

        // Remove pending equalities from higher levels
        let pending: Vec<_> = self.pending_equalities.drain().collect();
        for p in pending {
            if p.priority.decision_level <= level {
                self.pending_equalities.push(p);
            }
        }

        // Pop case splits above this level
        while let Some(split) = self.case_split_stack.last() {
            if split.level > level {
                self.case_split_stack.pop();
            } else {
                break;
            }
        }

        self.decision_level = level;
        self.stats.backtracks += 1;

        Ok(())
    }

    /// Assert an equality at current decision level.
    pub fn assert_equality(
        &mut self,
        eq: Equality,
        explanation: EqualityExplanation,
    ) -> Result<(), String> {
        if self.union_find.are_equal(eq.lhs, eq.rhs) {
            return Ok(());
        }

        // Check for conflicts with known disequalities
        // (This would be implemented with disequality tracking)

        self.union_find
            .union(eq.lhs, eq.rhs, explanation, self.decision_level);

        self.asserted_equalities
            .entry(self.decision_level)
            .or_default()
            .push(eq);

        Ok(())
    }

    /// Add a pending equality for propagation.
    pub fn add_pending_equality(
        &mut self,
        equality: Equality,
        source_theory: TheoryId,
        explanation: EqualityExplanation,
        priority_level: u32,
    ) {
        if self.propagated_equalities.contains(&equality) {
            return;
        }

        let relevancy = self.compute_relevancy(&equality);

        let pending = PendingEquality {
            equality,
            priority: EqualityPriority {
                level: priority_level,
                relevancy,
                decision_level: self.decision_level,
            },
            explanation,
            source_theory,
        };

        self.pending_equalities.push(pending);
        self.stats.delayed_equalities += 1;
    }

    /// Propagate pending equalities.
    pub fn propagate_equalities(
        &mut self,
        theories: &mut [&mut dyn TheorySolver],
    ) -> Result<CombinationResult, String> {
        let mut count = 0;

        while let Some(pending) = self.pending_equalities.pop() {
            if self.propagated_equalities.contains(&pending.equality) {
                continue;
            }

            // Assert equality to union-find
            self.assert_equality(pending.equality, pending.explanation.clone())?;

            // Propagate to all relevant theories
            for theory in theories.iter_mut() {
                if theory.theory_id() != pending.source_theory {
                    theory.assert_equality(pending.equality, self.decision_level)?;
                    self.stats.theory_calls += 1;
                }
            }

            self.propagated_equalities.insert(pending.equality);
            self.stats.equalities_propagated += 1;
            count += 1;

            if count >= self.config.propagation_batch_size {
                break;
            }
        }

        Ok(CombinationResult::Sat)
    }

    /// Combine theories using advanced Nelson-Oppen.
    pub fn combine(
        &mut self,
        theories: &mut [&mut dyn TheorySolver],
    ) -> Result<CombinationResult, String> {
        for _iteration in 0..self.config.max_iterations {
            self.stats.iterations += 1;

            // Propagate pending equalities
            let prop_result = self.propagate_equalities(theories)?;
            if let CombinationResult::Unsat(conflict) = prop_result {
                self.stats.conflicts += 1;
                return Ok(CombinationResult::Unsat(conflict));
            }

            let mut changed = false;
            let mut non_convex_theory_id = None;

            // Check each theory
            for theory in theories.iter_mut() {
                self.stats.theory_calls += 1;
                let result = theory.check_satisfiability()?;

                match result {
                    CombinationResult::Unsat(conflict) => {
                        self.stats.conflicts += 1;

                        // Handle conflict: learn clause or backtrack
                        if self.config.conflict_driven_learning {
                            self.learn_conflict_clause(&conflict);
                        }

                        return Ok(CombinationResult::Unsat(conflict));
                    }
                    CombinationResult::Sat => {
                        // Get theory properties
                        let properties = self
                            .theory_properties
                            .get(&theory.theory_id())
                            .copied()
                            .unwrap_or_default();

                        // Collect implied equalities from theory
                        let implied = theory.get_implied_equalities();

                        for (eq, explanation) in implied {
                            if self.config.delayed_sharing {
                                self.add_pending_equality(
                                    eq,
                                    theory.theory_id(),
                                    explanation,
                                    properties.priority,
                                );
                            } else {
                                // Eager propagation
                                self.assert_equality(eq, explanation)?;
                                changed = true;
                            }
                        }

                        // Handle non-convex theories
                        if !properties.is_convex
                            && self.config.model_based_combination
                            && self.needs_case_split(theory.theory_id())
                        {
                            non_convex_theory_id = Some(theory.theory_id());
                            break;
                        }
                    }
                    CombinationResult::Unknown => {}
                    CombinationResult::ResourceExceeded => {
                        return Ok(CombinationResult::ResourceExceeded);
                    }
                }
            }

            // Handle non-convex theory if needed (after loop to avoid borrow conflict)
            if let Some(theory_id) = non_convex_theory_id {
                return self.handle_non_convex_theory(theories, theory_id);
            }

            // Check termination
            if !changed && self.pending_equalities.is_empty() {
                return Ok(CombinationResult::Sat);
            }
        }

        Ok(CombinationResult::Unknown)
    }

    /// Largest number of shared terms for which a full arrangement enumeration
    /// (`Bell(n)` case splits) is attempted.  `Bell(8) = 4140`; beyond that the
    /// enumeration is answered `Unknown` rather than risking a combinatorial
    /// blow-up – never a fabricated `Sat`.
    const MAX_ARRANGEMENT_TERMS: usize = 8;

    /// Handle a non-convex theory by model-based case splitting over the
    /// equality arrangements of the shared terms.
    ///
    /// A non-convex theory need not propagate a single implied equality even
    /// when the conjunction of the shared-term (dis)equalities it *does* admit
    /// is what makes the combination (un)satisfiable.  Nelson-Oppen resolves
    /// this by guessing a full arrangement (partition) of the shared terms:
    /// the combined problem is satisfiable iff **some** arrangement is
    /// consistent with every theory.  We therefore enumerate the arrangements,
    /// assert each (equalities inside a class, disequalities across classes) to
    /// all theories under a fresh decision level, and:
    ///
    ///   * return `Sat` as soon as an arrangement satisfies every theory;
    ///   * return `Unsat` if **every** arrangement is refuted by some theory;
    ///   * return `Unknown` if the arrangement space is too large to enumerate
    ///     or the case-split budget is exhausted (never a guessed `Sat`).
    fn handle_non_convex_theory(
        &mut self,
        theories: &mut [&mut dyn TheorySolver],
        _theory_id: TheoryId,
    ) -> Result<CombinationResult, String> {
        if self.stats.case_splits >= self.config.max_case_splits as u64 {
            return Ok(CombinationResult::Unknown);
        }

        let shared: Vec<TermId> = self.shared_terms.iter().copied().collect();
        if shared.len() < 2 {
            // A single shared term admits only the trivial arrangement, which
            // adds no constraint: nothing to split on.
            return Ok(CombinationResult::Sat);
        }
        if shared.len() > Self::MAX_ARRANGEMENT_TERMS {
            // Too many arrangements to enumerate soundly: stay honest.
            return Ok(CombinationResult::Unknown);
        }

        let arrangements = self.generate_arrangements(&shared);
        let mut last_conflict: Vec<Equality> = Vec::new();

        for partition in arrangements {
            if self.stats.case_splits >= self.config.max_case_splits as u64 {
                return Ok(CombinationResult::Unknown);
            }
            self.stats.case_splits += 1;

            let base_level = self.decision_level;
            self.push_decision_level();
            let level = self.decision_level;

            let equalities = partition.get_equalities();
            let disequalities = Self::cross_class_disequalities(&partition, &shared);

            // Assert the arrangement to every theory.
            let mut arrangement_ok = true;
            'assert: for theory in theories.iter_mut() {
                for eq in &equalities {
                    if theory.assert_equality(*eq, level).is_err() {
                        arrangement_ok = false;
                        break 'assert;
                    }
                }
                for diseq in &disequalities {
                    if theory.assert_disequality(*diseq, level).is_err() {
                        arrangement_ok = false;
                        break 'assert;
                    }
                }
            }

            // Check every theory under this arrangement.
            let mut resource_exceeded = false;
            if arrangement_ok {
                for theory in theories.iter_mut() {
                    match theory.check_satisfiability()? {
                        CombinationResult::Sat => {}
                        CombinationResult::Unsat(conflict) => {
                            last_conflict = conflict;
                            arrangement_ok = false;
                            break;
                        }
                        CombinationResult::Unknown => {
                            arrangement_ok = false;
                            break;
                        }
                        CombinationResult::ResourceExceeded => {
                            resource_exceeded = true;
                            arrangement_ok = false;
                            break;
                        }
                    }
                }
            }

            // Roll the arrangement back before trying the next one.
            for theory in theories.iter_mut() {
                theory.backtrack(base_level)?;
            }
            self.backtrack(base_level)?;

            if resource_exceeded {
                return Ok(CombinationResult::ResourceExceeded);
            }
            if arrangement_ok {
                // A consistent arrangement witnesses satisfiability.
                return Ok(CombinationResult::Sat);
            }
        }

        // No arrangement satisfied every theory.
        Ok(CombinationResult::Unsat(last_conflict))
    }

    /// The disequalities implied by a partition: one for every pair of shared
    /// terms that fall in different classes.
    fn cross_class_disequalities(partition: &TermPartition, shared: &[TermId]) -> Vec<Disequality> {
        let mut diseqs = Vec::new();
        for i in 0..shared.len() {
            for j in (i + 1)..shared.len() {
                if !partition.are_equal(shared[i], shared[j]) {
                    diseqs.push(Disequality::new(shared[i], shared[j]));
                }
            }
        }
        diseqs
    }

    /// Whether a case split over shared-term arrangements is warranted for a
    /// non-convex theory: only when there are at least two shared terms (so
    /// distinct arrangements exist) and the theory is actually non-convex.
    fn needs_case_split(&self, theory_id: TheoryId) -> bool {
        let is_non_convex = self
            .theory_properties
            .get(&theory_id)
            .is_some_and(|properties| !properties.is_convex);
        is_non_convex && self.shared_terms.len() >= 2
    }

    /// Learn a conflict clause from theory conflict.
    fn learn_conflict_clause(&mut self, conflict: &[Equality]) {
        self.learned_arrangements.push(conflict.to_vec());
        self.stats.learned_arrangements += 1;
    }

    /// Compute relevancy score for an equality.
    fn compute_relevancy(&self, eq: &Equality) -> u32 {
        if !self.config.relevancy_tracking {
            return 100;
        }

        let lhs_relevancy = self.relevancy_scores.get(&eq.lhs).copied().unwrap_or(0);
        let rhs_relevancy = self.relevancy_scores.get(&eq.rhs).copied().unwrap_or(0);

        lhs_relevancy.max(rhs_relevancy)
    }

    /// Update relevancy score for a term.
    pub fn update_relevancy(&mut self, term: TermId, score: u32) {
        self.relevancy_scores.insert(term, score);
    }

    /// Generate every equality arrangement of `terms`, i.e. every set partition
    /// (there are `Bell(|terms|)` of them).  Each returned [`TermPartition`]
    /// groups the terms that the arrangement forces equal; terms in different
    /// classes are implicitly distinct.
    ///
    /// Enumeration uses restricted growth strings (Knuth, TAOCP 7.2.1.5): the
    /// canonical bijection between length-`n` RGS and partitions of an `n`-set,
    /// so no partition is produced twice and none is missed.
    pub fn generate_arrangements(&self, terms: &[TermId]) -> Vec<TermPartition> {
        if terms.is_empty() {
            return vec![TermPartition::new(&[])];
        }
        let n = terms.len();
        let mut rgs = vec![0usize; n];
        let mut arrangements = Vec::new();
        loop {
            // Materialise the partition for the current RGS: equal RGS values
            // share a class.
            let mut partition = TermPartition::new(terms);
            let mut first_index_of_block: Vec<Option<usize>> = Vec::new();
            for (i, &block) in rgs.iter().enumerate() {
                if block >= first_index_of_block.len() {
                    first_index_of_block.resize(block + 1, None);
                }
                match first_index_of_block[block] {
                    None => first_index_of_block[block] = Some(i),
                    // Both operands were placed in `partition` by `new(terms)`,
                    // so `merge` cannot fail here; ignore the unreachable error.
                    Some(j) => {
                        let _ = partition.merge(terms[j], terms[i]);
                    }
                }
            }
            arrangements.push(partition);

            if !Self::next_restricted_growth_string(&mut rgs) {
                break;
            }
        }
        arrangements
    }

    /// Advance `rgs` in place to the next restricted growth string, returning
    /// `false` once the final one (all classes distinct) has been passed.
    ///
    /// A valid RGS has `a[0] = 0` and `a[i] <= 1 + max(a[0..i])`; the successor
    /// increments the rightmost position that can still grow and zeroes the
    /// suffix.
    fn next_restricted_growth_string(rgs: &mut [usize]) -> bool {
        let n = rgs.len();
        let mut i = n;
        while i > 1 {
            i -= 1;
            let max_before = rgs[..i].iter().copied().max().unwrap_or(0);
            if rgs[i] <= max_before {
                rgs[i] += 1;
                for slot in rgs.iter_mut().skip(i + 1) {
                    *slot = 0;
                }
                return true;
            }
        }
        false
    }

    /// Refine partition based on learned constraints.
    pub fn refine_partition(
        &self,
        partition: &mut TermPartition,
        constraints: &[Equality],
    ) -> Result<(), String> {
        for eq in constraints {
            partition.merge(eq.lhs, eq.rhs)?;
        }
        Ok(())
    }

    /// Clear all state.
    pub fn clear(&mut self) {
        self.shared_terms.clear();
        self.asserted_equalities.clear();
        self.pending_equalities.clear();
        self.propagated_equalities.clear();
        self.decision_level = 0;
        self.union_find.clear();
        self.case_split_stack.clear();
        self.conflicts.clear();
    }

    /// Reset statistics.
    pub fn reset_stats(&mut self) {
        self.stats = AdvancedNelsonOppenStats::default();
    }
}

impl Default for AdvancedNelsonOppen {
    fn default() -> Self {
        Self::new()
    }
}

/// Partition refinement algorithm.
pub struct PartitionRefinement {
    /// Current partition.
    partition: TermPartition,
    /// Refinement history.
    history: Vec<TermPartition>,
}

impl PartitionRefinement {
    /// Create new refinement algorithm.
    pub fn new(terms: &[TermId]) -> Self {
        let partition = TermPartition::new(terms);
        Self {
            partition,
            history: Vec::new(),
        }
    }

    /// Refine partition with equality.
    pub fn refine_with_equality(&mut self, eq: Equality) -> Result<(), String> {
        self.history.push(self.partition.clone());
        self.partition.merge(eq.lhs, eq.rhs)
    }

    /// Get current partition.
    pub fn current_partition(&self) -> &TermPartition {
        &self.partition
    }

    /// Backtrack one refinement.
    pub fn backtrack(&mut self) -> Result<(), String> {
        self.partition = self.history.pop().ok_or("No refinement to backtrack")?;
        Ok(())
    }
}

/// Model-based theory combination helper.
pub struct ModelBasedCombination {
    /// Current model assignments.
    model: FxHashMap<TermId, TermId>,
    /// Model generation queue.
    model_queue: VecDeque<(TheoryId, Vec<(TermId, TermId)>)>,
}

impl ModelBasedCombination {
    /// Create new model-based combination.
    pub fn new() -> Self {
        Self {
            model: FxHashMap::default(),
            model_queue: VecDeque::new(),
        }
    }

    /// Add model from theory.
    pub fn add_theory_model(&mut self, theory_id: TheoryId, assignments: Vec<(TermId, TermId)>) {
        self.model_queue.push_back((theory_id, assignments));
    }

    /// Merge theory models.
    pub fn merge_models(&mut self) -> Result<FxHashMap<TermId, TermId>, String> {
        self.model.clear();

        while let Some((_theory_id, assignments)) = self.model_queue.pop_front() {
            for (term, value) in assignments {
                if let Some(&existing_value) = self.model.get(&term)
                    && existing_value != value
                {
                    return Err("Model conflict".to_string());
                }
                self.model.insert(term, value);
            }
        }

        Ok(self.model.clone())
    }

    /// Clear model state.
    pub fn clear(&mut self) {
        self.model.clear();
        self.model_queue.clear();
    }
}

impl Default for ModelBasedCombination {
    fn default() -> Self {
        Self::new()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_equality_creation() {
        let eq1 = Equality::new(1, 2);
        let eq2 = Equality::new(2, 1);
        assert_eq!(eq1, eq2);
    }

    #[test]
    fn test_partition_creation() {
        let terms = vec![1, 2, 3, 4];
        let partition = TermPartition::new(&terms);
        assert_eq!(partition.num_classes(), 4);
    }

    #[test]
    fn test_partition_merge() {
        let terms = vec![1, 2, 3, 4];
        let mut partition = TermPartition::new(&terms);
        partition.merge(1, 2).expect("Merge failed");
        assert_eq!(partition.num_classes(), 3);
        assert!(partition.are_equal(1, 2));
    }

    #[test]
    fn test_partition_equalities() {
        let terms = vec![1, 2, 3];
        let mut partition = TermPartition::new(&terms);
        partition.merge(1, 2).expect("Merge failed");

        let equalities = partition.get_equalities();
        assert_eq!(equalities.len(), 1);
        assert_eq!(equalities[0], Equality::new(1, 2));
    }

    #[test]
    fn test_union_find_creation() {
        let mut uf = UnionFindWithExplanation::new();
        assert!(!uf.are_equal(1, 2));
    }

    #[test]
    fn test_union_find_union() {
        let mut uf = UnionFindWithExplanation::new();
        uf.union(1, 2, EqualityExplanation::Given, 0);
        assert!(uf.are_equal(1, 2));
    }

    #[test]
    fn test_union_find_transitivity() {
        let mut uf = UnionFindWithExplanation::new();
        uf.union(1, 2, EqualityExplanation::Given, 0);
        uf.union(2, 3, EqualityExplanation::Given, 0);
        assert!(uf.are_equal(1, 3));
    }

    #[test]
    fn test_advanced_nelson_oppen_creation() {
        let no = AdvancedNelsonOppen::new();
        assert_eq!(no.stats().iterations, 0);
    }

    #[test]
    fn test_register_theory() {
        let mut no = AdvancedNelsonOppen::new();
        let props = TheoryProperties::default();
        no.register_theory(0, props);
    }

    #[test]
    fn test_add_shared_term() {
        let mut no = AdvancedNelsonOppen::new();
        no.add_shared_term(1);
        assert!(no.shared_terms.contains(&1));
    }

    #[test]
    fn test_decision_level() {
        let mut no = AdvancedNelsonOppen::new();
        assert_eq!(no.current_decision_level(), 0);
        no.push_decision_level();
        assert_eq!(no.current_decision_level(), 1);
    }

    #[test]
    fn test_backtrack() {
        let mut no = AdvancedNelsonOppen::new();
        no.push_decision_level();
        no.push_decision_level();
        assert_eq!(no.current_decision_level(), 2);

        no.backtrack(1).expect("Backtrack failed");
        assert_eq!(no.current_decision_level(), 1);
    }

    #[test]
    fn test_assert_equality() {
        let mut no = AdvancedNelsonOppen::new();
        let eq = Equality::new(1, 2);
        no.assert_equality(eq, EqualityExplanation::Given)
            .expect("Assert failed");
        assert!(no.union_find.are_equal(1, 2));
    }

    #[test]
    fn test_pending_equality_priority() {
        let p1 = EqualityPriority {
            level: 10,
            relevancy: 5,
            decision_level: 0,
        };
        let p2 = EqualityPriority {
            level: 20,
            relevancy: 5,
            decision_level: 0,
        };
        assert!(p2 > p1);
    }

    #[test]
    fn test_partition_refinement() {
        let terms = vec![1, 2, 3, 4];
        let mut refinement = PartitionRefinement::new(&terms);

        refinement
            .refine_with_equality(Equality::new(1, 2))
            .expect("Refinement failed");

        assert!(refinement.current_partition().are_equal(1, 2));
    }

    #[test]
    fn test_partition_refinement_backtrack() {
        let terms = vec![1, 2, 3, 4];
        let mut refinement = PartitionRefinement::new(&terms);

        refinement
            .refine_with_equality(Equality::new(1, 2))
            .expect("Refinement failed");
        refinement.backtrack().expect("Backtrack failed");

        assert!(!refinement.current_partition().are_equal(1, 2));
    }

    #[test]
    fn test_model_based_combination() {
        let mut mbc = ModelBasedCombination::new();
        mbc.add_theory_model(0, vec![(1, 10), (2, 20)]);

        let model = mbc.merge_models().expect("Merge failed");
        assert_eq!(model.get(&1), Some(&10));
        assert_eq!(model.get(&2), Some(&20));
    }

    #[test]
    fn test_model_conflict_detection() {
        let mut mbc = ModelBasedCombination::new();
        mbc.add_theory_model(0, vec![(1, 10)]);
        mbc.add_theory_model(1, vec![(1, 20)]);

        let result = mbc.merge_models();
        assert!(result.is_err());
    }

    #[test]
    fn test_theory_properties() {
        let props = TheoryProperties {
            is_convex: false,
            is_stably_infinite: true,
            ..Default::default()
        };

        assert!(!props.is_convex);
        assert!(props.is_stably_infinite);
    }

    #[test]
    fn test_disequality_creation() {
        let d1 = Disequality::new(1, 2);
        let d2 = Disequality::new(2, 1);
        assert_eq!(d1.lhs, d2.lhs);
        assert_eq!(d1.rhs, d2.rhs);
    }

    #[test]
    fn test_generate_arrangements_bell_numbers() {
        let no = AdvancedNelsonOppen::new();
        // Bell(0..=4) = 1, 1, 2, 5, 15.
        assert_eq!(no.generate_arrangements(&[]).len(), 1);
        assert_eq!(no.generate_arrangements(&[1]).len(), 1);
        assert_eq!(no.generate_arrangements(&[1, 2]).len(), 2);
        assert_eq!(no.generate_arrangements(&[1, 2, 3]).len(), 5);
        assert_eq!(no.generate_arrangements(&[1, 2, 3, 4]).len(), 15);

        // Every arrangement of three terms is a distinct set partition.
        let arrangements = no.generate_arrangements(&[1, 2, 3]);
        let signatures: FxHashSet<Vec<usize>> = arrangements
            .iter()
            .map(|p| {
                let mut sig = vec![
                    usize::from(p.are_equal(1, 2)),
                    usize::from(p.are_equal(1, 3)),
                    usize::from(p.are_equal(2, 3)),
                ];
                sig.push(p.num_classes());
                sig
            })
            .collect();
        assert_eq!(signatures.len(), 5, "arrangements must be distinct");
    }

    /// Non-convex theory mock that tracks the arrangement asserted to it and is
    /// UNSAT exactly when a forbidden equality or forbidden disequality is
    /// present.  Assertions are level-scoped so `backtrack` undoes a trial
    /// arrangement.
    struct ArrangementMock {
        id: TheoryId,
        forbid_equal: Option<Equality>,
        forbid_diseq: Option<Disequality>,
        eqs: Vec<(Equality, DecisionLevel)>,
        diseqs: Vec<(Disequality, DecisionLevel)>,
        level: DecisionLevel,
    }

    impl ArrangementMock {
        fn new(
            id: TheoryId,
            forbid_equal: Option<Equality>,
            forbid_diseq: Option<Disequality>,
        ) -> Self {
            Self {
                id,
                forbid_equal,
                forbid_diseq,
                eqs: Vec::new(),
                diseqs: Vec::new(),
                level: 0,
            }
        }
    }

    impl TheorySolver for ArrangementMock {
        fn theory_id(&self) -> TheoryId {
            self.id
        }
        fn properties(&self) -> TheoryProperties {
            TheoryProperties {
                is_convex: false,
                ..Default::default()
            }
        }
        fn assert_equality(&mut self, eq: Equality, level: DecisionLevel) -> Result<(), String> {
            self.level = self.level.max(level);
            self.eqs.push((eq, level));
            Ok(())
        }
        fn assert_disequality(
            &mut self,
            diseq: Disequality,
            level: DecisionLevel,
        ) -> Result<(), String> {
            self.level = self.level.max(level);
            self.diseqs.push((diseq, level));
            Ok(())
        }
        fn check_satisfiability(&mut self) -> Result<CombinationResult, String> {
            if let Some(fe) = self.forbid_equal
                && self.eqs.iter().any(|(e, _)| *e == fe)
            {
                return Ok(CombinationResult::Unsat(vec![fe]));
            }
            if let Some(fd) = self.forbid_diseq
                && self.diseqs.iter().any(|(d, _)| *d == fd)
            {
                return Ok(CombinationResult::Unsat(Vec::new()));
            }
            Ok(CombinationResult::Sat)
        }
        fn get_implied_equalities(&self) -> Vec<(Equality, EqualityExplanation)> {
            Vec::new()
        }
        fn backtrack(&mut self, level: DecisionLevel) -> Result<(), String> {
            self.eqs.retain(|(_, l)| *l <= level);
            self.diseqs.retain(|(_, l)| *l <= level);
            self.level = level;
            Ok(())
        }
        fn decision_level(&self) -> DecisionLevel {
            self.level
        }
        fn reset(&mut self) {
            self.eqs.clear();
            self.diseqs.clear();
            self.level = 0;
        }
    }

    #[test]
    fn test_non_convex_case_split_finds_consistent_arrangement() {
        // Theory forbids 10 = 20, so the arrangement 10 != 20 must be chosen –
        // the case split has to discover it rather than guessing SAT blindly.
        let mut no = AdvancedNelsonOppen::new();
        no.register_theory(
            0,
            TheoryProperties {
                is_convex: false,
                ..Default::default()
            },
        );
        no.add_shared_term(10);
        no.add_shared_term(20);

        let mut theory = ArrangementMock::new(0, Some(Equality::new(10, 20)), None);
        let mut theories: Vec<&mut dyn TheorySolver> = vec![&mut theory];
        let result = no.combine(&mut theories).expect("combine");
        assert_eq!(result, CombinationResult::Sat);
        assert!(
            no.stats().case_splits > 0,
            "a case split must have occurred"
        );
    }

    #[test]
    fn test_non_convex_case_split_all_arrangements_refuted_is_unsat() {
        // One theory forbids 10 = 20, another forbids 10 != 20: no arrangement
        // of the two shared terms satisfies both, so the combination is UNSAT.
        let mut no = AdvancedNelsonOppen::new();
        no.register_theory(
            0,
            TheoryProperties {
                is_convex: false,
                ..Default::default()
            },
        );
        no.add_shared_term(10);
        no.add_shared_term(20);

        let mut theory_a = ArrangementMock::new(0, Some(Equality::new(10, 20)), None);
        let mut theory_b = ArrangementMock::new(1, None, Some(Disequality::new(10, 20)));
        let mut theories: Vec<&mut dyn TheorySolver> = vec![&mut theory_a, &mut theory_b];
        let result = no.combine(&mut theories).expect("combine");
        assert!(
            matches!(result, CombinationResult::Unsat(_)),
            "no arrangement can satisfy both theories, expected Unsat, got {:?}",
            result
        );
    }
}
