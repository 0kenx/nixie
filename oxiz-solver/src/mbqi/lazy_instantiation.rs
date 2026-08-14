//! Lazy Quantifier Instantiation
//!
//! This module implements lazy instantiation strategies that defer creating
//! instantiations until they are needed. This helps manage the explosion of
//! instantiations in complex quantified formulas.
//!
//! # Strategies
//!
//! - **On-Demand**: Generate instantiations only when conflicts occur
//! - **Relevance-Based**: Instantiate only relevant quantifiers
//! - **Cost-Guided**: Prioritize instantiations by estimated cost
//! - **Incremental**: Add instantiations incrementally with backtracking

#[allow(unused_imports)]
use crate::prelude::*;
use oxiz_core::ast::{TermId, TermKind, TermManager};
use oxiz_core::interner::Spur;
use oxiz_core::sort::SortId;

use super::counterexample::CounterExampleGenerator;
use super::model_completion::CompletedModel;
use super::{Instantiation, QuantifiedFormula};

/// Lazy instantiation strategy
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum LazyStrategy {
    /// Generate all instantiations eagerly
    Eager,
    /// Generate instantiations on-demand when needed
    OnDemand,
    /// Use relevance-based instantiation
    Relevance,
    /// Cost-guided instantiation
    CostGuided,
    /// Incremental instantiation with backtracking
    Incremental,
}

/// Matching context for pattern-based instantiation
#[derive(Debug)]
pub struct MatchingContext {
    /// E-graph (simplified representation)
    pub egraph: EGraph,
    /// Term database for pattern matching
    pub term_db: TermDatabase,
    /// Matching cache
    pub match_cache: FxHashMap<TermId, Vec<Match>>,
}

impl MatchingContext {
    /// Create a new matching context
    pub fn new() -> Self {
        Self {
            egraph: EGraph::new(),
            term_db: TermDatabase::new(),
            match_cache: FxHashMap::default(),
        }
    }

    /// Add a term to the matching context
    pub fn add_term(&mut self, term: TermId, manager: &TermManager) {
        self.term_db.add_term(term, manager);
        self.egraph.add_term(term, manager);
    }

    /// Find matches for a pattern
    pub fn find_matches(&mut self, pattern: TermId, manager: &TermManager) -> Vec<Match> {
        // Check cache first
        if let Some(cached) = self.match_cache.get(&pattern) {
            return cached.clone();
        }

        // Perform matching
        let matches = self.term_db.match_pattern(pattern, manager);

        // Cache results
        self.match_cache.insert(pattern, matches.clone());

        matches
    }

    /// Clear the cache
    pub fn clear_cache(&mut self) {
        self.match_cache.clear();
    }
}

impl Default for MatchingContext {
    fn default() -> Self {
        Self::new()
    }
}

/// Simplified E-graph for equality reasoning
#[derive(Debug)]
pub struct EGraph {
    /// Equivalence classes (representative -> members)
    classes: FxHashMap<TermId, Vec<TermId>>,
    /// Term to representative mapping
    representatives: FxHashMap<TermId, TermId>,
}

impl EGraph {
    /// Create a new E-graph
    pub fn new() -> Self {
        Self {
            classes: FxHashMap::default(),
            representatives: FxHashMap::default(),
        }
    }

    /// Add a term to the E-graph
    pub fn add_term(&mut self, term: TermId, _manager: &TermManager) {
        if !self.representatives.contains_key(&term) {
            // Create new equivalence class
            self.classes.insert(term, vec![term]);
            self.representatives.insert(term, term);
        }
    }

    /// Merge two equivalence classes
    pub fn merge(&mut self, a: TermId, b: TermId) {
        let rep_a = self.find(a);
        let rep_b = self.find(b);

        if rep_a == rep_b {
            return;
        }

        // Merge smaller class into larger
        let size_a = self.classes.get(&rep_a).map_or(0, |c| c.len());
        let size_b = self.classes.get(&rep_b).map_or(0, |c| c.len());

        let (smaller, larger) = if size_a < size_b {
            (rep_a, rep_b)
        } else {
            (rep_b, rep_a)
        };

        // Move members from smaller to larger
        if let Some(members) = self.classes.remove(&smaller) {
            for &member in &members {
                self.representatives.insert(member, larger);
            }
            self.classes.entry(larger).or_default().extend(members);
        }
    }

    /// Find representative of equivalence class
    pub fn find(&self, term: TermId) -> TermId {
        self.representatives.get(&term).copied().unwrap_or(term)
    }

    /// Get all members of an equivalence class
    pub fn members(&self, term: TermId) -> Vec<TermId> {
        let rep = self.find(term);
        self.classes
            .get(&rep)
            .cloned()
            .unwrap_or_else(|| vec![term])
    }
}

impl Default for EGraph {
    fn default() -> Self {
        Self::new()
    }
}

/// Term database for efficient pattern matching
#[derive(Debug)]
pub struct TermDatabase {
    /// Terms indexed by top symbol
    by_symbol: FxHashMap<Spur, Vec<TermId>>,
    /// All ground terms
    ground_terms: Vec<TermId>,
    /// Terms by sort
    by_sort: FxHashMap<SortId, Vec<TermId>>,
}

impl TermDatabase {
    /// Create a new term database
    pub fn new() -> Self {
        Self {
            by_symbol: FxHashMap::default(),
            ground_terms: Vec::new(),
            by_sort: FxHashMap::default(),
        }
    }

    /// Add a term to the database
    pub fn add_term(&mut self, term: TermId, manager: &TermManager) {
        let Some(t) = manager.get(term) else {
            return;
        };

        // Index by sort
        self.by_sort.entry(t.sort).or_default().push(term);

        // Index by top symbol
        if let TermKind::Apply { func, .. } = t.kind {
            self.by_symbol.entry(func).or_default().push(term);
        }

        // Track ground terms
        if self.is_ground(term, manager) {
            self.ground_terms.push(term);
        }
    }

    /// Check if a term is ground (no free variables).
    ///
    /// Delegates to [`utils::is_ground`](crate::mbqi::macros::utils::is_ground),
    /// i.e. `free_vars_including_patterns(term).is_empty()` on the exhaustive,
    /// binder-aware, explicit-stack free-variable walk in `oxiz-core`.
    ///
    /// This used to be a local recursive walk that descended only
    /// `Apply`/`Not`/`Neg`/`And`/`Or` and then fell through `_ => true`, so
    /// every other kind was classified ground *without looking at its
    /// children*: `(+ x 1)`, `(bvadd x #x01)`, `(select a i)`, `(ite b x y)`
    /// all counted as "ground" despite the free `x`. That is the unsound
    /// direction for this database: a variable-containing term entered
    /// `ground_terms`, was offered to `match_pattern`, and a pattern variable
    /// could then bind to a term that still contains variables, producing a
    /// non-ground "instance". Binders fell through the same arm, so a closed
    /// `forall` answered `true` only by accident and a `forall` with a free
    /// variable under it answered `true` incorrectly. The core query is
    /// exhaustive over `TermKind` (a new variant is a compile error there,
    /// not a silent misclassification here) and scope-aware, so both
    /// directions are now correct.
    fn is_ground(&self, term: TermId, manager: &TermManager) -> bool {
        crate::mbqi::macros::utils::is_ground(term, manager)
    }

    /// Match a pattern against the database
    pub fn match_pattern(&self, pattern: TermId, manager: &TermManager) -> Vec<Match> {
        let mut matches = Vec::new();

        // Try matching against all ground terms
        for &term in &self.ground_terms {
            if let Some(binding) = self.try_match(pattern, term, manager) {
                matches.push(Match {
                    pattern,
                    term,
                    binding,
                });
            }
        }

        matches
    }

    /// Try to match a pattern against a term.
    ///
    /// Iterative worklist over `(pattern, term)` pairs with a visited-pair
    /// set, replacing a native recursion that had no memoisation at all: the
    /// two-sided walk re-expanded shared subterms of the hash-consed DAG once
    /// per path (exponential on a doubling DAG) and overflowed the native
    /// stack on deep patterns. Skipping an already-seen pair is sound because
    /// this walk is a pure conjunction with no backtracking: bindings only
    /// ever grow within one attempt, the first failing pair fails the whole
    /// attempt, and a pair that succeeded pinned every pattern variable below
    /// it to the corresponding subterm of `term`, so revisiting it cannot
    /// change the outcome.
    fn try_match(
        &self,
        pattern: TermId,
        term: TermId,
        manager: &TermManager,
    ) -> Option<FxHashMap<Spur, TermId>> {
        let mut binding: FxHashMap<Spur, TermId> = FxHashMap::default();
        let mut seen: FxHashSet<(TermId, TermId)> = FxHashSet::default();
        // Pairs still to match; children are pushed in reverse so they are
        // matched left-to-right, exactly as the recursive walk did.
        let mut work: Vec<(TermId, TermId)> = vec![(pattern, term)];

        while let Some((p_id, t_id)) = work.pop() {
            if !seen.insert((p_id, t_id)) {
                continue;
            }

            let p = manager.get(p_id)?;

            // Variable matches anything (but must be consistent)
            if let TermKind::Var(var_name) = p.kind {
                match binding.get(&var_name) {
                    Some(&bound_term) => {
                        if bound_term != t_id {
                            return None;
                        }
                    }
                    None => {
                        binding.insert(var_name, t_id);
                    }
                }
                continue;
            }

            let t = manager.get(t_id)?;

            // Structural match
            match (&p.kind, &t.kind) {
                (
                    TermKind::Apply { func: pf, args: pa },
                    TermKind::Apply { func: tf, args: ta },
                ) => {
                    if pf != tf || pa.len() != ta.len() {
                        return None;
                    }
                    for (parg, targ) in pa.iter().zip(ta.iter()).rev() {
                        work.push((*parg, *targ));
                    }
                }
                (TermKind::Not(pa), TermKind::Not(ta)) => work.push((*pa, *ta)),
                (TermKind::IntConst(pv), TermKind::IntConst(tv)) => {
                    if pv != tv {
                        return None;
                    }
                }
                (TermKind::True, TermKind::True) | (TermKind::False, TermKind::False) => {}
                // Any other shape pair is simply not matched by this matcher.
                // Failing is the conservative (sound) direction: it can only
                // miss an instantiation, never fabricate a binding.
                _ => return None,
            }
        }

        Some(binding)
    }

    /// Get terms by symbol
    pub fn get_by_symbol(&self, symbol: Spur) -> &[TermId] {
        self.by_symbol.get(&symbol).map_or(&[], |v| v.as_slice())
    }

    /// Get terms by sort
    pub fn get_by_sort(&self, sort: SortId) -> &[TermId] {
        self.by_sort.get(&sort).map_or(&[], |v| v.as_slice())
    }
}

impl Default for TermDatabase {
    fn default() -> Self {
        Self::new()
    }
}

/// A pattern match
#[derive(Debug, Clone)]
pub struct Match {
    /// The pattern that was matched
    pub pattern: TermId,
    /// The term that matched the pattern
    pub term: TermId,
    /// Variable bindings
    pub binding: FxHashMap<Spur, TermId>,
}

impl Match {
    /// Create a new match
    pub fn new(pattern: TermId, term: TermId, binding: FxHashMap<Spur, TermId>) -> Self {
        Self {
            pattern,
            term,
            binding,
        }
    }
}

/// Lazy instantiator that defers instantiation
#[derive(Debug)]
pub struct LazyInstantiator {
    /// Instantiation strategy
    strategy: LazyStrategy,
    /// Queue of pending instantiations
    pending_queue: VecDeque<PendingInstantiation>,
    /// Priority queue for cost-guided strategy
    priority_queue: BinaryHeap<ScoredInstantiation>,
    /// Matching context
    matching_context: MatchingContext,
    /// Counterexample generator
    cex_generator: CounterExampleGenerator,
    /// Relevance tracker
    relevance: RelevanceTracker,
    /// Statistics
    stats: LazyStats,
}

impl LazyInstantiator {
    /// Create a new lazy instantiator
    pub fn new() -> Self {
        Self {
            strategy: LazyStrategy::OnDemand,
            pending_queue: VecDeque::new(),
            priority_queue: BinaryHeap::new(),
            matching_context: MatchingContext::new(),
            cex_generator: CounterExampleGenerator::new(),
            relevance: RelevanceTracker::new(),
            stats: LazyStats::default(),
        }
    }

    /// Create with specific strategy
    pub fn with_strategy(strategy: LazyStrategy) -> Self {
        let mut inst = Self::new();
        inst.strategy = strategy;
        inst
    }

    /// Process quantifiers and generate instantiations lazily.
    ///
    /// Only **universal** quantifiers are instantiated, whichever strategy is
    /// selected. For an existential, `body[t/x]` is not entailed by
    /// `(exists x. body)`, so emitting it as a lemma over-constrains the
    /// solver and can flip SAT to UNSAT -- the same rationale as the
    /// `is_universal` gate in `mbqi::integration`. Existential entries in
    /// `quantifiers` are skipped.
    pub fn process(
        &mut self,
        quantifiers: &[QuantifiedFormula],
        model: &CompletedModel,
        manager: &mut TermManager,
        max_instantiations: usize,
    ) -> Vec<Instantiation> {
        self.stats.num_process_calls += 1;

        match self.strategy {
            LazyStrategy::Eager => self.process_eager(quantifiers, model, manager),
            LazyStrategy::OnDemand => {
                self.process_on_demand(quantifiers, model, manager, max_instantiations)
            }
            LazyStrategy::Relevance => self.process_relevance(quantifiers, model, manager),
            LazyStrategy::CostGuided => self.process_cost_guided(quantifiers, model, manager),
            LazyStrategy::Incremental => {
                self.process_incremental(quantifiers, model, manager, max_instantiations)
            }
        }
    }

    /// Eager strategy: generate all instantiations immediately
    fn process_eager(
        &mut self,
        quantifiers: &[QuantifiedFormula],
        model: &CompletedModel,
        manager: &mut TermManager,
    ) -> Vec<Instantiation> {
        let mut instantiations = Vec::new();

        for quantifier in quantifiers {
            // Universal quantifiers only (see `process`).
            if !quantifier.is_universal {
                continue;
            }
            let cex_result = self.cex_generator.generate(quantifier, model, manager);

            for cex in cex_result.counterexamples {
                let substituted =
                    self.apply_substitution(quantifier.body, &cex.assignment, manager);
                let inst = cex.to_instantiation(substituted);
                instantiations.push(inst);
            }
        }

        self.stats.num_instantiations_generated += instantiations.len();
        instantiations
    }

    /// On-demand strategy: queue instantiations and generate as needed
    fn process_on_demand(
        &mut self,
        quantifiers: &[QuantifiedFormula],
        model: &CompletedModel,
        manager: &mut TermManager,
        max_instantiations: usize,
    ) -> Vec<Instantiation> {
        // Add quantifiers to pending queue (universal only, see `process`)
        for quantifier in quantifiers {
            if quantifier.is_universal && quantifier.can_instantiate() {
                self.pending_queue.push_back(PendingInstantiation {
                    quantifier: quantifier.clone(),
                    priority: quantifier.priority_score(),
                });
            }
        }

        // Generate up to max_instantiations
        let mut instantiations = Vec::new();

        while instantiations.len() < max_instantiations {
            let Some(pending) = self.pending_queue.pop_front() else {
                break;
            };

            let cex_result = self
                .cex_generator
                .generate(&pending.quantifier, model, manager);

            for cex in cex_result.counterexamples {
                if instantiations.len() >= max_instantiations {
                    break;
                }

                let substituted =
                    self.apply_substitution(pending.quantifier.body, &cex.assignment, manager);
                let inst = cex.to_instantiation(substituted);
                instantiations.push(inst);
            }
        }

        self.stats.num_instantiations_generated += instantiations.len();
        instantiations
    }

    /// Relevance-based strategy: only instantiate relevant quantifiers
    fn process_relevance(
        &mut self,
        quantifiers: &[QuantifiedFormula],
        model: &CompletedModel,
        manager: &mut TermManager,
    ) -> Vec<Instantiation> {
        let mut instantiations = Vec::new();

        // Update relevance based on model
        self.relevance.update_from_model(model, manager);

        for quantifier in quantifiers {
            // Universal quantifiers only (see `process`).
            if !quantifier.is_universal {
                continue;
            }
            // Check if quantifier is relevant
            if !self.relevance.is_relevant(quantifier.term) {
                self.stats.num_relevance_filtered += 1;
                continue;
            }

            let cex_result = self.cex_generator.generate(quantifier, model, manager);

            for cex in cex_result.counterexamples {
                let substituted =
                    self.apply_substitution(quantifier.body, &cex.assignment, manager);
                let inst = cex.to_instantiation(substituted);
                instantiations.push(inst);
            }
        }

        self.stats.num_instantiations_generated += instantiations.len();
        instantiations
    }

    /// Cost-guided strategy: prioritize by estimated cost
    fn process_cost_guided(
        &mut self,
        quantifiers: &[QuantifiedFormula],
        model: &CompletedModel,
        manager: &mut TermManager,
    ) -> Vec<Instantiation> {
        // Add quantifiers to priority queue (universal only, see `process`)
        for quantifier in quantifiers {
            if quantifier.is_universal && quantifier.can_instantiate() {
                let cost = self.estimate_cost(quantifier, manager);
                let scored = ScoredInstantiation {
                    quantifier: quantifier.clone(),
                    score: cost,
                };
                self.priority_queue.push(scored);
            }
        }

        let mut instantiations = Vec::new();

        // Process in priority order
        while let Some(scored) = self.priority_queue.pop() {
            let cex_result = self
                .cex_generator
                .generate(&scored.quantifier, model, manager);

            for cex in cex_result.counterexamples {
                let substituted =
                    self.apply_substitution(scored.quantifier.body, &cex.assignment, manager);
                let inst = cex.to_instantiation(substituted);
                instantiations.push(inst);
            }

            // Limit total instantiations
            if instantiations.len() >= 100 {
                break;
            }
        }

        self.stats.num_instantiations_generated += instantiations.len();
        instantiations
    }

    /// Incremental strategy: add instantiations incrementally
    fn process_incremental(
        &mut self,
        quantifiers: &[QuantifiedFormula],
        model: &CompletedModel,
        manager: &mut TermManager,
        max_per_round: usize,
    ) -> Vec<Instantiation> {
        let mut instantiations = Vec::new();

        for quantifier in quantifiers {
            // Universal quantifiers only (see `process`).
            if !quantifier.is_universal {
                continue;
            }
            if instantiations.len() >= max_per_round {
                break;
            }

            let cex_result = self.cex_generator.generate(quantifier, model, manager);

            for cex in cex_result.counterexamples {
                if instantiations.len() >= max_per_round {
                    break;
                }

                let substituted =
                    self.apply_substitution(quantifier.body, &cex.assignment, manager);
                let inst = cex.to_instantiation(substituted);
                instantiations.push(inst);
            }
        }

        self.stats.num_instantiations_generated += instantiations.len();
        instantiations
    }

    /// Estimate the cost of instantiating a quantifier
    fn estimate_cost(&self, quantifier: &QuantifiedFormula, manager: &TermManager) -> f64 {
        // Factors:
        // - Number of variables (more = higher cost)
        // - Body complexity (larger = higher cost)
        // - Previous instantiation count (more = higher cost to avoid loops)

        let var_cost = quantifier.num_vars() as f64;
        let body_size = self.term_size(quantifier.body, manager) as f64;
        let inst_penalty = quantifier.instantiation_count as f64;

        var_cost + body_size + inst_penalty
    }

    /// Number of distinct nodes reachable through the propositional
    /// connectives `And`/`Or`/`Not`; every other kind counts as one leaf.
    ///
    /// This is a cost heuristic only -- the deliberately shallow descent set
    /// is part of its semantics -- but the walk itself is an explicit-stack
    /// loop with a visited set, so no input depth can overflow the call
    /// stack and shared subterms are counted once.
    fn term_size(&self, term: TermId, manager: &TermManager) -> usize {
        let mut visited: FxHashSet<TermId> = FxHashSet::default();
        let mut size = 0usize;
        let mut work = vec![term];
        while let Some(t_id) = work.pop() {
            if !visited.insert(t_id) {
                continue;
            }
            size += 1;
            let Some(t) = manager.get(t_id) else {
                continue;
            };
            match &t.kind {
                TermKind::And(args) | TermKind::Or(args) => work.extend(args.iter().copied()),
                TermKind::Not(arg) => work.push(*arg),
                // Deliberate leaf classification: only propositional
                // structure contributes to this cost estimate.
                _ => {}
            }
        }
        size
    }

    /// Substitute a quantifier's bound variables in `term`, by variable name.
    ///
    /// Delegates to [`utils::substitute`](crate::mbqi::macros::utils::substitute),
    /// the one shared implementation for this crate, which resolves the
    /// name-keyed map against the term's actual free occurrences and hands the
    /// result to [`TermManager::substitute`].
    ///
    /// This used to be a local recursive walk with a memo table and a
    /// `TermKind` whitelist that ended in `_ => term`, so every kind outside
    /// the whitelist was returned **unchanged** -- the whitelist covered only
    /// `Var`/`Not`/`And`/`Or`, so *every* arithmetic, bit-vector, array,
    /// string, floating-point, datatype and equality operator, and every
    /// binder, fell through. A
    /// bound variable sitting anywhere under such a kind therefore survived
    /// into the "ground instance", which is then not an instance at all: the
    /// engine reported a substitution it had not performed. Four
    /// near-identical copies of that walk existed in this module (here, and in
    /// `instantiation`, `counterexample`, `lazy_instantiation`,
    /// `conflict_driven`); they are all now this one call, because a duplicate
    /// that has diverged four times will diverge again.
    ///
    /// The shared routine additionally descends into
    /// `Forall`/`Exists`/`Let`/`Match` bodies, bindings, cases and trigger
    /// patterns with capture-avoiding alpha-renaming, and walks with an
    /// explicit heap stack rather than native recursion.
    ///
    /// [`TermManager::substitute`]: oxiz_core::ast::TermManager::substitute
    fn apply_substitution(
        &self,
        term: TermId,
        subst: &FxHashMap<Spur, TermId>,
        manager: &mut TermManager,
    ) -> TermId {
        crate::mbqi::macros::utils::substitute(term, subst, manager)
    }

    /// Clear all caches and queues
    pub fn clear(&mut self) {
        self.pending_queue.clear();
        self.priority_queue.clear();
        self.matching_context.clear_cache();
        self.cex_generator.clear_cache();
        self.relevance.clear();
    }

    /// Get statistics
    pub fn stats(&self) -> &LazyStats {
        &self.stats
    }
}

impl Default for LazyInstantiator {
    fn default() -> Self {
        Self::new()
    }
}

/// A pending instantiation request
#[derive(Debug, Clone)]
struct PendingInstantiation {
    quantifier: QuantifiedFormula,
    priority: f64,
}

/// A scored instantiation for priority queue
#[derive(Debug, Clone)]
struct ScoredInstantiation {
    quantifier: QuantifiedFormula,
    score: f64,
}

impl PartialEq for ScoredInstantiation {
    fn eq(&self, other: &Self) -> bool {
        self.score == other.score
    }
}

impl Eq for ScoredInstantiation {}

impl PartialOrd for ScoredInstantiation {
    fn partial_cmp(&self, other: &Self) -> Option<core::cmp::Ordering> {
        Some(self.cmp(other))
    }
}

impl Ord for ScoredInstantiation {
    fn cmp(&self, other: &Self) -> core::cmp::Ordering {
        // Lower score = higher priority (min-heap behavior)
        other
            .score
            .partial_cmp(&self.score)
            .unwrap_or(core::cmp::Ordering::Equal)
    }
}

/// Tracks relevance of quantifiers and terms
#[derive(Debug)]
pub struct RelevanceTracker {
    /// Relevant terms
    relevant_terms: FxHashSet<TermId>,
    /// Relevant quantifiers
    relevant_quantifiers: FxHashSet<TermId>,
}

impl RelevanceTracker {
    /// Create a new relevance tracker
    pub fn new() -> Self {
        Self {
            relevant_terms: FxHashSet::default(),
            relevant_quantifiers: FxHashSet::default(),
        }
    }

    /// Mark a term as relevant
    pub fn mark_relevant(&mut self, term: TermId) {
        self.relevant_terms.insert(term);
    }

    /// Mark a quantifier as relevant
    pub fn mark_quantifier_relevant(&mut self, quantifier: TermId) {
        self.relevant_quantifiers.insert(quantifier);
    }

    /// Check if a term is relevant
    pub fn is_relevant(&self, term: TermId) -> bool {
        self.relevant_terms.contains(&term) || self.relevant_quantifiers.contains(&term)
    }

    /// Update relevance from model
    pub fn update_from_model(&mut self, model: &CompletedModel, _manager: &TermManager) {
        // Mark all terms in model as relevant
        for &term in model.assignments.keys() {
            self.mark_relevant(term);
        }
    }

    /// Clear all relevance info
    pub fn clear(&mut self) {
        self.relevant_terms.clear();
        self.relevant_quantifiers.clear();
    }
}

impl Default for RelevanceTracker {
    fn default() -> Self {
        Self::new()
    }
}

/// Statistics for lazy instantiation
#[derive(Debug, Clone, Default)]
pub struct LazyStats {
    /// Number of process calls
    pub num_process_calls: usize,
    /// Number of instantiations generated
    pub num_instantiations_generated: usize,
    /// Number of instantiations filtered by relevance
    pub num_relevance_filtered: usize,
}

#[cfg(test)]
mod tests {
    use super::*;

    // ======== Substitution regression tests ========
    //
    // `apply_substitution` used to be a local recursive walk whose `TermKind`
    // whitelist ended in `_ => term`, so a bound variable under any unlisted
    // kind survived into the supposedly ground instance. All four copies in
    // this module now delegate to `crate::mbqi::macros::utils::substitute`.

    /// A body whose only variable occurrence sits under a kind the old
    /// whitelist missed must still be substituted.
    #[test]
    fn substitution_reaches_kinds_outside_the_old_whitelist() {
        let mut m = TermManager::new();
        let bool_sort = m.sorts.bool_sort;
        let int_sort = m.sorts.int_sort;
        let bv8 = m.sorts.bitvec(8);

        let p = m.mk_var("p", bool_sort);
        let i = m.mk_var("i", int_sort);
        let b = m.mk_var("b", bv8);

        let p_name = match m.get(p).map(|t| &t.kind) {
            Some(TermKind::Var(n)) => *n,
            _ => panic!("p is a variable"),
        };
        let i_name = match m.get(i).map(|t| &t.kind) {
            Some(TermKind::Var(n)) => *n,
            _ => panic!("i is a variable"),
        };
        let b_name = match m.get(b).map(|t| &t.kind) {
            Some(TermKind::Var(n)) => *n,
            _ => panic!("b is a variable"),
        };

        let truth = m.mk_true();
        let two = m.mk_int(2);
        let ones = m.mk_bitvec(1, 8);

        // Every one of these was returned unchanged by the old walk.
        let xor = m.mk_xor(p, truth);
        let distinct = m.mk_distinct([i, two]);
        let bv_lt = m.mk_bv_ult(b, ones);
        let implies = m.mk_implies(p, truth);
        let nested = m.mk_forall([("z", int_sort)], distinct);

        let mut subst: FxHashMap<Spur, TermId> = FxHashMap::default();
        subst.insert(p_name, truth);
        subst.insert(i_name, two);
        subst.insert(b_name, ones);

        let subject = LazyInstantiator::new();
        for (label, term) in [
            ("xor", xor),
            ("distinct", distinct),
            ("bvult", bv_lt),
            ("implies", implies),
            ("nested forall", nested),
        ] {
            let result = subject.apply_substitution(term, &subst, &mut m);
            let free = m.free_vars_including_patterns(result);
            assert!(
                free.is_empty(),
                "{label}: substitution left free variables {free:?} in the result"
            );
        }
    }
    use smallvec::SmallVec;

    /// Run `f` to completion on a dedicated thread with a 128 KiB stack --
    /// deliberately far smaller than the default main-thread stack. A stack
    /// overflow aborts the whole process, so for the deep-nesting tests the
    /// call *returning at all* is itself part of the assertion.
    ///
    /// This stack and every depth below were scaled down together by a factor
    /// of 8 (from 1 MiB / 100 000).  The pin is the ~10 bytes of stack per
    /// nesting level, not the absolute depth, and the smaller pair keeps the
    /// interned terms out of swap.  Never raise one without the other.
    fn run_on_small_stack<T: Send + 'static>(f: impl FnOnce() -> T + Send + 'static) -> T {
        std::thread::Builder::new()
            .stack_size(1 << 17)
            .spawn(f)
            .expect("spawning the constrained-stack test thread should succeed")
            .join()
            .expect("the constrained-stack thread must not panic")
    }

    /// `TermDatabase::is_ground` used to classify every kind outside a small
    /// whitelist as ground without looking at its children (`_ => true`),
    /// and binders fell through the same arm. Pin the corrected behavior.
    #[test]
    fn term_database_is_ground_is_exhaustive_and_binder_aware() {
        let mut m = TermManager::new();
        let int_sort = m.sorts.int_sort;
        let bool_sort = m.sorts.bool_sort;
        let bv8 = m.sorts.bitvec(8);
        let db = TermDatabase::new();

        let x = m.mk_var("x", int_sort);
        let one = m.mk_int(1);
        let sum = m.mk_add([x, one]);
        assert!(
            !db.is_ground(sum, &m),
            "(+ x 1) is not ground; the old catch-all said it was"
        );

        let b = m.mk_var("b", bv8);
        let bv_one = m.mk_bitvec(1, 8);
        let bv_sum = m.mk_bv_add(b, bv_one);
        assert!(!db.is_ground(bv_sum, &m), "(bvadd b #x01) is not ground");

        let two = m.mk_int(2);
        assert!(db.is_ground(two, &m), "an integer literal is ground");

        // A closed forall is ground (previously true only by fall-through).
        let zero = m.mk_int(0);
        let gt = m.mk_gt(x, zero);
        let closed = m.mk_forall([("x", int_sort)], gt);
        assert!(
            db.is_ground(closed, &m),
            "(forall ((x Int)) (> x 0)) has no free variables"
        );

        // A forall with a free variable under it is NOT ground.
        let z = m.mk_var("z", int_sort);
        let p = m.mk_apply("P", [x, z], bool_sort);
        let open = m.mk_forall([("x", int_sort)], p);
        assert!(
            !db.is_ground(open, &m),
            "(forall ((x Int)) (P x z)) has z free"
        );
    }

    /// A variable-containing term must never enter the ground-term index, so
    /// a pattern variable can never bind to it.
    #[test]
    fn match_pattern_only_matches_ground_terms() {
        let mut m = TermManager::new();
        let int_sort = m.sorts.int_sort;
        let mut db = TermDatabase::new();

        let y = m.mk_var("y", int_sort);
        let one = m.mk_int(1);
        let non_ground = m.mk_add([y, one]);
        let ground = m.mk_int(42);
        db.add_term(non_ground, &m);
        db.add_term(ground, &m);

        // The pattern is a bare variable: it would match anything offered.
        let x = m.mk_var("x", int_sort);
        let matches = db.match_pattern(x, &m);
        assert_eq!(matches.len(), 1, "only the literal 42 is ground");
        assert_eq!(matches[0].term, ground);
    }

    /// The pattern matcher must survive a 12 500-deep pattern/term pair on a
    /// 128 KiB stack (the old recursion overflowed) and still produce the
    /// correct binding.
    #[test]
    fn try_match_survives_deep_patterns_on_a_tiny_stack() {
        const DEPTH: usize = 12_500;
        run_on_small_stack(|| {
            let mut m = TermManager::new();
            let int_sort = m.sorts.int_sort;
            let x = m.mk_var("x", int_sort);
            let seven = m.mk_int(7);

            let mut pattern = x;
            let mut term = seven;
            for _ in 0..DEPTH {
                pattern = m.mk_apply("f", [pattern], int_sort);
                term = m.mk_apply("f", [term], int_sort);
            }

            let db = TermDatabase::new();
            let binding = db
                .try_match(pattern, term, &m)
                .expect("the deep pattern must match the deep term");
            let x_name = match m.get(x).map(|t| &t.kind) {
                Some(TermKind::Var(n)) => *n,
                _ => panic!("x is a variable"),
            };
            assert_eq!(binding.get(&x_name), Some(&seven));

            // And a mismatch deep inside must be detected, not overflowed
            // on: a constant-leaf pattern against a different constant leaf.
            let eight = m.mk_int(8);
            let mut const_pattern = seven;
            let mut wrong = eight;
            for _ in 0..DEPTH {
                const_pattern = m.mk_apply("f", [const_pattern], int_sort);
                wrong = m.mk_apply("f", [wrong], int_sort);
            }
            assert!(db.try_match(const_pattern, wrong, &m).is_none());
        });
    }

    /// A doubling (pattern, term) DAG is exponential without the
    /// visited-pair set; with it the match must complete essentially
    /// instantly.
    #[test]
    fn try_match_handles_shared_dag_without_blowup() {
        const LEVELS: usize = 55;
        let mut m = TermManager::new();
        let int_sort = m.sorts.int_sort;
        let x = m.mk_var("x", int_sort);
        let seven = m.mk_int(7);

        let mut pattern = x;
        let mut term = seven;
        for _ in 0..LEVELS {
            pattern = m.mk_apply("g", [pattern, pattern], int_sort);
            term = m.mk_apply("g", [term, term], int_sort);
        }

        let db = TermDatabase::new();
        let binding = db
            .try_match(pattern, term, &m)
            .expect("the doubling DAGs must match");
        let x_name = match m.get(x).map(|t| &t.kind) {
            Some(TermKind::Var(n)) => *n,
            _ => panic!("x is a variable"),
        };
        assert_eq!(binding.get(&x_name), Some(&seven));
    }

    /// `term_size` (cost heuristic) must survive deep propositional nesting
    /// on a tiny stack and keep counting each distinct shared node once.
    #[test]
    fn term_size_survives_deep_nesting_and_counts_shared_nodes_once() {
        const DEPTH: usize = 12_500;
        let size = run_on_small_stack(|| {
            let mut m = TermManager::new();
            let bool_sort = m.sorts.bool_sort;
            let x = m.mk_var("p", bool_sort);
            let y = m.mk_var("q", bool_sort);
            // Alternate And/Not so neither `mk_and` flattening nor
            // `mk_not` double-negation folding can collapse the chain.
            let mut chain = y;
            for _ in 0..DEPTH {
                let conj = m.mk_and([x, chain]);
                chain = m.mk_not(conj);
            }
            let inst = LazyInstantiator::new();
            inst.term_size(chain, &m)
        });
        // Each level adds one And and one Not; x and y are counted once.
        assert_eq!(size, 2 * DEPTH + 2);
    }

    /// The lazy instantiator must never instantiate an existential:
    /// `body[t/x]` is not entailed by `(exists x. body)`. The same setup
    /// with a universal quantifier does produce instantiations, so the
    /// empty result for the existential is the gate, not a vacuity.
    #[test]
    fn lazy_instantiator_skips_existential_quantifiers() {
        let mut m = TermManager::new();
        let bool_sort = m.sorts.bool_sort;
        let x = m.mk_var("x", bool_sort);
        let x_name = match m.get(x).map(|t| &t.kind) {
            Some(TermKind::Var(n)) => *n,
            _ => panic!("x is a variable"),
        };
        let body = x;
        let forall = m.mk_forall([("x", bool_sort)], body);
        let exists = m.mk_exists([("x", bool_sort)], body);
        let vars: SmallVec<[(Spur, SortId); 4]> = core::iter::once((x_name, bool_sort)).collect();
        let universal = QuantifiedFormula::new(forall, vars.clone(), body, true);
        let existential = QuantifiedFormula::new(exists, vars, body, false);
        let model = CompletedModel::new();

        for strategy in [
            LazyStrategy::Eager,
            LazyStrategy::OnDemand,
            LazyStrategy::CostGuided,
            LazyStrategy::Incremental,
        ] {
            let mut inst = LazyInstantiator::with_strategy(strategy);
            let from_universal =
                inst.process(core::slice::from_ref(&universal), &model, &mut m, 16);
            assert!(
                !from_universal.is_empty(),
                "{strategy:?}: the universal Bool quantifier must instantiate"
            );

            let mut inst = LazyInstantiator::with_strategy(strategy);
            let from_existential =
                inst.process(core::slice::from_ref(&existential), &model, &mut m, 16);
            assert!(
                from_existential.is_empty(),
                "{strategy:?}: an existential must never be instantiated"
            );
        }
    }

    #[test]
    fn test_lazy_strategy_equality() {
        assert_eq!(LazyStrategy::Eager, LazyStrategy::Eager);
        assert_ne!(LazyStrategy::Eager, LazyStrategy::OnDemand);
    }

    #[test]
    fn test_matching_context_creation() {
        let ctx = MatchingContext::new();
        assert_eq!(ctx.match_cache.len(), 0);
    }

    #[test]
    fn test_egraph_creation() {
        let egraph = EGraph::new();
        assert_eq!(egraph.classes.len(), 0);
    }

    #[test]
    fn test_egraph_find() {
        let mut egraph = EGraph::new();
        let term = TermId::new(1);
        let manager = TermManager::new();
        egraph.add_term(term, &manager);
        assert_eq!(egraph.find(term), term);
    }

    #[test]
    fn test_egraph_merge() {
        let mut egraph = EGraph::new();
        let manager = TermManager::new();
        let term1 = TermId::new(1);
        let term2 = TermId::new(2);
        egraph.add_term(term1, &manager);
        egraph.add_term(term2, &manager);
        egraph.merge(term1, term2);
        assert_eq!(egraph.find(term1), egraph.find(term2));
    }

    #[test]
    fn test_term_database_creation() {
        let db = TermDatabase::new();
        assert_eq!(db.ground_terms.len(), 0);
    }

    #[test]
    fn test_match_creation() {
        let m = Match::new(TermId::new(1), TermId::new(2), FxHashMap::default());
        assert_eq!(m.pattern, TermId::new(1));
        assert_eq!(m.term, TermId::new(2));
    }

    #[test]
    fn test_lazy_instantiator_creation() {
        let inst = LazyInstantiator::new();
        assert_eq!(inst.strategy, LazyStrategy::OnDemand);
    }

    #[test]
    fn test_lazy_instantiator_with_strategy() {
        let inst = LazyInstantiator::with_strategy(LazyStrategy::CostGuided);
        assert_eq!(inst.strategy, LazyStrategy::CostGuided);
    }

    #[test]
    fn test_relevance_tracker_creation() {
        let tracker = RelevanceTracker::new();
        assert!(!tracker.is_relevant(TermId::new(1)));
    }

    #[test]
    fn test_relevance_tracker_mark() {
        let mut tracker = RelevanceTracker::new();
        let term = TermId::new(1);
        tracker.mark_relevant(term);
        assert!(tracker.is_relevant(term));
    }

    #[test]
    fn test_scored_instantiation_ordering() {
        let q1 = QuantifiedFormula::new(TermId::new(1), SmallVec::new(), TermId::new(2), true);
        let q2 = QuantifiedFormula::new(TermId::new(3), SmallVec::new(), TermId::new(4), true);

        let s1 = ScoredInstantiation {
            quantifier: q1,
            score: 1.0,
        };
        let s2 = ScoredInstantiation {
            quantifier: q2,
            score: 2.0,
        };

        // Lower score should be higher priority
        assert!(s1 > s2);
    }
}
