//! Model-Based Instantiation Engine
//!
//! This module implements the core instantiation logic for MBQI. It handles:
//! - Extracting instantiations from models and counterexamples
//! - Conflict-driven instantiation
//! - Pattern matching and trigger selection
//! - Instantiation deduplication and filtering

#![allow(missing_docs)]

#[allow(unused_imports)]
use crate::prelude::*;
use nixie_core::ast::{TermId, TermKind, TermManager};
use nixie_core::interner::Spur;
use nixie_core::sort::SortId;
use num_bigint::BigInt;

use super::counterexample::CounterExampleGenerator;
use super::model_completion::CompletedModel;
use super::{Instantiation, InstantiationReason, QuantifiedFormula};

/// Context for instantiation
#[derive(Debug)]
pub struct InstantiationContext {
    /// Term manager
    pub manager: TermManager,
    /// Current model
    pub model: CompletedModel,
    /// Generation counter
    pub generation: u32,
    /// E-graph for equality reasoning (simplified)
    pub equalities: FxHashMap<TermId, TermId>,
}

impl InstantiationContext {
    /// Create a new instantiation context
    pub fn new(manager: TermManager) -> Self {
        Self {
            manager,
            model: CompletedModel::new(),
            generation: 0,
            equalities: FxHashMap::default(),
        }
    }

    /// Set the current model
    pub fn set_model(&mut self, model: CompletedModel) {
        self.model = model;
    }

    /// Increment generation
    pub fn next_generation(&mut self) {
        self.generation += 1;
    }

    /// Add an equality
    pub fn add_equality(&mut self, lhs: TermId, rhs: TermId) {
        self.equalities.insert(lhs, rhs);
        self.equalities.insert(rhs, lhs);
    }

    /// Find representative in equality graph
    pub fn find_representative(&self, term: TermId) -> TermId {
        let mut current = term;
        let mut visited = FxHashSet::default();

        while let Some(&next) = self.equalities.get(&current) {
            if visited.contains(&next) {
                break; // Cycle detected
            }
            visited.insert(current);
            current = next;
        }

        current
    }
}

/// Pattern for instantiation (E-matching style)
#[derive(Debug, Clone)]
pub struct InstantiationPattern {
    /// Terms that form the pattern
    pub terms: Vec<TermId>,
    /// Variables that must be matched
    pub vars: FxHashSet<Spur>,
    /// Number of variables
    pub num_vars: usize,
    /// Pattern quality (higher = better)
    pub quality: f64,
}

impl InstantiationPattern {
    /// Create a new pattern
    pub fn new(terms: Vec<TermId>) -> Self {
        Self {
            terms,
            vars: FxHashSet::default(),
            num_vars: 0,
            quality: 1.0,
        }
    }

    /// Extract patterns from a quantified formula
    pub fn extract_patterns(quantifier: &QuantifiedFormula, manager: &TermManager) -> Vec<Self> {
        let mut patterns = Vec::new();

        // Use explicit patterns if available
        if !quantifier.patterns.is_empty() {
            for pattern_terms in &quantifier.patterns {
                let mut pattern = Self::new(pattern_terms.clone());
                pattern.collect_vars(manager);
                pattern.calculate_quality(manager);
                patterns.push(pattern);
            }
        } else {
            // Auto-generate patterns from the body
            let generated = Self::generate_patterns(quantifier.body, manager);
            patterns.extend(generated);
        }

        patterns
    }

    /// Generate patterns from a term
    fn generate_patterns(term: TermId, manager: &TermManager) -> Vec<Self> {
        let mut patterns = Vec::new();
        let candidates = Self::collect_pattern_candidates(term, manager);

        for candidate in candidates {
            let mut pattern = Self::new(vec![candidate]);
            pattern.collect_vars(manager);
            if pattern.num_vars > 0 {
                pattern.calculate_quality(manager);
                patterns.push(pattern);
            }
        }

        patterns
    }

    /// Collect pattern candidates from a term
    fn collect_pattern_candidates(term: TermId, manager: &TermManager) -> Vec<TermId> {
        let mut candidates = Vec::new();
        let mut visited = FxHashSet::default();
        Self::collect_candidates_iterative(term, &mut candidates, &mut visited, manager);
        candidates
    }

    /// Iteratively collect pattern candidates from a term.
    ///
    /// Pre-order over the deliberately bounded descent set (`Apply` args,
    /// `And`/`Or` args, `Eq`/`Lt`/`Le` sides -- the shapes candidates are
    /// drawn from; other kinds are intentionally not candidate sources), with
    /// an explicit heap stack instead of native recursion so that no input
    /// depth can overflow the call stack. Children are pushed in reverse so
    /// they are visited left-to-right, preserving the recursive walk's
    /// candidate order exactly.
    fn collect_candidates_iterative(
        term: TermId,
        candidates: &mut Vec<TermId>,
        visited: &mut FxHashSet<TermId>,
        manager: &TermManager,
    ) {
        let mut work = vec![term];
        while let Some(t_id) = work.pop() {
            if !visited.insert(t_id) {
                continue;
            }

            let Some(t) = manager.get(t_id) else {
                continue;
            };

            // Function applications are good pattern candidates
            if matches!(t.kind, TermKind::Apply { .. }) {
                candidates.push(t_id);
            }

            match &t.kind {
                TermKind::Apply { args, .. } => {
                    for &arg in args.iter().rev() {
                        work.push(arg);
                    }
                }
                TermKind::And(args) | TermKind::Or(args) => {
                    for &arg in args.iter().rev() {
                        work.push(arg);
                    }
                }
                TermKind::Eq(lhs, rhs) | TermKind::Lt(lhs, rhs) | TermKind::Le(lhs, rhs) => {
                    work.push(*rhs);
                    work.push(*lhs);
                }
                _ => {}
            }
        }
    }

    /// Collect the variables a matcher must bind for this pattern: the free
    /// variables of the pattern terms.
    ///
    /// Delegates to [`utils::free_vars`](crate::mbqi::macros::utils::free_vars)
    /// (the exhaustive, binder-aware, explicit-stack walk in `nixie-core`).
    /// This used to be a local recursive walk that descended only
    /// `Apply`/`Not`/`Neg`/`And`/`Or` and silently dropped everything else,
    /// so a variable sitting under `Eq`, `Ite`, any arithmetic, bit-vector,
    /// array or string operator was never collected: `num_vars` came out
    /// wrong, variable-bearing candidates were discarded by
    /// `generate_patterns` (`num_vars > 0` filter), and a matcher driven by
    /// this set would leave those variables unbound. A variable bound by a
    /// nested binder inside the pattern is correctly *not* collected -- it is
    /// not matchable from outside.
    fn collect_vars(&mut self, manager: &TermManager) {
        self.vars.clear();
        for &term in &self.terms {
            self.vars
                .extend(crate::mbqi::macros::utils::free_vars(term, manager));
        }
        self.num_vars = self.vars.len();
    }

    /// Calculate pattern quality
    fn calculate_quality(&mut self, manager: &TermManager) {
        // Quality factors:
        // - More variables = better (more specific)
        // - Fewer terms = better (simpler)
        // - Contains function applications = better

        let var_factor = 1.0 + (self.num_vars as f64);
        let term_factor = 1.0 / (1.0 + self.terms.len() as f64);
        let func_factor = if self.has_function_applications(manager) {
            2.0
        } else {
            1.0
        };

        self.quality = var_factor * term_factor * func_factor;
    }

    fn has_function_applications(&self, manager: &TermManager) -> bool {
        for &term in &self.terms {
            if let Some(t) = manager.get(term)
                && matches!(t.kind, TermKind::Apply { .. })
            {
                return true;
            }
        }
        false
    }
}

/// Quantifier instantiator
#[derive(Debug)]
pub struct QuantifierInstantiator {
    /// Counterexample generator
    cex_generator: CounterExampleGenerator,
    /// Deduplication cache
    dedup_cache: FxHashSet<InstantiationKey>,
    /// Per-quantifier instantiation depth tracking.
    ///
    /// When a quantifier is instantiated this counter is incremented.  If the
    /// counter reaches `max_depth` (when `max_depth > 0`) further
    /// instantiations of that quantifier are suppressed.
    depth_tracking: FxHashMap<TermId, u32>,
    /// Maximum allowed instantiation depth per quantifier (0 = unlimited).
    pub max_depth: u32,
    /// Statistics
    stats: InstantiatorStats,
}

impl QuantifierInstantiator {
    /// Create a new instantiator (no depth limit)
    pub fn new() -> Self {
        Self {
            cex_generator: CounterExampleGenerator::new(),
            dedup_cache: FxHashSet::default(),
            depth_tracking: FxHashMap::default(),
            max_depth: 0,
            stats: InstantiatorStats::default(),
        }
    }

    /// Create with a specified depth limit
    pub fn with_max_depth(max_depth: u32) -> Self {
        Self {
            cex_generator: CounterExampleGenerator::new(),
            dedup_cache: FxHashSet::default(),
            depth_tracking: FxHashMap::default(),
            max_depth,
            stats: InstantiatorStats::default(),
        }
    }

    /// Return the current depth for a quantifier (0 if not yet instantiated)
    pub fn current_depth(&self, quantifier: TermId) -> u32 {
        self.depth_tracking.get(&quantifier).copied().unwrap_or(0)
    }

    /// Check whether the depth limit permits another instantiation
    fn depth_allows(&self, quantifier: TermId) -> bool {
        if self.max_depth == 0 {
            return true; // unlimited
        }
        self.current_depth(quantifier) < self.max_depth
    }

    /// Increment the depth counter for a quantifier after a successful instantiation.
    pub fn increment_depth(&mut self, quantifier: TermId) {
        let entry = self.depth_tracking.entry(quantifier).or_insert(0);
        *entry = entry.saturating_add(1);
    }

    /// Generate instantiations for a quantifier using model-based approach
    pub fn instantiate_from_model(
        &mut self,
        quantifier: &QuantifiedFormula,
        model: &CompletedModel,
        manager: &mut TermManager,
    ) -> Vec<Instantiation> {
        self.stats.num_instantiation_attempts += 1;

        // Universal quantifiers only: for an existential, body[t/x] is not
        // entailed by (exists x. body), so emitting it as a lemma
        // over-constrains the solver and can flip SAT to UNSAT (same
        // rationale as the is_universal gate in mbqi::integration).
        if !quantifier.is_universal {
            return Vec::new();
        }

        // Depth-bound guard: skip entirely if this quantifier has already been
        // instantiated to the maximum allowed depth.
        if !self.depth_allows(quantifier.term) {
            return Vec::new();
        }

        let mut instantiations = Vec::new();

        // Generate counterexamples
        let cex_result = self.cex_generator.generate(quantifier, model, manager);

        // Convert counterexamples to instantiations
        for cex in cex_result.counterexamples {
            // Recheck depth inside the loop – a single MBQI round may produce
            // many counterexamples but we still want to cap the total.
            if !self.depth_allows(quantifier.term) {
                break;
            }

            // Apply substitution to get ground instance
            let ground_body = self.apply_substitution(quantifier.body, &cex.assignment, manager);

            let inst = cex.to_instantiation(ground_body);

            // Check for duplicates
            if self.is_duplicate(&inst) {
                self.stats.num_duplicates_filtered += 1;
                continue;
            }

            self.record_instantiation(&inst);
            self.increment_depth(quantifier.term);
            instantiations.push(inst);
        }

        self.stats.num_instantiations_generated += instantiations.len();
        instantiations
    }

    /// Generate instantiations using conflict-driven approach
    pub fn instantiate_from_conflict(
        &mut self,
        quantifier: &QuantifiedFormula,
        conflict: &[TermId],
        model: &CompletedModel,
        manager: &mut TermManager,
    ) -> Vec<Instantiation> {
        // Universal quantifiers only (see `instantiate_from_model`).
        if !quantifier.is_universal {
            return Vec::new();
        }

        // Depth-bound guard
        if !self.depth_allows(quantifier.term) {
            return Vec::new();
        }

        let mut instantiations = Vec::new();

        // Analyze the conflict to extract relevant terms
        let conflict_terms = self.extract_relevant_terms(conflict, manager);

        // Try to build instantiations from conflict terms
        for assignment in
            self.build_assignments_from_terms(&quantifier.bound_vars, &conflict_terms, manager)
        {
            if !self.depth_allows(quantifier.term) {
                break;
            }

            let ground_body = self.apply_substitution(quantifier.body, &assignment, manager);

            let inst = Instantiation::with_reason(
                quantifier.term,
                assignment,
                ground_body,
                model.generation,
                InstantiationReason::Conflict,
            );

            if !self.is_duplicate(&inst) {
                self.record_instantiation(&inst);
                self.increment_depth(quantifier.term);
                instantiations.push(inst);
            }
        }

        instantiations
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
    /// the whitelist was returned **unchanged** -- the whitelist covered 12 kinds, so
    /// `Xor`, `Distinct`, `Implies`, `Ite`, `Sub`/`Div`/`Mod`/`Neg`,
    /// `Gt`/`Ge`, every bit-vector, string, floating-point and datatype
    /// operator, and every binder fell through. A
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
    /// [`TermManager::substitute`]: nixie_core::ast::TermManager::substitute
    fn apply_substitution(
        &self,
        term: TermId,
        subst: &FxHashMap<Spur, TermId>,
        manager: &mut TermManager,
    ) -> TermId {
        crate::mbqi::macros::utils::substitute(term, subst, manager)
    }

    /// Extract relevant terms from a conflict clause.
    ///
    /// Explicit-stack pre-order walk (children pushed in reverse so they are
    /// visited left-to-right, preserving the retired recursion's collection
    /// order); the descent set (`Not`/`Neg`, `And`/`Or`, `Eq`/`Lt` sides,
    /// `Apply` args) is the deliberately bounded shape this heuristic draws
    /// witness values from, unchanged.
    fn extract_relevant_terms(&self, conflict: &[TermId], manager: &TermManager) -> Vec<TermId> {
        let mut terms = Vec::new();
        let mut visited: FxHashSet<TermId> = FxHashSet::default();
        let mut work: Vec<TermId> = Vec::new();

        for &root in conflict {
            work.push(root);
            while let Some(t_id) = work.pop() {
                if !visited.insert(t_id) {
                    continue;
                }

                let Some(t) = manager.get(t_id) else {
                    continue;
                };

                // Collect ground terms
                if self.is_ground_value(t_id, manager) {
                    terms.push(t_id);
                }

                match &t.kind {
                    TermKind::Not(arg) | TermKind::Neg(arg) => work.push(*arg),
                    TermKind::And(args) | TermKind::Or(args) => {
                        for &arg in args.iter().rev() {
                            work.push(arg);
                        }
                    }
                    TermKind::Eq(lhs, rhs) | TermKind::Lt(lhs, rhs) => {
                        work.push(*rhs);
                        work.push(*lhs);
                    }
                    TermKind::Apply { args, .. } => {
                        for &arg in args.iter().rev() {
                            work.push(arg);
                        }
                    }
                    _ => {}
                }
            }
        }

        terms
    }

    /// Check if a term is a ground value
    fn is_ground_value(&self, term: TermId, manager: &TermManager) -> bool {
        let Some(t) = manager.get(term) else {
            return false;
        };

        matches!(
            t.kind,
            TermKind::True
                | TermKind::False
                | TermKind::IntConst(_)
                | TermKind::RealConst(_)
                | TermKind::BitVecConst { .. }
        )
    }

    /// Build assignments from terms
    fn build_assignments_from_terms(
        &self,
        bound_vars: &[(Spur, SortId)],
        terms: &[TermId],
        manager: &TermManager,
    ) -> Vec<FxHashMap<Spur, TermId>> {
        let mut assignments = Vec::new();

        // Group terms by sort
        let mut terms_by_sort: FxHashMap<SortId, Vec<TermId>> = FxHashMap::default();
        for &term in terms {
            if let Some(t) = manager.get(term) {
                terms_by_sort.entry(t.sort).or_default().push(term);
            }
        }

        // Build candidate lists for each variable
        let mut candidates = Vec::new();
        for &(_name, sort) in bound_vars {
            let sort_terms = terms_by_sort
                .get(&sort)
                .map(|v| v.as_slice())
                .unwrap_or(&[]);
            candidates.push(sort_terms.to_vec());
        }

        // Enumerate combinations (limited)
        let max_combinations = 10;
        let mut indices = vec![0usize; bound_vars.len()];

        for _ in 0..max_combinations {
            let mut assignment = FxHashMap::default();
            let mut valid = true;

            for (i, &idx) in indices.iter().enumerate() {
                if let Some(cands) = candidates.get(i) {
                    if let Some(&term) = cands.get(idx) {
                        if let Some((name, _)) = bound_vars.get(i) {
                            assignment.insert(*name, term);
                        }
                    } else {
                        valid = false;
                        break;
                    }
                }
            }

            if valid && assignment.len() == bound_vars.len() {
                assignments.push(assignment);
            }

            // Increment indices
            let mut carry = true;
            for (i, idx) in indices.iter_mut().enumerate() {
                if carry {
                    *idx += 1;
                    let limit = candidates.get(i).map_or(1, |c| c.len());
                    if *idx >= limit {
                        *idx = 0;
                    } else {
                        carry = false;
                    }
                }
            }

            if carry {
                break;
            }
        }

        assignments
    }

    /// Check if an instantiation is a duplicate
    fn is_duplicate(&self, inst: &Instantiation) -> bool {
        let key = InstantiationKey::from_instantiation(inst);
        self.dedup_cache.contains(&key)
    }

    /// Record an instantiation for deduplication
    fn record_instantiation(&mut self, inst: &Instantiation) {
        let key = InstantiationKey::from_instantiation(inst);
        self.dedup_cache.insert(key);
    }

    /// Clear deduplication cache and reset depth counters
    pub fn clear_cache(&mut self) {
        self.dedup_cache.clear();
        self.depth_tracking.clear();
        self.cex_generator.clear_cache();
    }

    /// Get statistics
    pub fn stats(&self) -> &InstantiatorStats {
        &self.stats
    }
}

impl Default for QuantifierInstantiator {
    fn default() -> Self {
        Self::new()
    }
}

/// Key for instantiation deduplication
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
struct InstantiationKey {
    quantifier: TermId,
    binding: Vec<(Spur, TermId)>,
}

impl InstantiationKey {
    fn from_instantiation(inst: &Instantiation) -> Self {
        let mut binding: Vec<_> = inst.substitution.iter().map(|(&k, &v)| (k, v)).collect();
        binding.sort_by_key(|(k, _)| *k);
        Self {
            quantifier: inst.quantifier,
            binding,
        }
    }
}

/// Instantiation engine that coordinates all instantiation strategies
#[derive(Debug)]
pub struct InstantiationEngine {
    /// Main quantifier instantiator
    instantiator: QuantifierInstantiator,
    /// Pattern matcher
    pattern_matcher: PatternMatcher,
    /// Enumerative instantiation
    enumerative: EnumerativeInstantiator,
    /// Statistics
    stats: EngineStats,
}

impl InstantiationEngine {
    /// Create a new instantiation engine
    pub fn new() -> Self {
        Self {
            instantiator: QuantifierInstantiator::new(),
            pattern_matcher: PatternMatcher::new(),
            enumerative: EnumerativeInstantiator::new(),
            stats: EngineStats::default(),
        }
    }

    /// Generate instantiations for a quantifier.
    ///
    /// **Universal quantifiers only.** For an existential, `body[t/x]` is not
    /// entailed by `(exists x. body)`: asserting an arbitrary instance as a
    /// lemma over-constrains the solver and can flip SAT to UNSAT. The
    /// integration layer already refuses to route existentials here
    /// (`mbqi::integration` gates every call on `is_universal`); this check
    /// closes the same hole on the public API, where nothing else guards the
    /// pattern-based and enumerative strategies below.
    pub fn instantiate(
        &mut self,
        quantifier: &QuantifiedFormula,
        model: &CompletedModel,
        manager: &mut TermManager,
    ) -> Vec<Instantiation> {
        if !quantifier.is_universal {
            return Vec::new();
        }

        let mut instantiations = Vec::new();

        // Strategy 1: Model-based instantiation
        let model_based = self
            .instantiator
            .instantiate_from_model(quantifier, model, manager);
        instantiations.extend(model_based);

        // Strategy 2: Pattern-based instantiation (if patterns exist)
        if !quantifier.patterns.is_empty() {
            let pattern_based = self
                .pattern_matcher
                .match_patterns(quantifier, model, manager);
            instantiations.extend(pattern_based);
        }

        // Strategy 3: Enumerative instantiation (as fallback)
        if instantiations.is_empty() {
            let enumerative = self.enumerative.enumerate(quantifier, model, manager, 10);
            instantiations.extend(enumerative);
        }

        self.stats.num_instantiations += instantiations.len();
        instantiations
    }

    /// Clear all caches
    pub fn clear_caches(&mut self) {
        self.instantiator.clear_cache();
        self.pattern_matcher.clear_cache();
    }

    /// Get statistics
    pub fn stats(&self) -> &EngineStats {
        &self.stats
    }
}

impl Default for InstantiationEngine {
    fn default() -> Self {
        Self::new()
    }
}

/// Pattern matcher for E-matching style instantiation
#[derive(Debug)]
struct PatternMatcher {
    /// Match cache
    cache: FxHashMap<TermId, Vec<FxHashMap<Spur, TermId>>>,
}

impl PatternMatcher {
    fn new() -> Self {
        Self {
            cache: FxHashMap::default(),
        }
    }

    fn match_patterns(
        &mut self,
        quantifier: &QuantifiedFormula,
        model: &CompletedModel,
        manager: &mut TermManager,
    ) -> Vec<Instantiation> {
        let mut instantiations = Vec::new();

        // Extract patterns
        let patterns = InstantiationPattern::extract_patterns(quantifier, manager);

        // Match each pattern
        for pattern in patterns {
            let matches = self.match_pattern(&pattern, model, manager);
            for assignment in matches {
                let ground_body = self.apply_substitution(quantifier.body, &assignment, manager);
                let inst = Instantiation::with_reason(
                    quantifier.term,
                    assignment,
                    ground_body,
                    model.generation,
                    InstantiationReason::EMatching,
                );
                instantiations.push(inst);
            }
        }

        instantiations
    }

    fn match_pattern(
        &self,
        _pattern: &InstantiationPattern,
        _model: &CompletedModel,
        _manager: &TermManager,
    ) -> Vec<FxHashMap<Spur, TermId>> {
        // Simplified pattern matching
        // A full implementation would use E-matching algorithms
        Vec::new()
    }

    /// See [`QuantifierInstantiator::apply_substitution`]; both are the same
    /// call into [`utils::substitute`](crate::mbqi::macros::utils::substitute).
    fn apply_substitution(
        &self,
        term: TermId,
        subst: &FxHashMap<Spur, TermId>,
        manager: &mut TermManager,
    ) -> TermId {
        crate::mbqi::macros::utils::substitute(term, subst, manager)
    }

    fn clear_cache(&mut self) {
        self.cache.clear();
    }
}

/// Enumerative instantiator (brute-force small domain)
#[derive(Debug)]
struct EnumerativeInstantiator;

impl EnumerativeInstantiator {
    fn new() -> Self {
        Self
    }

    fn enumerate(
        &self,
        quantifier: &QuantifiedFormula,
        model: &CompletedModel,
        manager: &mut TermManager,
        max_per_var: usize,
    ) -> Vec<Instantiation> {
        let mut instantiations = Vec::new();

        // Build small domains for each variable
        let domains = self.build_small_domains(&quantifier.bound_vars, model, manager, max_per_var);

        // Enumerate all combinations
        let combinations = self.enumerate_combinations(&domains);

        for combo in combinations {
            let mut assignment = FxHashMap::default();
            for (i, &value) in combo.iter().enumerate() {
                if let Some((name, _)) = quantifier.bound_vars.get(i) {
                    assignment.insert(*name, value);
                }
            }

            let ground_body =
                crate::mbqi::macros::utils::substitute(quantifier.body, &assignment, manager);

            let inst = Instantiation::with_reason(
                quantifier.term,
                assignment,
                ground_body,
                model.generation,
                InstantiationReason::Enumerative,
            );
            instantiations.push(inst);
        }

        instantiations
    }

    fn build_small_domains(
        &self,
        bound_vars: &[(Spur, SortId)],
        model: &CompletedModel,
        manager: &mut TermManager,
        max_per_var: usize,
    ) -> Vec<Vec<TermId>> {
        let mut domains = Vec::new();

        for &(_name, sort) in bound_vars {
            let mut domain = Vec::new();

            // Use universe if available
            if let Some(universe) = model.universe(sort) {
                domain.extend_from_slice(universe);
            }

            // Add default integer candidates from -2 to 5
            if sort == manager.sorts.int_sort {
                for i in -2i64..=5 {
                    let val = manager.mk_int(BigInt::from(i));
                    if !domain.contains(&val) {
                        domain.push(val);
                    }
                }
            } else if sort == manager.sorts.bool_sort {
                domain.push(manager.mk_true());
                domain.push(manager.mk_false());
            }

            domain.truncate(max_per_var);
            domains.push(domain);
        }

        domains
    }

    fn enumerate_combinations(&self, domains: &[Vec<TermId>]) -> Vec<Vec<TermId>> {
        if domains.is_empty() {
            return vec![vec![]];
        }

        let mut results = Vec::new();
        let mut indices = vec![0usize; domains.len()];
        let max_results = 100; // Limit total combinations

        loop {
            let combo: Vec<TermId> = indices
                .iter()
                .enumerate()
                .filter_map(|(i, &idx)| domains.get(i).and_then(|d| d.get(idx).copied()))
                .collect();

            if combo.len() == domains.len() {
                results.push(combo);
            }

            if results.len() >= max_results {
                break;
            }

            // Increment
            let mut carry = true;
            for (i, idx) in indices.iter_mut().enumerate() {
                if carry {
                    *idx += 1;
                    let limit = domains.get(i).map_or(1, |d| d.len());
                    if *idx >= limit {
                        *idx = 0;
                    } else {
                        carry = false;
                    }
                }
            }

            if carry {
                break;
            }
        }

        results
    }
}

/// Statistics for instantiator
#[derive(Debug, Clone, Default)]
pub struct InstantiatorStats {
    pub num_instantiation_attempts: usize,
    pub num_instantiations_generated: usize,
    pub num_duplicates_filtered: usize,
}

/// Statistics for engine
#[derive(Debug, Clone, Default)]
pub struct EngineStats {
    pub num_instantiations: usize,
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

    /// Every instantiation the public [`InstantiationEngine::instantiate`]
    /// emits must actually be an instance: ground, with the bound variable
    /// replaced by the recorded witness.
    ///
    /// This is the reproduction at the public boundary. For
    /// `(forall ((x Bool)) (xor x (not x)))` the engine used to return two
    /// instantiations -- one for `x := true`, one for `x := false` -- whose
    /// `result` was the *quantifier body itself*, still containing `x` free,
    /// because `Xor` was outside `apply_substitution`'s whitelist. Since a
    /// declared constant and a bound variable share the `TermKind::Var`
    /// representation, that lemma silently constrains whatever global constant
    /// happens to be named `x`. `MBQIIntegration` feeds these results straight
    /// into `all_instantiations` with no groundedness guard of its own.
    #[test]
    fn instantiation_engine_emits_only_real_instances() {
        let mut m = TermManager::new();
        let bool_sort = m.sorts.bool_sort;
        let x = m.mk_var("x", bool_sort);
        let not_x = m.mk_not(x);
        let body = m.mk_xor(x, not_x);
        let q_term = m.mk_forall([("x", bool_sort)], body);
        let x_name = match m.get(x).map(|t| &t.kind) {
            Some(TermKind::Var(n)) => *n,
            _ => panic!("x is a variable"),
        };
        let qf = QuantifiedFormula::new(
            q_term,
            core::iter::once((x_name, bool_sort)).collect(),
            body,
            true,
        );

        let model = CompletedModel::new();
        let mut engine = InstantiationEngine::new();
        let insts = engine.instantiate(&qf, &model, &mut m);

        assert!(
            !insts.is_empty(),
            "the Bool domain is enumerated, so instances are expected"
        );
        for inst in &insts {
            let free = m.free_vars_including_patterns(inst.result);
            assert!(
                free.is_empty(),
                "instantiation {:?} left {free:?} free -- not an instance",
                inst.substitution
            );
        }
    }

    /// The engine must refuse to instantiate an existential quantifier:
    /// `body[t/x]` is not entailed by `(exists x. body)`. The identical
    /// setup with `is_universal = true` (the test above) produces
    /// instantiations, so the empty result here is the gate, not a vacuity.
    #[test]
    fn instantiation_engine_refuses_existential_quantifiers() {
        let mut m = TermManager::new();
        let bool_sort = m.sorts.bool_sort;
        let x = m.mk_var("x", bool_sort);
        let not_x = m.mk_not(x);
        let body = m.mk_xor(x, not_x);
        let q_term = m.mk_exists([("x", bool_sort)], body);
        let x_name = match m.get(x).map(|t| &t.kind) {
            Some(TermKind::Var(n)) => *n,
            _ => panic!("x is a variable"),
        };
        let qf = QuantifiedFormula::new(
            q_term,
            core::iter::once((x_name, bool_sort)).collect(),
            body,
            false,
        );

        let model = CompletedModel::new();
        let mut engine = InstantiationEngine::new();
        let insts = engine.instantiate(&qf, &model, &mut m);
        assert!(
            insts.is_empty(),
            "an existential must never be instantiated, got {insts:?}"
        );

        // The lower-level instantiators are public API too and carry the
        // same gate.
        let mut instantiator = QuantifierInstantiator::new();
        assert!(
            instantiator
                .instantiate_from_model(&qf, &model, &mut m)
                .is_empty()
        );
        assert!(
            instantiator
                .instantiate_from_conflict(&qf, &[], &model, &mut m)
                .is_empty()
        );
    }

    /// `InstantiationPattern::collect_vars` used to descend only
    /// `Apply`/`Not`/`Neg`/`And`/`Or` and silently drop every other kind, so
    /// variables under `Eq`, `Distinct`, bit-vector or arithmetic operators
    /// were never counted and the variable-bearing pattern was discarded.
    #[test]
    fn pattern_collect_vars_sees_all_kinds_and_respects_binders() {
        let mut m = TermManager::new();
        let int_sort = m.sorts.int_sort;
        let bool_sort = m.sorts.bool_sort;
        let bv8 = m.sorts.bitvec(8);

        let i = m.mk_var("i", int_sort);
        let b = m.mk_var("b", bv8);
        let two = m.mk_int(2);
        let ones = m.mk_bitvec(1, 8);

        // Both kinds were outside the old whitelist.
        let distinct = m.mk_distinct([i, two]);
        let bv_lt = m.mk_bv_ult(b, ones);

        let mut pattern = InstantiationPattern::new(vec![distinct, bv_lt]);
        pattern.collect_vars(&m);
        assert_eq!(
            pattern.num_vars, 2,
            "i (under Distinct) and b (under BvUlt) must both be collected"
        );

        // A variable bound by a nested binder is not matchable from outside
        // and must not be collected; the free y must be.
        let z = m.mk_var("z", int_sort);
        let y = m.mk_var("y", int_sort);
        let p = m.mk_apply("P", [z, y], bool_sort);
        let nested = m.mk_forall([("z", int_sort)], p);
        let mut pattern = InstantiationPattern::new(vec![nested]);
        pattern.collect_vars(&m);
        let y_name = match m.get(y).map(|t| &t.kind) {
            Some(TermKind::Var(n)) => *n,
            _ => panic!("y is a variable"),
        };
        assert_eq!(pattern.num_vars, 1);
        assert!(pattern.vars.contains(&y_name));
    }

    /// Run `f` on a dedicated 128 KiB stack: overflow aborts the process, so
    /// returning at all is part of the assertion.
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

    /// The candidate and relevant-term collectors must survive 12 500-deep
    /// terms on a tiny stack (the old recursion overflowed).
    #[test]
    fn collectors_survive_deep_terms_on_a_tiny_stack() {
        const DEPTH: usize = 12_500;
        run_on_small_stack(|| {
            let mut m = TermManager::new();
            let int_sort = m.sorts.int_sort;
            let x = m.mk_var("x", int_sort);
            let mut chain = x;
            for _ in 0..DEPTH {
                chain = m.mk_apply("f", [chain], int_sort);
            }

            let candidates = InstantiationPattern::collect_pattern_candidates(chain, &m);
            assert_eq!(
                candidates.len(),
                DEPTH,
                "every f-application is a candidate"
            );

            let instantiator = QuantifierInstantiator::new();
            let relevant = instantiator.extract_relevant_terms(&[chain], &m);
            // No ground values anywhere in the chain (x is a variable).
            assert!(relevant.is_empty());
        });
    }

    /// Candidate collection order is pre-order left-to-right; pinned so the
    /// iterative conversion is proven behavior-preserving.
    #[test]
    fn candidate_collection_preserves_preorder() {
        let mut m = TermManager::new();
        let int_sort = m.sorts.int_sort;
        let x = m.mk_var("x", int_sort);
        let g_x = m.mk_apply("g", [x], int_sort);
        let h_x = m.mk_apply("h", [x], int_sort);
        let f = m.mk_apply("f", [g_x, h_x], int_sort);

        let candidates = InstantiationPattern::collect_pattern_candidates(f, &m);
        assert_eq!(candidates, vec![f, g_x, h_x]);
    }

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

        let subject = QuantifierInstantiator::new();
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
    use nixie_core::interner::Key;

    #[test]
    fn test_instantiation_context_creation() {
        let manager = TermManager::new();
        let ctx = InstantiationContext::new(manager);
        assert_eq!(ctx.generation, 0);
    }

    #[test]
    fn test_instantiation_context_generation() {
        let manager = TermManager::new();
        let mut ctx = InstantiationContext::new(manager);
        ctx.next_generation();
        assert_eq!(ctx.generation, 1);
    }

    #[test]
    fn test_instantiation_pattern_creation() {
        let pattern = InstantiationPattern::new(vec![TermId::new(1)]);
        assert_eq!(pattern.terms.len(), 1);
        assert_eq!(pattern.num_vars, 0);
    }

    #[test]
    fn test_quantifier_instantiator_creation() {
        let inst = QuantifierInstantiator::new();
        assert_eq!(inst.stats.num_instantiation_attempts, 0);
    }

    #[test]
    fn test_instantiation_key_equality() {
        let key1 = InstantiationKey {
            quantifier: TermId::new(1),
            binding: vec![(
                Spur::try_from_usize(1).expect("valid spur"),
                TermId::new(10),
            )],
        };
        let key2 = InstantiationKey {
            quantifier: TermId::new(1),
            binding: vec![(
                Spur::try_from_usize(1).expect("valid spur"),
                TermId::new(10),
            )],
        };
        assert_eq!(key1, key2);
    }

    #[test]
    fn test_instantiation_engine_creation() {
        let engine = InstantiationEngine::new();
        assert_eq!(engine.stats.num_instantiations, 0);
    }

    #[test]
    fn test_pattern_matcher_creation() {
        let matcher = PatternMatcher::new();
        assert_eq!(matcher.cache.len(), 0);
    }

    #[test]
    fn test_enumerative_instantiator_creation() {
        let _enum_inst = EnumerativeInstantiator::new();
    }
}
