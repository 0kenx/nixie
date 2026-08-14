//! Conflict-Driven Quantifier Instantiation (CDQI)
//!
//! When theory conflicts involve quantified formulas, this module extracts
//! relevant instances from conflict analysis and uses conflict clause
//! participation to guide which quantifier instances to add.
//!
//! Key ideas:
//! - Analyze conflict clauses to extract terms relevant to quantified formulas
//! - Score quantifier instances by how often they participate in conflicts
//! - Prioritize instances that are likely to resolve or contribute to conflicts
//! - Keep a relevance score that decays over time (activity-style aging)

#![allow(missing_docs)]
#![allow(dead_code)]

#[allow(unused_imports)]
use crate::prelude::*;
use oxiz_core::ast::{TermId, TermKind, TermManager};
use oxiz_core::interner::Spur;
use oxiz_core::sort::SortId;

use super::model_completion::CompletedModel;
use super::{Instantiation, InstantiationReason, QuantifiedFormula, QuantifierId};

/// Configuration for conflict-driven instantiation
#[derive(Debug, Clone)]
pub struct CDQIConfig {
    /// Maximum instances to generate per conflict
    pub max_instances_per_conflict: usize,
    /// Relevance decay factor (0..1, higher = slower decay)
    pub relevance_decay: f64,
    /// Minimum relevance score to keep tracking
    pub min_relevance_threshold: f64,
    /// Maximum tracked instances (memory limit)
    pub max_tracked_instances: usize,
    /// Enable conflict generalization
    pub generalize_conflicts: bool,
    /// Bonus score for instances matching conflict variables
    pub conflict_variable_bonus: f64,
}

impl Default for CDQIConfig {
    fn default() -> Self {
        Self {
            max_instances_per_conflict: 10,
            relevance_decay: 0.95,
            min_relevance_threshold: 0.01,
            max_tracked_instances: 10000,
            generalize_conflicts: true,
            conflict_variable_bonus: 2.0,
        }
    }
}

/// A tracked instance with relevance scoring
#[derive(Debug, Clone)]
pub struct TrackedInstance {
    /// The quantifier this instance belongs to
    pub quantifier: TermId,
    /// The substitution
    pub substitution: FxHashMap<Spur, TermId>,
    /// The ground body
    pub result: TermId,
    /// Relevance score (activity-style, decays over time)
    pub relevance_score: f64,
    /// Number of conflicts this instance participated in
    pub conflict_count: u64,
    /// Generation when this instance was created
    pub creation_generation: u32,
    /// Last conflict generation this participated in
    pub last_conflict_generation: u32,
}

impl TrackedInstance {
    /// Create a new tracked instance
    pub fn new(
        quantifier: TermId,
        substitution: FxHashMap<Spur, TermId>,
        result: TermId,
        generation: u32,
    ) -> Self {
        Self {
            quantifier,
            substitution,
            result,
            relevance_score: 1.0,
            conflict_count: 0,
            creation_generation: generation,
            last_conflict_generation: 0,
        }
    }

    /// Bump the relevance score when participating in a conflict
    pub fn bump_relevance(&mut self, bonus: f64, generation: u32) {
        self.relevance_score += bonus;
        self.conflict_count += 1;
        self.last_conflict_generation = generation;
    }

    /// Apply decay to the relevance score
    pub fn decay(&mut self, factor: f64) {
        self.relevance_score *= factor;
    }

    /// Convert to an Instantiation
    pub fn to_instantiation(&self) -> Instantiation {
        Instantiation::with_reason(
            self.quantifier,
            self.substitution.clone(),
            self.result,
            self.creation_generation,
            InstantiationReason::Conflict,
        )
    }
}

/// Conflict analysis result
#[derive(Debug, Clone)]
pub struct ConflictAnalysis {
    /// Terms involved in the conflict
    pub conflict_terms: Vec<TermId>,
    /// Variables (bound variable names) that appear in the conflict
    pub conflict_variables: FxHashSet<Spur>,
    /// Ground values found in the conflict
    pub ground_values: FxHashMap<SortId, Vec<TermId>>,
    /// Quantifiers potentially related to the conflict
    pub related_quantifiers: Vec<TermId>,
}

/// VSIDS-style conflict activity scores for quantifiers.
#[derive(Debug, Clone)]
pub struct ConflictScores {
    /// Integer activity score by quantifier.
    pub scores: HashMap<QuantifierId, u32>,
    /// Multiplicative decay factor applied on restart.
    pub decay_factor: f64,
}

impl ConflictScores {
    /// Create a new score table.
    pub fn new(decay_factor: f64) -> Self {
        Self {
            scores: HashMap::new(),
            decay_factor,
        }
    }

    /// Record a conflict for one quantifier.
    pub fn record_conflict(&mut self, qid: QuantifierId) {
        let entry = self.scores.entry(qid).or_insert(0);
        *entry = entry.saturating_add(1);
    }

    /// Apply decay to all scores on restart.
    pub fn decay_on_restart(&mut self) {
        for score in self.scores.values_mut() {
            *score = ((*score as f64) * self.decay_factor).round() as u32;
        }
    }

    /// Return quantifiers in descending priority order.
    pub fn priority_order(&self) -> Vec<QuantifierId> {
        let mut ordered: Vec<_> = self
            .scores
            .iter()
            .map(|(&qid, &score)| (qid, score))
            .collect();
        ordered.sort_by(|(lhs_qid, lhs_score), (rhs_qid, rhs_score)| {
            rhs_score.cmp(lhs_score).then_with(|| lhs_qid.cmp(rhs_qid))
        });
        ordered.into_iter().map(|(qid, _)| qid).collect()
    }

    /// Read one score.
    pub fn score(&self, qid: QuantifierId) -> Option<u32> {
        self.scores.get(&qid).copied()
    }
}

/// Conflict-driven quantifier instantiation engine
#[derive(Debug)]
pub struct ConflictDrivenInstantiator {
    /// Configuration
    config: CDQIConfig,
    /// Tracked instances with relevance scores
    tracked_instances: Vec<TrackedInstance>,
    /// Index: quantifier -> tracked instance indices
    quantifier_index: FxHashMap<TermId, Vec<usize>>,
    /// Deduplication: (quantifier, sorted binding) -> index
    dedup: FxHashMap<(TermId, Vec<(Spur, TermId)>), usize>,
    /// Current generation counter
    generation: u32,
    /// Quantifier conflict activity
    conflict_scores: ConflictScores,
    /// Statistics
    stats: CDQIStats,
}

/// Statistics for conflict-driven instantiation
#[derive(Debug, Clone, Default)]
pub struct CDQIStats {
    /// Total conflicts analyzed
    pub conflicts_analyzed: u64,
    /// Total instances generated from conflicts
    pub instances_from_conflicts: u64,
    /// Total relevance bumps
    pub relevance_bumps: u64,
    /// Total instances pruned (below threshold)
    pub instances_pruned: u64,
    /// Total decay rounds
    pub decay_rounds: u64,
    /// Peak tracked instances
    pub peak_tracked: usize,
}

impl ConflictDrivenInstantiator {
    /// Create a new conflict-driven instantiator
    pub fn new(config: CDQIConfig) -> Self {
        let relevance_decay = config.relevance_decay;
        Self {
            config,
            tracked_instances: Vec::new(),
            quantifier_index: FxHashMap::default(),
            dedup: FxHashMap::default(),
            generation: 0,
            conflict_scores: ConflictScores::new(relevance_decay),
            stats: CDQIStats::default(),
        }
    }

    /// Create with default config
    pub fn default_config() -> Self {
        Self::new(CDQIConfig::default())
    }

    /// Analyze a conflict and generate relevant instantiations.
    ///
    /// When a theory conflict is detected, this method:
    /// 1. Extracts terms and ground values from the conflict clause
    /// 2. Identifies which quantifiers are relevant
    /// 3. Builds instantiations using conflict terms as witnesses
    /// 4. Bumps relevance of existing instances that match conflict terms
    pub fn analyze_conflict(
        &mut self,
        conflict_clause: &[TermId],
        quantifiers: &[QuantifiedFormula],
        model: &CompletedModel,
        manager: &mut TermManager,
    ) -> Vec<Instantiation> {
        self.generation += 1;
        self.stats.conflicts_analyzed += 1;

        // Step 1: Analyze the conflict
        let analysis = self.extract_conflict_info(conflict_clause, quantifiers, manager);
        for &qid in &analysis.related_quantifiers {
            self.conflict_scores.record_conflict(qid);
        }

        // Step 2: Bump relevance of existing instances that match
        self.bump_matching_instances(&analysis);

        // Step 3: Generate new instances from conflict
        let new_instances =
            self.generate_instances_from_conflict(&analysis, quantifiers, model, manager);

        // Step 4: Apply decay to all tracked instances
        self.apply_decay();

        // Step 5: Prune low-relevance instances
        self.prune_low_relevance();

        new_instances
    }

    /// Apply restart-style decay to quantifier conflict activity.
    pub fn decay_on_restart(&mut self) {
        self.conflict_scores.decay_on_restart();
    }

    /// Access the quantifier conflict scores.
    pub fn conflict_scores(&self) -> &ConflictScores {
        &self.conflict_scores
    }

    /// Extract information from a conflict clause
    fn extract_conflict_info(
        &self,
        conflict_clause: &[TermId],
        quantifiers: &[QuantifiedFormula],
        manager: &TermManager,
    ) -> ConflictAnalysis {
        let mut analysis = ConflictAnalysis {
            conflict_terms: Vec::new(),
            conflict_variables: FxHashSet::default(),
            ground_values: FxHashMap::default(),
            related_quantifiers: Vec::new(),
        };

        // Collect all terms and ground values from the conflict
        let mut visited = FxHashSet::default();
        for &term in conflict_clause {
            self.collect_conflict_terms(term, &mut analysis, &mut visited, manager);
        }

        // Find quantifiers whose body terms overlap with conflict terms
        let conflict_set: FxHashSet<TermId> = analysis.conflict_terms.iter().copied().collect();
        for qf in quantifiers {
            if self.quantifier_overlaps_conflict(qf, &conflict_set, manager) {
                analysis.related_quantifiers.push(qf.term);
            }
        }

        analysis
    }

    /// Collect terms from a conflict clause.
    ///
    /// Explicit-stack pre-order walk (children pushed in reverse so they are
    /// visited left-to-right, preserving the retired recursion's collection
    /// order exactly); no input depth can overflow the call stack. The
    /// descent set is unchanged: kinds outside it are recorded as conflict
    /// terms but deliberately not descended by this heuristic.
    fn collect_conflict_terms(
        &self,
        term: TermId,
        analysis: &mut ConflictAnalysis,
        visited: &mut FxHashSet<TermId>,
        manager: &TermManager,
    ) {
        let mut work = vec![term];
        while let Some(t_id) = work.pop() {
            if !visited.insert(t_id) {
                continue;
            }
            analysis.conflict_terms.push(t_id);

            let Some(t) = manager.get(t_id) else {
                continue;
            };

            // Collect ground values by sort
            match &t.kind {
                TermKind::IntConst(_) | TermKind::RealConst(_) | TermKind::BitVecConst { .. } => {
                    analysis.ground_values.entry(t.sort).or_default().push(t_id);
                }
                TermKind::True | TermKind::False => {
                    analysis.ground_values.entry(t.sort).or_default().push(t_id);
                }
                TermKind::Var(name) => {
                    analysis.conflict_variables.insert(*name);
                }
                _ => {}
            }

            // Descend
            match &t.kind {
                TermKind::Not(a) | TermKind::Neg(a) => work.push(*a),
                TermKind::And(args) | TermKind::Or(args) => {
                    for &a in args.iter().rev() {
                        work.push(a);
                    }
                }
                TermKind::Eq(l, r)
                | TermKind::Lt(l, r)
                | TermKind::Le(l, r)
                | TermKind::Gt(l, r)
                | TermKind::Ge(l, r)
                | TermKind::Implies(l, r)
                | TermKind::Sub(l, r)
                | TermKind::Div(l, r)
                | TermKind::Mod(l, r) => {
                    work.push(*r);
                    work.push(*l);
                }
                TermKind::Add(args) | TermKind::Mul(args) => {
                    for &a in args.iter().rev() {
                        work.push(a);
                    }
                }
                TermKind::Ite(c, t_br, e_br) => {
                    work.push(*e_br);
                    work.push(*t_br);
                    work.push(*c);
                }
                TermKind::Apply { args, .. } => {
                    for &a in args.iter().rev() {
                        work.push(a);
                    }
                }
                TermKind::Select(arr, idx) => {
                    work.push(*idx);
                    work.push(*arr);
                }
                TermKind::Store(arr, idx, val) => {
                    work.push(*val);
                    work.push(*idx);
                    work.push(*arr);
                }
                _ => {}
            }
        }
    }

    /// Check if a quantifier's body overlaps with conflict terms
    fn quantifier_overlaps_conflict(
        &self,
        qf: &QuantifiedFormula,
        conflict_set: &FxHashSet<TermId>,
        manager: &TermManager,
    ) -> bool {
        // Check if any function symbols in the quantifier body appear in the conflict
        let body_funcs = self.collect_function_symbols(qf.body, manager);
        let conflict_funcs: FxHashSet<Spur> = conflict_set
            .iter()
            .flat_map(|&t| self.collect_function_symbols(t, manager))
            .collect();

        body_funcs.intersection(&conflict_funcs).next().is_some()
    }

    /// Collect function symbol names from a term.
    ///
    /// Explicit-stack walk with a visited set (the output is a set, so
    /// traversal order is irrelevant); no input depth can overflow the call
    /// stack. The descent set (`Apply` args, `Not`/`Neg`, `And`/`Or`,
    /// `Eq`/`Lt`/`Le`/`Implies` sides) is the retired recursion's, unchanged.
    fn collect_function_symbols(&self, term: TermId, manager: &TermManager) -> FxHashSet<Spur> {
        let mut symbols = FxHashSet::default();
        let mut visited: FxHashSet<TermId> = FxHashSet::default();
        let mut work = vec![term];
        while let Some(t_id) = work.pop() {
            if !visited.insert(t_id) {
                continue;
            }

            let Some(t) = manager.get(t_id) else {
                continue;
            };

            if let TermKind::Apply { func, args } = &t.kind {
                symbols.insert(*func);
                for &a in args.iter() {
                    work.push(a);
                }
            }

            match &t.kind {
                TermKind::Not(a) | TermKind::Neg(a) => work.push(*a),
                TermKind::And(args) | TermKind::Or(args) => {
                    for &a in args {
                        work.push(a);
                    }
                }
                TermKind::Eq(l, r)
                | TermKind::Lt(l, r)
                | TermKind::Le(l, r)
                | TermKind::Implies(l, r) => {
                    work.push(*l);
                    work.push(*r);
                }
                _ => {}
            }
        }
        symbols
    }

    /// Bump relevance of tracked instances that match the conflict
    fn bump_matching_instances(&mut self, analysis: &ConflictAnalysis) {
        let conflict_set: FxHashSet<TermId> = analysis.conflict_terms.iter().copied().collect();
        let bonus = self.config.conflict_variable_bonus;
        let current_gen = self.generation;

        for inst in &mut self.tracked_instances {
            // Check if this instance's result term appears in the conflict
            if conflict_set.contains(&inst.result) {
                inst.bump_relevance(bonus, current_gen);
                self.stats.relevance_bumps += 1;
            }
            // Check if any substitution value appears in the conflict
            for &val in inst.substitution.values() {
                if conflict_set.contains(&val) {
                    inst.bump_relevance(bonus * 0.5, current_gen);
                    self.stats.relevance_bumps += 1;
                    break; // only bump once per instance for sub values
                }
            }
        }
    }

    /// Generate new instances from conflict analysis
    fn generate_instances_from_conflict(
        &mut self,
        analysis: &ConflictAnalysis,
        quantifiers: &[QuantifiedFormula],
        model: &CompletedModel,
        manager: &mut TermManager,
    ) -> Vec<Instantiation> {
        let mut new_instances = Vec::new();

        for qf in quantifiers {
            if !qf.can_instantiate() || !qf.is_universal {
                continue;
            }

            // Only instantiate quantifiers related to the conflict
            if !analysis.related_quantifiers.contains(&qf.term) {
                continue;
            }

            // Build assignments from conflict ground values
            let assignments = self.build_conflict_assignments(qf, analysis, model, manager);

            for assignment in assignments {
                if new_instances.len() >= self.config.max_instances_per_conflict {
                    break;
                }

                // Check deduplication
                let binding_key = Self::make_binding_key(&assignment, qf);
                let dedup_key = (qf.term, binding_key.clone());
                if self.dedup.contains_key(&dedup_key) {
                    continue;
                }

                let ground_body = self.apply_substitution(qf.body, &assignment, manager);

                // Skip tautologies
                if manager
                    .get(ground_body)
                    .is_some_and(|t| matches!(t.kind, TermKind::True))
                {
                    continue;
                }

                let inst = Instantiation::with_reason(
                    qf.term,
                    assignment.clone(),
                    ground_body,
                    self.generation,
                    InstantiationReason::Conflict,
                );

                // Track the instance
                let tracked =
                    TrackedInstance::new(qf.term, assignment, ground_body, self.generation);
                let idx = self.tracked_instances.len();
                self.tracked_instances.push(tracked);
                self.quantifier_index.entry(qf.term).or_default().push(idx);
                self.dedup.insert(dedup_key, idx);

                if self.tracked_instances.len() > self.stats.peak_tracked {
                    self.stats.peak_tracked = self.tracked_instances.len();
                }

                new_instances.push(inst);
                self.stats.instances_from_conflicts += 1;
            }
        }

        new_instances
    }

    /// Build assignments from conflict ground values
    fn build_conflict_assignments(
        &self,
        qf: &QuantifiedFormula,
        analysis: &ConflictAnalysis,
        model: &CompletedModel,
        _manager: &TermManager,
    ) -> Vec<FxHashMap<Spur, TermId>> {
        let mut assignments = Vec::new();

        // For each bound variable, collect candidate values from:
        // 1. Ground values in the conflict that match the sort
        // 2. Model values for the sort
        let mut candidates_per_var: Vec<Vec<TermId>> = Vec::new();

        for &(name, sort) in &qf.bound_vars {
            let mut cands = Vec::new();

            // Priority 1: values from conflict
            if let Some(conflict_vals) = analysis.ground_values.get(&sort) {
                cands.extend_from_slice(conflict_vals);
            }

            // Priority 2: values from model universe
            if let Some(universe) = model.universe(sort) {
                for &val in universe {
                    if !cands.contains(&val) {
                        cands.push(val);
                    }
                }
            }

            // Limit candidates
            cands.truncate(self.config.max_instances_per_conflict);
            candidates_per_var.push(cands);

            // Store the variable name for assignment building
            let _ = name;
        }

        // If any variable has no candidates, return empty
        if candidates_per_var.iter().any(|c| c.is_empty()) {
            return assignments;
        }

        // Enumerate combinations (limited)
        let max_combos = self.config.max_instances_per_conflict;
        let mut indices = vec![0usize; qf.bound_vars.len()];

        for _ in 0..max_combos {
            let mut assignment = FxHashMap::default();
            let mut valid = true;

            for (i, &idx) in indices.iter().enumerate() {
                if let Some(cands) = candidates_per_var.get(i) {
                    if let Some(&val) = cands.get(idx) {
                        let (name, _) = qf.bound_vars[i];
                        assignment.insert(name, val);
                    } else {
                        valid = false;
                        break;
                    }
                }
            }

            if valid && assignment.len() == qf.bound_vars.len() {
                assignments.push(assignment);
            }

            // Increment indices (odometer)
            let mut carry = true;
            for (i, idx) in indices.iter_mut().enumerate() {
                if carry {
                    *idx += 1;
                    let limit = candidates_per_var.get(i).map_or(1, |c| c.len());
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

    /// Make a sorted binding key for deduplication
    fn make_binding_key(
        assignment: &FxHashMap<Spur, TermId>,
        _qf: &QuantifiedFormula,
    ) -> Vec<(Spur, TermId)> {
        let mut key: Vec<_> = assignment.iter().map(|(&k, &v)| (k, v)).collect();
        key.sort_by_key(|(k, _)| *k);
        key
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
    /// the whitelist was returned **unchanged** -- the whitelist covered 19 kinds, so
    /// `Xor`, `Distinct`, every bit-vector, string, floating-point and
    /// datatype operator, and every binder fell through. A
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

    /// Apply decay to all tracked instances
    fn apply_decay(&mut self) {
        let factor = self.config.relevance_decay;
        for inst in &mut self.tracked_instances {
            inst.decay(factor);
        }
        self.stats.decay_rounds += 1;
    }

    /// Prune instances with relevance below threshold
    fn prune_low_relevance(&mut self) {
        let threshold = self.config.min_relevance_threshold;
        let max = self.config.max_tracked_instances;

        if self.tracked_instances.len() <= max {
            return;
        }

        // Remove low-relevance instances
        let before = self.tracked_instances.len();
        self.tracked_instances
            .retain(|inst| inst.relevance_score >= threshold);
        self.stats.instances_pruned += (before - self.tracked_instances.len()) as u64;

        // Rebuild indices
        self.rebuild_indices();
    }

    /// Rebuild internal indices after pruning
    fn rebuild_indices(&mut self) {
        self.quantifier_index.clear();
        self.dedup.clear();

        for (idx, inst) in self.tracked_instances.iter().enumerate() {
            self.quantifier_index
                .entry(inst.quantifier)
                .or_default()
                .push(idx);

            let mut binding: Vec<_> = inst.substitution.iter().map(|(&k, &v)| (k, v)).collect();
            binding.sort_by_key(|(k, _)| *k);
            self.dedup.insert((inst.quantifier, binding), idx);
        }
    }

    /// Get the top-N most relevant instances for a quantifier
    pub fn top_relevant_instances(&self, quantifier: TermId, n: usize) -> Vec<&TrackedInstance> {
        let Some(indices) = self.quantifier_index.get(&quantifier) else {
            return Vec::new();
        };

        let mut instances: Vec<&TrackedInstance> = indices
            .iter()
            .filter_map(|&idx| self.tracked_instances.get(idx))
            .collect();

        instances.sort_by(|a, b| {
            b.relevance_score
                .partial_cmp(&a.relevance_score)
                .unwrap_or(core::cmp::Ordering::Equal)
        });

        instances.truncate(n);
        instances
    }

    /// Get statistics
    pub fn stats(&self) -> &CDQIStats {
        &self.stats
    }

    /// Get current generation
    pub fn generation(&self) -> u32 {
        self.generation
    }

    /// Number of tracked instances
    pub fn num_tracked(&self) -> usize {
        self.tracked_instances.len()
    }

    /// Clear all state
    pub fn clear(&mut self) {
        self.tracked_instances.clear();
        self.quantifier_index.clear();
        self.dedup.clear();
        self.generation = 0;
    }
}

impl Default for ConflictDrivenInstantiator {
    fn default() -> Self {
        Self::default_config()
    }
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

        let subject = ConflictDrivenInstantiator::default_config();
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
    use oxiz_core::interner::Key;
    use smallvec::SmallVec;

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

    /// Conflict analysis must survive a 12 500-deep conflict term on a tiny
    /// stack (the old recursion overflowed), through the public entry point.
    #[test]
    fn conflict_analysis_survives_deep_terms_on_a_tiny_stack() {
        const DEPTH: usize = 12_500;
        run_on_small_stack(|| {
            let mut manager = TermManager::new();
            let int_sort = manager.sorts.int_sort;
            let forty_two = manager.mk_int(42);
            let mut chain = forty_two;
            for _ in 0..DEPTH {
                chain = manager.mk_apply("f", [chain], int_sort);
            }

            let mut cdqi = ConflictDrivenInstantiator::default_config();
            let model = CompletedModel::new();
            let result = cdqi.analyze_conflict(&[chain], &[], &model, &mut manager);
            assert!(result.is_empty(), "no quantifiers, so no instances");

            // The private symbol collector shares the same shape; exercise
            // it directly as well.
            let symbols = cdqi.collect_function_symbols(chain, &manager);
            assert_eq!(symbols.len(), 1, "only the symbol f occurs");
        });
    }

    /// Pin the exact traversal artifacts of `collect_conflict_terms` --
    /// pre-order term order, ground values by sort, and conflict variables
    /// -- so the iterative conversion is proven behavior-preserving.
    #[test]
    fn collect_conflict_terms_preserves_preorder_and_classification() {
        let mut manager = TermManager::new();
        let int_sort = manager.sorts.int_sort;
        let bool_sort = manager.sorts.bool_sort;

        let cond = manager.mk_var("c", bool_sort);
        let a = manager.mk_var("a", int_sort);
        let forty_two = manager.mk_int(42);
        let ite = manager.mk_ite(cond, a, forty_two);

        let cdqi = ConflictDrivenInstantiator::default_config();
        let mut analysis = ConflictAnalysis {
            conflict_terms: Vec::new(),
            conflict_variables: FxHashSet::default(),
            ground_values: FxHashMap::default(),
            related_quantifiers: Vec::new(),
        };
        let mut visited = FxHashSet::default();
        cdqi.collect_conflict_terms(ite, &mut analysis, &mut visited, &manager);

        assert_eq!(
            analysis.conflict_terms,
            vec![ite, cond, a, forty_two],
            "pre-order, children left to right"
        );
        assert_eq!(
            analysis.conflict_variables.len(),
            2,
            "c and a are variables"
        );
        assert_eq!(
            analysis.ground_values.get(&int_sort).map(Vec::as_slice),
            Some(&[forty_two][..])
        );
    }

    fn make_qf(term_id: u32, body_id: u32, var_names: &[usize]) -> QuantifiedFormula {
        let bound_vars: SmallVec<[(Spur, SortId); 4]> = var_names
            .iter()
            .map(|&n| (Spur::try_from_usize(n).expect("valid spur"), SortId::new(0)))
            .collect();
        QuantifiedFormula::new(TermId::new(term_id), bound_vars, TermId::new(body_id), true)
    }

    #[test]
    fn test_cdqi_creation() {
        let cdqi = ConflictDrivenInstantiator::default_config();
        assert_eq!(cdqi.generation(), 0);
        assert_eq!(cdqi.num_tracked(), 0);
    }

    #[test]
    fn test_cdqi_config() {
        let config = CDQIConfig {
            max_instances_per_conflict: 5,
            relevance_decay: 0.9,
            ..Default::default()
        };
        let cdqi = ConflictDrivenInstantiator::new(config);
        assert_eq!(cdqi.config.max_instances_per_conflict, 5);
    }

    #[test]
    fn test_tracked_instance_creation() {
        let tracked = TrackedInstance::new(TermId::new(1), FxHashMap::default(), TermId::new(2), 0);
        assert_eq!(tracked.relevance_score, 1.0);
        assert_eq!(tracked.conflict_count, 0);
    }

    #[test]
    fn test_tracked_instance_bump() {
        let mut tracked =
            TrackedInstance::new(TermId::new(1), FxHashMap::default(), TermId::new(2), 0);
        tracked.bump_relevance(2.0, 1);
        assert_eq!(tracked.relevance_score, 3.0);
        assert_eq!(tracked.conflict_count, 1);
        assert_eq!(tracked.last_conflict_generation, 1);
    }

    #[test]
    fn test_tracked_instance_decay() {
        let mut tracked =
            TrackedInstance::new(TermId::new(1), FxHashMap::default(), TermId::new(2), 0);
        tracked.bump_relevance(9.0, 1); // score = 10.0
        tracked.decay(0.5);
        assert!((tracked.relevance_score - 5.0).abs() < 1e-6);
    }

    #[test]
    fn test_tracked_instance_to_instantiation() {
        let mut subst = FxHashMap::default();
        subst.insert(
            Spur::try_from_usize(1).expect("valid spur"),
            TermId::new(10),
        );
        let tracked = TrackedInstance::new(TermId::new(1), subst, TermId::new(2), 5);
        let inst = tracked.to_instantiation();
        assert_eq!(inst.quantifier, TermId::new(1));
        assert_eq!(inst.result, TermId::new(2));
        assert_eq!(inst.generation, 5);
        assert_eq!(inst.reason, InstantiationReason::Conflict);
    }

    #[test]
    fn test_cdqi_analyze_empty_conflict() {
        let mut cdqi = ConflictDrivenInstantiator::default_config();
        let mut manager = TermManager::new();
        let model = CompletedModel::new();

        let result = cdqi.analyze_conflict(&[], &[], &model, &mut manager);
        assert!(result.is_empty());
        assert_eq!(cdqi.stats.conflicts_analyzed, 1);
    }

    #[test]
    fn test_cdqi_generation_increments() {
        let mut cdqi = ConflictDrivenInstantiator::default_config();
        let mut manager = TermManager::new();
        let model = CompletedModel::new();

        let _ = cdqi.analyze_conflict(&[], &[], &model, &mut manager);
        assert_eq!(cdqi.generation(), 1);

        let _ = cdqi.analyze_conflict(&[], &[], &model, &mut manager);
        assert_eq!(cdqi.generation(), 2);
    }

    #[test]
    fn test_cdqi_stats_tracking() {
        let mut cdqi = ConflictDrivenInstantiator::default_config();
        let mut manager = TermManager::new();
        let model = CompletedModel::new();

        for _ in 0..5 {
            let _ = cdqi.analyze_conflict(&[], &[], &model, &mut manager);
        }

        assert_eq!(cdqi.stats().conflicts_analyzed, 5);
        assert_eq!(cdqi.stats().decay_rounds, 5);
    }

    #[test]
    fn test_cdqi_clear() {
        let mut cdqi = ConflictDrivenInstantiator::default_config();
        let mut manager = TermManager::new();
        let model = CompletedModel::new();

        let _ = cdqi.analyze_conflict(&[], &[], &model, &mut manager);
        assert_eq!(cdqi.generation(), 1);

        cdqi.clear();
        assert_eq!(cdqi.generation(), 0);
        assert_eq!(cdqi.num_tracked(), 0);
    }

    #[test]
    fn test_cdqi_conflict_analysis_with_ground_terms() {
        let mut cdqi = ConflictDrivenInstantiator::default_config();
        let mut manager = TermManager::new();
        let model = CompletedModel::new();

        // Create some ground terms in the conflict
        let int_val = manager.mk_int(num_bigint::BigInt::from(42));
        let conflict = vec![int_val];

        let result = cdqi.analyze_conflict(&conflict, &[], &model, &mut manager);
        // No quantifiers, so no instances
        assert!(result.is_empty());
        assert_eq!(cdqi.stats.conflicts_analyzed, 1);
    }

    #[test]
    fn test_cdqi_top_relevant_instances_empty() {
        let cdqi = ConflictDrivenInstantiator::default_config();
        let top = cdqi.top_relevant_instances(TermId::new(1), 5);
        assert!(top.is_empty());
    }

    #[test]
    fn test_conflict_analysis_struct() {
        let analysis = ConflictAnalysis {
            conflict_terms: vec![TermId::new(1), TermId::new(2)],
            conflict_variables: FxHashSet::default(),
            ground_values: FxHashMap::default(),
            related_quantifiers: vec![TermId::new(10)],
        };
        assert_eq!(analysis.conflict_terms.len(), 2);
        assert_eq!(analysis.related_quantifiers.len(), 1);
    }
}
