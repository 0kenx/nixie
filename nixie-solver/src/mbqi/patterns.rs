//! Pattern Matching and Trigger Generation for MBQI
//!
//! This module implements sophisticated pattern matching and trigger generation
//! algorithms for E-matching style quantifier instantiation.

#[allow(unused_imports)]
use crate::prelude::*;
use nixie_core::ast::{TermId, TermKind, TermManager};
use nixie_core::interner::Spur;

use super::{QuantifiedFormula, QuantifierConfig};

/// Strategy for ranking pattern candidates.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum PatternStrategy {
    /// Prefer shallower, cheaper patterns.
    StaticDepth,
    /// Prefer patterns that greedily cover more e-graph ground-term shapes.
    GreedyCover,
}

/// Coarse structural shape of a term for coverage scoring.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum TermShape {
    /// Boolean constant.
    BoolConst,
    /// Integer constant.
    IntConst,
    /// Real constant.
    RealConst,
    /// Variable occurrence.
    Var,
    /// Uninterpreted application with arity.
    Apply { arity: usize },
    /// Equality-like comparison.
    Eq,
    /// Strict inequality.
    StrictIneq,
    /// Non-strict inequality.
    NonStrictIneq,
    /// Arithmetic sum.
    Add { arity: usize },
    /// Arithmetic product.
    Mul { arity: usize },
    /// Catch-all for other shapes.
    Other,
}

impl TermShape {
    fn from_term(term: TermId, manager: &TermManager) -> Self {
        let Some(node) = manager.get(term) else {
            return Self::Other;
        };

        match &node.kind {
            TermKind::True | TermKind::False => Self::BoolConst,
            TermKind::IntConst(_) => Self::IntConst,
            TermKind::RealConst(_) => Self::RealConst,
            TermKind::Var(_) => Self::Var,
            TermKind::Apply { args, .. } => Self::Apply { arity: args.len() },
            TermKind::Eq(_, _) => Self::Eq,
            TermKind::Lt(_, _) | TermKind::Gt(_, _) => Self::StrictIneq,
            TermKind::Le(_, _) | TermKind::Ge(_, _) => Self::NonStrictIneq,
            TermKind::Add(args) => Self::Add { arity: args.len() },
            TermKind::Mul(args) => Self::Mul { arity: args.len() },
            _ => Self::Other,
        }
    }
}

/// Scores candidate pattern sets by greedy coverage over observed term shapes.
#[derive(Debug, Default, Clone)]
pub struct PatternCoverScorer;

impl PatternCoverScorer {
    /// Score pattern sets by greedy set cover over e-graph ground-term shapes.
    pub fn score_cover(
        &self,
        candidate_patterns: &[PatternSet],
        egraph_ground_terms: &[TermShape],
    ) -> Vec<(usize, f64)> {
        if candidate_patterns.is_empty() {
            return Vec::new();
        }

        let total_shapes = egraph_ground_terms
            .iter()
            .cloned()
            .collect::<FxHashSet<_>>();
        if total_shapes.is_empty() {
            return candidate_patterns
                .iter()
                .enumerate()
                .map(|(idx, _)| (idx, 0.0))
                .collect();
        }

        let mut remaining = total_shapes;
        let mut pending: Vec<usize> = (0..candidate_patterns.len()).collect();
        let mut ranked = Vec::with_capacity(candidate_patterns.len());

        while !pending.is_empty() {
            let mut best_pos = 0usize;
            let mut best_gain = 0usize;
            let mut best_score = 0.0f64;

            for (pos, &idx) in pending.iter().enumerate() {
                let covered = candidate_patterns[idx]
                    .covered_shapes
                    .iter()
                    .filter(|shape| remaining.contains(*shape))
                    .count();
                let score = covered as f64 / egraph_ground_terms.len() as f64;
                if covered > best_gain || (covered == best_gain && score > best_score) {
                    best_pos = pos;
                    best_gain = covered;
                    best_score = score;
                }
            }

            let chosen_idx = pending.remove(best_pos);
            for shape in &candidate_patterns[chosen_idx].covered_shapes {
                remaining.remove(shape);
            }
            ranked.push((chosen_idx, best_score));
        }

        ranked
    }
}

/// A pattern for E-matching
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Pattern {
    /// The pattern terms
    pub terms: Vec<TermId>,
    /// Variables in the pattern
    pub variables: FxHashSet<Spur>,
    /// Pattern quality score
    pub quality: u32,
    /// Pattern type
    pub pattern_type: PatternType,
}

impl Pattern {
    /// Create a new pattern
    pub fn new(terms: Vec<TermId>) -> Self {
        Self {
            terms,
            variables: FxHashSet::default(),
            quality: 0,
            pattern_type: PatternType::MultiPattern,
        }
    }

    /// Extract variables from the pattern.
    ///
    /// Explicit-stack walk with a visited set per pattern term (a set-valued
    /// result, so traversal order is irrelevant); no input depth can
    /// overflow the call stack. The descent set (`Apply` args, `Not`/`Neg`,
    /// `And`/`Or` -- the shapes triggers are made of) is the retired
    /// recursion's, unchanged.
    pub fn extract_variables(&mut self, manager: &TermManager) {
        self.variables.clear();
        for &root in &self.terms {
            let mut visited: FxHashSet<TermId> = FxHashSet::default();
            let mut work = vec![root];
            while let Some(t_id) = work.pop() {
                if !visited.insert(t_id) {
                    continue;
                }

                let Some(t) = manager.get(t_id) else {
                    continue;
                };

                if let TermKind::Var(name) = t.kind {
                    self.variables.insert(name);
                    continue;
                }

                match &t.kind {
                    TermKind::Apply { args, .. } => work.extend(args.iter().copied()),
                    TermKind::Not(arg) | TermKind::Neg(arg) => work.push(*arg),
                    TermKind::And(args) | TermKind::Or(args) => {
                        work.extend(args.iter().copied());
                    }
                    _ => {}
                }
            }
        }
    }

    /// Calculate pattern quality
    pub fn calculate_quality(&mut self, manager: &TermManager) {
        // Quality factors:
        // 1. Number of function symbols (more = better)
        // 2. Number of variables covered
        // 3. Pattern complexity

        let num_funcs = self.count_function_symbols(manager);
        let num_vars = self.variables.len();
        let complexity_penalty = self.terms.len();

        self.quality = (num_funcs * 100 + num_vars * 50) as u32 - complexity_penalty as u32;
    }

    /// Count distinct function applications reachable through `Apply`
    /// spines (other kinds are leaves for this quality metric, unchanged).
    ///
    /// Explicit-stack walk with a visited set shared across the pattern's
    /// terms; no input depth can overflow the call stack.
    fn count_function_symbols(&self, manager: &TermManager) -> usize {
        let mut count = 0usize;
        let mut visited: FxHashSet<TermId> = FxHashSet::default();
        let mut work: Vec<TermId> = self.terms.clone();

        while let Some(t_id) = work.pop() {
            if !visited.insert(t_id) {
                continue;
            }
            if let Some(t) = manager.get(t_id)
                && let TermKind::Apply { args, .. } = &t.kind
            {
                count += 1;
                work.extend(args.iter().copied());
            }
        }

        count
    }
}

/// Type of pattern
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum PatternType {
    /// Single term pattern
    SingleTerm,
    /// Multi-pattern (multiple terms)
    MultiPattern,
    /// User-specified pattern
    UserSpecified,
    /// Auto-generated pattern
    AutoGenerated,
}

/// Pattern generator
#[derive(Debug)]
pub struct PatternGenerator {
    /// Maximum patterns to generate
    max_patterns: usize,
    /// Minimum pattern quality
    min_quality: u32,
    /// Statistics
    stats: GeneratorStats,
    /// Pattern ranking strategy
    strategy: PatternStrategy,
}

impl PatternGenerator {
    /// Create a new pattern generator
    pub fn new() -> Self {
        let config = QuantifierConfig::default();
        Self {
            max_patterns: 10,
            min_quality: 0,
            stats: GeneratorStats::default(),
            strategy: config.pattern_strategy,
        }
    }

    /// Generate patterns for a quantifier
    pub fn generate(
        &mut self,
        quantifier: &QuantifiedFormula,
        manager: &TermManager,
    ) -> Vec<Pattern> {
        self.stats.num_generations += 1;

        // If user specified patterns, use those
        if !quantifier.patterns.is_empty() {
            return self.user_patterns_to_patterns(&quantifier.patterns, manager);
        }

        // Auto-generate patterns
        let mut patterns = Vec::new();

        // Strategy 1: Function application patterns
        patterns.extend(self.generate_function_patterns(quantifier.body, manager));

        // Strategy 2: Equality patterns
        patterns.extend(self.generate_equality_patterns(quantifier.body, manager));

        // Strategy 3: Arithmetic patterns
        patterns.extend(self.generate_arithmetic_patterns(quantifier.body, manager));

        // Filter by quality
        patterns.retain(|p| p.quality >= self.min_quality);

        match self.strategy {
            PatternStrategy::StaticDepth => {
                patterns.sort_by_key(|p| std::cmp::Reverse(p.quality));
            }
            PatternStrategy::GreedyCover => {
                patterns.sort_by_key(|p| std::cmp::Reverse(p.quality));
            }
        }

        // Limit number of patterns
        patterns.truncate(self.max_patterns);

        self.stats.num_patterns_generated += patterns.len();

        patterns
    }

    fn user_patterns_to_patterns(
        &self,
        user_patterns: &[Vec<TermId>],
        manager: &TermManager,
    ) -> Vec<Pattern> {
        let mut patterns = Vec::new();

        for pattern_terms in user_patterns {
            let mut pattern = Pattern::new(pattern_terms.clone());
            pattern.extract_variables(manager);
            pattern.calculate_quality(manager);
            pattern.pattern_type = PatternType::UserSpecified;
            patterns.push(pattern);
        }

        patterns
    }

    fn generate_function_patterns(&self, body: TermId, manager: &TermManager) -> Vec<Pattern> {
        let mut patterns = Vec::new();
        let func_apps = self.collect_function_applications(body, manager);

        for func_app in func_apps {
            let mut pattern = Pattern::new(vec![func_app]);
            pattern.extract_variables(manager);
            pattern.calculate_quality(manager);
            pattern.pattern_type = PatternType::AutoGenerated;
            patterns.push(pattern);
        }

        patterns
    }

    fn generate_equality_patterns(&self, body: TermId, manager: &TermManager) -> Vec<Pattern> {
        let mut patterns = Vec::new();
        let equalities = self.collect_equalities(body, manager);

        for eq_term in equalities {
            let mut pattern = Pattern::new(vec![eq_term]);
            pattern.extract_variables(manager);
            pattern.calculate_quality(manager);
            pattern.pattern_type = PatternType::AutoGenerated;
            patterns.push(pattern);
        }

        patterns
    }

    fn generate_arithmetic_patterns(&self, body: TermId, manager: &TermManager) -> Vec<Pattern> {
        let mut patterns = Vec::new();
        let arith_terms = self.collect_arithmetic_terms(body, manager);

        for arith_term in arith_terms {
            let mut pattern = Pattern::new(vec![arith_term]);
            pattern.extract_variables(manager);
            pattern.calculate_quality(manager);
            pattern.pattern_type = PatternType::AutoGenerated;
            patterns.push(pattern);
        }

        patterns
    }

    /// Collect function applications in pre-order (children left-to-right,
    /// preserving the retired recursion's result order exactly) with an
    /// explicit heap stack, so no input depth can overflow the call stack.
    fn collect_function_applications(&self, term: TermId, manager: &TermManager) -> Vec<TermId> {
        let mut results = Vec::new();
        let mut visited: FxHashSet<TermId> = FxHashSet::default();
        let mut work = vec![term];

        while let Some(t_id) = work.pop() {
            if !visited.insert(t_id) {
                continue;
            }

            let Some(t) = manager.get(t_id) else {
                continue;
            };

            if let TermKind::Apply { args, .. } = &t.kind {
                results.push(t_id);
                for &arg in args.iter().rev() {
                    work.push(arg);
                }
            }

            match &t.kind {
                TermKind::Not(arg) | TermKind::Neg(arg) => work.push(*arg),
                TermKind::And(args) | TermKind::Or(args) => {
                    for &arg in args.iter().rev() {
                        work.push(arg);
                    }
                }
                _ => {}
            }
        }

        results
    }

    /// Collect equality terms in pre-order (descending only the boolean
    /// structure `Not`/`Neg`/`And`/`Or`, unchanged) with an explicit heap
    /// stack, so no input depth can overflow the call stack.
    fn collect_equalities(&self, term: TermId, manager: &TermManager) -> Vec<TermId> {
        let mut results = Vec::new();
        let mut visited: FxHashSet<TermId> = FxHashSet::default();
        let mut work = vec![term];

        while let Some(t_id) = work.pop() {
            if !visited.insert(t_id) {
                continue;
            }

            let Some(t) = manager.get(t_id) else {
                continue;
            };

            if matches!(t.kind, TermKind::Eq(_, _)) {
                results.push(t_id);
            }

            match &t.kind {
                TermKind::Not(arg) | TermKind::Neg(arg) => work.push(*arg),
                TermKind::And(args) | TermKind::Or(args) => {
                    for &arg in args.iter().rev() {
                        work.push(arg);
                    }
                }
                _ => {}
            }
        }

        results
    }

    /// Collect arithmetic comparison terms in pre-order (descending only the
    /// boolean structure `Not`/`Neg`/`And`/`Or`, unchanged) with an explicit
    /// heap stack, so no input depth can overflow the call stack.
    fn collect_arithmetic_terms(&self, term: TermId, manager: &TermManager) -> Vec<TermId> {
        let mut results = Vec::new();
        let mut visited: FxHashSet<TermId> = FxHashSet::default();
        let mut work = vec![term];

        while let Some(t_id) = work.pop() {
            if !visited.insert(t_id) {
                continue;
            }

            let Some(t) = manager.get(t_id) else {
                continue;
            };

            match &t.kind {
                TermKind::Lt(_, _)
                | TermKind::Le(_, _)
                | TermKind::Gt(_, _)
                | TermKind::Ge(_, _) => {
                    results.push(t_id);
                }
                TermKind::Not(arg) | TermKind::Neg(arg) => work.push(*arg),
                TermKind::And(args) | TermKind::Or(args) => {
                    for &arg in args.iter().rev() {
                        work.push(arg);
                    }
                }
                _ => {}
            }
        }

        results
    }

    /// Get statistics
    pub fn stats(&self) -> &GeneratorStats {
        &self.stats
    }
}

impl Default for PatternGenerator {
    fn default() -> Self {
        Self::new()
    }
}

/// Statistics for pattern generation
#[derive(Debug, Clone, Default)]
pub struct GeneratorStats {
    /// Number of generation calls
    pub num_generations: usize,
    /// Total patterns generated
    pub num_patterns_generated: usize,
}

/// Multi-pattern coordinator
#[derive(Debug)]
pub struct MultiPatternCoordinator {
    /// Pattern sets
    pattern_sets: Vec<PatternSet>,
    /// Matching cache
    match_cache: FxHashMap<TermId, Vec<PatternMatch>>,
}

impl MultiPatternCoordinator {
    /// Create a new coordinator
    pub fn new() -> Self {
        Self {
            pattern_sets: Vec::new(),
            match_cache: FxHashMap::default(),
        }
    }

    /// Add a pattern set
    pub fn add_pattern_set(&mut self, patterns: Vec<Pattern>, manager: &TermManager) {
        self.pattern_sets
            .push(PatternSet::from_patterns(patterns, manager));
    }

    /// Find matches for all pattern sets against a pool of candidate ground
    /// terms (e.g. subterms collected from the current e-graph / asserted
    /// formulas), populating the per-trigger-term `match_cache` on demand.
    ///
    /// E-matching support covers `TermKind::Apply` trigger shapes -- the
    /// overwhelmingly common case for quantifier triggers -- with exact
    /// structural/id equality as a conservative fallback for every other
    /// term shape (see `unify_trigger`). A candidate is only ever reported
    /// as a match when every non-variable position agrees exactly with the
    /// pattern, so this can under-match relative to a full E-matching engine
    /// but never fabricates an unsound binding.
    pub fn find_matches(
        &mut self,
        ground_terms: &[TermId],
        manager: &TermManager,
    ) -> Vec<MultiMatch> {
        let mut multi_matches = Vec::new();

        for pattern_set in &self.pattern_sets {
            // Find matches for each pattern in the set
            let mut set_matches = Vec::new();

            for pattern in &pattern_set.patterns {
                for &term in &pattern.terms {
                    if let std::collections::hash_map::Entry::Vacant(entry) =
                        self.match_cache.entry(term)
                    {
                        let mut found = Vec::new();
                        for &candidate in ground_terms {
                            let mut bindings = FxHashMap::default();
                            if unify_trigger(
                                term,
                                candidate,
                                &pattern.variables,
                                manager,
                                &mut bindings,
                            ) {
                                found.push(PatternMatch {
                                    pattern: pattern.clone(),
                                    matched_term: candidate,
                                    bindings,
                                });
                            }
                        }
                        entry.insert(found);
                    }

                    if let Some(cached) = self.match_cache.get(&term) {
                        set_matches.extend(cached.iter().cloned());
                    }
                }
            }

            // Combine matches
            if !set_matches.is_empty() {
                multi_matches.push(MultiMatch {
                    pattern_set: pattern_set.patterns.clone(),
                    matches: set_matches,
                });
            }
        }

        multi_matches
    }

    /// Clear cache
    pub fn clear_cache(&mut self) {
        self.match_cache.clear();
    }
}

impl Default for MultiPatternCoordinator {
    fn default() -> Self {
        Self::new()
    }
}

/// Attempt to unify a (possibly variable-containing) pattern/trigger term
/// against a concrete ground candidate term, recording bindings for the
/// pattern's bound variables as they are discovered.
///
/// Returns `true` (with `bindings` populated) iff `candidate` is a valid
/// E-matching instance of `pattern_term`. A pattern variable binds to the
/// first candidate subterm found at its position (subject to sort
/// agreement) and every subsequent occurrence of that variable must bind to
/// the identical term, matching standard E-matching semantics.
///
/// Iterative worklist over `(pattern, candidate)` pairs with a visited-pair
/// set, replacing a native recursion that had no memoisation: the two-sided
/// walk re-expanded shared subterms of the hash-consed DAG once per path
/// (exponential on a doubling DAG) and overflowed the native stack on deep
/// triggers. Skipping an already-seen pair is sound because the walk is a
/// pure conjunction with no backtracking: bindings only ever grow within
/// one attempt, the first failing pair fails the whole attempt, and a pair
/// that succeeded pinned every pattern variable below it to the
/// corresponding candidate subterm.
fn unify_trigger(
    pattern_term: TermId,
    candidate: TermId,
    pattern_vars: &FxHashSet<Spur>,
    manager: &TermManager,
    bindings: &mut FxHashMap<Spur, TermId>,
) -> bool {
    let mut seen: FxHashSet<(TermId, TermId)> = FxHashSet::default();
    // Pairs still to match; children are pushed in reverse so they are
    // matched left-to-right, exactly as the recursive walk did.
    let mut work: Vec<(TermId, TermId)> = vec![(pattern_term, candidate)];

    while let Some((p_id, c_id)) = work.pop() {
        if !seen.insert((p_id, c_id)) {
            continue;
        }

        if p_id == c_id {
            // Identical (possibly ground) subterm shared between pattern and
            // candidate -- always a valid match, whatever its shape.
            continue;
        }

        let (Some(p), Some(c)) = (manager.get(p_id), manager.get(c_id)) else {
            return false;
        };

        if let TermKind::Var(name) = &p.kind {
            if pattern_vars.contains(name) {
                match bindings.get(name) {
                    Some(&bound) => {
                        if bound != c_id {
                            return false;
                        }
                    }
                    None if p.sort == c.sort => {
                        bindings.insert(*name, c_id);
                    }
                    None => return false,
                }
                continue;
            }
            // A `Var` that is not one of the pattern's own bound variables is
            // a free reference (e.g. a declared constant); it only matches an
            // identical term, already handled by the `p_id == c_id` check
            // above.
            return false;
        }

        match (&p.kind, &c.kind) {
            (TermKind::Apply { func: pf, args: pa }, TermKind::Apply { func: cf, args: ca }) => {
                if pf != cf || pa.len() != ca.len() {
                    return false;
                }
                for (&pt, &ct) in pa.iter().zip(ca.iter()).rev() {
                    work.push((pt, ct));
                }
            }
            // Every other term shape falls back to exact structural equality,
            // which was already ruled out by the `p_id == c_id` fast path
            // above -- so no other shape can match here. This keeps the
            // matcher conservative (never a spurious binding) for shapes
            // beyond uninterpreted function application.
            _ => return false,
        }
    }

    true
}

/// A set of patterns that must be matched together
#[derive(Debug, Clone)]
pub struct PatternSet {
    pub patterns: Vec<Pattern>,
    pub matches: Vec<PatternMatch>,
    pub covered_shapes: FxHashSet<TermShape>,
}

impl PatternSet {
    /// Build a pattern set and precompute the term shapes it can match.
    pub fn from_patterns(patterns: Vec<Pattern>, manager: &TermManager) -> Self {
        let mut covered_shapes = FxHashSet::default();
        for pattern in &patterns {
            for &term in &pattern.terms {
                covered_shapes.insert(TermShape::from_term(term, manager));
            }
        }
        Self {
            patterns,
            matches: Vec::new(),
            covered_shapes,
        }
    }
}

/// A match for a pattern
#[derive(Debug, Clone)]
pub struct PatternMatch {
    /// The pattern that matched
    pub pattern: Pattern,
    /// The matched term
    pub matched_term: TermId,
    /// Variable bindings
    pub bindings: FxHashMap<Spur, TermId>,
}

/// A multi-pattern match
#[derive(Debug, Clone)]
pub struct MultiMatch {
    /// The pattern set
    pub pattern_set: Vec<Pattern>,
    /// Individual matches
    pub matches: Vec<PatternMatch>,
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_pattern_creation() {
        let pattern = Pattern::new(vec![TermId::new(1)]);
        assert_eq!(pattern.terms.len(), 1);
        assert_eq!(pattern.variables.len(), 0);
    }

    #[test]
    fn test_pattern_type_equality() {
        assert_eq!(PatternType::SingleTerm, PatternType::SingleTerm);
        assert_ne!(PatternType::SingleTerm, PatternType::MultiPattern);
    }

    #[test]
    fn test_pattern_generator_creation() {
        let generator = PatternGenerator::new();
        assert_eq!(generator.max_patterns, 10);
    }

    #[test]
    fn test_multi_pattern_coordinator() {
        let mut coord = MultiPatternCoordinator::new();
        let manager = TermManager::new();
        coord.add_pattern_set(vec![], &manager);
        assert_eq!(coord.pattern_sets.len(), 1);
    }

    /// Regression test for the audit finding that `find_matches` always
    /// returned an empty result because `match_cache` was read but never
    /// populated. With a trigger `f(x)` and ground candidates `f(1)` and
    /// `g(1)`, only `f(1)` (same function symbol) should match, binding `x`
    /// to the integer literal `1`.
    #[test]
    fn test_audit_find_matches_populates_cache_and_matches_apply_trigger() {
        let mut manager = TermManager::new();
        let int_sort = manager.sorts.int_sort;

        let x = manager.mk_var("x", int_sort);
        let trigger = manager.mk_apply("f", [x], int_sort);

        let one = manager.mk_int(1);
        let f_one = manager.mk_apply("f", [one], int_sort);
        let g_one = manager.mk_apply("g", [one], int_sort);

        let mut pattern = Pattern::new(vec![trigger]);
        pattern.extract_variables(&manager);
        assert_eq!(pattern.variables.len(), 1, "x should be a pattern variable");

        let mut coord = MultiPatternCoordinator::new();
        coord.add_pattern_set(vec![pattern], &manager);

        let ground_terms = [f_one, g_one];
        let matches = coord.find_matches(&ground_terms, &manager);

        assert_eq!(matches.len(), 1, "one pattern set should produce matches");
        assert_eq!(
            matches[0].matches.len(),
            1,
            "only f(1) should match the f(x) trigger, not g(1)"
        );
        assert_eq!(matches[0].matches[0].matched_term, f_one);

        // The bound variable `x` must be mapped to the literal `1`.
        let x_name = match manager.get(x).map(|t| t.kind.clone()) {
            Some(TermKind::Var(name)) => name,
            _ => panic!("x must be a Var term"),
        };
        assert_eq!(matches[0].matches[0].bindings.get(&x_name), Some(&one));

        // The match cache must now actually contain the populated entry
        // (this is the crux of the original bug: it was read but never
        // written).
        assert!(coord.match_cache.contains_key(&trigger));
        assert_eq!(coord.match_cache[&trigger].len(), 1);

        // A second call must reuse the cache rather than recomputing an
        // empty result.
        let matches_again = coord.find_matches(&ground_terms, &manager);
        assert_eq!(matches_again[0].matches.len(), 1);
    }

    #[test]
    fn test_audit_find_matches_no_candidates_no_matches() {
        let mut manager = TermManager::new();
        let int_sort = manager.sorts.int_sort;
        let x = manager.mk_var("x", int_sort);
        let trigger = manager.mk_apply("f", [x], int_sort);

        let mut pattern = Pattern::new(vec![trigger]);
        pattern.extract_variables(&manager);

        let mut coord = MultiPatternCoordinator::new();
        coord.add_pattern_set(vec![pattern], &manager);

        let matches = coord.find_matches(&[], &manager);
        assert!(matches.is_empty());
    }

    #[test]
    fn test_pattern_equality() {
        let p1 = Pattern::new(vec![TermId::new(1)]);
        let p2 = Pattern::new(vec![TermId::new(1)]);
        assert_eq!(p1, p2);
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

    /// All converted pattern walks must survive 12 500-deep terms on a
    /// 128 KiB stack (the retired recursions overflowed) with pinned outputs.
    #[test]
    fn pattern_walks_survive_deep_terms_on_a_tiny_stack() {
        const DEPTH: usize = 12_500;
        run_on_small_stack(|| {
            let mut m = TermManager::new();
            let int_sort = m.sorts.int_sort;
            let bool_sort = m.sorts.bool_sort;
            let x = m.mk_var("x", int_sort);
            let mut apply_chain = x;
            for _ in 0..DEPTH {
                apply_chain = m.mk_apply("f", [apply_chain], int_sort);
            }

            // extract_variables and count_function_symbols over the chain.
            let mut pattern = Pattern::new(vec![apply_chain]);
            pattern.extract_variables(&m);
            assert_eq!(pattern.variables.len(), 1, "x is under the Apply chain");
            assert_eq!(pattern.count_function_symbols(&m), DEPTH);

            // A deep boolean chain for the eq/arith/func collectors:
            // alternate And/Not so builder folding cannot collapse it.
            let zero = m.mk_int(0);
            let eq = m.mk_eq(x, zero);
            let lt = m.mk_lt(x, zero);
            let p_x = m.mk_apply("P", [x], bool_sort);
            let seed = m.mk_and([eq, lt, p_x]);
            let marker = m.mk_var("b", bool_sort);
            let mut bool_chain = seed;
            for _ in 0..DEPTH {
                let conj = m.mk_and([marker, bool_chain]);
                bool_chain = m.mk_not(conj);
            }

            let generator = PatternGenerator::new();
            assert_eq!(generator.collect_equalities(bool_chain, &m), vec![eq]);
            assert_eq!(generator.collect_arithmetic_terms(bool_chain, &m), vec![lt]);
            assert_eq!(
                generator.collect_function_applications(bool_chain, &m),
                vec![p_x]
            );

            // unify_trigger over a deep pattern/candidate pair.
            let seven = m.mk_int(7);
            let mut deep_pattern = x;
            let mut deep_candidate = seven;
            for _ in 0..DEPTH {
                deep_pattern = m.mk_apply("g", [deep_pattern], int_sort);
                deep_candidate = m.mk_apply("g", [deep_candidate], int_sort);
            }
            let x_name = match m.get(x).map(|t| &t.kind) {
                Some(TermKind::Var(n)) => *n,
                _ => panic!("x is a variable"),
            };
            let pattern_vars: FxHashSet<Spur> = core::iter::once(x_name).collect();
            let mut bindings = FxHashMap::default();
            assert!(unify_trigger(
                deep_pattern,
                deep_candidate,
                &pattern_vars,
                &m,
                &mut bindings
            ));
            assert_eq!(bindings.get(&x_name), Some(&seven));
        });
    }

    /// A doubling (pattern, candidate) DAG is exponential without the
    /// visited-pair set; with it the unification must complete essentially
    /// instantly.
    #[test]
    fn unify_trigger_handles_shared_dag_without_blowup() {
        const LEVELS: usize = 55;
        let mut m = TermManager::new();
        let int_sort = m.sorts.int_sort;
        let x = m.mk_var("x", int_sort);
        let seven = m.mk_int(7);

        let mut pattern = x;
        let mut candidate = seven;
        for _ in 0..LEVELS {
            pattern = m.mk_apply("g", [pattern, pattern], int_sort);
            candidate = m.mk_apply("g", [candidate, candidate], int_sort);
        }

        let x_name = match m.get(x).map(|t| &t.kind) {
            Some(TermKind::Var(n)) => *n,
            _ => panic!("x is a variable"),
        };
        let pattern_vars: FxHashSet<Spur> = core::iter::once(x_name).collect();
        let mut bindings = FxHashMap::default();
        assert!(unify_trigger(
            pattern,
            candidate,
            &pattern_vars,
            &m,
            &mut bindings
        ));
        assert_eq!(bindings.get(&x_name), Some(&seven));

        // A conflicting occurrence must still be rejected: same doubling
        // pattern against a candidate whose two halves disagree at the leaf.
        let eight = m.mk_int(8);
        let mut left = seven;
        let mut right = eight;
        for _ in 0..(LEVELS - 1) {
            left = m.mk_apply("g", [left, left], int_sort);
            right = m.mk_apply("g", [right, right], int_sort);
        }
        let mismatched = m.mk_apply("g", [left, right], int_sort);
        let mut bindings = FxHashMap::default();
        assert!(!unify_trigger(
            pattern,
            mismatched,
            &pattern_vars,
            &m,
            &mut bindings
        ));
    }

    /// Function-application collection order is pre-order left-to-right;
    /// pinned so the iterative conversion is proven behavior-preserving.
    #[test]
    fn collect_function_applications_preserves_preorder() {
        let mut m = TermManager::new();
        let int_sort = m.sorts.int_sort;
        let x = m.mk_var("x", int_sort);
        let g_x = m.mk_apply("g", [x], int_sort);
        let h_x = m.mk_apply("h", [x], int_sort);
        let f = m.mk_apply("f", [g_x, h_x], int_sort);

        let generator = PatternGenerator::new();
        assert_eq!(
            generator.collect_function_applications(f, &m),
            vec![f, g_x, h_x]
        );
    }
}
