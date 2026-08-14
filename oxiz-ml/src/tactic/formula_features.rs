//! Formula Feature Extraction
#![allow(clippy::too_many_arguments)] // ML feature extraction
//!
//! Extract features from SMT formulas for tactic selection.
//!
//! The extractor parses an SMT-LIB2 formula (or full script) with
//! `oxiz-core`'s real parser and walks the resulting term DAG to compute
//! structural statistics – atom counts per theory, quantifier count and
//! nesting depth, term size and depth, per-sort variable counts, a
//! multiplicative-degree proxy for arithmetic non-linearity, the set of
//! bit-vector widths in play, and a declared-symbol arity histogram. These
//! feed a fixed-width feature vector consumed by the tactic selector.

use std::collections::{BTreeMap, BTreeSet, HashMap, HashSet};

use oxiz_core::ast::{
    TermId, TermKind, TermManager, collect_free_vars, collect_subterms, get_children,
};
use oxiz_core::smtlib::{Command, parse_script, parse_term};
use oxiz_core::sort::SortKind;

use crate::TACTIC_FEATURE_SIZE;

/// Formula features for ML prediction
#[derive(Debug, Clone)]
pub struct FormulaFeatures {
    /// Feature vector
    pub features: Vec<f64>,
}

impl FormulaFeatures {
    /// Create from feature vector
    pub fn from_vec(features: Vec<f64>) -> Self {
        Self { features }
    }

    /// Extract features from formula statistics
    pub fn extract(
        num_variables: usize,
        num_clauses: usize,
        avg_clause_size: f64,
        num_quantifiers: usize,
        num_boolean_vars: usize,
        num_arithmetic_vars: usize,
        num_theory_atoms: usize,
        max_nesting_depth: usize,
        has_arrays: bool,
        has_bitvectors: bool,
        has_uninterpreted_functions: bool,
    ) -> Self {
        let mut features = Vec::with_capacity(TACTIC_FEATURE_SIZE);

        // 1. Number of variables (log scale)
        features.push((1.0 + num_variables as f64).ln() / 20.0);

        // 2. Number of clauses (log scale)
        features.push((1.0 + num_clauses as f64).ln() / 20.0);

        // 3. Average clause size
        features.push(avg_clause_size / 50.0);

        // 4. Clause/variable ratio
        let clause_var_ratio = if num_variables > 0 {
            num_clauses as f64 / num_variables as f64
        } else {
            1.0
        };
        features.push(clause_var_ratio.min(10.0) / 10.0);

        // 5. Number of quantifiers
        features.push((1.0 + num_quantifiers as f64).ln() / 10.0);

        // 6. Boolean variable ratio
        let bool_ratio = if num_variables > 0 {
            num_boolean_vars as f64 / num_variables as f64
        } else {
            1.0
        };
        features.push(bool_ratio);

        // 7. Arithmetic variable ratio
        let arith_ratio = if num_variables > 0 {
            num_arithmetic_vars as f64 / num_variables as f64
        } else {
            0.0
        };
        features.push(arith_ratio);

        // 8. Theory atom density
        let theory_density = if num_clauses > 0 {
            num_theory_atoms as f64 / num_clauses as f64
        } else {
            0.0
        };
        features.push(theory_density);

        // 9. Nesting depth (normalized)
        features.push(max_nesting_depth as f64 / 50.0);

        // 10. Has arrays (binary)
        features.push(if has_arrays { 1.0 } else { 0.0 });

        // 11. Has bitvectors (binary)
        features.push(if has_bitvectors { 1.0 } else { 0.0 });

        // 12. Has uninterpreted functions (binary)
        features.push(if has_uninterpreted_functions {
            1.0
        } else {
            0.0
        });

        // 13. Formula complexity (combined metric)
        let complexity = (num_variables as f64 * num_clauses as f64).sqrt() / 100.0;
        features.push(complexity);

        // 14-20. Reserved for future features
        features.resize(TACTIC_FEATURE_SIZE, 0.0);

        Self { features }
    }

    /// Build a feature vector from fully-computed [`FormulaStats`].
    ///
    /// Slots 1-13 reuse [`FormulaFeatures::extract`]'s established encoding;
    /// slots 14-20 (previously always zero) carry the richer term-level
    /// statistics – quantifier nesting, multiplicative arithmetic degree,
    /// bit-vector width, uninterpreted-function / array operation density,
    /// declared-symbol arity, and overall term size – so the extra capacity
    /// of the 20-wide vector is genuinely used.
    pub fn from_stats(stats: &FormulaStats) -> Self {
        let mut feats = Self::extract(
            stats.num_variables,
            stats.num_assertions,
            stats.avg_clause_size(),
            stats.num_quantifiers,
            stats.num_bool_vars,
            stats.num_arithmetic_vars(),
            stats.num_theory_atoms,
            stats.max_term_depth,
            stats.has_arrays,
            stats.has_bitvectors,
            stats.has_uf,
        );

        let node_denom = (stats.total_term_nodes as f64) + 1.0;

        // 14. Quantifier nesting depth (normalized).
        feats.features[13] = stats.max_quantifier_depth as f64 / 10.0;
        // 15. Multiplicative arithmetic degree (proxy for non-linearity).
        feats.features[14] = stats.max_arith_degree as f64 / 10.0;
        // 16. Widest bit-vector in the formula (normalized against 64).
        feats.features[15] = stats.max_bv_width() as f64 / 64.0;
        // 17. Uninterpreted-function application density.
        feats.features[16] = stats.num_uf_apps as f64 / node_denom;
        // 18. Array-operation density.
        feats.features[17] = stats.num_array_ops as f64 / node_denom;
        // 19. Maximum declared-symbol arity (normalized).
        feats.features[18] = stats.max_symbol_arity() as f64 / 10.0;
        // 20. Overall term size (normalized).
        feats.features[19] = stats.total_term_nodes as f64 / 1000.0;

        feats
    }
}

impl Default for FormulaFeatures {
    fn default() -> Self {
        Self {
            features: vec![0.0; TACTIC_FEATURE_SIZE],
        }
    }
}

/// Structural statistics extracted from an SMT formula/script.
///
/// This is the raw, human-interpretable feature set (before the fixed-width
/// numeric encoding in [`FormulaFeatures::from_stats`]).
#[derive(Debug, Clone, Default, PartialEq)]
pub struct FormulaStats {
    /// Distinct free variables across all assertions.
    pub num_variables: usize,
    /// Free variables of Boolean sort.
    pub num_bool_vars: usize,
    /// Free variables of Int sort.
    pub num_int_vars: usize,
    /// Free variables of Real sort.
    pub num_real_vars: usize,
    /// Free variables of bit-vector sort.
    pub num_bv_vars: usize,
    /// Top-level assertions (the "clauses").
    pub num_assertions: usize,
    /// Sum, over assertions, of that assertion's term-DAG node count.
    pub total_assertion_nodes: usize,
    /// Distinct term nodes across every assertion (shared subterms counted
    /// once).
    pub total_term_nodes: usize,
    /// Maximum term (height) depth over all assertions.
    pub max_term_depth: usize,
    /// Number of quantifier nodes (`forall`/`exists`).
    pub num_quantifiers: usize,
    /// Deepest quantifier nesting on any root-to-leaf path.
    pub max_quantifier_depth: usize,
    /// Theory-relevant atoms (equalities, comparisons, predicate applications).
    pub num_theory_atoms: usize,
    /// Arithmetic operator nodes.
    pub num_arith_ops: usize,
    /// Bit-vector operator nodes.
    pub num_bv_ops: usize,
    /// Array `select`/`store` nodes.
    pub num_array_ops: usize,
    /// Uninterpreted-function application nodes.
    pub num_uf_apps: usize,
    /// Deepest multiplicative nesting (proxy for polynomial degree).
    pub max_arith_degree: usize,
    /// Distinct bit-vector widths present anywhere in the formula.
    pub bv_widths: BTreeSet<u32>,
    /// Histogram mapping declared-symbol arity -> count of declared symbols.
    pub arity_histogram: BTreeMap<usize, usize>,
    /// Whether the formula uses the theory of arrays.
    pub has_arrays: bool,
    /// Whether the formula uses bit-vectors.
    pub has_bitvectors: bool,
    /// Whether the formula uses uninterpreted functions.
    pub has_uf: bool,
}

impl FormulaStats {
    /// Arithmetic (Int + Real) free-variable count.
    pub fn num_arithmetic_vars(&self) -> usize {
        self.num_int_vars + self.num_real_vars
    }

    /// Average per-assertion term size.
    pub fn avg_clause_size(&self) -> f64 {
        if self.num_assertions == 0 {
            0.0
        } else {
            self.total_assertion_nodes as f64 / self.num_assertions as f64
        }
    }

    /// Widest bit-vector width present (0 if none).
    pub fn max_bv_width(&self) -> u32 {
        self.bv_widths.iter().copied().max().unwrap_or(0)
    }

    /// Largest declared-symbol arity (0 if none declared).
    pub fn max_symbol_arity(&self) -> usize {
        self.arity_histogram.keys().copied().max().unwrap_or(0)
    }
}

/// Parse `formula` (a full SMT-LIB2 script or a single bare term) and extract
/// its [`FormulaStats`].
///
/// Robust to both shapes: a script such as
/// `(declare-const x Int) (assert (> x 0)) (check-sat)` is parsed with the
/// full command grammar, while a bare term such as `(and p q)` is parsed via
/// the lenient single-term path (unknown symbols become Boolean variables).
/// An input that parses as neither yields empty stats (all-zero features) –
/// an honest "nothing to measure" rather than a fabricated vector.
pub fn extract_formula_stats(formula: &str) -> FormulaStats {
    let mut manager = TermManager::new();
    let mut stats = FormulaStats::default();
    let mut assertions: Vec<TermId> = Vec::new();

    if let Ok(commands) = parse_script(formula, &mut manager) {
        for command in commands {
            match command {
                Command::Assert(term) | Command::AssertNamed(term, _) => assertions.push(term),
                Command::DeclareConst(_, _) => {
                    *stats.arity_histogram.entry(0).or_insert(0) += 1;
                }
                Command::DeclareFun(_, arg_sorts, _) => {
                    *stats.arity_histogram.entry(arg_sorts.len()).or_insert(0) += 1;
                }
                _ => {}
            }
        }
    }

    // If the script grammar produced no assertions (e.g. the input was a bare
    // term with no declarations), fall back to the lenient single-term path.
    if assertions.is_empty() {
        let mut term_manager = TermManager::new();
        if let Ok(term) = parse_term(formula, &mut term_manager) {
            manager = term_manager;
            assertions.push(term);
            // A bare term declares nothing, so reset any partial arity data.
            stats.arity_histogram.clear();
        }
    }

    if assertions.is_empty() {
        return stats;
    }

    accumulate_term_stats(&manager, &assertions, &mut stats);
    stats
}

/// Walk every assertion's term DAG and accumulate the structural counters.
fn accumulate_term_stats(manager: &TermManager, assertions: &[TermId], stats: &mut FormulaStats) {
    stats.num_assertions = assertions.len();

    // Classify each distinct term node once, globally, so subterms shared
    // across assertions are not double-counted.
    let mut classified: HashSet<TermId> = HashSet::new();
    // Union of free variables across assertions (deduplicated by term id).
    let mut free_vars: HashSet<TermId> = HashSet::new();

    for &assertion in assertions {
        let subterms = collect_subterms(assertion, manager); // post-order: children first

        stats.total_assertion_nodes += subterms.len();

        // Per-assertion memoized depth / quantifier-depth / mul-depth maps.
        let mut depth: HashMap<TermId, usize> = HashMap::new();
        let mut qdepth: HashMap<TermId, usize> = HashMap::new();
        let mut mdepth: HashMap<TermId, usize> = HashMap::new();

        for &id in &subterms {
            let Some(term) = manager.get(id) else {
                continue;
            };
            let kind = &term.kind;
            let children = get_children(kind);

            let child_depth = children
                .iter()
                .filter_map(|c| depth.get(c))
                .copied()
                .max()
                .unwrap_or(0);
            let child_qdepth = children
                .iter()
                .filter_map(|c| qdepth.get(c))
                .copied()
                .max()
                .unwrap_or(0);
            let child_mdepth = children
                .iter()
                .filter_map(|c| mdepth.get(c))
                .copied()
                .max()
                .unwrap_or(0);

            let is_quantifier = matches!(kind, TermKind::Forall { .. } | TermKind::Exists { .. });
            let is_mul = matches!(kind, TermKind::Mul(_) | TermKind::BvMul(_, _));

            depth.insert(id, child_depth + 1);
            qdepth.insert(id, child_qdepth + usize::from(is_quantifier));
            mdepth.insert(id, child_mdepth + usize::from(is_mul));

            // Record bit-vector widths from this node's sort.
            if let Some(SortKind::BitVec(width)) =
                manager.sorts.get(term.sort).map(|s| s.kind.clone())
            {
                stats.bv_widths.insert(width);
                stats.has_bitvectors = true;
            }

            // Classify the node exactly once across the whole formula.
            if classified.insert(id) {
                classify_node(kind, stats);
            }
        }

        stats.max_term_depth = stats
            .max_term_depth
            .max(depth.get(&assertion).copied().unwrap_or(0));
        stats.max_quantifier_depth = stats
            .max_quantifier_depth
            .max(qdepth.get(&assertion).copied().unwrap_or(0));
        stats.max_arith_degree = stats
            .max_arith_degree
            .max(mdepth.get(&assertion).copied().unwrap_or(0));

        for var in collect_free_vars(assertion, manager) {
            free_vars.insert(var);
        }
    }

    stats.total_term_nodes = classified.len();
    stats.num_variables = free_vars.len();

    // Classify each free variable by sort.
    for var in free_vars {
        let Some(term) = manager.get(var) else {
            continue;
        };
        match manager.sorts.get(term.sort).map(|s| s.kind.clone()) {
            Some(SortKind::Bool) => stats.num_bool_vars += 1,
            Some(SortKind::Int) => stats.num_int_vars += 1,
            Some(SortKind::Real) => stats.num_real_vars += 1,
            Some(SortKind::BitVec(width)) => {
                stats.num_bv_vars += 1;
                stats.bv_widths.insert(width);
                stats.has_bitvectors = true;
            }
            _ => {}
        }
    }
}

/// Update the theory / operator counters for a single term node.
fn classify_node(kind: &TermKind, stats: &mut FormulaStats) {
    match kind {
        // Equality / comparison / relational atoms.
        TermKind::Eq(_, _) | TermKind::Distinct(_) => stats.num_theory_atoms += 1,

        // Arithmetic.
        TermKind::Neg(_)
        | TermKind::Add(_)
        | TermKind::Sub(_, _)
        | TermKind::Mul(_)
        | TermKind::Div(_, _)
        | TermKind::Mod(_, _) => stats.num_arith_ops += 1,
        TermKind::Lt(_, _) | TermKind::Le(_, _) | TermKind::Gt(_, _) | TermKind::Ge(_, _) => {
            stats.num_arith_ops += 1;
            stats.num_theory_atoms += 1;
        }

        // Bit-vectors: operators and predicates.
        TermKind::BvNot(_)
        | TermKind::BvAnd(_, _)
        | TermKind::BvOr(_, _)
        | TermKind::BvXor(_, _)
        | TermKind::BvAdd(_, _)
        | TermKind::BvSub(_, _)
        | TermKind::BvMul(_, _)
        | TermKind::BvUdiv(_, _)
        | TermKind::BvSdiv(_, _)
        | TermKind::BvUrem(_, _)
        | TermKind::BvSrem(_, _)
        | TermKind::BvShl(_, _)
        | TermKind::BvLshr(_, _)
        | TermKind::BvAshr(_, _)
        | TermKind::BvConcat(_, _)
        | TermKind::BvExtract { .. } => {
            stats.num_bv_ops += 1;
            stats.has_bitvectors = true;
        }
        TermKind::BvUlt(_, _)
        | TermKind::BvUle(_, _)
        | TermKind::BvSlt(_, _)
        | TermKind::BvSle(_, _) => {
            stats.num_bv_ops += 1;
            stats.num_theory_atoms += 1;
            stats.has_bitvectors = true;
        }
        TermKind::BitVecConst { width, .. } => {
            stats.bv_widths.insert(*width);
            stats.has_bitvectors = true;
        }

        // Arrays.
        TermKind::Select(_, _) | TermKind::Store(_, _, _) => {
            stats.num_array_ops += 1;
            stats.has_arrays = true;
        }

        // Uninterpreted-function applications.
        TermKind::Apply { .. } => {
            stats.num_uf_apps += 1;
            stats.has_uf = true;
        }

        // Quantifiers.
        TermKind::Forall { .. } | TermKind::Exists { .. } => stats.num_quantifiers += 1,

        _ => {}
    }
}

/// Extract the fixed-width feature vector directly from a formula string.
///
/// Returns the all-zero [`FormulaFeatures::default`] vector when the input
/// contains nothing measurable (empty, comment-only, or unparseable), and a
/// genuinely populated vector otherwise.
pub fn extract_formula_features(formula: &str) -> FormulaFeatures {
    let stats = extract_formula_stats(formula);
    if stats.num_assertions == 0 {
        return FormulaFeatures::default();
    }
    FormulaFeatures::from_stats(&stats)
}

/// Formula feature extractor (stateful)
pub struct FeatureExtractor {
    /// Cached features
    cached_features: Option<FormulaFeatures>,
}

impl FeatureExtractor {
    /// Create a new feature extractor
    pub fn new() -> Self {
        Self {
            cached_features: None,
        }
    }

    /// Extract features from a formula string.
    ///
    /// Parses the formula with `oxiz-core` and walks the resulting term DAG
    /// to populate a real feature vector (see [`extract_formula_features`]).
    /// The result is cached for [`FeatureExtractor::cached`].
    pub fn extract_from_formula(&mut self, formula: &str) -> FormulaFeatures {
        let features = extract_formula_features(formula);
        self.cached_features = Some(features.clone());
        features
    }

    /// Return the most recently extracted features, if any.
    pub fn cached(&self) -> Option<&FormulaFeatures> {
        self.cached_features.as_ref()
    }

    /// Invalidate cache
    pub fn invalidate_cache(&mut self) {
        self.cached_features = None;
    }
}

impl Default for FeatureExtractor {
    fn default() -> Self {
        Self::new()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_formula_features_extract() {
        let features = FormulaFeatures::extract(
            100,   // num_variables
            200,   // num_clauses
            5.0,   // avg_clause_size
            10,    // num_quantifiers
            80,    // num_boolean_vars
            20,    // num_arithmetic_vars
            50,    // num_theory_atoms
            10,    // max_nesting_depth
            true,  // has_arrays
            false, // has_bitvectors
            true,  // has_uninterpreted_functions
        );

        assert_eq!(features.features.len(), TACTIC_FEATURE_SIZE);
        assert!(features.features.iter().all(|&f| f.is_finite()));
    }

    #[test]
    fn test_formula_features_default() {
        let features = FormulaFeatures::default();
        assert_eq!(features.features.len(), TACTIC_FEATURE_SIZE);
    }

    #[test]
    fn test_feature_extractor_bare_term_is_nonzero() {
        let mut extractor = FeatureExtractor::new();
        let features = extractor.extract_from_formula("(and p q)");
        assert_eq!(features.features.len(), TACTIC_FEATURE_SIZE);
        // Two Boolean variables => a non-zero variable-count feature.
        assert!(
            features.features[0] > 0.0,
            "expected a non-zero variable feature for a real formula, got {:?}",
            features.features
        );
        assert!(extractor.cached().is_some());
    }

    #[test]
    fn test_extract_stats_linear_arithmetic_script() {
        let script = "(declare-const x Int)\n\
                      (declare-const y Int)\n\
                      (assert (> x 0))\n\
                      (assert (< (+ x y) 10))\n\
                      (check-sat)\n";
        let stats = extract_formula_stats(script);

        assert_eq!(stats.num_variables, 2, "x and y");
        assert_eq!(stats.num_int_vars, 2);
        assert_eq!(stats.num_bool_vars, 0);
        assert_eq!(stats.num_assertions, 2);
        assert!(stats.num_arith_ops >= 1, "the (+ x y) add and comparisons");
        assert!(stats.num_theory_atoms >= 2, "two comparison atoms");
        assert!(!stats.has_bitvectors);
        assert!(!stats.has_arrays);
        assert!(!stats.has_uf);
        // declare-const registers two arity-0 symbols.
        assert_eq!(stats.arity_histogram.get(&0).copied(), Some(2));
    }

    #[test]
    fn test_extract_stats_detects_theories() {
        let script = "(declare-const a (Array Int Int))\n\
                      (declare-const b (_ BitVec 8))\n\
                      (declare-fun f (Int) Int)\n\
                      (assert (= (select a 0) 1))\n\
                      (assert (= (bvadd b b) b))\n\
                      (assert (> (f 3) 0))\n\
                      (check-sat)\n";
        let stats = extract_formula_stats(script);

        assert!(stats.has_arrays, "select => arrays");
        assert!(stats.has_bitvectors, "bvadd / (_ BitVec 8) => bitvectors");
        assert!(stats.has_uf, "f application => UF");
        assert!(stats.num_array_ops >= 1);
        assert!(stats.num_bv_ops >= 1);
        assert!(stats.num_uf_apps >= 1);
        assert!(stats.bv_widths.contains(&8));
        // f has arity 1.
        assert_eq!(stats.arity_histogram.get(&1).copied(), Some(1));
    }

    #[test]
    fn test_extract_stats_quantifier_depth() {
        let script = "(declare-fun p (Int Int) Bool)\n\
                      (assert (forall ((x Int)) (exists ((y Int)) (p x y))))\n\
                      (check-sat)\n";
        let stats = extract_formula_stats(script);

        assert_eq!(stats.num_quantifiers, 2, "one forall, one exists");
        assert_eq!(stats.max_quantifier_depth, 2, "exists nested in forall");
    }

    #[test]
    fn test_extract_stats_arithmetic_degree() {
        // (* x x x) => multiplicative degree of 1 at the Mul node (single Mul
        // node), whereas nested multiplication increases the degree.
        let script = "(declare-const x Int)\n\
                      (assert (> (* x (* x x)) 0))\n\
                      (check-sat)\n";
        let stats = extract_formula_stats(script);
        assert!(
            stats.max_arith_degree >= 2,
            "nested multiplications should raise the degree, got {}",
            stats.max_arith_degree
        );
    }

    #[test]
    fn test_features_from_stats_uses_extended_slots() {
        let script = "(declare-const b (_ BitVec 16))\n\
                      (assert (= (bvmul b b) b))\n\
                      (check-sat)\n";
        let features = extract_formula_features(script);
        assert_eq!(features.features.len(), TACTIC_FEATURE_SIZE);
        // Slot 11 (index 10) = has_bitvectors.
        assert_eq!(features.features[10], 1.0);
        // Slot 16 (index 15) = max bv width / 64 = 16/64.
        assert!((features.features[15] - (16.0 / 64.0)).abs() < 1e-9);
        // Slot 15 (index 14) = arithmetic degree > 0 (bvmul present).
        assert!(features.features[14] > 0.0);
    }

    #[test]
    fn test_empty_input_yields_zero_features() {
        // Nothing measurable (empty / comment-only): honest all-zero vector,
        // not a fabricated one.
        for input in ["", "   \n\t ", "; just a comment\n"] {
            let features = extract_formula_features(input);
            assert_eq!(features.features.len(), TACTIC_FEATURE_SIZE);
            assert!(
                features.features.iter().all(|&f| f == 0.0),
                "expected all-zero features for {input:?}, got {:?}",
                features.features
            );
        }
    }
}
