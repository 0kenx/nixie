//! Omega Test for Integer Linear Arithmetic QE.
//!
//! Implements the Omega Test algorithm for quantifier elimination
//! over Presburger arithmetic (linear integer arithmetic).
//!
//! ## Algorithm
//!
//! For `∃x. φ(x)` where φ is a conjunction of linear constraints:
//! 1. Isolate bounds on x (x ≥ a₁, ..., x ≤ b₁, ...)
//! 2. Check real shadow (∃x ∈ ℝ. φ)
//! 3. Compute dark shadow and gray shadow
//! 4. Recursively eliminate if needed
//!
//! ## References
//!
//! - "The Omega Test" (Pugh, 1992)
//! - Z3's `qe/qe_arith.cpp`

/// Variable identifier.
#[allow(unused_imports)]
use crate::prelude::*;
/// Variable identifier for Omega test.
pub type VarId = usize;

/// Linear constraint: Σ aᵢxᵢ ≤ b.
#[derive(Debug, Clone)]
pub struct LinearConstraint {
    /// Coefficients.
    pub coeffs: FxHashMap<VarId, i64>,
    /// Right-hand side.
    pub rhs: i64,
}

impl LinearConstraint {
    /// Create a new linear constraint.
    pub fn new(coeffs: FxHashMap<VarId, i64>, rhs: i64) -> Self {
        Self { coeffs, rhs }
    }

    /// Get coefficient for a variable.
    pub fn get_coeff(&self, var: VarId) -> i64 {
        self.coeffs.get(&var).copied().unwrap_or(0)
    }
}

/// Omega test result.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum OmegaResult {
    /// Formula is satisfiable.
    Satisfiable,
    /// Formula is unsatisfiable.
    Unsatisfiable,
    /// Unknown (timeout or complexity limit).
    Unknown,
}

/// Value of a shadow gap expression `b·α − a·β`.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum ShadowValue {
    /// The gap reduces to a constant (no other variables remain).
    Const(i64),
    /// The gap still depends on other variables — undecidable here.
    Symbolic,
}

/// Configuration for Omega test.
#[derive(Debug, Clone)]
pub struct OmegaTestConfig {
    /// Enable real shadow check.
    pub enable_real_shadow: bool,
    /// Enable dark shadow.
    pub enable_dark_shadow: bool,
    /// Maximum recursion depth.
    pub max_depth: usize,
}

impl Default for OmegaTestConfig {
    fn default() -> Self {
        Self {
            enable_real_shadow: true,
            enable_dark_shadow: true,
            max_depth: 10,
        }
    }
}

/// Statistics for Omega test.
#[derive(Debug, Clone, Default)]
pub struct OmegaTestStats {
    /// Variables eliminated.
    pub vars_eliminated: u64,
    /// Real shadow checks.
    pub real_shadow_checks: u64,
    /// Dark shadow checks.
    pub dark_shadow_checks: u64,
    /// Recursive calls.
    pub recursive_calls: u64,
}

/// Omega test engine.
#[derive(Debug)]
pub struct OmegaTester {
    /// Current constraints.
    constraints: Vec<LinearConstraint>,
    /// Configuration.
    config: OmegaTestConfig,
    /// Statistics.
    stats: OmegaTestStats,
    /// Current recursion depth.
    depth: usize,
}

impl OmegaTester {
    /// Create a new Omega tester.
    pub fn new(config: OmegaTestConfig) -> Self {
        Self {
            constraints: Vec::new(),
            config,
            stats: OmegaTestStats::default(),
            depth: 0,
        }
    }

    /// Create with default configuration.
    pub fn default_config() -> Self {
        Self::new(OmegaTestConfig::default())
    }

    /// Add a constraint.
    pub fn add_constraint(&mut self, constraint: LinearConstraint) {
        self.constraints.push(constraint);
    }

    /// Eliminate a variable using the Omega test.
    ///
    /// Projects `var` out of the current constraint system using Pugh's real
    /// and dark shadow tests, and reports whether the projection is
    /// satisfiable, unsatisfiable, or undetermined:
    ///
    /// * `Unsatisfiable` — some lower/upper bound pair yields an empty real
    ///   interval that reduces to a constant contradiction, or a
    ///   variable-free constraint is violated.
    /// * `Satisfiable` — every constraint mentions only `var`, every real
    ///   shadow is (constantly) non-empty, and every dark shadow holds, so an
    ///   integer solution is guaranteed.
    /// * `Unknown` — the projection still involves other variables (the exact
    ///   Omega splitting/recursion is not carried out here), so no sound
    ///   definite answer can be given.
    pub fn eliminate(&mut self, var: VarId) -> OmegaResult {
        if self.depth >= self.config.max_depth {
            return OmegaResult::Unknown;
        }

        self.stats.vars_eliminated += 1;
        self.depth += 1;

        let result = self.eliminate_inner(var);

        self.depth -= 1;
        result
    }

    /// Core projection logic (see [`OmegaTester::eliminate`]).
    fn eliminate_inner(&mut self, var: VarId) -> OmegaResult {
        // Reject variable-free constraints that are already contradictory
        // (0 ≤ rhs with rhs < 0), and detect whether the projection leaves any
        // constraint mentioning a variable other than `var`.
        let mut has_other_vars = false;
        for constraint in &self.constraints {
            let mentions_var = constraint.get_coeff(var) != 0;
            let mentions_other = constraint.coeffs.iter().any(|(&v, &c)| v != var && c != 0);
            if !mentions_var {
                if !mentions_other {
                    // Purely constant constraint: 0 ≤ rhs.
                    if constraint.rhs < 0 {
                        return OmegaResult::Unsatisfiable;
                    }
                } else {
                    // Remains after projecting out `var`.
                    has_other_vars = true;
                }
            } else if mentions_other {
                has_other_vars = true;
            }
        }

        // Split the constraints on `var` into lower and upper bounds.
        // Constraint form: Σ cₖ·xₖ ≤ rhs. For `var` with coefficient c:
        //   c > 0 → upper bound on var:  c·var ≤ α   (α = rhs − rest)
        //   c < 0 → lower bound on var:  b·var ≥ β   (b = |c|, β = rest − rhs)
        // `extract_bound_indices` returns (coeff > 0, coeff < 0), i.e.
        // (upper-bound indices, lower-bound indices).
        let (upper_indices, lower_indices) = self.extract_bound_indices(var);

        let mut definite = !has_other_vars;

        if self.config.enable_real_shadow {
            for &upper_idx in &upper_indices {
                for &lower_idx in &lower_indices {
                    match self.real_shadow_pair(var, upper_idx, lower_idx) {
                        ShadowValue::Const(k) => {
                            // Real shadow feasible ⟺ k ≥ 0.
                            if k < 0 {
                                return OmegaResult::Unsatisfiable;
                            }
                        }
                        ShadowValue::Symbolic => definite = false,
                    }
                }
            }
        } else {
            // Cannot rule out infeasibility without the real shadow.
            definite = false;
        }

        if self.config.enable_dark_shadow {
            for &upper_idx in &upper_indices {
                for &lower_idx in &lower_indices {
                    if !self.dark_shadow_pair(var, upper_idx, lower_idx) {
                        definite = false;
                    }
                }
            }
        } else {
            definite = false;
        }

        if definite {
            OmegaResult::Satisfiable
        } else {
            self.stats.recursive_calls += 1;
            OmegaResult::Unknown
        }
    }

    /// Extract lower and upper bound constraint indices for a variable.
    ///
    /// The returned pair is `(coeff > 0 indices, coeff < 0 indices)`.
    fn extract_bound_indices(&self, var: VarId) -> (Vec<usize>, Vec<usize>) {
        let mut lower = Vec::new();
        let mut upper = Vec::new();

        for (idx, constraint) in self.constraints.iter().enumerate() {
            let coeff = constraint.get_coeff(var);
            if coeff > 0 {
                lower.push(idx);
            } else if coeff < 0 {
                upper.push(idx);
            }
        }

        (lower, upper)
    }

    /// Real shadow value for an (upper, lower) constraint pair.
    ///
    /// `upper_idx` has `var`-coefficient `a > 0` giving `a·var ≤ α`;
    /// `lower_idx` has `var`-coefficient `−b < 0` giving `b·var ≥ β`.
    /// The real shadow requires `a·β ≤ b·α`, i.e. `b·α − a·β ≥ 0`.
    /// Returns the constant value of `b·α − a·β` when it does not involve any
    /// other variable, otherwise [`ShadowValue::Symbolic`].
    fn real_shadow_pair(&mut self, var: VarId, upper_idx: usize, lower_idx: usize) -> ShadowValue {
        self.stats.real_shadow_checks += 1;
        self.shadow_gap(var, upper_idx, lower_idx)
    }

    /// Dark shadow test for an (upper, lower) constraint pair.
    ///
    /// With `a·var ≤ α` and `b·var ≥ β`, the dark shadow holds when
    /// `b·α − a·β ≥ (a − 1)(b − 1)`, which guarantees an integer in the
    /// interval. Only decidable when the gap is a constant.
    fn dark_shadow_pair(&mut self, var: VarId, upper_idx: usize, lower_idx: usize) -> bool {
        self.stats.dark_shadow_checks += 1;
        let a = self.constraints[upper_idx].get_coeff(var); // > 0
        let b = -self.constraints[lower_idx].get_coeff(var); // > 0
        match self.shadow_gap(var, upper_idx, lower_idx) {
            ShadowValue::Const(gap) => {
                let threshold = (a - 1) * (b - 1);
                gap >= threshold
            }
            ShadowValue::Symbolic => false,
        }
    }

    /// Compute `b·α − a·β` for the pair, as a [`ShadowValue`].
    ///
    /// `α = rhs_u − rest_u` (from `a·var + rest_u ≤ rhs_u`) and
    /// `β = rest_l − rhs_l` (from `−b·var + rest_l ≤ rhs_l`, i.e.
    /// `b·var ≥ rest_l − rhs_l`). The result's non-`var` variable coefficients
    /// are `b·(−rest_u) − a·(rest_l)`; if all vanish the gap is constant.
    fn shadow_gap(&self, var: VarId, upper_idx: usize, lower_idx: usize) -> ShadowValue {
        let upper = &self.constraints[upper_idx];
        let lower = &self.constraints[lower_idx];
        let a = upper.get_coeff(var); // a > 0
        let b = -lower.get_coeff(var); // b > 0

        // Accumulate coefficients of the other variables in b·α − a·β.
        let mut acc: FxHashMap<VarId, i64> = FxHashMap::default();
        // α = rhs_u − rest_u  →  contributes b·α: constant b·rhs_u, vars −b·rest_u.
        for (&v, &c) in &upper.coeffs {
            if v == var {
                continue;
            }
            *acc.entry(v).or_insert(0) += -b * c;
        }
        // β = rest_l − rhs_l  →  contributes −a·β: constant a·rhs_l, vars −a·rest_l.
        for (&v, &c) in &lower.coeffs {
            if v == var {
                continue;
            }
            *acc.entry(v).or_insert(0) += -a * c;
        }

        if acc.values().any(|&c| c != 0) {
            return ShadowValue::Symbolic;
        }

        // Constant part: b·rhs_u − a·(−rhs_l) = b·rhs_u + a·rhs_l.
        let gap = b * upper.rhs + a * lower.rhs;
        ShadowValue::Const(gap)
    }

    /// Get statistics.
    pub fn stats(&self) -> &OmegaTestStats {
        &self.stats
    }

    /// Reset statistics.
    pub fn reset_stats(&mut self) {
        self.stats = OmegaTestStats::default();
    }
}

impl Default for OmegaTester {
    fn default() -> Self {
        Self::default_config()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_tester_creation() {
        let tester = OmegaTester::default_config();
        assert_eq!(tester.stats().vars_eliminated, 0);
    }

    #[test]
    fn test_add_constraint() {
        let mut tester = OmegaTester::default_config();
        let mut coeffs = FxHashMap::default();
        coeffs.insert(0, 1);

        tester.add_constraint(LinearConstraint::new(coeffs, 10));
        assert_eq!(tester.constraints.len(), 1);
    }

    #[test]
    fn test_extract_bounds() {
        let mut tester = OmegaTester::default_config();

        // x ≥ 5 (equivalently -x ≤ -5, so coeff of x is -1)
        let mut coeffs1 = FxHashMap::default();
        coeffs1.insert(0, -1);
        tester.add_constraint(LinearConstraint::new(coeffs1, -5));

        // x ≤ 10 (coeff of x is 1)
        let mut coeffs2 = FxHashMap::default();
        coeffs2.insert(0, 1);
        tester.add_constraint(LinearConstraint::new(coeffs2, 10));

        let (lower, upper) = tester.extract_bound_indices(0);
        assert_eq!(lower.len(), 1); // x ≤ 10
        assert_eq!(upper.len(), 1); // -x ≤ -5 (upper bound)
    }

    #[test]
    fn test_eliminate() {
        let mut tester = OmegaTester::default_config();
        let mut coeffs = FxHashMap::default();
        coeffs.insert(0, 1);

        tester.add_constraint(LinearConstraint::new(coeffs, 10));

        let result = tester.eliminate(0);
        assert!(matches!(
            result,
            OmegaResult::Satisfiable | OmegaResult::Unknown
        ));
        assert_eq!(tester.stats().vars_eliminated, 1);
    }

    #[test]
    fn test_stats() {
        let mut tester = OmegaTester::default_config();
        tester.stats.vars_eliminated = 5;

        assert_eq!(tester.stats().vars_eliminated, 5);

        tester.reset_stats();
        assert_eq!(tester.stats().vars_eliminated, 0);
    }

    /// Helper: `Σ coeffs ≤ rhs` from `(var, coeff)` pairs.
    fn constraint(pairs: &[(VarId, i64)], rhs: i64) -> LinearConstraint {
        let mut coeffs = FxHashMap::default();
        for &(v, c) in pairs {
            coeffs.insert(v, c);
        }
        LinearConstraint::new(coeffs, rhs)
    }

    #[test]
    fn test_real_shadow_detects_unsat() {
        // x ≤ 3  ∧  x ≥ 5  (i.e. -x ≤ -5) — empty interval.
        let mut tester = OmegaTester::default_config();
        tester.add_constraint(constraint(&[(0, 1)], 3));
        tester.add_constraint(constraint(&[(0, -1)], -5));

        assert_eq!(tester.eliminate(0), OmegaResult::Unsatisfiable);
        assert!(tester.stats().real_shadow_checks >= 1);
    }

    #[test]
    fn test_dark_shadow_detects_sat() {
        // 2x ≤ 7  ∧  2x ≥ 3 (i.e. -2x ≤ -3): integers 2, 3 lie in [1.5, 3.5].
        let mut tester = OmegaTester::default_config();
        tester.add_constraint(constraint(&[(0, 2)], 7));
        tester.add_constraint(constraint(&[(0, -2)], -3));

        assert_eq!(tester.eliminate(0), OmegaResult::Satisfiable);
        assert!(tester.stats().dark_shadow_checks >= 1);
    }

    #[test]
    fn test_gray_shadow_is_unknown() {
        // 3x ≤ 4 ∧ 3x ≥ 3: real shadow feasible but dark shadow fails, so the
        // Omega test (without the splitting recursion) honestly reports Unknown
        // rather than fabricating an answer.
        let mut tester = OmegaTester::default_config();
        tester.add_constraint(constraint(&[(0, 3)], 4));
        tester.add_constraint(constraint(&[(0, -3)], -3));

        assert_eq!(tester.eliminate(0), OmegaResult::Unknown);
    }

    #[test]
    fn test_other_variables_are_unknown() {
        // x ≤ y ∧ x ≥ 0 — projection still depends on y → Unknown.
        let mut tester = OmegaTester::default_config();
        tester.add_constraint(constraint(&[(0, 1), (1, -1)], 0)); // x - y ≤ 0
        tester.add_constraint(constraint(&[(0, -1)], 0)); // -x ≤ 0

        assert_eq!(tester.eliminate(0), OmegaResult::Unknown);
    }

    #[test]
    fn test_constant_contradiction_is_unsat() {
        // A variable-free contradictory constraint 0 ≤ -1.
        let mut tester = OmegaTester::default_config();
        tester.add_constraint(constraint(&[(0, 1)], 10));
        tester.add_constraint(constraint(&[], -1));

        assert_eq!(tester.eliminate(0), OmegaResult::Unsatisfiable);
    }
}
