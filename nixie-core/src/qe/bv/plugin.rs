//! BitVector Quantifier Elimination Plugin.
//!
//! Eliminates existential quantifiers over bit-vector variables using three
//! *sound* strategies, tried in order of cost:
//!
//! 1. **Unused variable** – if the quantified variable does not occur free in
//!    the body, `∃ x. φ ≡ φ`.
//! 2. **Definitional equality** – if the body is (or conjoins) `x = t` with
//!    `x` not occurring in `t`, then `∃ x. (x = t ∧ ψ) ≡ ψ[x := t]`.
//! 3. **Small-width brute force** – for a width `w` up to a configured bound
//!    (default 4) and within a term-size budget,
//!    `∃ x:bv[w]. φ ≡ ⋁_{v=0}^{2^w-1} φ[x := v]`.
//!
//! Anything outside these cases returns `None` (an honest "could not
//! eliminate"), never a fabricated formula.
//!
//! Reference: Niemetz et al., "Solving Quantified Bit-Vectors Using
//! Invertibility Conditions"; Z3's `qe/qe_bv_plugin.cpp`.

use crate::ast::{TermId, TermKind, TermManager};
#[allow(unused_imports)]
use crate::prelude::*;

/// Variable identifier.
pub type VarId = usize;

/// BitVector constraint.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum BvConstraint {
    /// x = value
    Eq(VarId, u64),
    /// x != value
    Neq(VarId, u64),
    /// x < value (unsigned)
    ULt(VarId, u64),
    /// x > value (unsigned)
    UGt(VarId, u64),
    /// Conjunction of constraints.
    And(Vec<BvConstraint>),
    /// Disjunction of constraints.
    Or(Vec<BvConstraint>),
}

/// Configuration for BV quantifier elimination.
#[derive(Debug, Clone)]
pub struct BvQeConfig {
    /// Enable bit-blasting (reserved; the current front-end does not bit-blast).
    pub enable_bit_blasting: bool,
    /// Maximum bitvector width to attempt elimination on at all.
    pub max_bv_width: u32,
    /// Enable case splitting / brute-force enumeration.
    pub enable_case_split: bool,
    /// Maximum width for which brute-force value enumeration is used.
    pub max_brute_force_width: u32,
    /// Term-size budget: brute force is skipped if `term_size(φ) * 2^w`
    /// exceeds this bound.
    pub brute_force_size_budget: usize,
}

impl Default for BvQeConfig {
    fn default() -> Self {
        Self {
            enable_bit_blasting: true,
            max_bv_width: 64,
            enable_case_split: true,
            max_brute_force_width: 4,
            brute_force_size_budget: 4096,
        }
    }
}

/// Statistics for BV quantifier elimination.
#[derive(Debug, Clone, Default)]
pub struct BvQeStats {
    /// Number of quantifiers eliminated.
    pub quantifiers_eliminated: u64,
    /// Number of unused-variable eliminations.
    pub unused_var: u64,
    /// Number of definitional-equality eliminations.
    pub definitional: u64,
    /// Number of brute-force enumerations.
    pub brute_force: u64,
}

/// BitVector quantifier elimination plugin.
#[derive(Debug)]
pub struct BvQePlugin {
    /// Configuration.
    config: BvQeConfig,
    /// Statistics.
    stats: BvQeStats,
}

impl BvQePlugin {
    /// Create a new BV QE plugin.
    pub fn new(config: BvQeConfig) -> Self {
        Self {
            config,
            stats: BvQeStats::default(),
        }
    }

    /// Create with default configuration.
    pub fn default_config() -> Self {
        Self::new(BvQeConfig::default())
    }

    /// Eliminate an existential quantifier over the bit-vector variable `var`
    /// from `formula`.
    ///
    /// `var` must be a `Var` term of bit-vector sort. Returns a formula
    /// equivalent to `∃ var. formula`, or `None` when none of the sound
    /// strategies apply.
    pub fn eliminate(
        &mut self,
        var: TermId,
        formula: TermId,
        tm: &mut TermManager,
    ) -> Option<TermId> {
        let sort = tm.get(var)?.sort;
        let width = tm.sorts.get(sort).and_then(|s| s.bitvec_width())?;
        if width > self.config.max_bv_width {
            return None;
        }

        // 1. Unused variable. The pattern-aware query is used deliberately:
        // an occurrence surviving only in a quantifier trigger still means
        // the variable is *not* unused, and reporting the formula as already
        // var-free would claim an elimination that never happened.
        if !tm.free_vars_including_patterns(formula).contains(&var) {
            self.stats.quantifiers_eliminated += 1;
            self.stats.unused_var += 1;
            return Some(formula);
        }

        // 2. Definitional equality x = t.
        if let Some(result) = self.try_definitional_equality(var, formula, tm) {
            self.stats.quantifiers_eliminated += 1;
            self.stats.definitional += 1;
            return Some(result);
        }

        // 3. Small-width brute force.
        if self.config.enable_case_split
            && width <= self.config.max_brute_force_width
            && let Some(result) = self.eliminate_via_enumeration(var, width, formula, tm)
        {
            self.stats.quantifiers_eliminated += 1;
            self.stats.brute_force += 1;
            return Some(result);
        }

        None
    }

    /// Try `∃ x. (x = t ∧ ψ) ≡ ψ[x := t]` (with `t` free of `x`), covering the
    /// standalone `∃ x. (x = t) ≡ true` case as well.
    fn try_definitional_equality(
        &self,
        var: TermId,
        formula: TermId,
        tm: &mut TermManager,
    ) -> Option<TermId> {
        let kind = tm.get(formula)?.kind.clone();
        match kind {
            TermKind::Eq(a, b) => {
                let def = self.definition_side(var, a, b, tm)?;
                // ∃ x. (x = t) is satisfiable (choose x = t) -> true.
                let _ = def;
                Some(tm.mk_true())
            }
            TermKind::And(args) => {
                // Find a conjunct that is a definition `x = t`.
                let mut def_term: Option<TermId> = None;
                let mut def_index: Option<usize> = None;
                for (i, &conj) in args.iter().enumerate() {
                    if let Some(TermKind::Eq(a, b)) = tm.get(conj).map(|t| t.kind.clone())
                        && let Some(t) = self.definition_side(var, a, b, tm)
                    {
                        def_term = Some(t);
                        def_index = Some(i);
                        break;
                    }
                }
                let (def_term, def_index) = (def_term?, def_index?);

                // Build the remaining conjunction and substitute x := t.
                let rest: Vec<TermId> = args
                    .iter()
                    .enumerate()
                    .filter(|(i, _)| *i != def_index)
                    .map(|(_, &c)| c)
                    .collect();
                let rest_formula = tm.mk_and(rest);
                let mut subst = FxHashMap::default();
                subst.insert(var, def_term);
                Some(tm.substitute(rest_formula, &subst))
            }
            _ => None,
        }
    }

    /// If `a = b` defines `var` (one side is exactly `var`, the other side does
    /// not contain `var`), return the defining term.
    fn definition_side(
        &self,
        var: TermId,
        a: TermId,
        b: TermId,
        tm: &TermManager,
    ) -> Option<TermId> {
        // Pattern-aware on purpose: an occurrence of `var` hiding in a
        // trigger on the other side would make the "definition" circular.
        if a == var && !tm.free_vars_including_patterns(b).contains(&var) {
            Some(b)
        } else if b == var && !tm.free_vars_including_patterns(a).contains(&var) {
            Some(a)
        } else {
            None
        }
    }

    /// `∃ x:bv[w]. φ ≡ ⋁_{v} φ[x := v]`, subject to the size budget.
    fn eliminate_via_enumeration(
        &self,
        var: TermId,
        width: u32,
        formula: TermId,
        tm: &mut TermManager,
    ) -> Option<TermId> {
        let count = 1u64 << width; // width <= 4 -> at most 16
        let size = tm.term_size(formula);
        if size.saturating_mul(count as usize) > self.config.brute_force_size_budget {
            return None;
        }

        let mut disjuncts = Vec::with_capacity(count as usize);
        for v in 0..count {
            let value = tm.mk_bitvec(v as i64, width);
            let mut subst = FxHashMap::default();
            subst.insert(var, value);
            disjuncts.push(tm.substitute(formula, &subst));
        }
        Some(tm.mk_or(disjuncts))
    }

    /// Extract bit-vector constraints on `var` from `formula`.
    ///
    /// Constraint extraction over the legacy [`VarId`]-based [`BvConstraint`]
    /// model is not implemented; this returns an empty vector (honestly, "no
    /// constraints extracted"), never fabricated ones. The elimination
    /// strategies above do not depend on it.
    pub fn extract_constraints(&self, _formula: TermId, _var: TermId) -> Vec<BvConstraint> {
        Vec::new()
    }

    /// Get statistics.
    pub fn stats(&self) -> &BvQeStats {
        &self.stats
    }

    /// Reset plugin state.
    pub fn reset(&mut self) {
        self.stats = BvQeStats::default();
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::model::{Model, ModelEvaluator, Value};

    /// Evaluate a bit-vector/Boolean formula to a bool under an assignment of
    /// `(var -> (width, value))`.
    fn eval(formula: TermId, assign: &[(TermId, u32, u64)], tm: &TermManager) -> Option<bool> {
        let mut model = Model::new();
        for &(v, w, val) in assign {
            model.assign(v, Value::BitVec(w, val));
        }
        let mut evaluator = ModelEvaluator::new(&model);
        evaluator
            .eval(formula, tm)
            .value()
            .and_then(|v| v.as_bool())
    }

    /// Check `∃ x. φ` (by enumerating x over its width) is equivalent to
    /// `eliminated` for every assignment of the free variable `y`.
    fn check_equiv(
        var: TermId,
        var_width: u32,
        y: TermId,
        y_width: u32,
        original: TermId,
        eliminated: TermId,
        tm: &TermManager,
    ) {
        for yv in 0..(1u64 << y_width) {
            // ∃ x. φ  under y := yv.
            let mut exists_val = false;
            for xv in 0..(1u64 << var_width) {
                if eval(original, &[(var, var_width, xv), (y, y_width, yv)], tm) == Some(true) {
                    exists_val = true;
                    break;
                }
            }
            let elim_val = eval(eliminated, &[(y, y_width, yv)], tm)
                .expect("eliminated formula must be evaluable without x");
            assert_eq!(exists_val, elim_val, "mismatch at y={yv}");
        }
    }

    #[test]
    fn test_plugin_creation() {
        let plugin = BvQePlugin::default_config();
        assert_eq!(plugin.stats().quantifiers_eliminated, 0);
    }

    #[test]
    fn test_config_defaults() {
        let config = BvQeConfig::default();
        assert!(config.enable_bit_blasting);
        assert_eq!(config.max_bv_width, 64);
        assert_eq!(config.max_brute_force_width, 4);
    }

    #[test]
    fn test_unused_variable() {
        // ∃ x:bv4. (y = y-ish) with x absent -> formula unchanged.
        let mut tm = TermManager::new();
        let bv4 = tm.sorts.bitvec(4);
        let x = tm.mk_var("x", bv4);
        let y = tm.mk_var("y", bv4);
        let three = tm.mk_bitvec(3i64, 4);
        let phi = tm.mk_bv_ult(y, three);

        let mut plugin = BvQePlugin::default_config();
        let result = plugin.eliminate(x, phi, &mut tm).expect("should eliminate");
        assert_eq!(result, phi);
        assert_eq!(plugin.stats().unused_var, 1);
    }

    #[test]
    fn test_definitional_equality_standalone() {
        // ∃ x:bv4. (x = a) ≡ true.
        let mut tm = TermManager::new();
        let bv4 = tm.sorts.bitvec(4);
        let x = tm.mk_var("x", bv4);
        let a = tm.mk_var("a", bv4);
        let phi = tm.mk_eq(x, a);

        let mut plugin = BvQePlugin::default_config();
        let result = plugin.eliminate(x, phi, &mut tm).expect("should eliminate");
        assert_eq!(result, tm.mk_true());
        assert_eq!(plugin.stats().definitional, 1);
    }

    #[test]
    fn test_definitional_equality_conjunction() {
        // ∃ x:bv4. (x = a ∧ x = b) ≡ (a = b).
        let mut tm = TermManager::new();
        let bv4 = tm.sorts.bitvec(4);
        let x = tm.mk_var("x", bv4);
        let a = tm.mk_var("a", bv4);
        let b = tm.mk_var("b", bv4);
        let eq_xa = tm.mk_eq(x, a);
        let eq_xb = tm.mk_eq(x, b);
        let phi = tm.mk_and([eq_xa, eq_xb]);

        let mut plugin = BvQePlugin::default_config();
        let result = plugin.eliminate(x, phi, &mut tm).expect("should eliminate");
        // x must be gone.
        assert!(!tm.free_vars(result).contains(&x));
        // Equivalent to a = b: check by evaluation over bv2-sized samples.
        // (Use a and b as the two free vars.)
        for av in 0..16u64 {
            for bv in 0..16u64 {
                let mut model = Model::new();
                model.assign(a, Value::BitVec(4, av));
                model.assign(b, Value::BitVec(4, bv));
                let mut evaluator = ModelEvaluator::new(&model);
                let got = evaluator
                    .eval(result, &tm)
                    .value()
                    .and_then(|v| v.as_bool())
                    .expect("evaluable");
                assert_eq!(got, av == bv, "at a={av}, b={bv}");
            }
        }
    }

    #[test]
    fn test_brute_force_enumeration_true() {
        // ∃ x:bv2. (x + a = 0) ≡ true (x = -a always exists).
        let mut tm = TermManager::new();
        let bv2 = tm.sorts.bitvec(2);
        let x = tm.mk_var("x", bv2);
        let a = tm.mk_var("a", bv2);
        let sum = tm.mk_bv_add(x, a);
        let zero = tm.mk_bitvec(0i64, 2);
        let phi = tm.mk_eq(sum, zero);

        let mut plugin = BvQePlugin::default_config();
        let result = plugin.eliminate(x, phi, &mut tm).expect("should eliminate");
        assert!(!tm.free_vars(result).contains(&x));
        check_equiv(x, 2, a, 2, phi, result, &tm);
        assert_eq!(plugin.stats().brute_force, 1);
    }

    #[test]
    fn test_brute_force_enumeration_constraint() {
        // ∃ x:bv2. (x + a = 0 ∧ a = 1) – only true when a = 1.
        let mut tm = TermManager::new();
        let bv2 = tm.sorts.bitvec(2);
        let x = tm.mk_var("x", bv2);
        let a = tm.mk_var("a", bv2);
        let sum = tm.mk_bv_add(x, a);
        let zero = tm.mk_bitvec(0i64, 2);
        let one = tm.mk_bitvec(1i64, 2);
        let eq0 = tm.mk_eq(sum, zero);
        let a_is_1 = tm.mk_eq(a, one);
        let phi = tm.mk_and([eq0, a_is_1]);

        let mut plugin = BvQePlugin::default_config();
        let result = plugin.eliminate(x, phi, &mut tm).expect("should eliminate");
        assert!(!tm.free_vars(result).contains(&x));
        check_equiv(x, 2, a, 2, phi, result, &tm);
    }

    #[test]
    fn test_large_width_returns_none() {
        // Width 32, no unused/definitional structure -> None (honest).
        let mut tm = TermManager::new();
        let bv32 = tm.sorts.bitvec(32);
        let x = tm.mk_var("x", bv32);
        let a = tm.mk_var("a", bv32);
        let phi = tm.mk_bv_ult(x, a);

        let mut plugin = BvQePlugin::default_config();
        assert!(plugin.eliminate(x, phi, &mut tm).is_none());
    }
}
