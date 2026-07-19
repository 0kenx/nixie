//! Bit-Vector Rewriting Tactic.
//!
//! Applies algebraic and structural rewrites to simplify bit-vector formulas.
//! Essential preprocessing for efficient solving.
//!
//! ## Rewrites
//!
//! - **Algebraic**: x + 0 = x, x * 1 = x, x & x = x
//! - **Structural**: Flatten nested operations, normalize constants
//! - **Bit-tricks**: Use XOR/AND identities for simplification
//!
//! ## References
//!
//! - "Effective Bit-Width Analysis" (Brummayer & Biere, 2009)
//! - Z3's `tactic/bv/bv_rewriter.cpp`

#[allow(unused_imports)]
use crate::prelude::*;
use crate::{TermId, TermKind, TermManager};
use num_bigint::BigInt;
use num_traits::Zero;

/// Bit-vector width.
pub type BvWidth = u32;

/// Configuration for BV rewriter.
#[derive(Debug, Clone)]
pub struct BvRewriterConfig {
    /// Enable algebraic rewrites.
    pub enable_algebraic: bool,
    /// Enable structural rewrites.
    pub enable_structural: bool,
    /// Enable bit-trick rewrites.
    pub enable_bit_tricks: bool,
    /// Flatten associative operators.
    pub flatten_associative: bool,
    /// Normalize constants to canonical form.
    pub normalize_constants: bool,
}

impl Default for BvRewriterConfig {
    fn default() -> Self {
        Self {
            enable_algebraic: true,
            enable_structural: true,
            enable_bit_tricks: true,
            flatten_associative: true,
            normalize_constants: true,
        }
    }
}

/// Statistics for BV rewriter.
#[derive(Debug, Clone, Default)]
pub struct BvRewriterStats {
    /// Algebraic rewrites applied.
    pub algebraic_rewrites: u64,
    /// Structural rewrites applied.
    pub structural_rewrites: u64,
    /// Bit-trick rewrites applied.
    pub bit_trick_rewrites: u64,
    /// Terms rewritten.
    pub terms_rewritten: u64,
    /// Terms unchanged.
    pub terms_unchanged: u64,
}

/// BV rewriting tactic.
pub struct BvRewriterTactic {
    /// Term manager.
    manager: TermManager,
    /// Rewrite cache.
    cache: FxHashMap<TermId, TermId>,
    /// Configuration.
    config: BvRewriterConfig,
    /// Statistics.
    stats: BvRewriterStats,
}

impl BvRewriterTactic {
    /// Create a new BV rewriter tactic.
    pub fn new(manager: TermManager, config: BvRewriterConfig) -> Self {
        Self {
            manager,
            cache: FxHashMap::default(),
            config,
            stats: BvRewriterStats::default(),
        }
    }

    /// Create with default configuration.
    pub fn default_config(manager: TermManager) -> Self {
        Self::new(manager, BvRewriterConfig::default())
    }

    /// Rewrite a term.
    pub fn rewrite(&mut self, term: TermId) -> TermId {
        // Check cache
        if let Some(&cached) = self.cache.get(&term) {
            return cached;
        }

        let result = self.rewrite_uncached(term);

        // Update cache
        self.cache.insert(term, result);

        if result != term {
            self.stats.terms_rewritten += 1;
        } else {
            self.stats.terms_unchanged += 1;
        }

        result
    }

    /// Rewrite without caching.
    fn rewrite_uncached(&mut self, term: TermId) -> TermId {
        let term_data = match self.manager.get(term) {
            Some(t) => t.clone(),
            None => return term,
        };

        match &term_data.kind {
            TermKind::BvAdd(arg1, arg2) => self.rewrite_bv_add(*arg1, *arg2),
            TermKind::BvMul(arg1, arg2) => self.rewrite_bv_mul(*arg1, *arg2),
            TermKind::BvAnd(arg1, arg2) => self.rewrite_bv_and(*arg1, *arg2),
            TermKind::BvOr(arg1, arg2) => self.rewrite_bv_or(*arg1, *arg2),
            TermKind::BvXor(arg1, arg2) => self.rewrite_bv_xor(*arg1, *arg2),
            TermKind::BvNot(arg) => self.rewrite_bv_not(*arg),
            TermKind::BvSub(arg1, arg2) => self.rewrite_bv_sub(*arg1, *arg2),
            _ => term, // Other operators unchanged
        }
    }

    /// Rewrite BV addition: x + 0 = x, 0 + x = x
    fn rewrite_bv_add(&mut self, arg1: TermId, arg2: TermId) -> TermId {
        if !self.config.enable_algebraic {
            return self.reconstruct_bv_add(arg1, arg2);
        }

        let rewritten_arg1 = self.rewrite(arg1);
        let rewritten_arg2 = self.rewrite(arg2);

        // x + 0 = x
        if self.is_bv_zero(rewritten_arg2) {
            self.stats.algebraic_rewrites += 1;
            return rewritten_arg1;
        }

        // 0 + x = x
        if self.is_bv_zero(rewritten_arg1) {
            self.stats.algebraic_rewrites += 1;
            return rewritten_arg2;
        }

        self.reconstruct_bv_add(rewritten_arg1, rewritten_arg2)
    }

    /// Rewrite BV multiplication: x * 1 = x, x * 0 = 0
    fn rewrite_bv_mul(&mut self, arg1: TermId, arg2: TermId) -> TermId {
        if !self.config.enable_algebraic {
            return self.reconstruct_bv_mul(arg1, arg2);
        }

        let rewritten_arg1 = self.rewrite(arg1);
        let rewritten_arg2 = self.rewrite(arg2);

        // x * 0 = 0
        if self.is_bv_zero(rewritten_arg2) {
            self.stats.algebraic_rewrites += 1;
            return rewritten_arg2;
        }

        // 0 * x = 0
        if self.is_bv_zero(rewritten_arg1) {
            self.stats.algebraic_rewrites += 1;
            return rewritten_arg1;
        }

        // x * 1 = x
        if self.is_bv_one(rewritten_arg2) {
            self.stats.algebraic_rewrites += 1;
            return rewritten_arg1;
        }

        // 1 * x = x
        if self.is_bv_one(rewritten_arg1) {
            self.stats.algebraic_rewrites += 1;
            return rewritten_arg2;
        }

        self.reconstruct_bv_mul(rewritten_arg1, rewritten_arg2)
    }

    /// Rewrite BV AND: x & x = x, x & 0 = 0, x & ~0 = x
    fn rewrite_bv_and(&mut self, arg1: TermId, arg2: TermId) -> TermId {
        if !self.config.enable_algebraic {
            return self.reconstruct_bv_and(arg1, arg2);
        }

        let rewritten_arg1 = self.rewrite(arg1);
        let rewritten_arg2 = self.rewrite(arg2);

        // x & 0 = 0
        if self.is_bv_zero(rewritten_arg2) {
            self.stats.algebraic_rewrites += 1;
            return rewritten_arg2;
        }

        // 0 & x = 0
        if self.is_bv_zero(rewritten_arg1) {
            self.stats.algebraic_rewrites += 1;
            return rewritten_arg1;
        }

        // x & ~0 = x
        if self.is_bv_all_ones(rewritten_arg2) {
            self.stats.algebraic_rewrites += 1;
            return rewritten_arg1;
        }

        // ~0 & x = x
        if self.is_bv_all_ones(rewritten_arg1) {
            self.stats.algebraic_rewrites += 1;
            return rewritten_arg2;
        }

        // x & x = x
        if rewritten_arg1 == rewritten_arg2 {
            self.stats.algebraic_rewrites += 1;
            return rewritten_arg1;
        }

        self.reconstruct_bv_and(rewritten_arg1, rewritten_arg2)
    }

    /// Rewrite BV OR: x | x = x, x | 0 = x, x | ~0 = ~0
    fn rewrite_bv_or(&mut self, arg1: TermId, arg2: TermId) -> TermId {
        if !self.config.enable_algebraic {
            return self.reconstruct_bv_or(arg1, arg2);
        }

        let rewritten_arg1 = self.rewrite(arg1);
        let rewritten_arg2 = self.rewrite(arg2);

        // x | ~0 = ~0
        if self.is_bv_all_ones(rewritten_arg2) {
            self.stats.algebraic_rewrites += 1;
            return rewritten_arg2;
        }

        // ~0 | x = ~0
        if self.is_bv_all_ones(rewritten_arg1) {
            self.stats.algebraic_rewrites += 1;
            return rewritten_arg1;
        }

        // x | 0 = x
        if self.is_bv_zero(rewritten_arg2) {
            self.stats.algebraic_rewrites += 1;
            return rewritten_arg1;
        }

        // 0 | x = x
        if self.is_bv_zero(rewritten_arg1) {
            self.stats.algebraic_rewrites += 1;
            return rewritten_arg2;
        }

        // x | x = x
        if rewritten_arg1 == rewritten_arg2 {
            self.stats.algebraic_rewrites += 1;
            return rewritten_arg1;
        }

        self.reconstruct_bv_or(rewritten_arg1, rewritten_arg2)
    }

    /// Rewrite BV XOR: x ^ x = 0, x ^ 0 = x
    fn rewrite_bv_xor(&mut self, arg1: TermId, arg2: TermId) -> TermId {
        if !self.config.enable_bit_tricks {
            return self.reconstruct_bv_xor(arg1, arg2);
        }

        let rewritten_arg1 = self.rewrite(arg1);
        let rewritten_arg2 = self.rewrite(arg2);

        // x ^ 0 = x
        if self.is_bv_zero(rewritten_arg2) {
            self.stats.bit_trick_rewrites += 1;
            return rewritten_arg1;
        }

        // 0 ^ x = x
        if self.is_bv_zero(rewritten_arg1) {
            self.stats.bit_trick_rewrites += 1;
            return rewritten_arg2;
        }

        // x ^ x = 0
        if rewritten_arg1 == rewritten_arg2 {
            self.stats.bit_trick_rewrites += 1;
            return self.make_bv_zero(self.get_bv_width(rewritten_arg1));
        }

        self.reconstruct_bv_xor(rewritten_arg1, rewritten_arg2)
    }

    /// Rewrite BV NOT: ~~x = x
    fn rewrite_bv_not(&mut self, arg: TermId) -> TermId {
        let rewritten_arg = self.rewrite(arg);

        // Check for double negation
        if let Some(term) = self.manager.get(rewritten_arg)
            && let TermKind::BvNot(inner) = term.kind
        {
            self.stats.structural_rewrites += 1;
            return inner;
        }

        self.reconstruct_bv_not(rewritten_arg)
    }

    /// Rewrite BV SUB: x - 0 = x
    fn rewrite_bv_sub(&mut self, arg1: TermId, arg2: TermId) -> TermId {
        let rewritten_arg1 = self.rewrite(arg1);
        let rewritten_arg2 = self.rewrite(arg2);

        // x - 0 = x
        if self.is_bv_zero(rewritten_arg2) {
            self.stats.algebraic_rewrites += 1;
            return rewritten_arg1;
        }

        self.reconstruct_bv_sub(rewritten_arg1, rewritten_arg2)
    }

    // Helper methods

    /// Mask consisting of `width` set bits (i.e. `2^width - 1`), used to
    /// recognize/construct the all-ones bit-vector constant.
    fn all_ones_mask(width: BvWidth) -> BigInt {
        if width == 0 {
            BigInt::zero()
        } else {
            (BigInt::from(1) << width) - BigInt::from(1)
        }
    }

    fn is_bv_zero(&self, term: TermId) -> bool {
        matches!(
            self.manager.get(term).map(|t| &t.kind),
            Some(TermKind::BitVecConst { value, .. }) if value.is_zero()
        )
    }

    fn is_bv_one(&self, term: TermId) -> bool {
        matches!(
            self.manager.get(term).map(|t| &t.kind),
            Some(TermKind::BitVecConst { value, .. }) if *value == BigInt::from(1)
        )
    }

    fn is_bv_all_ones(&self, term: TermId) -> bool {
        matches!(
            self.manager.get(term).map(|t| &t.kind),
            Some(TermKind::BitVecConst { value, width }) if *value == Self::all_ones_mask(*width)
        )
    }

    fn make_bv_zero(&mut self, width: BvWidth) -> TermId {
        self.manager.mk_bitvec(0u64, width)
    }

    #[allow(dead_code)]
    fn make_bv_one(&mut self, width: BvWidth) -> TermId {
        self.manager.mk_bitvec(1u64, width)
    }

    #[allow(dead_code)]
    fn make_bv_all_ones(&mut self, width: BvWidth) -> TermId {
        self.manager.mk_bitvec(Self::all_ones_mask(width), width)
    }

    /// Get the bit-vector width of `term` from its sort. Falls back to 32
    /// only for malformed/dangling term ids, which cannot occur for terms
    /// reached through well-typed `BvXor`/etc. arguments.
    fn get_bv_width(&self, term: TermId) -> BvWidth {
        self.manager
            .get(term)
            .and_then(|t| self.manager.sorts.get(t.sort))
            .and_then(|s| s.bitvec_width())
            .unwrap_or(32)
    }

    fn reconstruct_bv_add(&mut self, arg1: TermId, arg2: TermId) -> TermId {
        self.manager.mk_bv_add(arg1, arg2)
    }

    fn reconstruct_bv_mul(&mut self, arg1: TermId, arg2: TermId) -> TermId {
        self.manager.mk_bv_mul(arg1, arg2)
    }

    fn reconstruct_bv_and(&mut self, arg1: TermId, arg2: TermId) -> TermId {
        self.manager.mk_bv_and(arg1, arg2)
    }

    fn reconstruct_bv_or(&mut self, arg1: TermId, arg2: TermId) -> TermId {
        self.manager.mk_bv_or(arg1, arg2)
    }

    fn reconstruct_bv_xor(&mut self, arg1: TermId, arg2: TermId) -> TermId {
        self.manager.mk_bv_xor(arg1, arg2)
    }

    fn reconstruct_bv_not(&mut self, arg: TermId) -> TermId {
        self.manager.mk_bv_not(arg)
    }

    fn reconstruct_bv_sub(&mut self, arg1: TermId, arg2: TermId) -> TermId {
        self.manager.mk_bv_sub(arg1, arg2)
    }

    /// Clear rewrite cache.
    pub fn clear_cache(&mut self) {
        self.cache.clear();
    }

    /// Get statistics.
    pub fn stats(&self) -> &BvRewriterStats {
        &self.stats
    }

    /// Reset statistics.
    pub fn reset_stats(&mut self) {
        self.stats = BvRewriterStats::default();
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_tactic_creation() {
        let manager = TermManager::default();
        let tactic = BvRewriterTactic::default_config(manager);
        assert_eq!(tactic.stats().terms_rewritten, 0);
    }

    #[test]
    fn test_config_default() {
        let config = BvRewriterConfig::default();
        assert!(config.enable_algebraic);
        assert!(config.enable_structural);
        assert!(config.enable_bit_tricks);
    }

    #[test]
    fn test_stats() {
        let manager = TermManager::default();
        let mut tactic = BvRewriterTactic::default_config(manager);

        tactic.stats.algebraic_rewrites = 10;
        tactic.stats.structural_rewrites = 5;

        assert_eq!(tactic.stats().algebraic_rewrites, 10);
        assert_eq!(tactic.stats().structural_rewrites, 5);

        tactic.reset_stats();
        assert_eq!(tactic.stats().algebraic_rewrites, 0);
    }

    #[test]
    fn test_clear_cache() {
        let manager = TermManager::default();
        let mut tactic = BvRewriterTactic::default_config(manager);

        tactic.cache.insert(TermId(0), TermId(1));
        assert!(!tactic.cache.is_empty());

        tactic.clear_cache();
        assert!(tactic.cache.is_empty());
    }

    // Regression tests for the data-corruption bug where every
    // reconstruct_* helper returned the arbitrary sentinel `TermId(0)`
    // instead of a real reconstructed (or simplified) term.

    #[test]
    fn test_rewrite_add_zero_returns_original_term() {
        let mut manager = TermManager::default();
        let bv8 = manager.sorts.bitvec(8);
        let x = manager.mk_var("x", bv8);
        let zero = manager.mk_bitvec(0u64, 8);
        let add = manager.mk_bv_add(x, zero);

        let mut tactic = BvRewriterTactic::default_config(manager);
        let result = tactic.rewrite(add);

        assert_ne!(result, TermId(0));
        assert_eq!(result, x);
    }

    #[test]
    fn test_rewrite_and_self_returns_original_term() {
        let mut manager = TermManager::default();
        let bv8 = manager.sorts.bitvec(8);
        let x = manager.mk_var("x", bv8);
        let and_term = manager.mk_bv_and(x, x);

        let mut tactic = BvRewriterTactic::default_config(manager);
        let result = tactic.rewrite(and_term);

        assert_ne!(result, TermId(0));
        assert_eq!(result, x);
    }

    #[test]
    fn test_rewrite_generic_add_reconstructs_valid_bv_term() {
        let mut manager = TermManager::default();
        let bv8 = manager.sorts.bitvec(8);
        let x = manager.mk_var("x", bv8);
        let y = manager.mk_var("y", bv8);
        let add = manager.mk_bv_add(x, y);

        let mut tactic = BvRewriterTactic::default_config(manager);
        let result = tactic.rewrite(add);

        // Must not be the old data-corrupting sentinel.
        assert_ne!(result, TermId(0));
        // Must be exactly the (interned) reconstructed addition term.
        let expected = tactic.manager.mk_bv_add(x, y);
        assert_eq!(result, expected);
    }

    #[test]
    fn test_rewrite_xor_self_returns_zero_constant() {
        let mut manager = TermManager::default();
        let bv8 = manager.sorts.bitvec(8);
        let x = manager.mk_var("x", bv8);
        let xor_term = manager.mk_bv_xor(x, x);

        let mut tactic = BvRewriterTactic::default_config(manager);
        let result = tactic.rewrite(xor_term);

        assert_ne!(result, TermId(0));
        let term = tactic
            .manager
            .get(result)
            .expect("rewritten term must exist");
        match &term.kind {
            TermKind::BitVecConst { value, width } => {
                assert!(value.is_zero());
                assert_eq!(*width, 8);
            }
            other => panic!("expected BitVecConst 0, got {other:?}"),
        }
    }

    #[test]
    fn test_is_bv_all_ones_detection() {
        let mut manager = TermManager::default();
        let all_ones = manager.mk_bitvec(0xFFu64, 8);
        let not_all_ones = manager.mk_bitvec(0x0Fu64, 8);
        let tactic = BvRewriterTactic::default_config(manager);

        assert!(tactic.is_bv_all_ones(all_ones));
        assert!(!tactic.is_bv_all_ones(not_all_ones));
    }

    #[test]
    fn test_rewrite_and_with_all_ones_returns_other_operand() {
        let mut manager = TermManager::default();
        let bv8 = manager.sorts.bitvec(8);
        let x = manager.mk_var("x", bv8);
        let all_ones = manager.mk_bitvec(0xFFu64, 8);
        let and_term = manager.mk_bv_and(x, all_ones);

        let mut tactic = BvRewriterTactic::default_config(manager);
        let result = tactic.rewrite(and_term);

        assert_ne!(result, TermId(0));
        assert_eq!(result, x);
    }
}
