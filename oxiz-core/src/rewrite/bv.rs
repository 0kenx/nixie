//! Bit-Vector Term Rewriter
//!
//! This module provides rewriting rules for bit-vector expressions:
//! - Constant folding for BV operations
//! - Simplification of identity operations
//! - Zero/One simplification
//! - Algebraic simplifications
//! - Shift simplifications
//! - Extract/Concat normalization

use super::{RewriteContext, RewriteResult, Rewriter};
use crate::ast::{TermId, TermKind, TermManager};
#[allow(unused_imports)]
use crate::prelude::*;
use num_bigint::BigInt;
use num_traits::Zero;

/// Bit-vector rewriter
#[derive(Debug, Clone)]
pub struct BvRewriter {
    /// Enable aggressive bit-blasting optimization
    pub optimize_bitblast: bool,
    /// Enable extract/concat simplification
    pub simplify_extract_concat: bool,
    /// Cache for constant BV values
    const_cache: FxHashMap<TermId, (BigInt, u32)>, // (value, width)
}

impl Default for BvRewriter {
    fn default() -> Self {
        Self::new()
    }
}

impl BvRewriter {
    /// Create a new BV rewriter
    pub fn new() -> Self {
        Self {
            optimize_bitblast: true,
            simplify_extract_concat: true,
            const_cache: FxHashMap::default(),
        }
    }

    /// Try to extract constant BV value
    fn get_bv_const(&mut self, term: TermId, manager: &TermManager) -> Option<(BigInt, u32)> {
        if let Some(cached) = self.const_cache.get(&term) {
            return Some(cached.clone());
        }

        let t = manager.get(term)?;
        if let TermKind::BitVecConst { value, width } = &t.kind {
            let result = (value.clone(), *width);
            self.const_cache.insert(term, result.clone());
            return Some(result);
        }
        None
    }

    /// Get width of a BV term (from the sort)
    fn get_width(&self, term: TermId, manager: &TermManager) -> Option<u32> {
        let t = manager.get(term)?;
        let sort = manager.sorts.get(t.sort)?;
        sort.bitvec_width()
    }

    /// Check if BV is all zeros
    fn is_zero(&mut self, term: TermId, manager: &TermManager) -> bool {
        self.get_bv_const(term, manager)
            .is_some_and(|(v, _)| v.is_zero())
    }

    /// Check if BV is all ones
    fn is_all_ones(&mut self, term: TermId, manager: &TermManager) -> bool {
        self.get_bv_const(term, manager)
            .is_some_and(|(v, w)| v == Self::mask_big(w))
    }

    /// Get mask for width as BigInt
    fn mask_big(width: u32) -> BigInt {
        if width == 0 {
            BigInt::zero()
        } else {
            (BigInt::from(1) << width) - 1
        }
    }

    /// Rewrite BV AND
    fn rewrite_bvand(
        &mut self,
        lhs: TermId,
        rhs: TermId,
        ctx: &mut RewriteContext,
        manager: &mut TermManager,
    ) -> RewriteResult {
        let width = self.get_width(lhs, manager).unwrap_or(32);

        // x & 0 → 0
        if self.is_zero(lhs, manager) || self.is_zero(rhs, manager) {
            ctx.stats_mut().record_rule("bv_and_zero");
            return RewriteResult::Rewritten(manager.mk_bitvec(BigInt::zero(), width));
        }

        // x & 1...1 → x
        if self.is_all_ones(lhs, manager) {
            ctx.stats_mut().record_rule("bv_and_ones");
            return RewriteResult::Rewritten(rhs);
        }
        if self.is_all_ones(rhs, manager) {
            ctx.stats_mut().record_rule("bv_and_ones");
            return RewriteResult::Rewritten(lhs);
        }

        // x & x → x
        if lhs == rhs {
            ctx.stats_mut().record_rule("bv_and_self");
            return RewriteResult::Rewritten(lhs);
        }

        // Constant folding
        if let (Some((v1, w1)), Some((v2, _))) = (
            self.get_bv_const(lhs, manager),
            self.get_bv_const(rhs, manager),
        ) {
            ctx.stats_mut().record_rule("bv_and_const");
            return RewriteResult::Rewritten(manager.mk_bitvec(&v1 & &v2, w1));
        }

        RewriteResult::Unchanged(manager.mk_bv_and(lhs, rhs))
    }

    /// Rewrite BV OR
    fn rewrite_bvor(
        &mut self,
        lhs: TermId,
        rhs: TermId,
        ctx: &mut RewriteContext,
        manager: &mut TermManager,
    ) -> RewriteResult {
        let width = self.get_width(lhs, manager).unwrap_or(32);

        // x | 0 → x
        if self.is_zero(lhs, manager) {
            ctx.stats_mut().record_rule("bv_or_zero");
            return RewriteResult::Rewritten(rhs);
        }
        if self.is_zero(rhs, manager) {
            ctx.stats_mut().record_rule("bv_or_zero");
            return RewriteResult::Rewritten(lhs);
        }

        // x | 1...1 → 1...1
        if self.is_all_ones(lhs, manager) || self.is_all_ones(rhs, manager) {
            ctx.stats_mut().record_rule("bv_or_ones");
            return RewriteResult::Rewritten(manager.mk_bitvec(Self::mask_big(width), width));
        }

        // x | x → x
        if lhs == rhs {
            ctx.stats_mut().record_rule("bv_or_self");
            return RewriteResult::Rewritten(lhs);
        }

        // Constant folding
        if let (Some((v1, w1)), Some((v2, _))) = (
            self.get_bv_const(lhs, manager),
            self.get_bv_const(rhs, manager),
        ) {
            ctx.stats_mut().record_rule("bv_or_const");
            return RewriteResult::Rewritten(manager.mk_bitvec(&v1 | &v2, w1));
        }

        RewriteResult::Unchanged(manager.mk_bv_or(lhs, rhs))
    }

    /// Rewrite BV XOR
    fn rewrite_bvxor(
        &mut self,
        lhs: TermId,
        rhs: TermId,
        ctx: &mut RewriteContext,
        manager: &mut TermManager,
    ) -> RewriteResult {
        let width = self.get_width(lhs, manager).unwrap_or(32);

        // x ^ 0 → x
        if self.is_zero(lhs, manager) {
            ctx.stats_mut().record_rule("bv_xor_zero");
            return RewriteResult::Rewritten(rhs);
        }
        if self.is_zero(rhs, manager) {
            ctx.stats_mut().record_rule("bv_xor_zero");
            return RewriteResult::Rewritten(lhs);
        }

        // x ^ x → 0
        if lhs == rhs {
            ctx.stats_mut().record_rule("bv_xor_self");
            return RewriteResult::Rewritten(manager.mk_bitvec(BigInt::zero(), width));
        }

        // x ^ 1...1 → ~x
        if self.is_all_ones(lhs, manager) {
            ctx.stats_mut().record_rule("bv_xor_ones");
            return RewriteResult::Rewritten(manager.mk_bv_not(rhs));
        }
        if self.is_all_ones(rhs, manager) {
            ctx.stats_mut().record_rule("bv_xor_ones");
            return RewriteResult::Rewritten(manager.mk_bv_not(lhs));
        }

        // Constant folding
        if let (Some((v1, w1)), Some((v2, _))) = (
            self.get_bv_const(lhs, manager),
            self.get_bv_const(rhs, manager),
        ) {
            ctx.stats_mut().record_rule("bv_xor_const");
            return RewriteResult::Rewritten(manager.mk_bitvec(&v1 ^ &v2, w1));
        }

        // None of the simplification rules above applied: rebuild the
        // original XOR term (`TermManager::mk_bv_xor` exists and must be
        // used here — building an OR term instead, as this previously did,
        // silently changed `x ^ y` into `x | y`).
        RewriteResult::Unchanged(manager.mk_bv_xor(lhs, rhs))
    }

    /// Rewrite BV NOT
    fn rewrite_bvnot(
        &mut self,
        arg: TermId,
        ctx: &mut RewriteContext,
        manager: &mut TermManager,
    ) -> RewriteResult {
        let _width = self.get_width(arg, manager).unwrap_or(32);
        let Some(t) = manager.get(arg).cloned() else {
            return RewriteResult::Unchanged(manager.mk_bv_not(arg));
        };

        match &t.kind {
            // ~0 → 1...1
            TermKind::BitVecConst { value, width: w } if value.is_zero() => {
                ctx.stats_mut().record_rule("bv_not_zero");
                RewriteResult::Rewritten(manager.mk_bitvec(Self::mask_big(*w), *w))
            }
            // ~1...1 → 0
            TermKind::BitVecConst { value, width: w } if *value == Self::mask_big(*w) => {
                ctx.stats_mut().record_rule("bv_not_ones");
                RewriteResult::Rewritten(manager.mk_bitvec(BigInt::zero(), *w))
            }
            // ~~x → x
            TermKind::BvNot(inner) => {
                ctx.stats_mut().record_rule("bv_double_not");
                RewriteResult::Rewritten(*inner)
            }
            // Constant folding
            TermKind::BitVecConst { value, width: w } => {
                ctx.stats_mut().record_rule("bv_not_const");
                let mask = Self::mask_big(*w);
                let result = (!value) & mask;
                RewriteResult::Rewritten(manager.mk_bitvec(result, *w))
            }
            _ => RewriteResult::Unchanged(manager.mk_bv_not(arg)),
        }
    }

    /// Rewrite BV addition
    fn rewrite_bvadd(
        &mut self,
        lhs: TermId,
        rhs: TermId,
        ctx: &mut RewriteContext,
        manager: &mut TermManager,
    ) -> RewriteResult {
        // x + 0 → x
        if self.is_zero(lhs, manager) {
            ctx.stats_mut().record_rule("bv_add_zero");
            return RewriteResult::Rewritten(rhs);
        }
        if self.is_zero(rhs, manager) {
            ctx.stats_mut().record_rule("bv_add_zero");
            return RewriteResult::Rewritten(lhs);
        }

        // Constant folding
        if let (Some((v1, w1)), Some((v2, _))) = (
            self.get_bv_const(lhs, manager),
            self.get_bv_const(rhs, manager),
        ) {
            ctx.stats_mut().record_rule("bv_add_const");
            let result = (&v1 + &v2) & Self::mask_big(w1);
            return RewriteResult::Rewritten(manager.mk_bitvec(result, w1));
        }

        RewriteResult::Unchanged(manager.mk_bv_add(lhs, rhs))
    }

    /// Rewrite BV subtraction
    fn rewrite_bvsub(
        &mut self,
        lhs: TermId,
        rhs: TermId,
        ctx: &mut RewriteContext,
        manager: &mut TermManager,
    ) -> RewriteResult {
        let width = self.get_width(lhs, manager).unwrap_or(32);

        // x - 0 → x
        if self.is_zero(rhs, manager) {
            ctx.stats_mut().record_rule("bv_sub_zero");
            return RewriteResult::Rewritten(lhs);
        }

        // x - x → 0
        if lhs == rhs {
            ctx.stats_mut().record_rule("bv_sub_self");
            return RewriteResult::Rewritten(manager.mk_bitvec(BigInt::zero(), width));
        }

        // Constant folding
        if let (Some((v1, w1)), Some((v2, _))) = (
            self.get_bv_const(lhs, manager),
            self.get_bv_const(rhs, manager),
        ) {
            ctx.stats_mut().record_rule("bv_sub_const");
            // Handle wraparound for subtraction
            let mask = Self::mask_big(w1);
            let result = ((&v1 - &v2) + &mask + BigInt::from(1)) & &mask;
            return RewriteResult::Rewritten(manager.mk_bitvec(result, w1));
        }

        RewriteResult::Unchanged(manager.mk_bv_sub(lhs, rhs))
    }

    /// Rewrite BV multiplication
    fn rewrite_bvmul(
        &mut self,
        lhs: TermId,
        rhs: TermId,
        ctx: &mut RewriteContext,
        manager: &mut TermManager,
    ) -> RewriteResult {
        let width = self.get_width(lhs, manager).unwrap_or(32);

        // x * 0 → 0
        if self.is_zero(lhs, manager) || self.is_zero(rhs, manager) {
            ctx.stats_mut().record_rule("bv_mul_zero");
            return RewriteResult::Rewritten(manager.mk_bitvec(BigInt::zero(), width));
        }

        // x * 1 → x
        if let Some((v, _)) = self.get_bv_const(lhs, manager)
            && v == BigInt::from(1)
        {
            ctx.stats_mut().record_rule("bv_mul_one");
            return RewriteResult::Rewritten(rhs);
        }
        if let Some((v, _)) = self.get_bv_const(rhs, manager)
            && v == BigInt::from(1)
        {
            ctx.stats_mut().record_rule("bv_mul_one");
            return RewriteResult::Rewritten(lhs);
        }

        // Constant folding
        if let (Some((v1, w1)), Some((v2, _))) = (
            self.get_bv_const(lhs, manager),
            self.get_bv_const(rhs, manager),
        ) {
            ctx.stats_mut().record_rule("bv_mul_const");
            let result = (&v1 * &v2) & Self::mask_big(w1);
            return RewriteResult::Rewritten(manager.mk_bitvec(result, w1));
        }

        RewriteResult::Unchanged(manager.mk_bv_mul(lhs, rhs))
    }

    /// Rewrite BV shift left
    fn rewrite_bvshl(
        &mut self,
        lhs: TermId,
        rhs: TermId,
        ctx: &mut RewriteContext,
        manager: &mut TermManager,
    ) -> RewriteResult {
        let width = self.get_width(lhs, manager).unwrap_or(32);

        // 0 << x → 0
        if self.is_zero(lhs, manager) {
            ctx.stats_mut().record_rule("bv_shl_zero");
            return RewriteResult::Rewritten(manager.mk_bitvec(BigInt::zero(), width));
        }

        // x << 0 → x
        if self.is_zero(rhs, manager) {
            ctx.stats_mut().record_rule("bv_shl_by_zero");
            return RewriteResult::Rewritten(lhs);
        }

        // Constant folding
        if let (Some((v1, w1)), Some((v2, _))) = (
            self.get_bv_const(lhs, manager),
            self.get_bv_const(rhs, manager),
        ) {
            ctx.stats_mut().record_rule("bv_shl_const");
            let shift: u32 = (&v2)
                .try_into()
                .ok()
                .and_then(|v: u64| v.try_into().ok())
                .unwrap_or(w1);
            let result = if shift >= w1 {
                BigInt::zero()
            } else {
                (&v1 << shift) & Self::mask_big(w1)
            };
            return RewriteResult::Rewritten(manager.mk_bitvec(result, w1));
        }

        // Symbolic shift: rebuild the term rather than dropping the shift.
        RewriteResult::Unchanged(manager.mk_bv_shl(lhs, rhs))
    }

    /// Rewrite BV logical shift right
    fn rewrite_bvlshr(
        &mut self,
        lhs: TermId,
        rhs: TermId,
        ctx: &mut RewriteContext,
        manager: &mut TermManager,
    ) -> RewriteResult {
        let width = self.get_width(lhs, manager).unwrap_or(32);

        // 0 >> x → 0
        if self.is_zero(lhs, manager) {
            ctx.stats_mut().record_rule("bv_lshr_zero");
            return RewriteResult::Rewritten(manager.mk_bitvec(BigInt::zero(), width));
        }

        // x >> 0 → x
        if self.is_zero(rhs, manager) {
            ctx.stats_mut().record_rule("bv_lshr_by_zero");
            return RewriteResult::Rewritten(lhs);
        }

        // Constant folding
        if let (Some((v1, w1)), Some((v2, _))) = (
            self.get_bv_const(lhs, manager),
            self.get_bv_const(rhs, manager),
        ) {
            ctx.stats_mut().record_rule("bv_lshr_const");
            let shift: u32 = (&v2)
                .try_into()
                .ok()
                .and_then(|v: u64| v.try_into().ok())
                .unwrap_or(w1);
            let result = if shift >= w1 {
                BigInt::zero()
            } else {
                &v1 >> shift
            };
            return RewriteResult::Rewritten(manager.mk_bitvec(result, w1));
        }

        // Symbolic shift: rebuild the term rather than dropping the shift.
        RewriteResult::Unchanged(manager.mk_bv_lshr(lhs, rhs))
    }

    /// Rewrite BV equality
    fn rewrite_bveq(
        &mut self,
        lhs: TermId,
        rhs: TermId,
        ctx: &mut RewriteContext,
        manager: &mut TermManager,
    ) -> RewriteResult {
        // x = x → true
        if lhs == rhs {
            ctx.stats_mut().record_rule("bv_eq_self");
            return RewriteResult::Rewritten(manager.mk_true());
        }

        // Constant equality
        if let (Some((v1, _)), Some((v2, _))) = (
            self.get_bv_const(lhs, manager),
            self.get_bv_const(rhs, manager),
        ) {
            ctx.stats_mut().record_rule("bv_eq_const");
            if v1 == v2 {
                return RewriteResult::Rewritten(manager.mk_true());
            } else {
                return RewriteResult::Rewritten(manager.mk_false());
            }
        }

        RewriteResult::Unchanged(manager.mk_eq(lhs, rhs))
    }

    /// Rewrite BV extract
    fn rewrite_extract(
        &mut self,
        arg: TermId,
        high: u32,
        low: u32,
        ctx: &mut RewriteContext,
        manager: &mut TermManager,
    ) -> RewriteResult {
        let Some(t) = manager.get(arg).cloned() else {
            return RewriteResult::Unchanged(manager.mk_bv_extract(high, low, arg));
        };

        // Constant extraction
        if let TermKind::BitVecConst { value, .. } = &t.kind {
            ctx.stats_mut().record_rule("bv_extract_const");
            let width = high - low + 1;
            let extracted = (value >> low) & Self::mask_big(width);
            return RewriteResult::Rewritten(manager.mk_bitvec(extracted, width));
        }

        // extract(concat(x, y), h, l) simplification
        if self.simplify_extract_concat
            && let TermKind::BvConcat(lhs_part, rhs_part) = &t.kind
            // Check the widths of the parts
            && let (Some(_lw), Some(rw)) = (
                self.get_width(*lhs_part, manager),
                self.get_width(*rhs_part, manager),
            )
        {
            // concat(lhs, rhs): rhs is lower bits [0..rw), lhs is upper bits [rw..rw+lw)
            if high < rw {
                // Extraction entirely from rhs
                ctx.stats_mut().record_rule("bv_extract_concat_rhs");
                return RewriteResult::Rewritten(manager.mk_bv_extract(high, low, *rhs_part));
            } else if low >= rw {
                // Extraction entirely from lhs
                ctx.stats_mut().record_rule("bv_extract_concat_lhs");
                return RewriteResult::Rewritten(manager.mk_bv_extract(
                    high - rw,
                    low - rw,
                    *lhs_part,
                ));
            }
        }

        RewriteResult::Unchanged(manager.mk_bv_extract(high, low, arg))
    }

    /// Check if a term is a BV term
    fn is_bv_term(&self, term: TermId, manager: &TermManager) -> bool {
        self.get_width(term, manager).is_some()
    }

    /// Clear the constant cache
    pub fn clear_cache(&mut self) {
        self.const_cache.clear();
    }
}

impl Rewriter for BvRewriter {
    fn rewrite(
        &mut self,
        term: TermId,
        ctx: &mut RewriteContext,
        manager: &mut TermManager,
    ) -> RewriteResult {
        let Some(t) = manager.get(term).cloned() else {
            return RewriteResult::Unchanged(term);
        };

        match &t.kind {
            TermKind::BvAnd(lhs, rhs) => self.rewrite_bvand(*lhs, *rhs, ctx, manager),
            TermKind::BvOr(lhs, rhs) => self.rewrite_bvor(*lhs, *rhs, ctx, manager),
            TermKind::BvXor(lhs, rhs) => self.rewrite_bvxor(*lhs, *rhs, ctx, manager),
            TermKind::BvNot(arg) => self.rewrite_bvnot(*arg, ctx, manager),
            TermKind::BvAdd(lhs, rhs) => self.rewrite_bvadd(*lhs, *rhs, ctx, manager),
            TermKind::BvSub(lhs, rhs) => self.rewrite_bvsub(*lhs, *rhs, ctx, manager),
            TermKind::BvMul(lhs, rhs) => self.rewrite_bvmul(*lhs, *rhs, ctx, manager),
            TermKind::BvShl(lhs, rhs) => self.rewrite_bvshl(*lhs, *rhs, ctx, manager),
            TermKind::BvLshr(lhs, rhs) => self.rewrite_bvlshr(*lhs, *rhs, ctx, manager),
            TermKind::BvExtract { high, low, arg } => {
                self.rewrite_extract(*arg, *high, *low, ctx, manager)
            }
            TermKind::Eq(lhs, rhs) => {
                // Check if both sides are BV
                if self.is_bv_term(*lhs, manager) || self.is_bv_term(*rhs, manager) {
                    return self.rewrite_bveq(*lhs, *rhs, ctx, manager);
                }
                RewriteResult::Unchanged(term)
            }
            _ => RewriteResult::Unchanged(term),
        }
    }

    fn name(&self) -> &str {
        "BvRewriter"
    }

    fn can_handle(&self, term: TermId, manager: &TermManager) -> bool {
        let Some(t) = manager.get(term) else {
            return false;
        };

        matches!(
            t.kind,
            TermKind::BvAnd(_, _)
                | TermKind::BvOr(_, _)
                | TermKind::BvXor(_, _)
                | TermKind::BvNot(_)
                | TermKind::BvAdd(_, _)
                | TermKind::BvSub(_, _)
                | TermKind::BvMul(_, _)
                | TermKind::BvShl(_, _)
                | TermKind::BvLshr(_, _)
                | TermKind::BvAshr(_, _)
                | TermKind::BvExtract { .. }
                | TermKind::BvConcat(_, _)
                | TermKind::Eq(_, _)
        )
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn setup() -> (TermManager, RewriteContext, BvRewriter) {
        (TermManager::new(), RewriteContext::new(), BvRewriter::new())
    }

    /// Build a bit-vector operation node **without** the term manager's
    /// constant folding.
    ///
    /// `TermManager`'s `mk_bv_*` constructors apply these same identities at
    /// construction time, so building `bvand x #x0` through the public API
    /// hands back `#x0` directly and this rewriter would never be asked to do
    /// anything.  The rules under test still have to work on terms that reach
    /// the rewriter from elsewhere (a substitution that turned an operand into
    /// a literal, a deserialised term, ...), so the tests intern the raw node.
    fn raw_bv_op(manager: &mut TermManager, kind: TermKind, width: u32) -> TermId {
        let sort = manager.sorts.bitvec(width);
        manager.intern_term(kind, sort)
    }

    #[test]
    fn test_bvand_zero() {
        let (mut manager, mut ctx, mut rewriter) = setup();

        let bv_sort = manager.sorts.bitvec(32);
        let x = manager.mk_var("x", bv_sort);
        let zero = manager.mk_bitvec(BigInt::zero(), 32);
        let and = raw_bv_op(&mut manager, TermKind::BvAnd(x, zero), 32);

        let result = rewriter.rewrite(and, &mut ctx, &mut manager);
        assert!(result.was_rewritten());

        let t = manager.get(result.term()).expect("term should exist");
        assert!(matches!(t.kind, TermKind::BitVecConst { .. }));
    }

    #[test]
    fn test_bvand_self() {
        let (mut manager, mut ctx, mut rewriter) = setup();

        let bv_sort = manager.sorts.bitvec(32);
        let x = manager.mk_var("x", bv_sort);
        let and = raw_bv_op(&mut manager, TermKind::BvAnd(x, x), 32);

        let result = rewriter.rewrite(and, &mut ctx, &mut manager);
        assert!(result.was_rewritten());
        assert_eq!(result.term(), x);
    }

    #[test]
    fn test_bvor_zero() {
        let (mut manager, mut ctx, mut rewriter) = setup();

        let bv_sort = manager.sorts.bitvec(32);
        let x = manager.mk_var("x", bv_sort);
        let zero = manager.mk_bitvec(BigInt::zero(), 32);
        let or = raw_bv_op(&mut manager, TermKind::BvOr(x, zero), 32);

        let result = rewriter.rewrite(or, &mut ctx, &mut manager);
        assert!(result.was_rewritten());
        assert_eq!(result.term(), x);
    }

    #[test]
    fn test_bvnot_double() {
        let (mut manager, mut ctx, mut rewriter) = setup();

        let bv_sort = manager.sorts.bitvec(32);
        let x = manager.mk_var("x", bv_sort);
        let not1 = raw_bv_op(&mut manager, TermKind::BvNot(x), 32);
        let not2 = raw_bv_op(&mut manager, TermKind::BvNot(not1), 32);

        let result = rewriter.rewrite(not2, &mut ctx, &mut manager);
        assert!(result.was_rewritten());
        assert_eq!(result.term(), x);
    }

    #[test]
    fn test_bvadd_zero() {
        let (mut manager, mut ctx, mut rewriter) = setup();

        let bv_sort = manager.sorts.bitvec(32);
        let x = manager.mk_var("x", bv_sort);
        let zero = manager.mk_bitvec(BigInt::zero(), 32);
        let add = raw_bv_op(&mut manager, TermKind::BvAdd(x, zero), 32);

        let result = rewriter.rewrite(add, &mut ctx, &mut manager);
        assert!(result.was_rewritten());
        assert_eq!(result.term(), x);
    }

    #[test]
    fn test_bvsub_self() {
        let (mut manager, mut ctx, mut rewriter) = setup();

        let bv_sort = manager.sorts.bitvec(32);
        let x = manager.mk_var("x", bv_sort);
        let sub = raw_bv_op(&mut manager, TermKind::BvSub(x, x), 32);

        let result = rewriter.rewrite(sub, &mut ctx, &mut manager);
        assert!(result.was_rewritten());

        let t = manager.get(result.term()).expect("term should exist");
        assert!(matches!(t.kind, TermKind::BitVecConst { .. }));
    }

    #[test]
    fn test_bvmul_zero() {
        let (mut manager, mut ctx, mut rewriter) = setup();

        let bv_sort = manager.sorts.bitvec(32);
        let x = manager.mk_var("x", bv_sort);
        let zero = manager.mk_bitvec(BigInt::zero(), 32);
        let mul = raw_bv_op(&mut manager, TermKind::BvMul(x, zero), 32);

        let result = rewriter.rewrite(mul, &mut ctx, &mut manager);
        assert!(result.was_rewritten());

        let t = manager.get(result.term()).expect("term should exist");
        assert!(matches!(t.kind, TermKind::BitVecConst { .. }));
    }

    #[test]
    fn test_bvshl_symbolic_preserves_shift() {
        // Regression for: x << y (both symbolic) must NOT collapse to `x`.
        let (mut manager, mut ctx, mut rewriter) = setup();

        let bv_sort = manager.sorts.bitvec(32);
        let x = manager.mk_var("x", bv_sort);
        let y = manager.mk_var("y", bv_sort);
        let shl = manager.mk_bv_shl(x, y);

        let result = rewriter.rewrite(shl, &mut ctx, &mut manager);
        // The rewrite legitimately reports "unchanged" (no simplification
        // applies), but the returned term must still be the shift, not `x`.
        assert_ne!(
            result.term(),
            x,
            "symbolic BvShl must not be replaced by its lhs operand"
        );
        let t = manager.get(result.term()).expect("term should exist");
        assert!(matches!(t.kind, TermKind::BvShl(l, r) if l == x && r == y));
    }

    #[test]
    fn test_bvlshr_symbolic_preserves_shift() {
        // Regression for: x >> y (both symbolic) must NOT collapse to `x`.
        let (mut manager, mut ctx, mut rewriter) = setup();

        let bv_sort = manager.sorts.bitvec(32);
        let x = manager.mk_var("x", bv_sort);
        let y = manager.mk_var("y", bv_sort);
        let lshr = manager.mk_bv_lshr(x, y);

        let result = rewriter.rewrite(lshr, &mut ctx, &mut manager);
        assert_ne!(
            result.term(),
            x,
            "symbolic BvLshr must not be replaced by its lhs operand"
        );
        let t = manager.get(result.term()).expect("term should exist");
        assert!(matches!(t.kind, TermKind::BvLshr(l, r) if l == x && r == y));
    }

    #[test]
    fn test_bveq_self() {
        let (mut manager, _ctx, _rewriter) = setup();

        // Note: mk_eq already simplifies eq(x, x) -> true at term creation
        let bv_sort = manager.sorts.bitvec(32);
        let x = manager.mk_var("x", bv_sort);
        let eq = manager.mk_eq(x, x);

        // Verify the simplification happened at creation time
        let t = manager.get(eq).expect("term should exist");
        assert!(matches!(t.kind, TermKind::True));
    }

    #[test]
    fn test_bvxor_symbolic_stays_xor_not_or() {
        // Regression test: the "no direct XOR method" fallback used to
        // rebuild the term as `mk_bv_or(lhs, rhs)`, silently turning `x ^ y`
        // into `x | y` whenever none of the simplification rules fired.
        let (mut manager, mut ctx, mut rewriter) = setup();

        let bv_sort = manager.sorts.bitvec(32);
        let x = manager.mk_var("x", bv_sort);
        let y = manager.mk_var("y", bv_sort);
        let xor = manager.mk_bv_xor(x, y);

        let result = rewriter.rewrite(xor, &mut ctx, &mut manager);
        let t = manager.get(result.term()).expect("term should exist");
        assert!(
            matches!(t.kind, TermKind::BvXor(l, r) if l == x && r == y),
            "expected the term to remain a BvXor(x, y), got {:?}",
            t.kind
        );
    }
}
