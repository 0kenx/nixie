//! Term query, analysis, substitution and simplification for TermManager

use super::super::term::{MatchCase, TermId, TermKind};
use super::super::traversal::{collect_free_vars, collect_subterms, get_children};
use crate::interner::Spur;
#[allow(unused_imports)]
use crate::prelude::*;
use crate::sort::SortId;
use num_bigint::BigInt;
use smallvec::SmallVec;
use std::cell::Cell;

use super::TermManager;

/// Result of [`TermManager::prepare_binder_subst`]: the effective
/// substitution to apply inside the binder scope, paired with any fresh
/// `(name, sort)` bindings introduced by alpha-renaming to avoid capture.
type BinderSubstPrep = (FxHashMap<TermId, TermId>, SmallVec<[(Spur, SortId); 2]>);

/// Maximum recursive nesting depth accepted by [`TermManager::substitute`]
/// (via `substitute_cached`) and [`TermManager::simplify`] (via
/// `simplify_cached`) before bailing out and returning the term unchanged,
/// mirroring the depth cap `RewriteContext` applies in
/// `rewrite/combined.rs` (`max_depth` 1000). A pathologically deep (but
/// otherwise valid) term would otherwise recurse once per nesting level and
/// overflow the native call stack; bailing out at this bound is sound (no
/// substitution/simplification applied to the over-deep subtree) rather
/// than a crash.
const MAX_QUERY_RECURSION_DEPTH: u32 = 1000;

thread_local! {
    /// Current combined recursion depth of `substitute_cached` /
    /// `simplify_cached` on this thread. Shared between the two so that one
    /// cannot be used to work around the other's cap by nesting calls.
    static QUERY_RECURSION_DEPTH: Cell<u32> = const { Cell::new(0) };
}

/// RAII guard that decrements [`QUERY_RECURSION_DEPTH`] on drop (including on
/// early return / unwinding), keeping the depth accurate across every return
/// path of the guarded recursive functions.
struct QueryDepthGuard;

impl Drop for QueryDepthGuard {
    fn drop(&mut self) {
        QUERY_RECURSION_DEPTH.with(|d| d.set(d.get().saturating_sub(1)));
    }
}

/// Enter one level of query recursion, returning `true` if within the cap
/// (in which case the caller must hold onto a [`QueryDepthGuard`] for the
/// duration of that level) or `false` if the cap has been exceeded.
fn enter_query_recursion() -> (QueryDepthGuard, bool) {
    let depth = QUERY_RECURSION_DEPTH.with(|d| {
        let next = d.get().saturating_add(1);
        d.set(next);
        next
    });
    (QueryDepthGuard, depth <= MAX_QUERY_RECURSION_DEPTH)
}

impl TermManager {
    // ===== Term Analysis =====

    /// Compute the size (number of nodes) of a term
    #[must_use]
    pub fn term_size(&self, id: TermId) -> usize {
        self.term_size_cached(id, &mut FxHashMap::default())
    }

    /// Compute the size with memoization
    fn term_size_cached(&self, id: TermId, cache: &mut FxHashMap<TermId, usize>) -> usize {
        if let Some(&size) = cache.get(&id) {
            return size;
        }

        let size = match self.get(id).map(|t| &t.kind) {
            None => 1,
            Some(
                TermKind::True
                | TermKind::False
                | TermKind::IntConst(_)
                | TermKind::RealConst(_)
                | TermKind::BitVecConst { .. }
                | TermKind::StringLit(_)
                | TermKind::Var(_),
            ) => 1,
            Some(
                TermKind::Not(arg)
                | TermKind::Neg(arg)
                | TermKind::BvNot(arg)
                | TermKind::StrLen(arg)
                | TermKind::StrToInt(arg)
                | TermKind::IntToStr(arg),
            ) => 1 + self.term_size_cached(*arg, cache),
            Some(TermKind::BvExtract { arg, .. }) => 1 + self.term_size_cached(*arg, cache),
            Some(
                TermKind::And(args)
                | TermKind::Or(args)
                | TermKind::Add(args)
                | TermKind::Mul(args)
                | TermKind::Distinct(args),
            ) => {
                1 + args
                    .iter()
                    .map(|&a| self.term_size_cached(a, cache))
                    .sum::<usize>()
            }
            Some(
                TermKind::Implies(a, b)
                | TermKind::Xor(a, b)
                | TermKind::Eq(a, b)
                | TermKind::Sub(a, b)
                | TermKind::Div(a, b)
                | TermKind::Mod(a, b)
                | TermKind::Lt(a, b)
                | TermKind::Le(a, b)
                | TermKind::Gt(a, b)
                | TermKind::Ge(a, b)
                | TermKind::Select(a, b)
                | TermKind::StrConcat(a, b)
                | TermKind::StrAt(a, b)
                | TermKind::StrContains(a, b)
                | TermKind::StrPrefixOf(a, b)
                | TermKind::StrSuffixOf(a, b)
                | TermKind::StrInRe(a, b)
                | TermKind::BvConcat(a, b)
                | TermKind::BvAnd(a, b)
                | TermKind::BvOr(a, b)
                | TermKind::BvXor(a, b)
                | TermKind::BvAdd(a, b)
                | TermKind::BvSub(a, b)
                | TermKind::BvMul(a, b)
                | TermKind::BvUdiv(a, b)
                | TermKind::BvSdiv(a, b)
                | TermKind::BvUrem(a, b)
                | TermKind::BvSrem(a, b)
                | TermKind::BvShl(a, b)
                | TermKind::BvLshr(a, b)
                | TermKind::BvAshr(a, b)
                | TermKind::BvUlt(a, b)
                | TermKind::BvUle(a, b)
                | TermKind::BvSlt(a, b)
                | TermKind::BvSle(a, b),
            ) => 1 + self.term_size_cached(*a, cache) + self.term_size_cached(*b, cache),
            Some(
                TermKind::Ite(c, t, e)
                | TermKind::Store(c, t, e)
                | TermKind::StrSubstr(c, t, e)
                | TermKind::StrIndexOf(c, t, e)
                | TermKind::StrReplace(c, t, e)
                | TermKind::StrReplaceAll(c, t, e),
            ) => {
                1 + self.term_size_cached(*c, cache)
                    + self.term_size_cached(*t, cache)
                    + self.term_size_cached(*e, cache)
            }
            Some(TermKind::Apply { args, .. }) => {
                1 + args
                    .iter()
                    .map(|&a| self.term_size_cached(a, cache))
                    .sum::<usize>()
            }
            Some(TermKind::Forall { body, .. } | TermKind::Exists { body, .. }) => {
                1 + self.term_size_cached(*body, cache)
            }
            Some(TermKind::Let { bindings, body }) => {
                1 + bindings
                    .iter()
                    .map(|(_, t)| self.term_size_cached(*t, cache))
                    .sum::<usize>()
                    + self.term_size_cached(*body, cache)
            }
            // Floating-point operations - calculate size recursively
            Some(_) => self.get(id).map_or(0, |term| {
                1 + get_children(&term.kind)
                    .iter()
                    .map(|&child| self.term_size_cached(child, cache))
                    .sum::<usize>()
            }),
        };

        cache.insert(id, size);
        size
    }

    /// Compute the depth of a term
    #[must_use]
    pub fn term_depth(&self, id: TermId) -> usize {
        self.term_depth_cached(id, &mut FxHashMap::default())
    }

    /// Compute the depth with memoization
    fn term_depth_cached(&self, id: TermId, cache: &mut FxHashMap<TermId, usize>) -> usize {
        if let Some(&depth) = cache.get(&id) {
            return depth;
        }

        let depth = match self.get(id).map(|t| &t.kind) {
            None => 0,
            Some(
                TermKind::True
                | TermKind::False
                | TermKind::IntConst(_)
                | TermKind::RealConst(_)
                | TermKind::BitVecConst { .. }
                | TermKind::StringLit(_)
                | TermKind::Var(_),
            ) => 0,
            Some(
                TermKind::Not(arg)
                | TermKind::Neg(arg)
                | TermKind::BvNot(arg)
                | TermKind::StrLen(arg)
                | TermKind::StrToInt(arg)
                | TermKind::IntToStr(arg),
            ) => 1 + self.term_depth_cached(*arg, cache),
            Some(TermKind::BvExtract { arg, .. }) => 1 + self.term_depth_cached(*arg, cache),
            Some(
                TermKind::And(args)
                | TermKind::Or(args)
                | TermKind::Add(args)
                | TermKind::Mul(args)
                | TermKind::Distinct(args),
            ) => {
                1 + args
                    .iter()
                    .map(|&a| self.term_depth_cached(a, cache))
                    .max()
                    .unwrap_or(0)
            }
            Some(
                TermKind::Implies(a, b)
                | TermKind::Xor(a, b)
                | TermKind::Eq(a, b)
                | TermKind::Sub(a, b)
                | TermKind::Div(a, b)
                | TermKind::Mod(a, b)
                | TermKind::Lt(a, b)
                | TermKind::Le(a, b)
                | TermKind::Gt(a, b)
                | TermKind::Ge(a, b)
                | TermKind::Select(a, b)
                | TermKind::StrConcat(a, b)
                | TermKind::StrAt(a, b)
                | TermKind::StrContains(a, b)
                | TermKind::StrPrefixOf(a, b)
                | TermKind::StrSuffixOf(a, b)
                | TermKind::StrInRe(a, b)
                | TermKind::BvConcat(a, b)
                | TermKind::BvAnd(a, b)
                | TermKind::BvOr(a, b)
                | TermKind::BvXor(a, b)
                | TermKind::BvAdd(a, b)
                | TermKind::BvSub(a, b)
                | TermKind::BvMul(a, b)
                | TermKind::BvUdiv(a, b)
                | TermKind::BvSdiv(a, b)
                | TermKind::BvUrem(a, b)
                | TermKind::BvSrem(a, b)
                | TermKind::BvShl(a, b)
                | TermKind::BvLshr(a, b)
                | TermKind::BvAshr(a, b)
                | TermKind::BvUlt(a, b)
                | TermKind::BvUle(a, b)
                | TermKind::BvSlt(a, b)
                | TermKind::BvSle(a, b),
            ) => {
                1 + self
                    .term_depth_cached(*a, cache)
                    .max(self.term_depth_cached(*b, cache))
            }
            Some(
                TermKind::Ite(c, t, e)
                | TermKind::Store(c, t, e)
                | TermKind::StrSubstr(c, t, e)
                | TermKind::StrIndexOf(c, t, e)
                | TermKind::StrReplace(c, t, e)
                | TermKind::StrReplaceAll(c, t, e),
            ) => {
                1 + self
                    .term_depth_cached(*c, cache)
                    .max(self.term_depth_cached(*t, cache))
                    .max(self.term_depth_cached(*e, cache))
            }
            Some(TermKind::Apply { args, .. }) => {
                1 + args
                    .iter()
                    .map(|&a| self.term_depth_cached(a, cache))
                    .max()
                    .unwrap_or(0)
            }
            Some(TermKind::Forall { body, .. } | TermKind::Exists { body, .. }) => {
                1 + self.term_depth_cached(*body, cache)
            }
            Some(TermKind::Let { bindings, body }) => {
                let binding_depth = bindings
                    .iter()
                    .map(|(_, t)| self.term_depth_cached(*t, cache))
                    .max()
                    .unwrap_or(0);
                1 + binding_depth.max(self.term_depth_cached(*body, cache))
            }
            // Floating-point operations - calculate depth recursively
            Some(_) => self.get(id).map_or(0, |term| {
                1 + get_children(&term.kind)
                    .iter()
                    .map(|&child| self.term_depth_cached(child, cache))
                    .max()
                    .unwrap_or(0)
            }),
        };

        cache.insert(id, depth);
        depth
    }

    /// Substitute variables in a term according to a mapping
    pub fn substitute(&mut self, id: TermId, subst: &FxHashMap<TermId, TermId>) -> TermId {
        self.substitute_cached(id, subst, &mut FxHashMap::default())
    }

    /// Substitute with memoization.
    ///
    /// Every `TermKind` variant is handled explicitly — there is deliberately
    /// no catch-all arm, so a newly added variant fails to compile here rather
    /// than being silently skipped (which would drop solved equations while
    /// leaving occurrences in place, yielding wrong sat/unsat results and wrong
    /// models).
    ///
    /// Substitution is capture-avoiding: descending into a binder (`Forall`,
    /// `Exists`, `Let`, `Match`) drops shadowed variables from the substitution
    /// domain and alpha-renames any bound variable whose name would otherwise
    /// capture a free variable of a replacement term.
    pub(super) fn substitute_cached(
        &mut self,
        id: TermId,
        subst: &FxHashMap<TermId, TermId>,
        cache: &mut FxHashMap<TermId, TermId>,
    ) -> TermId {
        // Check if this term is directly substituted
        if let Some(&replacement) = subst.get(&id) {
            return replacement;
        }

        // Check cache
        if let Some(&result) = cache.get(&id) {
            return result;
        }

        // Bound recursion depth: on a pathologically deep (but valid) term,
        // bail out returning the term unchanged rather than overflowing the
        // native call stack. Sound (no substitution applied) instead of a
        // crash; see `MAX_QUERY_RECURSION_DEPTH`.
        let (_guard, within_cap) = enter_query_recursion();
        if !within_cap {
            return id;
        }

        let (kind, sort) = match self.get(id) {
            Some(term) => (term.kind.clone(), term.sort),
            None => return id,
        };

        let result = match kind {
            // ===== Leaves: nothing to substitute into =====
            TermKind::True
            | TermKind::False
            | TermKind::IntConst(_)
            | TermKind::RealConst(_)
            | TermKind::BitVecConst { .. }
            | TermKind::Var(_)
            | TermKind::StringLit(_)
            | TermKind::FpLit { .. }
            | TermKind::FpPlusInfinity { .. }
            | TermKind::FpMinusInfinity { .. }
            | TermKind::FpPlusZero { .. }
            | TermKind::FpMinusZero { .. }
            | TermKind::FpNaN { .. } => id,

            // ===== Boolean connectives =====
            TermKind::Not(a) => {
                let a = self.substitute_cached(a, subst, cache);
                self.mk_not(a)
            }
            TermKind::And(args) => {
                let new = self.subst_vec(&args, subst, cache);
                self.mk_and(new)
            }
            TermKind::Or(args) => {
                let new = self.subst_vec(&args, subst, cache);
                self.mk_or(new)
            }
            TermKind::Xor(a, b) => {
                let a = self.substitute_cached(a, subst, cache);
                let b = self.substitute_cached(b, subst, cache);
                self.mk_xor(a, b)
            }
            TermKind::Implies(a, b) => {
                let a = self.substitute_cached(a, subst, cache);
                let b = self.substitute_cached(b, subst, cache);
                self.mk_implies(a, b)
            }
            TermKind::Ite(c, t, e) => {
                let c = self.substitute_cached(c, subst, cache);
                let t = self.substitute_cached(t, subst, cache);
                let e = self.substitute_cached(e, subst, cache);
                self.mk_ite(c, t, e)
            }

            // ===== Equality / distinct =====
            TermKind::Eq(a, b) => {
                let a = self.substitute_cached(a, subst, cache);
                let b = self.substitute_cached(b, subst, cache);
                self.mk_eq(a, b)
            }
            TermKind::Distinct(args) => {
                let new = self.subst_vec(&args, subst, cache);
                self.mk_distinct(new)
            }

            // ===== Arithmetic =====
            TermKind::Neg(a) => {
                let a = self.substitute_cached(a, subst, cache);
                self.mk_neg(a)
            }
            TermKind::Add(args) => {
                let new = self.subst_vec(&args, subst, cache);
                self.mk_add(new)
            }
            TermKind::Sub(a, b) => {
                let a = self.substitute_cached(a, subst, cache);
                let b = self.substitute_cached(b, subst, cache);
                self.mk_sub(a, b)
            }
            TermKind::Mul(args) => {
                let new = self.subst_vec(&args, subst, cache);
                self.mk_mul(new)
            }
            TermKind::Div(a, b) => {
                let a = self.substitute_cached(a, subst, cache);
                let b = self.substitute_cached(b, subst, cache);
                self.mk_div(a, b)
            }
            TermKind::Mod(a, b) => {
                let a = self.substitute_cached(a, subst, cache);
                let b = self.substitute_cached(b, subst, cache);
                self.mk_mod(a, b)
            }
            TermKind::Lt(a, b) => {
                let a = self.substitute_cached(a, subst, cache);
                let b = self.substitute_cached(b, subst, cache);
                self.mk_lt(a, b)
            }
            TermKind::Le(a, b) => {
                let a = self.substitute_cached(a, subst, cache);
                let b = self.substitute_cached(b, subst, cache);
                self.mk_le(a, b)
            }
            TermKind::Gt(a, b) => {
                let a = self.substitute_cached(a, subst, cache);
                let b = self.substitute_cached(b, subst, cache);
                self.mk_gt(a, b)
            }
            TermKind::Ge(a, b) => {
                let a = self.substitute_cached(a, subst, cache);
                let b = self.substitute_cached(b, subst, cache);
                self.mk_ge(a, b)
            }

            // ===== Arrays =====
            TermKind::Select(arr, idx) => {
                let arr = self.substitute_cached(arr, subst, cache);
                let idx = self.substitute_cached(idx, subst, cache);
                self.mk_select(arr, idx)
            }
            TermKind::Store(arr, idx, val) => {
                let arr = self.substitute_cached(arr, subst, cache);
                let idx = self.substitute_cached(idx, subst, cache);
                let val = self.substitute_cached(val, subst, cache);
                self.mk_store(arr, idx, val)
            }

            // ===== Bit vectors =====
            TermKind::BvConcat(a, b) => {
                let a = self.substitute_cached(a, subst, cache);
                let b = self.substitute_cached(b, subst, cache);
                self.mk_bv_concat(a, b)
            }
            TermKind::BvExtract { high, low, arg } => {
                let arg = self.substitute_cached(arg, subst, cache);
                self.mk_bv_extract(high, low, arg)
            }
            TermKind::BvNot(a) => {
                let a = self.substitute_cached(a, subst, cache);
                self.mk_bv_not(a)
            }
            TermKind::BvAnd(a, b) => {
                let a = self.substitute_cached(a, subst, cache);
                let b = self.substitute_cached(b, subst, cache);
                self.mk_bv_and(a, b)
            }
            TermKind::BvOr(a, b) => {
                let a = self.substitute_cached(a, subst, cache);
                let b = self.substitute_cached(b, subst, cache);
                self.mk_bv_or(a, b)
            }
            TermKind::BvXor(a, b) => {
                let a = self.substitute_cached(a, subst, cache);
                let b = self.substitute_cached(b, subst, cache);
                self.mk_bv_xor(a, b)
            }
            TermKind::BvAdd(a, b) => {
                let a = self.substitute_cached(a, subst, cache);
                let b = self.substitute_cached(b, subst, cache);
                self.mk_bv_add(a, b)
            }
            TermKind::BvSub(a, b) => {
                let a = self.substitute_cached(a, subst, cache);
                let b = self.substitute_cached(b, subst, cache);
                self.mk_bv_sub(a, b)
            }
            TermKind::BvMul(a, b) => {
                let a = self.substitute_cached(a, subst, cache);
                let b = self.substitute_cached(b, subst, cache);
                self.mk_bv_mul(a, b)
            }
            TermKind::BvUdiv(a, b) => {
                let a = self.substitute_cached(a, subst, cache);
                let b = self.substitute_cached(b, subst, cache);
                self.mk_bv_udiv(a, b)
            }
            TermKind::BvSdiv(a, b) => {
                let a = self.substitute_cached(a, subst, cache);
                let b = self.substitute_cached(b, subst, cache);
                self.mk_bv_sdiv(a, b)
            }
            TermKind::BvUrem(a, b) => {
                let a = self.substitute_cached(a, subst, cache);
                let b = self.substitute_cached(b, subst, cache);
                self.mk_bv_urem(a, b)
            }
            TermKind::BvSrem(a, b) => {
                let a = self.substitute_cached(a, subst, cache);
                let b = self.substitute_cached(b, subst, cache);
                self.mk_bv_srem(a, b)
            }
            TermKind::BvShl(a, b) => {
                let a = self.substitute_cached(a, subst, cache);
                let b = self.substitute_cached(b, subst, cache);
                self.mk_bv_shl(a, b)
            }
            TermKind::BvLshr(a, b) => {
                let a = self.substitute_cached(a, subst, cache);
                let b = self.substitute_cached(b, subst, cache);
                self.mk_bv_lshr(a, b)
            }
            TermKind::BvAshr(a, b) => {
                let a = self.substitute_cached(a, subst, cache);
                let b = self.substitute_cached(b, subst, cache);
                self.mk_bv_ashr(a, b)
            }
            TermKind::BvUlt(a, b) => {
                let a = self.substitute_cached(a, subst, cache);
                let b = self.substitute_cached(b, subst, cache);
                self.mk_bv_ult(a, b)
            }
            TermKind::BvUle(a, b) => {
                let a = self.substitute_cached(a, subst, cache);
                let b = self.substitute_cached(b, subst, cache);
                self.mk_bv_ule(a, b)
            }
            TermKind::BvSlt(a, b) => {
                let a = self.substitute_cached(a, subst, cache);
                let b = self.substitute_cached(b, subst, cache);
                self.mk_bv_slt(a, b)
            }
            TermKind::BvSle(a, b) => {
                let a = self.substitute_cached(a, subst, cache);
                let b = self.substitute_cached(b, subst, cache);
                self.mk_bv_sle(a, b)
            }

            // ===== Strings =====
            TermKind::StrConcat(a, b) => {
                let a = self.substitute_cached(a, subst, cache);
                let b = self.substitute_cached(b, subst, cache);
                self.mk_str_concat(a, b)
            }
            TermKind::StrLen(a) => {
                let a = self.substitute_cached(a, subst, cache);
                self.mk_str_len(a)
            }
            TermKind::StrSubstr(s, i, n) => {
                let s = self.substitute_cached(s, subst, cache);
                let i = self.substitute_cached(i, subst, cache);
                let n = self.substitute_cached(n, subst, cache);
                self.mk_str_substr(s, i, n)
            }
            TermKind::StrAt(a, b) => {
                let a = self.substitute_cached(a, subst, cache);
                let b = self.substitute_cached(b, subst, cache);
                self.mk_str_at(a, b)
            }
            TermKind::StrContains(a, b) => {
                let a = self.substitute_cached(a, subst, cache);
                let b = self.substitute_cached(b, subst, cache);
                self.mk_str_contains(a, b)
            }
            TermKind::StrPrefixOf(a, b) => {
                let a = self.substitute_cached(a, subst, cache);
                let b = self.substitute_cached(b, subst, cache);
                self.mk_str_prefixof(a, b)
            }
            TermKind::StrSuffixOf(a, b) => {
                let a = self.substitute_cached(a, subst, cache);
                let b = self.substitute_cached(b, subst, cache);
                self.mk_str_suffixof(a, b)
            }
            TermKind::StrIndexOf(s, t, o) => {
                let s = self.substitute_cached(s, subst, cache);
                let t = self.substitute_cached(t, subst, cache);
                let o = self.substitute_cached(o, subst, cache);
                self.mk_str_indexof(s, t, o)
            }
            TermKind::StrReplace(s, p, r) => {
                let s = self.substitute_cached(s, subst, cache);
                let p = self.substitute_cached(p, subst, cache);
                let r = self.substitute_cached(r, subst, cache);
                self.mk_str_replace(s, p, r)
            }
            TermKind::StrReplaceAll(s, p, r) => {
                let s = self.substitute_cached(s, subst, cache);
                let p = self.substitute_cached(p, subst, cache);
                let r = self.substitute_cached(r, subst, cache);
                self.mk_str_replace_all(s, p, r)
            }
            TermKind::StrToInt(a) => {
                let a = self.substitute_cached(a, subst, cache);
                self.mk_str_to_int(a)
            }
            TermKind::IntToStr(a) => {
                let a = self.substitute_cached(a, subst, cache);
                self.mk_int_to_str(a)
            }
            TermKind::StrInRe(a, b) => {
                let a = self.substitute_cached(a, subst, cache);
                let b = self.substitute_cached(b, subst, cache);
                self.mk_str_in_re(a, b)
            }

            // ===== Floating point =====
            TermKind::FpAbs(a) => {
                let a = self.substitute_cached(a, subst, cache);
                self.mk_fp_abs(a)
            }
            TermKind::FpNeg(a) => {
                let a = self.substitute_cached(a, subst, cache);
                self.mk_fp_neg(a)
            }
            TermKind::FpSqrt(rm, a) => {
                let a = self.substitute_cached(a, subst, cache);
                self.mk_fp_sqrt(rm, a)
            }
            TermKind::FpRoundToIntegral(rm, a) => {
                let a = self.substitute_cached(a, subst, cache);
                self.mk_fp_round_to_integral(rm, a)
            }
            TermKind::FpAdd(rm, a, b) => {
                let a = self.substitute_cached(a, subst, cache);
                let b = self.substitute_cached(b, subst, cache);
                self.mk_fp_add(rm, a, b)
            }
            TermKind::FpSub(rm, a, b) => {
                let a = self.substitute_cached(a, subst, cache);
                let b = self.substitute_cached(b, subst, cache);
                self.mk_fp_sub(rm, a, b)
            }
            TermKind::FpMul(rm, a, b) => {
                let a = self.substitute_cached(a, subst, cache);
                let b = self.substitute_cached(b, subst, cache);
                self.mk_fp_mul(rm, a, b)
            }
            TermKind::FpDiv(rm, a, b) => {
                let a = self.substitute_cached(a, subst, cache);
                let b = self.substitute_cached(b, subst, cache);
                self.mk_fp_div(rm, a, b)
            }
            TermKind::FpRem(a, b) => {
                let a = self.substitute_cached(a, subst, cache);
                let b = self.substitute_cached(b, subst, cache);
                self.mk_fp_rem(a, b)
            }
            TermKind::FpMin(a, b) => {
                let a = self.substitute_cached(a, subst, cache);
                let b = self.substitute_cached(b, subst, cache);
                self.mk_fp_min(a, b)
            }
            TermKind::FpMax(a, b) => {
                let a = self.substitute_cached(a, subst, cache);
                let b = self.substitute_cached(b, subst, cache);
                self.mk_fp_max(a, b)
            }
            TermKind::FpLeq(a, b) => {
                let a = self.substitute_cached(a, subst, cache);
                let b = self.substitute_cached(b, subst, cache);
                self.mk_fp_leq(a, b)
            }
            TermKind::FpLt(a, b) => {
                let a = self.substitute_cached(a, subst, cache);
                let b = self.substitute_cached(b, subst, cache);
                self.mk_fp_lt(a, b)
            }
            TermKind::FpGeq(a, b) => {
                let a = self.substitute_cached(a, subst, cache);
                let b = self.substitute_cached(b, subst, cache);
                self.mk_fp_geq(a, b)
            }
            TermKind::FpGt(a, b) => {
                let a = self.substitute_cached(a, subst, cache);
                let b = self.substitute_cached(b, subst, cache);
                self.mk_fp_gt(a, b)
            }
            TermKind::FpEq(a, b) => {
                let a = self.substitute_cached(a, subst, cache);
                let b = self.substitute_cached(b, subst, cache);
                self.mk_fp_eq(a, b)
            }
            TermKind::FpFma(rm, a, b, c) => {
                let a = self.substitute_cached(a, subst, cache);
                let b = self.substitute_cached(b, subst, cache);
                let c = self.substitute_cached(c, subst, cache);
                self.mk_fp_fma(rm, a, b, c)
            }
            TermKind::FpIsNormal(a) => {
                let a = self.substitute_cached(a, subst, cache);
                self.mk_fp_is_normal(a)
            }
            TermKind::FpIsSubnormal(a) => {
                let a = self.substitute_cached(a, subst, cache);
                self.mk_fp_is_subnormal(a)
            }
            TermKind::FpIsZero(a) => {
                let a = self.substitute_cached(a, subst, cache);
                self.mk_fp_is_zero(a)
            }
            TermKind::FpIsInfinite(a) => {
                let a = self.substitute_cached(a, subst, cache);
                self.mk_fp_is_infinite(a)
            }
            TermKind::FpIsNaN(a) => {
                let a = self.substitute_cached(a, subst, cache);
                self.mk_fp_is_nan(a)
            }
            TermKind::FpIsNegative(a) => {
                let a = self.substitute_cached(a, subst, cache);
                self.mk_fp_is_negative(a)
            }
            TermKind::FpIsPositive(a) => {
                let a = self.substitute_cached(a, subst, cache);
                self.mk_fp_is_positive(a)
            }
            TermKind::FpToReal(a) => {
                let a = self.substitute_cached(a, subst, cache);
                self.mk_fp_to_real(a)
            }
            TermKind::FpToFp { rm, arg, eb, sb } => {
                let arg = self.substitute_cached(arg, subst, cache);
                self.mk_fp_to_fp(rm, arg, eb, sb)
            }
            TermKind::FpToSBV { rm, arg, width } => {
                let arg = self.substitute_cached(arg, subst, cache);
                self.mk_fp_to_sbv(rm, arg, width)
            }
            TermKind::FpToUBV { rm, arg, width } => {
                let arg = self.substitute_cached(arg, subst, cache);
                self.mk_fp_to_ubv(rm, arg, width)
            }
            TermKind::RealToFp { rm, arg, eb, sb } => {
                let arg = self.substitute_cached(arg, subst, cache);
                self.mk_real_to_fp(rm, arg, eb, sb)
            }
            TermKind::SBVToFp { rm, arg, eb, sb } => {
                let arg = self.substitute_cached(arg, subst, cache);
                self.mk_sbv_to_fp(rm, arg, eb, sb)
            }
            TermKind::UBVToFp { rm, arg, eb, sb } => {
                let arg = self.substitute_cached(arg, subst, cache);
                self.mk_ubv_to_fp(rm, arg, eb, sb)
            }

            // ===== Uninterpreted function application =====
            TermKind::Apply { func, args } => {
                let args = self.subst_vec(&args, subst, cache);
                self.intern(TermKind::Apply { func, args }, sort)
            }

            // ===== Algebraic datatypes =====
            TermKind::DtConstructor { constructor, args } => {
                let args = self.subst_vec(&args, subst, cache);
                self.intern(TermKind::DtConstructor { constructor, args }, sort)
            }
            TermKind::DtTester { constructor, arg } => {
                let arg = self.substitute_cached(arg, subst, cache);
                self.intern(TermKind::DtTester { constructor, arg }, sort)
            }
            TermKind::DtSelector { selector, arg } => {
                let arg = self.substitute_cached(arg, subst, cache);
                self.intern(TermKind::DtSelector { selector, arg }, sort)
            }

            // ===== Binders (capture-avoiding) =====
            TermKind::Forall {
                vars,
                body,
                patterns,
            } => match self.subst_quantifier_parts(&vars, body, &patterns, subst) {
                None => id,
                Some((vars, body, patterns)) => self.intern(
                    TermKind::Forall {
                        vars,
                        body,
                        patterns,
                    },
                    sort,
                ),
            },
            TermKind::Exists {
                vars,
                body,
                patterns,
            } => match self.subst_quantifier_parts(&vars, body, &patterns, subst) {
                None => id,
                Some((vars, body, patterns)) => self.intern(
                    TermKind::Exists {
                        vars,
                        body,
                        patterns,
                    },
                    sort,
                ),
            },
            TermKind::Let { bindings, body } => self.subst_let(sort, bindings, body, subst, cache),
            TermKind::Match { scrutinee, cases } => {
                self.subst_match(sort, scrutinee, cases, subst, cache)
            }
        };

        cache.insert(id, result);
        result
    }

    /// Substitute every element of `args`, preserving order.
    fn subst_vec(
        &mut self,
        args: &[TermId],
        subst: &FxHashMap<TermId, TermId>,
        cache: &mut FxHashMap<TermId, TermId>,
    ) -> SmallVec<[TermId; 4]> {
        args.iter()
            .map(|&a| self.substitute_cached(a, subst, cache))
            .collect()
    }

    /// Substitute the body and triggers of a quantifier under capture-avoidance.
    ///
    /// Returns `None` when nothing in the quantifier scope is affected (so the
    /// caller can keep the original interned term), otherwise the rewritten
    /// bound variables, body and patterns.
    #[allow(clippy::type_complexity)]
    fn subst_quantifier_parts(
        &mut self,
        vars: &[(Spur, SortId)],
        body: TermId,
        patterns: &[SmallVec<[TermId; 2]>],
        subst: &FxHashMap<TermId, TermId>,
    ) -> Option<(
        SmallVec<[(Spur, SortId); 2]>,
        TermId,
        SmallVec<[SmallVec<[TermId; 2]>; 2]>,
    )> {
        let (effective, new_vars) = self.prepare_binder_subst(vars, body, subst)?;
        let mut inner_cache = FxHashMap::default();
        let new_body = self.substitute_cached(body, &effective, &mut inner_cache);
        let mut new_patterns: SmallVec<[SmallVec<[TermId; 2]>; 2]> = SmallVec::new();
        for pattern in patterns {
            let mut new_pattern: SmallVec<[TermId; 2]> = SmallVec::new();
            for &t in pattern {
                new_pattern.push(self.substitute_cached(t, &effective, &mut inner_cache));
            }
            new_patterns.push(new_pattern);
        }
        Some((new_vars, new_body, new_patterns))
    }

    /// Capture-avoiding substitution into a `let` expression.
    ///
    /// Bound values are substituted in the outer scope; the body is substituted
    /// with the let-bound names shadowed and alpha-renamed when necessary.
    fn subst_let(
        &mut self,
        sort: SortId,
        bindings: SmallVec<[(Spur, TermId); 2]>,
        body: TermId,
        subst: &FxHashMap<TermId, TermId>,
        cache: &mut FxHashMap<TermId, TermId>,
    ) -> TermId {
        let mut new_values: SmallVec<[TermId; 2]> = SmallVec::new();
        let mut bound: SmallVec<[(Spur, SortId); 2]> = SmallVec::new();
        for &(name, value) in &bindings {
            let new_value = self.substitute_cached(value, subst, cache);
            let value_sort = self.get(value).map_or(self.sorts.bool_sort, |t| t.sort);
            new_values.push(new_value);
            bound.push((name, value_sort));
        }

        let (final_names, new_body) = match self.prepare_binder_subst(&bound, body, subst) {
            None => (bound, body),
            Some((effective, new_bound)) => {
                let mut inner_cache = FxHashMap::default();
                let new_body = self.substitute_cached(body, &effective, &mut inner_cache);
                (new_bound, new_body)
            }
        };

        let new_bindings: SmallVec<[(Spur, TermId); 2]> = final_names
            .iter()
            .zip(new_values.iter())
            .map(|(&(name, _), &value)| (name, value))
            .collect();
        self.intern(
            TermKind::Let {
                bindings: new_bindings,
                body: new_body,
            },
            sort,
        )
    }

    /// Capture-avoiding substitution into a `match` expression.
    ///
    /// The scrutinee is substituted in the outer scope; each case body is
    /// substituted with its constructor-argument bindings shadowed and
    /// alpha-renamed when necessary.
    fn subst_match(
        &mut self,
        sort: SortId,
        scrutinee: TermId,
        cases: SmallVec<[MatchCase; 4]>,
        subst: &FxHashMap<TermId, TermId>,
        cache: &mut FxHashMap<TermId, TermId>,
    ) -> TermId {
        let new_scrutinee = self.substitute_cached(scrutinee, subst, cache);
        let mut new_cases: SmallVec<[MatchCase; 4]> = SmallVec::new();
        for case in cases {
            let mut bound: SmallVec<[(Spur, SortId); 2]> = SmallVec::new();
            for &name in &case.bindings {
                let var_sort = self
                    .find_var_sort(case.body, name)
                    .unwrap_or(self.sorts.bool_sort);
                bound.push((name, var_sort));
            }
            match self.prepare_binder_subst(&bound, case.body, subst) {
                None => new_cases.push(case),
                Some((effective, new_bound)) => {
                    let mut inner_cache = FxHashMap::default();
                    let new_body = self.substitute_cached(case.body, &effective, &mut inner_cache);
                    let bindings: SmallVec<[Spur; 4]> =
                        new_bound.iter().map(|&(name, _)| name).collect();
                    new_cases.push(MatchCase {
                        constructor: case.constructor,
                        bindings,
                        body: new_body,
                    });
                }
            }
        }
        self.intern(
            TermKind::Match {
                scrutinee: new_scrutinee,
                cases: new_cases,
            },
            sort,
        )
    }

    /// Build the effective substitution to apply inside a binder scope.
    ///
    /// Drops entries whose source is one of `bound` (the bound variable is
    /// shadowed) and, when a bound variable's name would capture a free
    /// variable of some replacement term, alpha-renames that bound variable to
    /// a fresh name (extending the returned substitution with the renaming).
    ///
    /// Returns `None` when the resulting substitution is empty (nothing to do,
    /// no capture) so the caller can preserve the original term.
    fn prepare_binder_subst(
        &mut self,
        bound: &[(Spur, SortId)],
        body: TermId,
        subst: &FxHashMap<TermId, TermId>,
    ) -> Option<BinderSubstPrep> {
        // Effective substitution: drop entries whose source is a bound variable.
        let mut effective: FxHashMap<TermId, TermId> = FxHashMap::default();
        for (&from, &to) in subst {
            let shadowed = self.get(from).is_some_and(|t| match &t.kind {
                TermKind::Var(name) => bound
                    .iter()
                    .any(|(bound_name, bound_sort)| bound_name == name && *bound_sort == t.sort),
                _ => false,
            });
            if !shadowed {
                effective.insert(from, to);
            }
        }
        if effective.is_empty() {
            return None;
        }

        // Names occurring free in the replacement range.
        let mut range_free: FxHashSet<Spur> = FxHashSet::default();
        for &to in effective.values() {
            for var in collect_free_vars(to, self) {
                if let Some(TermKind::Var(name)) = self.get(var).map(|t| &t.kind) {
                    range_free.insert(*name);
                }
            }
        }

        // Bound variables whose name would capture a replacement's free variable.
        let capturing: SmallVec<[usize; 2]> = bound
            .iter()
            .enumerate()
            .filter(|(_, (name, _))| range_free.contains(name))
            .map(|(index, _)| index)
            .collect();

        if capturing.is_empty() {
            return Some((effective, bound.iter().copied().collect()));
        }

        // Names that a freshly generated binder name must avoid.
        let mut avoid = range_free;
        for (name, _) in bound {
            avoid.insert(*name);
        }
        for var in collect_free_vars(body, self) {
            if let Some(TermKind::Var(name)) = self.get(var).map(|t| &t.kind) {
                avoid.insert(*name);
            }
        }

        let mut new_bound: SmallVec<[(Spur, SortId); 2]> = bound.iter().copied().collect();
        for index in capturing {
            let (name, var_sort) = bound[index];
            let (fresh_name, fresh_var) = self.fresh_var(name, var_sort, &avoid);
            avoid.insert(fresh_name);
            let old_var = self.intern(TermKind::Var(name), var_sort);
            effective.insert(old_var, fresh_var);
            new_bound[index] = (fresh_name, var_sort);
        }
        Some((effective, new_bound))
    }

    /// Create a fresh variable derived from `base` whose name is not in `avoid`.
    fn fresh_var(&mut self, base: Spur, sort: SortId, avoid: &FxHashSet<Spur>) -> (Spur, TermId) {
        let base_name = self.resolve_str(base).to_string();
        let mut counter: u64 = 0;
        loop {
            let candidate = format!("{base_name}!{counter}");
            let name = self.intern_str(&candidate);
            if !avoid.contains(&name) {
                let var = self.intern(TermKind::Var(name), sort);
                return (name, var);
            }
            counter += 1;
        }
    }

    /// Find the sort of a variable named `target` by locating an occurrence in
    /// `term` (used to reconstruct fresh binders for `match` cases, whose
    /// bindings do not carry sort information directly).
    fn find_var_sort(&self, term: TermId, target: Spur) -> Option<SortId> {
        for sub in collect_subterms(term, self) {
            if let Some(t) = self.get(sub)
                && let TermKind::Var(name) = t.kind
                && name == target
            {
                return Some(t.sort);
            }
        }
        None
    }

    /// Simplify a term by applying rewrite rules
    ///
    /// This performs bottom-up simplification including:
    /// - Constant folding for arithmetic
    /// - Boolean simplifications
    /// - Identity/annihilator rules
    pub fn simplify(&mut self, id: TermId) -> TermId {
        let mut cache = FxHashMap::default();
        self.simplify_cached(id, &mut cache)
    }

    fn simplify_cached(&mut self, id: TermId, cache: &mut FxHashMap<TermId, TermId>) -> TermId {
        if let Some(&result) = cache.get(&id) {
            return result;
        }

        // Bound recursion depth: on a pathologically deep (but valid) term,
        // bail out returning the term unchanged rather than overflowing the
        // native call stack. Sound (no simplification applied) instead of a
        // crash; see `MAX_QUERY_RECURSION_DEPTH`.
        let (_guard, within_cap) = enter_query_recursion();
        if !within_cap {
            return id;
        }

        let result = match self.get(id).map(|t| t.kind.clone()) {
            None
            | Some(
                TermKind::True
                | TermKind::False
                | TermKind::IntConst(_)
                | TermKind::RealConst(_)
                | TermKind::BitVecConst { .. }
                | TermKind::Var(_),
            ) => id,

            Some(TermKind::Not(arg)) => {
                let new_arg = self.simplify_cached(arg, cache);
                self.mk_not(new_arg)
            }
            Some(TermKind::And(args)) => {
                let new_args: SmallVec<[TermId; 4]> = args
                    .iter()
                    .map(|&a| self.simplify_cached(a, cache))
                    .collect();
                self.mk_and(new_args)
            }
            Some(TermKind::Or(args)) => {
                let new_args: SmallVec<[TermId; 4]> = args
                    .iter()
                    .map(|&a| self.simplify_cached(a, cache))
                    .collect();
                self.mk_or(new_args)
            }
            Some(TermKind::Implies(lhs, rhs)) => {
                let new_lhs = self.simplify_cached(lhs, cache);
                let new_rhs = self.simplify_cached(rhs, cache);
                self.mk_implies(new_lhs, new_rhs)
            }
            Some(TermKind::Eq(lhs, rhs)) => {
                let new_lhs = self.simplify_cached(lhs, cache);
                let new_rhs = self.simplify_cached(rhs, cache);
                self.mk_eq(new_lhs, new_rhs)
            }
            Some(TermKind::Ite(cond, then_br, else_br)) => {
                let new_cond = self.simplify_cached(cond, cache);
                let new_then = self.simplify_cached(then_br, cache);
                let new_else = self.simplify_cached(else_br, cache);
                self.mk_ite(new_cond, new_then, new_else)
            }
            Some(TermKind::Add(args)) => {
                let new_args: SmallVec<[TermId; 4]> = args
                    .iter()
                    .map(|&a| self.simplify_cached(a, cache))
                    .collect();
                self.simplify_add(new_args)
            }
            Some(TermKind::Sub(lhs, rhs)) => {
                let new_lhs = self.simplify_cached(lhs, cache);
                let new_rhs = self.simplify_cached(rhs, cache);
                self.simplify_sub(new_lhs, new_rhs)
            }
            Some(TermKind::Mul(args)) => {
                let new_args: SmallVec<[TermId; 4]> = args
                    .iter()
                    .map(|&a| self.simplify_cached(a, cache))
                    .collect();
                self.simplify_mul(new_args)
            }
            Some(TermKind::Neg(arg)) => {
                let new_arg = self.simplify_cached(arg, cache);
                self.simplify_neg(new_arg)
            }
            Some(TermKind::Lt(lhs, rhs)) => {
                let new_lhs = self.simplify_cached(lhs, cache);
                let new_rhs = self.simplify_cached(rhs, cache);
                self.simplify_lt(new_lhs, new_rhs)
            }
            Some(TermKind::Le(lhs, rhs)) => {
                let new_lhs = self.simplify_cached(lhs, cache);
                let new_rhs = self.simplify_cached(rhs, cache);
                self.simplify_le(new_lhs, new_rhs)
            }
            Some(TermKind::Gt(lhs, rhs)) => {
                let new_lhs = self.simplify_cached(lhs, cache);
                let new_rhs = self.simplify_cached(rhs, cache);
                self.simplify_gt(new_lhs, new_rhs)
            }
            Some(TermKind::Ge(lhs, rhs)) => {
                let new_lhs = self.simplify_cached(lhs, cache);
                let new_rhs = self.simplify_cached(rhs, cache);
                self.simplify_ge(new_lhs, new_rhs)
            }
            // For other terms, just return as-is
            Some(_) => id,
        };

        cache.insert(id, result);
        result
    }

    /// Simplify addition with constant folding
    fn simplify_add(&mut self, args: SmallVec<[TermId; 4]>) -> TermId {
        let mut constant_sum = BigInt::from(0);
        let mut other_args: SmallVec<[TermId; 4]> = SmallVec::new();

        for arg in args {
            if let Some(TermKind::IntConst(n)) = self.get(arg).map(|t| &t.kind) {
                constant_sum += n;
            } else {
                other_args.push(arg);
            }
        }

        let zero = BigInt::from(0);
        if other_args.is_empty() {
            return self.intern(TermKind::IntConst(constant_sum), self.sorts.int_sort);
        }

        if constant_sum != zero {
            other_args.push(self.intern(TermKind::IntConst(constant_sum), self.sorts.int_sort));
        }

        if other_args.len() == 1 {
            return other_args[0];
        }

        self.mk_add(other_args)
    }

    /// Simplify subtraction with constant folding
    fn simplify_sub(&mut self, lhs: TermId, rhs: TermId) -> TermId {
        let zero = BigInt::from(0);
        match (
            self.get(lhs).map(|t| t.kind.clone()),
            self.get(rhs).map(|t| t.kind.clone()),
        ) {
            (Some(TermKind::IntConst(a)), Some(TermKind::IntConst(b))) => {
                self.intern(TermKind::IntConst(a - b), self.sorts.int_sort)
            }
            (_, Some(TermKind::IntConst(n))) if n == zero => lhs,
            (Some(TermKind::IntConst(n)), _) if n == zero => self.simplify_neg(rhs),
            _ => self.mk_sub(lhs, rhs),
        }
    }

    /// Simplify multiplication with constant folding
    fn simplify_mul(&mut self, args: SmallVec<[TermId; 4]>) -> TermId {
        let mut constant_product = BigInt::from(1);
        let mut other_args: SmallVec<[TermId; 4]> = SmallVec::new();
        let zero = BigInt::from(0);
        let one = BigInt::from(1);

        for arg in args {
            if let Some(TermKind::IntConst(n)) = self.get(arg).map(|t| &t.kind) {
                if *n == zero {
                    return self.mk_int(0);
                }
                constant_product *= n;
            } else {
                other_args.push(arg);
            }
        }

        if other_args.is_empty() {
            return self.intern(TermKind::IntConst(constant_product), self.sorts.int_sort);
        }

        if constant_product == zero {
            return self.mk_int(0);
        }

        if constant_product != one {
            other_args.insert(
                0,
                self.intern(TermKind::IntConst(constant_product), self.sorts.int_sort),
            );
        }

        if other_args.len() == 1 {
            return other_args[0];
        }

        self.mk_mul(other_args)
    }

    /// Simplify negation
    fn simplify_neg(&mut self, arg: TermId) -> TermId {
        match self.get(arg).map(|t| t.kind.clone()) {
            Some(TermKind::IntConst(n)) => self.intern(TermKind::IntConst(-n), self.sorts.int_sort),
            Some(TermKind::Neg(inner)) => inner,
            _ => {
                let sort = self.get(arg).map_or(self.sorts.int_sort, |t| t.sort);
                self.intern(TermKind::Neg(arg), sort)
            }
        }
    }

    /// Simplify less-than with constant comparison and reflexivity
    fn simplify_lt(&mut self, lhs: TermId, rhs: TermId) -> TermId {
        // Reflexivity: a < a is always False
        if lhs == rhs {
            return self.false_id;
        }
        match (
            self.get(lhs).map(|t| t.kind.clone()),
            self.get(rhs).map(|t| t.kind.clone()),
        ) {
            (Some(TermKind::IntConst(a)), Some(TermKind::IntConst(b))) => self.mk_bool(a < b),
            _ => self.mk_lt(lhs, rhs),
        }
    }

    /// Simplify less-or-equal with constant comparison and reflexivity
    fn simplify_le(&mut self, lhs: TermId, rhs: TermId) -> TermId {
        // Reflexivity: a <= a is always True
        if lhs == rhs {
            return self.true_id;
        }
        match (
            self.get(lhs).map(|t| t.kind.clone()),
            self.get(rhs).map(|t| t.kind.clone()),
        ) {
            (Some(TermKind::IntConst(a)), Some(TermKind::IntConst(b))) => self.mk_bool(a <= b),
            _ => self.mk_le(lhs, rhs),
        }
    }

    /// Simplify greater-than with constant comparison and reflexivity
    fn simplify_gt(&mut self, lhs: TermId, rhs: TermId) -> TermId {
        // Reflexivity: a > a is always False
        if lhs == rhs {
            return self.false_id;
        }
        match (
            self.get(lhs).map(|t| t.kind.clone()),
            self.get(rhs).map(|t| t.kind.clone()),
        ) {
            (Some(TermKind::IntConst(a)), Some(TermKind::IntConst(b))) => self.mk_bool(a > b),
            _ => self.mk_gt(lhs, rhs),
        }
    }

    /// Simplify greater-or-equal with constant comparison and reflexivity
    fn simplify_ge(&mut self, lhs: TermId, rhs: TermId) -> TermId {
        // Reflexivity: a >= a is always True
        if lhs == rhs {
            return self.true_id;
        }
        match (
            self.get(lhs).map(|t| t.kind.clone()),
            self.get(rhs).map(|t| t.kind.clone()),
        ) {
            (Some(TermKind::IntConst(a)), Some(TermKind::IntConst(b))) => self.mk_bool(a >= b),
            _ => self.mk_ge(lhs, rhs),
        }
    }

    /// Collect all free variables in a term
    pub fn free_vars(&self, id: TermId) -> Vec<TermId> {
        let mut vars = Vec::new();
        let mut visited = FxHashMap::default();
        self.collect_free_vars(id, &mut vars, &mut visited);
        vars
    }

    fn collect_free_vars(
        &self,
        id: TermId,
        vars: &mut Vec<TermId>,
        visited: &mut FxHashMap<TermId, ()>,
    ) {
        if visited.contains_key(&id) {
            return;
        }
        visited.insert(id, ());

        match self.get(id).map(|t| &t.kind) {
            None => {}
            Some(TermKind::Var(_)) if !vars.contains(&id) => {
                vars.push(id);
            }
            Some(
                TermKind::True
                | TermKind::False
                | TermKind::IntConst(_)
                | TermKind::RealConst(_)
                | TermKind::BitVecConst { .. }
                | TermKind::StringLit(_),
            ) => {}
            Some(
                TermKind::Not(arg)
                | TermKind::Neg(arg)
                | TermKind::BvNot(arg)
                | TermKind::StrLen(arg)
                | TermKind::StrToInt(arg)
                | TermKind::IntToStr(arg),
            ) => {
                self.collect_free_vars(*arg, vars, visited);
            }
            Some(TermKind::BvExtract { arg, .. }) => {
                self.collect_free_vars(*arg, vars, visited);
            }
            Some(
                TermKind::And(args)
                | TermKind::Or(args)
                | TermKind::Add(args)
                | TermKind::Mul(args)
                | TermKind::Distinct(args),
            ) => {
                for &arg in args {
                    self.collect_free_vars(arg, vars, visited);
                }
            }
            Some(
                TermKind::Implies(a, b)
                | TermKind::Xor(a, b)
                | TermKind::Eq(a, b)
                | TermKind::Sub(a, b)
                | TermKind::Div(a, b)
                | TermKind::Mod(a, b)
                | TermKind::Lt(a, b)
                | TermKind::Le(a, b)
                | TermKind::Gt(a, b)
                | TermKind::Ge(a, b)
                | TermKind::Select(a, b)
                | TermKind::StrConcat(a, b)
                | TermKind::StrAt(a, b)
                | TermKind::StrContains(a, b)
                | TermKind::StrPrefixOf(a, b)
                | TermKind::StrSuffixOf(a, b)
                | TermKind::StrInRe(a, b)
                | TermKind::BvConcat(a, b)
                | TermKind::BvAnd(a, b)
                | TermKind::BvOr(a, b)
                | TermKind::BvXor(a, b)
                | TermKind::BvAdd(a, b)
                | TermKind::BvSub(a, b)
                | TermKind::BvMul(a, b)
                | TermKind::BvUdiv(a, b)
                | TermKind::BvSdiv(a, b)
                | TermKind::BvUrem(a, b)
                | TermKind::BvSrem(a, b)
                | TermKind::BvShl(a, b)
                | TermKind::BvLshr(a, b)
                | TermKind::BvAshr(a, b)
                | TermKind::BvUlt(a, b)
                | TermKind::BvUle(a, b)
                | TermKind::BvSlt(a, b)
                | TermKind::BvSle(a, b),
            ) => {
                self.collect_free_vars(*a, vars, visited);
                self.collect_free_vars(*b, vars, visited);
            }
            Some(
                TermKind::Ite(c, t, e)
                | TermKind::Store(c, t, e)
                | TermKind::StrSubstr(c, t, e)
                | TermKind::StrIndexOf(c, t, e)
                | TermKind::StrReplace(c, t, e)
                | TermKind::StrReplaceAll(c, t, e),
            ) => {
                self.collect_free_vars(*c, vars, visited);
                self.collect_free_vars(*t, vars, visited);
                self.collect_free_vars(*e, vars, visited);
            }
            Some(TermKind::Apply { args, .. }) => {
                for &arg in args {
                    self.collect_free_vars(arg, vars, visited);
                }
            }
            Some(TermKind::Forall { body, .. } | TermKind::Exists { body, .. }) => {
                // Note: This is simplified - we should track bound vars
                self.collect_free_vars(*body, vars, visited);
            }
            Some(TermKind::Let { bindings, body }) => {
                for (_, term) in bindings {
                    self.collect_free_vars(*term, vars, visited);
                }
                self.collect_free_vars(*body, vars, visited);
            }
            // Floating-point operations - collect vars from children
            Some(_) => {
                if let Some(term) = self.get(id) {
                    for &child in &get_children(&term.kind) {
                        self.collect_free_vars(child, vars, visited);
                    }
                }
            }
        }
    }
}

#[cfg(test)]
mod lint_regression_tests {
    //! Regression tests for the clippy `collapsible_if` / `type_complexity`
    //! lint fixes to `find_var_sort` and `prepare_binder_subst`. These pin
    //! down that the mechanical rewrites (nested `if let` -> `if let ... &&
    //! ...`, and the `BinderSubstPrep` type alias) preserved behavior
    //! exactly.
    use super::*;

    #[test]
    fn find_var_sort_locates_variable_occurrence() {
        let mut m = TermManager::new();
        let int_sort = m.sorts.int_sort;
        let bool_sort = m.sorts.bool_sort;
        let x = m.mk_var("x", int_sort);
        let zero = m.mk_int(0);
        let term = m.mk_gt(x, zero); // x > 0

        let TermKind::Var(x_name) = m.get(x).expect("x term").kind else {
            panic!("expected Var");
        };

        // Present: must find the sort of the matching-named variable.
        assert_eq!(m.find_var_sort(term, x_name), Some(int_sort));

        // Absent: a name that never occurs in `term` must yield None, not a
        // stray match on an unrelated subterm.
        let y_name = m.intern_str("y");
        assert_eq!(m.find_var_sort(term, y_name), None);

        // Same name, different sort must not be confused with a differently
        // sorted occurrence located elsewhere in the walk.
        let y_bool = m.mk_var("y", bool_sort);
        let combined = m.mk_and([term, y_bool]);
        assert_eq!(m.find_var_sort(combined, y_name), Some(bool_sort));
    }

    #[test]
    fn prepare_binder_subst_none_when_substitution_is_empty_after_shadowing() {
        let mut m = TermManager::new();
        let int_sort = m.sorts.int_sort;
        let x = m.mk_var("x", int_sort);
        let forty_two = m.mk_int(42);
        let body = m.mk_gt(x, forty_two);

        let TermKind::Var(x_name) = m.get(x).expect("x term").kind else {
            panic!("expected Var");
        };

        let mut subst = FxHashMap::default();
        subst.insert(x, forty_two);

        // x is shadowed by the binder, so the effective substitution is
        // empty and prepare_binder_subst must report None.
        let bound = [(x_name, int_sort)];
        assert!(m.prepare_binder_subst(&bound, body, &subst).is_none());
    }

    #[test]
    fn prepare_binder_subst_returns_effective_substitution() {
        let mut m = TermManager::new();
        let int_sort = m.sorts.int_sort;
        let x = m.mk_var("x", int_sort);
        let y = m.mk_var("y", int_sort);
        let forty_two = m.mk_int(42);
        let body = m.mk_gt(x, y);

        let mut subst = FxHashMap::default();
        subst.insert(y, forty_two);

        // y is free (not bound), so it must survive into the effective
        // substitution returned via the BinderSubstPrep-typed Some(..).
        let bound: [(Spur, SortId); 0] = [];
        let (effective, new_bound) = m
            .prepare_binder_subst(&bound, body, &subst)
            .expect("y is unshadowed, so a non-empty substitution is expected");
        assert_eq!(effective.get(&y), Some(&forty_two));
        assert!(new_bound.is_empty(), "no capture, so no fresh binders");
    }
}
