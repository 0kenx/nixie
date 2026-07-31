//! Additional simplification infrastructure for tactic-driven preprocessing.

use crate::ast::{TermId, TermKind, TermManager};
use crate::lru_cache::LruCache;
#[allow(unused_imports)]
use crate::prelude::*;
use num_bigint::BigInt;
use smallvec::SmallVec;

/// Maximum number of entries retained in the per-simplifier memo cache.
/// LRU eviction prevents unbounded growth on large formulas.
const SIMPLIFICATION_MEMO_CAPACITY: usize = 4096;

/// Maximum recursion depth for `simplify_cached`. Mirrors the depth-cap
/// approach used by `rewrite/combined.rs`'s `RewriteContext` (see
/// `enter`/`exit` there): on a pathologically deep (but valid) term, bail
/// out returning the term unchanged rather than overflowing the stack. This
/// is sound -- no rewrite applied below the cap is still a valid (if
/// less-simplified) result -- and avoids memoizing the capped, unsimplified
/// result so a shallower call on the same term can still simplify it fully.
///
/// `simplify_cached`'s match arm is significantly larger than
/// `rewrite_bottom_up`'s (many `BigInt`/`SmallVec` locals across its
/// branches), so its stack frame is much bigger per level; 1000 (the value
/// `combined.rs` uses safely) already overflows a default 2 MiB test-thread
/// stack here, so this cap is kept well below that.
const SIMPLIFICATION_MAX_DEPTH: usize = 200;

/// Configuration for tactic-driven simplification passes.
#[derive(Debug, Clone, Copy, Default)]
pub struct SimplificationConfig {
    /// Enable more expensive algebraic and Boolean rewrites.
    pub aggressive: bool,
}

/// Recursive simplifier that layers aggressive rewrites on top of `TermManager::simplify`.
///
/// The `memo_cache` field persists across multiple `simplify_term` calls so that
/// sub-term results computed for one top-level term are reused for subsequent ones.
/// The cache is bounded to `SIMPLIFICATION_MEMO_CAPACITY` entries via LRU eviction,
/// which prevents unbounded memory growth on large formulas.
pub struct AggressiveSimplifier<'a> {
    manager: &'a mut TermManager,
    config: SimplificationConfig,
    /// Persistent bounded memo table: maps `TermId` to simplified `TermId`.
    memo_cache: LruCache<TermId, TermId>,
    /// Current recursion depth of `simplify_cached`, bounded by
    /// `SIMPLIFICATION_MAX_DEPTH`.
    depth: usize,
    /// Monotone count of how many times the depth bound has been hit.
    ///
    /// `simplify_cached` samples it on entry and again before memoizing: if
    /// it moved, some subterm was returned *un*-simplified because the bound
    /// fired, so this node's result is under-simplified too and must not be
    /// cached. Without this, an under-simplified result computed during one
    /// deep call outlived that call and was served to every later, shallower
    /// call on the same term -- the depth bound leaking a permanently
    /// degraded answer into an unrelated query. (The bound itself is sound
    /// either way: its result is always a weaker simplification of the same
    /// term, never a different term.)
    capped_hits: u64,
}

impl<'a> AggressiveSimplifier<'a> {
    /// Create a new simplifier using the provided manager and configuration.
    pub fn new(manager: &'a mut TermManager, config: SimplificationConfig) -> Self {
        Self {
            manager,
            config,
            memo_cache: LruCache::new(SIMPLIFICATION_MEMO_CAPACITY),
            depth: 0,
            capped_hits: 0,
        }
    }

    /// Get the current memo cache stats: `(hits, misses, evictions)`.
    #[must_use]
    pub fn memo_stats(&self) -> (usize, usize, usize) {
        self.memo_cache.stats()
    }

    /// Simplify a term recursively.
    /// Results are memoized in an LRU cache shared across all calls on this instance.
    pub fn simplify_term(&mut self, term: TermId) -> TermId {
        self.simplify_cached(term)
    }

    /// Call `TermManager::simplify`.
    ///
    /// This used to be a conditional passthrough that turned into a no-op
    /// once this simplifier's own `SIMPLIFICATION_MAX_DEPTH` cap had
    /// triggered anywhere in the current top-level call, on the theory that
    /// `TermManager::simplify` was itself an unbounded-depth recursive
    /// traversal, so handing it an arbitrarily-deep subterm returned
    /// unprocessed by that cap would "move the stack overflow one layer
    /// out" instead of preventing it. That is no longer true --
    /// `TermManager::simplify` was converted to an explicit heap stack (see
    /// `ast/manager/query/simplify.rs`) and now has no depth limit at all,
    /// so it cannot overflow the native stack regardless of how deep the
    /// term it is given is. There is nothing left to guard against here:
    /// this is now a direct, unconditional passthrough, kept as a named
    /// method only as a single choke point for every call this type makes
    /// into `TermManager::simplify`.
    fn manager_simplify(&mut self, id: TermId) -> TermId {
        self.manager.simplify(id)
    }

    fn simplify_cached(&mut self, term: TermId) -> TermId {
        if let Some(cached) = self.memo_cache.get(&term) {
            return cached;
        }

        // Bound recursion depth (see `SIMPLIFICATION_MAX_DEPTH`). Deliberately
        // not memoized: a shallower future call on the same term must still
        // be able to simplify it fully rather than reusing an unsimplified
        // capped result.
        if self.depth >= SIMPLIFICATION_MAX_DEPTH {
            self.capped_hits = self.capped_hits.saturating_add(1);
            return term;
        }
        let capped_before = self.capped_hits;
        self.depth += 1;

        let simplified = match self.manager.get(term).map(|t| t.kind.clone()) {
            None
            | Some(
                TermKind::True
                | TermKind::False
                | TermKind::IntConst(_)
                | TermKind::RealConst(_)
                | TermKind::BitVecConst { .. }
                | TermKind::StringLit(_)
                | TermKind::Var(_),
            ) => term,
            Some(TermKind::Not(arg)) => {
                let arg = self.simplify_cached(arg);
                self.simplify_not(arg)
            }
            Some(TermKind::And(args)) => {
                let args = self.simplify_all(args);
                self.simplify_and(args)
            }
            Some(TermKind::Or(args)) => {
                let args = self.simplify_all(args);
                self.simplify_or(args)
            }
            Some(TermKind::Implies(lhs, rhs)) => {
                let lhs = self.simplify_cached(lhs);
                let rhs = self.simplify_cached(rhs);
                self.simplify_implies(lhs, rhs)
            }
            Some(TermKind::Xor(lhs, rhs)) => {
                let lhs = self.simplify_cached(lhs);
                let rhs = self.simplify_cached(rhs);
                // mk_xor already handles: Xor(a,a)->false, Xor(a,false)->a, Xor(a,true)->Not(a)
                self.manager.mk_xor(lhs, rhs)
            }
            Some(TermKind::Eq(lhs, rhs)) => {
                let lhs = self.simplify_cached(lhs);
                let rhs = self.simplify_cached(rhs);
                self.simplify_eq(lhs, rhs)
            }
            Some(TermKind::Ite(cond, then_branch, else_branch)) => {
                let cond = self.simplify_cached(cond);
                let then_branch = self.simplify_cached(then_branch);
                let else_branch = self.simplify_cached(else_branch);
                // mk_ite already handles: Ite(true,a,_)->a, Ite(false,_,b)->b, Ite(_,a,a)->a
                self.manager.mk_ite(cond, then_branch, else_branch)
            }
            Some(TermKind::Distinct(args)) => {
                let args = self.simplify_all(args);
                self.simplify_distinct(args)
            }
            Some(TermKind::Add(args)) => {
                let args = self.simplify_all(args);
                let rebuilt = self.manager.mk_add(args);
                self.manager_simplify(rebuilt)
            }
            Some(TermKind::Sub(lhs, rhs)) => {
                let lhs = self.simplify_cached(lhs);
                let rhs = self.simplify_cached(rhs);
                let rebuilt = self.manager.mk_sub(lhs, rhs);
                self.manager_simplify(rebuilt)
            }
            Some(TermKind::Mul(args)) => {
                let args = self.simplify_all(args);
                let rebuilt = self.manager.mk_mul(args);
                self.manager_simplify(rebuilt)
            }
            Some(TermKind::Neg(arg)) => {
                let arg = self.simplify_cached(arg);
                let rebuilt = self.manager.mk_neg(arg);
                self.manager_simplify(rebuilt)
            }
            Some(TermKind::Lt(lhs, rhs)) => {
                let lhs = self.simplify_cached(lhs);
                let rhs = self.simplify_cached(rhs);
                let rebuilt = self.manager.mk_lt(lhs, rhs);
                self.manager_simplify(rebuilt)
            }
            Some(TermKind::Le(lhs, rhs)) => {
                let lhs = self.simplify_cached(lhs);
                let rhs = self.simplify_cached(rhs);
                let rebuilt = self.manager.mk_le(lhs, rhs);
                self.manager_simplify(rebuilt)
            }
            Some(TermKind::Gt(lhs, rhs)) => {
                let lhs = self.simplify_cached(lhs);
                let rhs = self.simplify_cached(rhs);
                let rebuilt = self.manager.mk_gt(lhs, rhs);
                self.manager_simplify(rebuilt)
            }
            Some(TermKind::Ge(lhs, rhs)) => {
                let lhs = self.simplify_cached(lhs);
                let rhs = self.simplify_cached(rhs);
                let rebuilt = self.manager.mk_ge(lhs, rhs);
                self.manager_simplify(rebuilt)
            }
            // BV identity rules -- mk_bv_* does no simplification so we handle here.
            Some(TermKind::BvNot(arg)) => {
                let arg = self.simplify_cached(arg);
                self.simplify_bv_not(arg)
            }
            Some(TermKind::BvAnd(lhs, rhs)) => {
                let lhs = self.simplify_cached(lhs);
                let rhs = self.simplify_cached(rhs);
                self.simplify_bv_and(lhs, rhs)
            }
            Some(TermKind::BvOr(lhs, rhs)) => {
                let lhs = self.simplify_cached(lhs);
                let rhs = self.simplify_cached(rhs);
                self.simplify_bv_or(lhs, rhs)
            }
            Some(TermKind::BvXor(lhs, rhs)) => {
                let lhs = self.simplify_cached(lhs);
                let rhs = self.simplify_cached(rhs);
                self.simplify_bv_xor(lhs, rhs)
            }
            Some(_) => self.manager_simplify(term),
        };

        self.depth -= 1;
        // Only cache a result that was computed without the depth bound
        // firing anywhere beneath it -- see `capped_hits`.
        if self.capped_hits == capped_before {
            self.memo_cache.insert(term, simplified);
        }
        simplified
    }

    fn simplify_all(&mut self, args: SmallVec<[TermId; 4]>) -> SmallVec<[TermId; 4]> {
        args.into_iter()
            .map(|arg| self.simplify_cached(arg))
            .collect()
    }

    fn simplify_and(&mut self, args: SmallVec<[TermId; 4]>) -> TermId {
        let baseline = self.manager.mk_and(args.clone());
        if !self.config.aggressive {
            return baseline;
        }

        if let Some(absorbed) = self.try_boolean_absorption_in_and(&args) {
            return self.manager_simplify(absorbed);
        }

        baseline
    }

    fn simplify_or(&mut self, args: SmallVec<[TermId; 4]>) -> TermId {
        let baseline = self.manager.mk_or(args.clone());
        if !self.config.aggressive {
            return baseline;
        }

        if let Some(absorbed) = self.try_boolean_absorption_in_or(&args) {
            return self.manager_simplify(absorbed);
        }

        if let Some(factored) = self.try_factor_or_of_ands(&args) {
            return self.manager_simplify(factored);
        }

        baseline
    }

    /// Simplify `Not(arg)` -- mk_not already collapses Not(Not(a))->a and Not(true/false).
    /// This method additionally applies De Morgan push-down for And-of-children
    /// when aggressive mode is on, so downstream rules can fire on the resulting Or.
    fn simplify_not(&mut self, arg: TermId) -> TermId {
        let baseline = self.manager.mk_not(arg);
        if !self.config.aggressive {
            return baseline;
        }

        // De Morgan: Not(And(a, b, ...)) -> Or(Not(a), Not(b), ...)
        // Apply only when there are exactly 2 children to avoid blowing up size.
        if let Some(TermKind::And(and_args)) = self.manager.get(arg).map(|t| t.kind.clone())
            && and_args.len() == 2
        {
            let not_a = self.manager.mk_not(and_args[0]);
            let not_b = self.manager.mk_not(and_args[1]);
            return self.manager.mk_or([not_a, not_b]);
        }

        baseline
    }

    /// Simplify `Implies(lhs, rhs)`.
    /// mk_implies already handles: Implies(false,_)->true, Implies(true,b)->b, Implies(_,true)->true.
    /// This method adds: Implies(a,false)->Not(a) and Implies(a,a)->true.
    fn simplify_implies(&mut self, lhs: TermId, rhs: TermId) -> TermId {
        if lhs == rhs {
            return self.manager.mk_true();
        }

        let false_id = self.manager.mk_false();
        if rhs == false_id {
            return self.simplify_not(lhs);
        }

        self.manager.mk_implies(lhs, rhs)
    }

    fn simplify_eq(&mut self, lhs: TermId, rhs: TermId) -> TermId {
        let baseline = self.manager.mk_eq(lhs, rhs);
        if !self.config.aggressive {
            return baseline;
        }

        if let Some(rewritten) = self.try_solve_add_constant_eq(lhs, rhs) {
            return self.manager_simplify(rewritten);
        }
        if let Some(rewritten) = self.try_solve_add_constant_eq(rhs, lhs) {
            return self.manager_simplify(rewritten);
        }

        baseline
    }

    fn simplify_distinct(&mut self, args: SmallVec<[TermId; 4]>) -> TermId {
        let baseline = self.manager.mk_distinct(args.clone());
        if !self.config.aggressive {
            return baseline;
        }

        let mut seen = FxHashSet::default();
        for arg in args {
            if !seen.insert(arg) {
                return self.manager.mk_false();
            }
        }

        baseline
    }

    /// Boolean absorption inside a conjunction: `a AND (a OR b) = a`.
    ///
    /// When a conjunct `candidate` absorbs another conjunct `other = Or(.., candidate, ..)`,
    /// only the absorbed `Or` term may be dropped -- every *other* conjunct (including
    /// `candidate` itself and any unrelated conjuncts such as `c` in `And(a, Or(a,b), c)`)
    /// must be preserved, otherwise the conjunction is illegally weakened.
    fn try_boolean_absorption_in_and(&mut self, args: &[TermId]) -> Option<TermId> {
        for (other_idx, &other) in args.iter().enumerate() {
            let or_args = match self.manager.get(other).map(|t| &t.kind) {
                Some(TermKind::Or(or_args)) => or_args.clone(),
                _ => continue,
            };
            let absorbed = args
                .iter()
                .any(|&candidate| candidate != other && or_args.contains(&candidate));
            if absorbed {
                let remaining: SmallVec<[TermId; 4]> = args
                    .iter()
                    .enumerate()
                    .filter_map(|(i, &t)| (i != other_idx).then_some(t))
                    .collect();
                return Some(self.mk_bool_join_or_true(remaining, true));
            }
        }
        None
    }

    /// Boolean absorption inside a disjunction: `a OR (a AND b) = a`.
    ///
    /// When a disjunct `candidate` absorbs another disjunct `other = And(.., candidate, ..)`,
    /// only the absorbed `And` term may be dropped -- every *other* disjunct (including
    /// `candidate` itself and any unrelated disjuncts such as `c` in `Or(a, And(a,b), c)`)
    /// must be preserved, otherwise the disjunction is illegally strengthened.
    fn try_boolean_absorption_in_or(&mut self, args: &[TermId]) -> Option<TermId> {
        for (other_idx, &other) in args.iter().enumerate() {
            let and_args = match self.manager.get(other).map(|t| &t.kind) {
                Some(TermKind::And(and_args)) => and_args.clone(),
                _ => continue,
            };
            let absorbed = args
                .iter()
                .any(|&candidate| candidate != other && and_args.contains(&candidate));
            if absorbed {
                let remaining: SmallVec<[TermId; 4]> = args
                    .iter()
                    .enumerate()
                    .filter_map(|(i, &t)| (i != other_idx).then_some(t))
                    .collect();
                return Some(self.mk_bool_join_or_true(remaining, false));
            }
        }
        None
    }

    /// Factor a common conjunct out of two `And` disjuncts:
    /// `(x AND a) OR (x AND b) = x AND (a OR b)`.
    ///
    /// Only the two factored disjuncts are replaced by the factored term -- every
    /// other disjunct (such as `c` in `Or(And(x,a), And(x,b), c)`) must be carried
    /// through unchanged, otherwise the disjunction is illegally strengthened.
    fn try_factor_or_of_ands(&mut self, args: &[TermId]) -> Option<TermId> {
        for (left_idx, &left_term) in args.iter().enumerate() {
            let left_args = match self.manager.get(left_term).map(|term| &term.kind) {
                Some(TermKind::And(and_args)) => and_args.clone(),
                _ => continue,
            };

            for (offset, &right_term) in args[left_idx + 1..].iter().enumerate() {
                let right_idx = left_idx + 1 + offset;
                let right_args = match self.manager.get(right_term).map(|term| &term.kind) {
                    Some(TermKind::And(and_args)) => and_args.clone(),
                    _ => continue,
                };

                for &common in &left_args {
                    if right_args.contains(&common) {
                        let left_rest = without_one(&left_args, common);
                        let right_rest = without_one(&right_args, common);
                        let left_inner = self.mk_bool_join_or_true(left_rest, true);
                        let right_inner = self.mk_bool_join_or_true(right_rest, true);
                        let combined = self.manager.mk_or([left_inner, right_inner]);
                        let factored = self.manager.mk_and([common, combined]);

                        // Preserve every disjunct other than the two we just factored,
                        // then re-join them with the factored term into an `Or`.
                        let mut rebuilt: SmallVec<[TermId; 4]> = args
                            .iter()
                            .enumerate()
                            .filter_map(|(i, &t)| (i != left_idx && i != right_idx).then_some(t))
                            .collect();
                        rebuilt.push(factored);
                        return Some(self.mk_bool_join_or_true(rebuilt, false));
                    }
                }
            }
        }

        None
    }

    fn mk_bool_join_or_true(&mut self, args: SmallVec<[TermId; 4]>, as_and: bool) -> TermId {
        if args.is_empty() {
            self.manager.mk_true()
        } else if as_and {
            self.manager.mk_and(args)
        } else {
            self.manager.mk_or(args)
        }
    }

    /// Simplify `BvNot(arg)`.
    /// Rule: BvNot(BvNot(x)) -> x.
    fn simplify_bv_not(&mut self, arg: TermId) -> TermId {
        if let Some(TermKind::BvNot(inner)) = self.manager.get(arg).map(|t| t.kind.clone()) {
            return inner;
        }
        self.manager.mk_bv_not(arg)
    }

    /// Simplify `BvAnd(lhs, rhs)`.
    /// Rules: BvAnd(x, 0) -> 0; BvAnd(x, all_ones) -> x; BvAnd(x, x) -> x.
    fn simplify_bv_and(&mut self, lhs: TermId, rhs: TermId) -> TermId {
        if lhs == rhs {
            return lhs;
        }

        let width = bv_width(self.manager, lhs).or_else(|| bv_width(self.manager, rhs));

        if let Some(w) = width {
            let all_ones = (BigInt::from(1_i32) << w) - 1_i32;
            let lhs_val = bv_constant(self.manager, lhs);
            let rhs_val = bv_constant(self.manager, rhs);

            if lhs_val.as_ref() == Some(&BigInt::from(0_i32))
                || rhs_val.as_ref() == Some(&BigInt::from(0_i32))
            {
                return self.manager.mk_bitvec(BigInt::from(0_i32), w);
            }
            if lhs_val.as_ref() == Some(&all_ones) {
                return rhs;
            }
            if rhs_val.as_ref() == Some(&all_ones) {
                return lhs;
            }
        }

        self.manager.mk_bv_and(lhs, rhs)
    }

    /// Simplify `BvOr(lhs, rhs)`.
    /// Rules: BvOr(x, 0) -> x; BvOr(x, all_ones) -> all_ones; BvOr(x, x) -> x.
    fn simplify_bv_or(&mut self, lhs: TermId, rhs: TermId) -> TermId {
        if lhs == rhs {
            return lhs;
        }

        let width = bv_width(self.manager, lhs).or_else(|| bv_width(self.manager, rhs));

        if let Some(w) = width {
            let all_ones = (BigInt::from(1_i32) << w) - 1_i32;
            let lhs_val = bv_constant(self.manager, lhs);
            let rhs_val = bv_constant(self.manager, rhs);

            if lhs_val.as_ref() == Some(&BigInt::from(0_i32)) {
                return rhs;
            }
            if rhs_val.as_ref() == Some(&BigInt::from(0_i32)) {
                return lhs;
            }
            if lhs_val.as_ref() == Some(&all_ones) {
                return self.manager.mk_bitvec(all_ones, w);
            }
            if rhs_val.as_ref() == Some(&all_ones) {
                return self.manager.mk_bitvec(all_ones, w);
            }
        }

        self.manager.mk_bv_or(lhs, rhs)
    }

    /// Simplify `BvXor(lhs, rhs)`.
    /// Rules: BvXor(x, 0) -> x; BvXor(x, x) -> 0.
    fn simplify_bv_xor(&mut self, lhs: TermId, rhs: TermId) -> TermId {
        if lhs == rhs {
            let w = bv_width(self.manager, lhs).unwrap_or(1);
            return self.manager.mk_bitvec(BigInt::from(0_i32), w);
        }

        let lhs_val = bv_constant(self.manager, lhs);
        let rhs_val = bv_constant(self.manager, rhs);

        if lhs_val.as_ref() == Some(&BigInt::from(0_i32)) {
            return rhs;
        }
        if rhs_val.as_ref() == Some(&BigInt::from(0_i32)) {
            return lhs;
        }

        self.manager.mk_bv_xor(lhs, rhs)
    }

    fn try_solve_add_constant_eq(
        &mut self,
        add_side: TermId,
        const_side: TermId,
    ) -> Option<TermId> {
        let rhs_const = int_constant(self.manager, const_side)?;
        let add_args = match self.manager.get(add_side).map(|term| &term.kind) {
            Some(TermKind::Add(args)) => args.clone(),
            _ => return None,
        };

        let mut non_const = None;
        let mut constant_sum = BigInt::from(0_i32);
        for arg in add_args {
            if let Some(value) = int_constant(self.manager, arg) {
                constant_sum += value;
                continue;
            }
            if non_const.is_some() {
                return None;
            }
            non_const = Some(arg);
        }

        let lhs = non_const?;
        let rewritten_rhs = self.manager.mk_int(rhs_const - constant_sum);
        Some(self.manager.mk_eq(lhs, rewritten_rhs))
    }
}

fn int_constant(manager: &TermManager, term: TermId) -> Option<BigInt> {
    match manager.get(term).map(|t| &t.kind) {
        Some(TermKind::IntConst(value)) => Some(value.clone()),
        _ => None,
    }
}

/// Return the constant value of a BitVecConst term, or None if it is not a constant.
fn bv_constant(manager: &TermManager, term: TermId) -> Option<BigInt> {
    match manager.get(term).map(|t| &t.kind) {
        Some(TermKind::BitVecConst { value, .. }) => Some(value.clone()),
        _ => None,
    }
}

/// Return the bit-width of a bit-vector term's sort, or None if the sort is unknown.
fn bv_width(manager: &TermManager, term: TermId) -> Option<u32> {
    let sort = manager.get(term)?.sort;
    manager.sorts.get(sort)?.bitvec_width()
}

fn without_one(args: &[TermId], needle: TermId) -> SmallVec<[TermId; 4]> {
    let mut removed = false;
    args.iter()
        .copied()
        .filter(|&arg| {
            if !removed && arg == needle {
                removed = true;
                false
            } else {
                true
            }
        })
        .collect()
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn aggressive_simplifier_handles_same_branch_ite() {
        let mut manager = TermManager::new();
        let cond = manager.mk_var("cond", manager.sorts.bool_sort);
        let x = manager.mk_var("x", manager.sorts.int_sort);
        let ite = manager.mk_ite(cond, x, x);

        let mut simplifier =
            AggressiveSimplifier::new(&mut manager, SimplificationConfig { aggressive: true });
        let simplified = simplifier.simplify_term(ite);

        assert_eq!(simplified, x);
    }

    #[test]
    fn test_simplification_memo_bounded() {
        // Simplifying many distinct terms must not grow the cache unboundedly.
        // The LRU cache is capped at SIMPLIFICATION_MEMO_CAPACITY entries.
        let mut manager = TermManager::new();
        let int_sort = manager.sorts.int_sort;

        let num_terms = SIMPLIFICATION_MEMO_CAPACITY + 200;
        let terms: Vec<TermId> = (0..num_terms)
            .map(|i| manager.mk_var(format!("x_{i}").as_str(), int_sort))
            .collect();

        let mut simplifier =
            AggressiveSimplifier::new(&mut manager, SimplificationConfig { aggressive: false });
        for &term in &terms {
            simplifier.simplify_term(term);
        }

        assert!(
            simplifier.memo_cache.len() <= SIMPLIFICATION_MEMO_CAPACITY,
            "memo cache grew beyond capacity: {} > {}",
            simplifier.memo_cache.len(),
            SIMPLIFICATION_MEMO_CAPACITY,
        );
        let (_, _, evictions) = simplifier.memo_stats();
        assert!(
            evictions > 0,
            "expected LRU evictions when inserting more than capacity"
        );
    }

    #[test]
    fn aggressive_simplifier_deep_term_does_not_overflow_stack() {
        // Regression (wave-1 deferral): simplify_cached used to recurse one
        // AST level per call with no depth limit, mirroring the pre-fix
        // rewrite_bottom_up bug in rewrite/combined.rs. A pathologically deep
        // (but valid) term used to overflow the stack; it must now bail out
        // and return a sound (if only partially simplified) result instead.
        let mut manager = TermManager::new();
        let x = manager.mk_var("x", manager.sorts.int_sort);
        let mut term = x;
        const CHAIN_LEN: usize = 20_000;
        for _ in 0..CHAIN_LEN {
            term = manager.mk_neg(term);
        }

        let mut simplifier =
            AggressiveSimplifier::new(&mut manager, SimplificationConfig { aggressive: true });

        // Must return without stack-overflow/abort.
        let result = simplifier.simplify_term(term);

        // The result must still be a well-formed, retrievable term.
        assert!(simplifier.manager.get(result).is_some());
    }

    #[test]
    fn test_simplification_memo_cache_hit() {
        // Simplifying the same compound term twice should produce a cache hit on the
        // second call.
        let mut manager = TermManager::new();
        let x = manager.mk_var("x", manager.sorts.int_sort);
        let y = manager.mk_var("y", manager.sorts.int_sort);
        let add = manager.mk_add(vec![x, y]);

        let mut simplifier =
            AggressiveSimplifier::new(&mut manager, SimplificationConfig { aggressive: false });

        let result1 = simplifier.simplify_term(add);
        let (hits_before, _, _) = simplifier.memo_stats();

        let result2 = simplifier.simplify_term(add);
        let (hits_after, _, _) = simplifier.memo_stats();

        assert_eq!(result1, result2, "simplification must be deterministic");
        assert!(
            hits_after > hits_before,
            "second call should hit the memo cache (hits: {} -> {})",
            hits_before,
            hits_after,
        );
    }
}
