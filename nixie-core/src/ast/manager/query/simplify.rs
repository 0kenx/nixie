//! Iterative bottom-up term simplification.
//!
//! Split out of `ast/manager/query.rs`. See `super::substitute`'s module
//! doc comment for the general rationale (an explicit heap stack instead of
//! native recursion, replacing the removed `MAX_QUERY_RECURSION_DEPTH`
//! cap).
//!
//! `simplify`'s conversion is considerably simpler than `substitute`'s:
//! only a small, fixed set of Boolean/arithmetic `TermKind`s ever recurses
//! into its children at all. The prior recursive implementation's catch-all
//! arm was `Some(_) => id`, returning everything else -- bit-vector/string/
//! FP operators, function applications, algebraic datatypes, and every
//! binder (`Forall`/`Exists`/`Let`/`Match`) -- completely untouched,
//! *without even visiting their children*. Since binders are never
//! descended into, there is no capture-avoidance to preserve here, unlike
//! `substitute`.

use super::TermManager;
use crate::ast::term::{TermId, TermKind};
#[allow(unused_imports)]
use crate::prelude::*;
use num_bigint::BigInt;
use smallvec::SmallVec;

impl TermManager {
    /// Re-share a term for PRINTING: the DAG's multiply-referenced
    /// compound subtrees are lifted into `let` bindings, so printing the
    /// body and the bindings (with the stock printer) produces
    /// `let`-shared SMT-LIB text instead of tree-unfolding the sharing —
    /// which is exponential for fan-out chains (the nec-smt residual:
    /// 662 DAG nodes whose tree unfolding never finishes printing;
    /// `2026-09-19-smt-perf-gap-attribution.md`'s printer addendum).
    ///
    /// Returns `(bindings, body)` with `bindings` ordered
    /// children-before-parents (each binding's term may reference the
    /// names bound before it); printing
    /// `(let ((n1 b1)) (let ((n2 b2)) ... body))` is the shared
    /// spelling.  Two safety properties:
    /// * **Name capture is impossible**: candidate names are chosen
    ///   from the term's own symbol vocabulary's complement (every free
    ///   variable and function symbol name in the DAG is collected
    ///   first), so a user variable cannot collide with a binding name.
    /// * **Only compound subtrees bind** (size ≥
    ///   [`MIN_SHARED_SUBTREE_SIZE`]): shared leaves (variables,
    ///   constants) keep their plain spelling, so small terms print
    ///   exactly as before — the pass engages only where the unfolding
    ///   would actually repeat real content.
    pub fn share_for_printing(&mut self, root: TermId) -> (Vec<(String, TermId)>, TermId) {
        /// A subtree smaller than this is never let-bound: re-printing a
        /// shared leaf or a tiny atom is cheaper than a binding, and the
        /// threshold keeps ordinary terms' printed form unchanged.
        const MIN_SHARED_SUBTREE_SIZE: usize = 2;
        /// Bound on the number of bindings: pathological inputs must not
        /// mint unbounded names.
        const MAX_SHARED_BINDINGS: usize = 1000;

        // ---- 1. DAG walk: in-degree-with-multiplicity, subtree size,
        //         and the symbol vocabulary (for capture-free naming). ----
        let mut refs: FxHashMap<TermId, usize> = FxHashMap::default();
        let mut size: FxHashMap<TermId, usize> = FxHashMap::default();
        let mut vocab: FxHashSet<crate::interner::Spur> = FxHashSet::default();
        // DAG walk, two-phase (Expand/Combine) so sizes combine in TRUE
        // post-order — children's sizes are always inserted before their
        // parents read them.  (A reversed pre-order is NOT post-order:
        // this analysis's first version combined parents first, reading
        // `unwrap_or(1)` for not-yet-sized children — every size was
        // undercounted, the candidate order was not topological, and the
        // bindings' RHS kept un-cut shared subtrees whose printing
        // exploded.  The bug's signature: a 407-DAG-node RHS printing
        // gigabytes.)
        enum Frame {
            Expand(TermId),
            Combine(TermId),
        }
        let mut stack: Vec<Frame> = vec![Frame::Expand(root)];
        let mut seen: FxHashSet<TermId> = FxHashSet::default();
        while let Some(frame) = stack.pop() {
            match frame {
                Frame::Expand(t) => {
                    if !seen.insert(t) {
                        continue;
                    }
                    let Some(data) = self.get(t).cloned() else {
                        continue;
                    };
                    if let crate::ast::term::TermKind::Var(name) = &data.kind {
                        vocab.insert(*name);
                    }
                    if let crate::ast::term::TermKind::Apply { func, .. } = &data.kind {
                        vocab.insert(*func);
                    }
                    let children = crate::ast::traversal::get_children(&data.kind);
                    for c in children.iter() {
                        *refs.entry(*c).or_default() += 1;
                    }
                    stack.push(Frame::Combine(t));
                    for c in children.iter().rev() {
                        stack.push(Frame::Expand(*c));
                    }
                }
                Frame::Combine(t) => {
                    let Some(data) = self.get(t) else { continue };
                    let children = crate::ast::traversal::get_children(&data.kind);
                    let s = 1 + children
                        .iter()
                        .map(|c| size.get(c).copied().unwrap_or(1))
                        .sum::<usize>();
                    size.insert(t, s);
                }
            }
        }
        let root_size = size.get(&root).copied().unwrap_or(1);

        // ---- 2. Candidates: multiply-referenced compound subtrees. ----
        let mut candidates: Vec<TermId> = refs
            .iter()
            .filter(|&(t, &r)| {
                r >= 2 && size.get(t).copied().unwrap_or(1) >= MIN_SHARED_SUBTREE_SIZE && *t != root
            })
            .map(|(&t, _)| t)
            .collect();
        // Children before parents: a candidate's candidate children are
        // strictly smaller, so ascending size is a valid topological
        // order.
        candidates.sort_by_key(|t| size.get(t).copied().unwrap_or(1));
        candidates.truncate(MAX_SHARED_BINDINGS);
        if candidates.is_empty() || root_size < 2 * MIN_SHARED_SUBTREE_SIZE {
            return (Vec::new(), root);
        }

        // ---- 3. Name minting against the vocabulary's complement. ----
        let mut names: FxHashMap<TermId, TermId> = FxHashMap::default();
        let mut bindings: Vec<(String, TermId)> = Vec::new();
        let mut counter = 1u32;
        for cand in candidates {
            let name = loop {
                let candidate = format!("a!{counter}");
                counter += 1;
                let spur = self.intern_str(&candidate);
                if !vocab.contains(&spur) {
                    break candidate;
                }
            };
            // The binding's RHS: the candidate with its already-named
            // (smaller) candidate children replaced by their names.
            let rhs = self.substitute(cand, &names);
            let sort = self
                .get(cand)
                .map(|t| t.sort)
                .unwrap_or(self.sorts.bool_sort);
            let var = self.mk_var(&name, sort);
            bindings.push((name, rhs));
            names.insert(cand, var);
        }
        let body = self.substitute(root, &names);
        (bindings, body)
    }
    /// Simplify a term by applying rewrite rules.
    ///
    /// This performs bottom-up simplification including:
    /// - Constant folding for arithmetic
    /// - Boolean simplifications
    /// - Identity/annihilator rules
    pub fn simplify(&mut self, id: TermId) -> TermId {
        let mut cache = FxHashMap::default();
        self.simplify_cached(id, &mut cache)
    }

    /// Simplify with memoization, using an explicit heap stack instead of
    /// native recursion (see the module doc comment). The two-phase
    /// iterative post-order shape mirrors `size_depth::term_size_cached`;
    /// only the small, explicitly-listed set of kinds in
    /// [`Self::simplifiable_children`] is ever expanded into children --
    /// everything else resolves to itself immediately, matching the prior
    /// recursive catch-all exactly (and, like the prior code, never
    /// memoizes an unvisited node under a fabricated entry -- it simply
    /// isn't pushed).
    fn simplify_cached(&mut self, id: TermId, cache: &mut FxHashMap<TermId, TermId>) -> TermId {
        if let Some(&result) = cache.get(&id) {
            return result;
        }

        let mut stack: Vec<(TermId, bool)> = vec![(id, false)];
        while let Some((current, expanded)) = stack.pop() {
            if cache.contains_key(&current) {
                continue;
            }

            if expanded {
                let result = self.combine_simplified(current, cache);
                cache.insert(current, result);
            } else {
                let children = self.simplifiable_children(current);
                stack.push((current, true));
                for &child in children.iter().rev() {
                    if !cache.contains_key(&child) {
                        stack.push((child, false));
                    }
                }
            }
        }

        cache.get(&id).copied().unwrap_or(id)
    }

    /// The children `simplify_cached` should recurse into for `id`, or none
    /// for a leaf, an unrecognized term, or any kind the simplifier does
    /// not rewrite (matching the prior `Some(_) => id` catch-all, which
    /// never visited such a node's children at all).
    fn simplifiable_children(&self, id: TermId) -> SmallVec<[TermId; 4]> {
        match self.get(id).map(|t| &t.kind) {
            None
            | Some(
                TermKind::True
                | TermKind::False
                | TermKind::IntConst(_)
                | TermKind::RealConst(_)
                | TermKind::BitVecConst { .. }
                | TermKind::Var(_),
            ) => SmallVec::new(),
            Some(TermKind::Not(a) | TermKind::Neg(a)) => [*a].into_iter().collect(),
            Some(
                TermKind::And(args)
                | TermKind::Or(args)
                | TermKind::Add(args)
                | TermKind::Mul(args),
            ) => args.iter().copied().collect(),
            Some(
                TermKind::Implies(a, b)
                | TermKind::Eq(a, b)
                | TermKind::Sub(a, b)
                | TermKind::Lt(a, b)
                | TermKind::Le(a, b)
                | TermKind::Gt(a, b)
                | TermKind::Ge(a, b),
            ) => [*a, *b].into_iter().collect(),
            Some(TermKind::Ite(c, t, e)) => [*c, *t, *e].into_iter().collect(),
            Some(_) => SmallVec::new(),
        }
    }

    /// Rebuild `id` from its already-simplified children (see
    /// `simplify_cached`), applying the same rewrite/constant-folding rule
    /// the prior recursive match arm used for each kind.
    fn combine_simplified(&mut self, id: TermId, cache: &FxHashMap<TermId, TermId>) -> TermId {
        let sub =
            |cache: &FxHashMap<TermId, TermId>, t: TermId| cache.get(&t).copied().unwrap_or(t);
        match self.get(id).map(|t| t.kind.clone()) {
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
                let new_arg = sub(cache, arg);
                self.mk_not(new_arg)
            }
            Some(TermKind::And(args)) => {
                let new_args: SmallVec<[TermId; 4]> = args.iter().map(|&a| sub(cache, a)).collect();
                self.mk_and(new_args)
            }
            Some(TermKind::Or(args)) => {
                let new_args: SmallVec<[TermId; 4]> = args.iter().map(|&a| sub(cache, a)).collect();
                self.mk_or(new_args)
            }
            Some(TermKind::Implies(lhs, rhs)) => {
                let new_lhs = sub(cache, lhs);
                let new_rhs = sub(cache, rhs);
                self.mk_implies(new_lhs, new_rhs)
            }
            Some(TermKind::Eq(lhs, rhs)) => {
                let new_lhs = sub(cache, lhs);
                let new_rhs = sub(cache, rhs);
                self.mk_eq(new_lhs, new_rhs)
            }
            Some(TermKind::Ite(cond, then_br, else_br)) => {
                let new_cond = sub(cache, cond);
                let new_then = sub(cache, then_br);
                let new_else = sub(cache, else_br);
                self.mk_ite(new_cond, new_then, new_else)
            }
            Some(TermKind::Add(args)) => {
                let new_args: SmallVec<[TermId; 4]> = args.iter().map(|&a| sub(cache, a)).collect();
                self.simplify_add(new_args)
            }
            Some(TermKind::Sub(lhs, rhs)) => {
                let new_lhs = sub(cache, lhs);
                let new_rhs = sub(cache, rhs);
                self.simplify_sub(new_lhs, new_rhs)
            }
            Some(TermKind::Mul(args)) => {
                let new_args: SmallVec<[TermId; 4]> = args.iter().map(|&a| sub(cache, a)).collect();
                self.simplify_mul(new_args)
            }
            Some(TermKind::Neg(arg)) => {
                let new_arg = sub(cache, arg);
                self.simplify_neg(new_arg)
            }
            Some(TermKind::Lt(lhs, rhs)) => {
                let new_lhs = sub(cache, lhs);
                let new_rhs = sub(cache, rhs);
                self.simplify_lt(new_lhs, new_rhs)
            }
            Some(TermKind::Le(lhs, rhs)) => {
                let new_lhs = sub(cache, lhs);
                let new_rhs = sub(cache, rhs);
                self.simplify_le(new_lhs, new_rhs)
            }
            Some(TermKind::Gt(lhs, rhs)) => {
                let new_lhs = sub(cache, lhs);
                let new_rhs = sub(cache, rhs);
                self.simplify_gt(new_lhs, new_rhs)
            }
            Some(TermKind::Ge(lhs, rhs)) => {
                let new_lhs = sub(cache, lhs);
                let new_rhs = sub(cache, rhs);
                self.simplify_ge(new_lhs, new_rhs)
            }
            // Everything else: left untouched, matching the prior
            // recursive catch-all (its children are never visited, so
            // there is nothing to gather from `cache` for them either).
            Some(_) => id,
        }
    }

    /// Simplify addition with constant folding.
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

    /// Simplify subtraction with constant folding.
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

    /// Simplify multiplication with constant folding.
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

    /// Simplify negation.
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

    /// Simplify less-than with constant comparison and reflexivity.
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

    /// Simplify less-or-equal with constant comparison and reflexivity.
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

    /// Simplify greater-than with constant comparison and reflexivity.
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

    /// Simplify greater-or-equal with constant comparison and reflexivity.
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
}
