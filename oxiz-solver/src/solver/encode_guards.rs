//! Soundness guards for the encoder / theory dispatch.
//!
//! Two families of checks split out of `encode.rs` to keep every file under the
//! 2000-line limit:
//!
//!   * the **arithmetic honesty gate** — detect comparison/equality atoms the
//!     linear solver cannot represent (integer `div`/`mod`, nonlinear products,
//!     out-of-range constants), so `check` can answer `Unknown` rather than
//!     trust a free-Boolean encoding; and
//!   * the **depth guard** — a non-recursive scan that reports when a formula
//!     nests deeper than [`ENCODE_DEPTH_LIMIT`](super::ENCODE_DEPTH_LIMIT), used
//!     to bail out before a recursive pass overflows the native stack.

#[allow(unused_imports)]
use crate::prelude::*;
use num_traits::ToPrimitive;
use oxiz_core::ast::{TermId, TermKind, TermManager};

use super::Solver;
use super::types::Constraint;

impl Solver {
    /// Honesty gate (soundness): returns `true` when some *active* arithmetic
    /// comparison / equality atom could not be turned into a linear constraint
    /// and therefore carries no theory semantics — `encode` left it as a free
    /// Boolean.  Trusting the SAT layer to pick a truth value for such an atom
    /// produces a spurious `Sat`/`Unsat`, so `check` answers `Unknown` instead.
    ///
    /// Only atoms that genuinely contain a construct the linear solver cannot
    /// represent (integer `div`/`mod`, a nonlinear product, or an out-of-range
    /// constant) are gated; atoms with a valid linear parse, and BV atoms
    /// (handled by the BV solver), are ignored.
    pub(super) fn arith_atoms_need_theory(&self, manager: &TermManager) -> bool {
        for (var, constraint) in &self.var_to_constraint {
            let (lhs, rhs) = match constraint {
                Constraint::Lt(l, r)
                | Constraint::Le(l, r)
                | Constraint::Gt(l, r)
                | Constraint::Ge(l, r)
                | Constraint::Eq(l, r) => (*l, *r),
                _ => continue,
            };
            // Only Int/Real atoms are the linear ArithSolver's responsibility.
            let lhs_is_arith = manager.get(lhs).is_some_and(|t| {
                t.sort == manager.sorts.int_sort || t.sort == manager.sorts.real_sort
            });
            if !lhs_is_arith {
                continue;
            }
            // A successful linear parse means the atom is fully handled.
            if self.var_to_parsed_arith.contains_key(var) {
                continue;
            }
            if Self::term_contains_unhandled_arith(lhs, manager)
                || Self::term_contains_unhandled_arith(rhs, manager)
            {
                return true;
            }
        }
        false
    }

    /// Structural DAG scan (explicit stack, no unbounded recursion) that returns
    /// `true` when `term` contains an arithmetic construct the linear solver
    /// cannot encode: integer `div`/`mod`, a nonlinear multiplication (two or
    /// more variable factors), or a constant too large for `i64`.
    fn term_contains_unhandled_arith(term: TermId, manager: &TermManager) -> bool {
        let mut stack: Vec<TermId> = vec![term];
        let mut visited: FxHashSet<TermId> = FxHashSet::default();
        while let Some(t) = stack.pop() {
            if !visited.insert(t) {
                continue;
            }
            let Some(node) = manager.get(t) else {
                continue;
            };
            match &node.kind {
                TermKind::Div(_, _) | TermKind::Mod(_, _) => return true,
                TermKind::IntConst(n) if n.to_i64().is_none() => return true,
                TermKind::BitVecConst { value, .. } if value.to_i64().is_none() => return true,
                TermKind::Mul(args) => {
                    let mut variable_factors = 0usize;
                    for &a in args {
                        if Self::arith_subterm_has_variable(a, manager) {
                            variable_factors += 1;
                        }
                        stack.push(a);
                    }
                    if variable_factors >= 2 {
                        return true;
                    }
                }
                TermKind::Add(args) => {
                    for &a in args {
                        stack.push(a);
                    }
                }
                TermKind::Sub(a, b) => {
                    stack.push(*a);
                    stack.push(*b);
                }
                TermKind::Neg(a) => stack.push(*a),
                _ => {}
            }
        }
        false
    }

    /// Returns `true` if the arithmetic subtree rooted at `term` is not a pure
    /// constant — i.e. it reaches a variable, an uninterpreted application, an
    /// array select, or a div/mod node.  Used to count the non-constant factors
    /// of a product when deciding whether it is nonlinear.
    fn arith_subterm_has_variable(term: TermId, manager: &TermManager) -> bool {
        let mut stack: Vec<TermId> = vec![term];
        let mut visited: FxHashSet<TermId> = FxHashSet::default();
        while let Some(t) = stack.pop() {
            if !visited.insert(t) {
                continue;
            }
            let Some(node) = manager.get(t) else {
                continue;
            };
            match &node.kind {
                TermKind::Var(_)
                | TermKind::Apply { .. }
                | TermKind::Select(_, _)
                | TermKind::Div(_, _)
                | TermKind::Mod(_, _) => return true,
                TermKind::Add(args) | TermKind::Mul(args) => {
                    for &a in args {
                        stack.push(a);
                    }
                }
                TermKind::Sub(a, b) => {
                    stack.push(*a);
                    stack.push(*b);
                }
                TermKind::Neg(a) => stack.push(*a),
                _ => {}
            }
        }
        false
    }

    /// Returns `true` when the term rooted at `root` nests deeper than
    /// [`ENCODE_DEPTH_LIMIT`](super::ENCODE_DEPTH_LIMIT).
    ///
    /// The check is performed with an explicit work-stack (never native
    /// recursion), so it is itself immune to stack overflow.  It computes the
    /// longest root-to-leaf path over the term DAG, pruning any node already
    /// reached at an equal-or-greater depth so shared sub-terms are not
    /// re-expanded, and returns as soon as the limit is passed.
    pub(super) fn term_exceeds_encode_depth(&self, root: TermId, manager: &TermManager) -> bool {
        let limit = super::ENCODE_DEPTH_LIMIT;
        // Deepest depth at which each node has already been scheduled.
        let mut best: FxHashMap<TermId, u32> = FxHashMap::default();
        let mut stack: Vec<(TermId, u32)> = vec![(root, 1)];
        while let Some((t, depth)) = stack.pop() {
            if depth > limit {
                return true;
            }
            match best.get(&t) {
                Some(&prev) if prev >= depth => continue,
                _ => {}
            }
            best.insert(t, depth);
            Self::push_child_terms(t, manager, depth + 1, &mut stack);
        }
        false
    }

    /// Push every direct sub-term of `term` onto `stack` paired with
    /// `child_depth`.  Covers all `TermKind` variants that carry `TermId`
    /// children and can therefore contribute to formula depth; leaf and
    /// nullary kinds add nothing.
    fn push_child_terms(
        term: TermId,
        manager: &TermManager,
        child_depth: u32,
        stack: &mut Vec<(TermId, u32)>,
    ) {
        let Some(node) = manager.get(term) else {
            return;
        };
        let mut push = |t: TermId| stack.push((t, child_depth));
        match &node.kind {
            TermKind::Not(a) | TermKind::Neg(a) | TermKind::BvNot(a) => push(*a),
            TermKind::And(args)
            | TermKind::Or(args)
            | TermKind::Add(args)
            | TermKind::Mul(args)
            | TermKind::Distinct(args) => {
                for &a in args {
                    push(a);
                }
            }
            TermKind::Xor(a, b)
            | TermKind::Implies(a, b)
            | TermKind::Eq(a, b)
            | TermKind::Sub(a, b)
            | TermKind::Div(a, b)
            | TermKind::Mod(a, b)
            | TermKind::Lt(a, b)
            | TermKind::Le(a, b)
            | TermKind::Gt(a, b)
            | TermKind::Ge(a, b)
            | TermKind::BvConcat(a, b)
            | TermKind::BvAnd(a, b)
            | TermKind::BvOr(a, b)
            | TermKind::BvXor(a, b)
            | TermKind::BvAdd(a, b)
            | TermKind::BvSub(a, b)
            | TermKind::BvMul(a, b)
            | TermKind::BvShl(a, b)
            | TermKind::BvLshr(a, b)
            | TermKind::BvAshr(a, b)
            | TermKind::BvUdiv(a, b)
            | TermKind::BvSdiv(a, b)
            | TermKind::BvUrem(a, b)
            | TermKind::BvSrem(a, b)
            | TermKind::BvUlt(a, b)
            | TermKind::BvUle(a, b)
            | TermKind::BvSlt(a, b)
            | TermKind::BvSle(a, b)
            | TermKind::Select(a, b) => {
                push(*a);
                push(*b);
            }
            TermKind::Ite(a, b, c) | TermKind::Store(a, b, c) => {
                push(*a);
                push(*b);
                push(*c);
            }
            TermKind::BvExtract { arg, .. } => push(*arg),
            // String / FP operations that carry term children.  These can nest
            // arbitrarily too (e.g. a deep `str.++` chain), so include them so
            // the guard fires before a recursive pass overflows.
            TermKind::StrLen(a)
            | TermKind::StrToInt(a)
            | TermKind::IntToStr(a)
            | TermKind::FpAbs(a)
            | TermKind::FpNeg(a)
            | TermKind::FpToReal(a)
            | TermKind::FpIsNormal(a)
            | TermKind::FpIsSubnormal(a)
            | TermKind::FpIsZero(a)
            | TermKind::FpIsInfinite(a)
            | TermKind::FpIsNaN(a)
            | TermKind::FpIsNegative(a)
            | TermKind::FpIsPositive(a) => push(*a),
            TermKind::StrConcat(a, b)
            | TermKind::StrAt(a, b)
            | TermKind::StrInRe(a, b)
            | TermKind::StrContains(a, b)
            | TermKind::StrPrefixOf(a, b)
            | TermKind::StrSuffixOf(a, b)
            | TermKind::FpRem(a, b)
            | TermKind::FpMin(a, b)
            | TermKind::FpMax(a, b)
            | TermKind::FpLeq(a, b)
            | TermKind::FpLt(a, b)
            | TermKind::FpGeq(a, b)
            | TermKind::FpGt(a, b)
            | TermKind::FpEq(a, b) => {
                push(*a);
                push(*b);
            }
            // FP rounding-mode ops: the leading `RoundingMode` is not a term.
            TermKind::FpSqrt(_, a) | TermKind::FpRoundToIntegral(_, a) => push(*a),
            TermKind::FpAdd(_, a, b)
            | TermKind::FpSub(_, a, b)
            | TermKind::FpMul(_, a, b)
            | TermKind::FpDiv(_, a, b) => {
                push(*a);
                push(*b);
            }
            TermKind::StrSubstr(a, b, c)
            | TermKind::StrReplace(a, b, c)
            | TermKind::StrReplaceAll(a, b, c)
            | TermKind::StrIndexOf(a, b, c) => {
                push(*a);
                push(*b);
                push(*c);
            }
            TermKind::Apply { args, .. } => {
                for &a in args {
                    push(a);
                }
            }
            TermKind::Let { bindings, body } => {
                for (_name, value) in bindings {
                    push(*value);
                }
                push(*body);
            }
            TermKind::Forall { body, .. } | TermKind::Exists { body, .. } => push(*body),
            // Every other kind is a leaf or a shallow theory atom for the
            // purpose of depth: it cannot build unbounded nesting on its own.
            _ => {}
        }
    }
}
