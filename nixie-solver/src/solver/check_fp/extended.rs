//! Extended FP-constraint discovery: the polarity-aware walk that feeds
//! [`super::Solver::check_fp_constraints`]'s definite-conflict checks.
//!
//! Split out of `check_fp.rs` to keep that file under the workspace's
//! 2000-line ceiling; see its module doc for the theory-level picture of what
//! the collected facts are used for.
//!
//! # Why one function, not two
//!
//! This used to be two mutually-recursive methods: `collect_fp_constraints_extended`
//! (which records predicate-level facts -- isZero/isPositive/isNegative/isNaN,
//! comparisons, equalities, operation results -- but only while a sub-term is
//! still *unconditionally asserted*) and `collect_fp_constraints_extended_recurse`
//! ("helper to recurse without collecting predicates", a reduced-fidelity walk
//! that tracks only FP/Real conversion chains, entered once a sub-term is no
//! longer unconditionally asserted -- e.g. the operands of an `Eq`, or a
//! disjunct of an `Or`). Both were plain native recursion with no depth guard:
//! a term built directly through the `TermManager` builder API can nest
//! arbitrarily deep (there is no parser-side nesting cap once the builder is
//! called directly), and `collect_fp_constraints_extended` is reachable from
//! `check_sat`, so a sufficiently deep formula reached a native stack
//! overflow -- a fatal, `catch_unwind`-proof process abort -- instead of an
//! error value.
//!
//! The fix is an explicit heap-allocated worklist rather than a depth cap: a
//! cap would silently stop collecting constraints partway through the
//! formula, and for a *definite-conflict* collector like this one, an
//! incomplete fact set can only make the check *miss* a real conflict, never
//! fabricate one -- so the observable failure mode of a naive cap here would
//! be a false `Sat`. See `check_fp_constraints`'s doc comment and
//! `term_walk::asserted_children` for why that distinction matters in this
//! file specifically.
//!
//! Both original methods are folded into the single
//! [`Solver::collect_fp_constraints_extended`] below, driven by one explicit
//! stack holding a small tagged [`WalkItem`]: either `Extended(term, positive)`
//! (the old entry function's own logic) or `Recurse(term)` (the old helper's
//! logic). The helper never actually read its own `in_positive_context`
//! parameter -- true of every arm transcribed below -- so `Recurse` carries no
//! polarity, even though the task of un-recursing this file initially expected
//! a uniform `(TermId, bool)` item; once actually reading the code, keeping a
//! bool nobody reads would misstate why it is there. Keeping the two modes as
//! separate variants (rather than collapsing everything into one pass) is
//! what preserves behavior exactly: the two original functions traverse
//! *different* sets of `TermKind`s and record *different* facts, and `Or`'s
//! disjuncts deliberately drop into `Recurse` mode rather than continuing in
//! `Extended` mode, because a disjunct is not unconditionally asserted.
//!
//! # Traversal order
//!
//! Every call site below pushes a node's children in **reverse** order, so
//! that popping the stack reproduces the original recursion's left-to-right,
//! subtree-complete-before-next-sibling order exactly. This is not cosmetic:
//! `rounding_add_results` is a `HashMap`, and a later-inserted equal key
//! silently overwrites an earlier one -- `check_fp_constraints`'s Check 5
//! (RTP/RTN rounding conflict) depends on which insertion wins. Visiting
//! sub-terms out of order could change which `(op1, op2, rm) -> result`
//! mapping survives and, in turn, whether a real conflict is found. No
//! `visited` set is used, matching the original (neither method had one): a
//! shared sub-DAG can still be walked more than once, exactly as before --
//! only the *native stack* dependency is removed, not this pre-existing (and
//! separately-tracked-as-acceptable) duplicate-work characteristic. Adding
//! dedup here would risk exactly the failure mode this whole audit is
//! guarding against elsewhere: silently dropping a legitimate second visit
//! that a `HashMap`-keyed check depends on.
//!
//! Reference: none -- unlike most of this crate, this is Nixie's own
//! incomplete FP conflict search rather than a port of a single Z3 routine.

#[allow(unused_imports)]
use crate::prelude::*;
use nixie_core::ast::{RoundingMode, TermId, TermKind, TermManager};
use num_traits::ToPrimitive;

use super::super::Solver;

/// One entry of the explicit worklist that replaces the former
/// `collect_fp_constraints_extended` / `collect_fp_constraints_extended_recurse`
/// mutual native recursion; see the module doc for why two variants are used
/// instead of a single shape.
enum WalkItem {
    /// The old `collect_fp_constraints_extended`'s own logic: records
    /// predicate-level facts when `positive` matches the fact's required
    /// polarity, then pushes each child in whichever mode preserves what is
    /// genuinely still asserted about it.
    Extended(TermId, bool),
    /// The old `collect_fp_constraints_extended_recurse`'s logic: records
    /// only FP/Real conversion chains, for sub-terms that are no longer
    /// unconditionally asserted.
    Recurse(TermId),
}

impl Solver {
    /// Collect FP constraints from a term (extended version with additional
    /// tracking), driven by an explicit worklist -- see the module doc for why
    /// this single function now covers what used to be two.
    #[allow(clippy::too_many_arguments)]
    pub(super) fn collect_fp_constraints_extended(
        &self,
        term: TermId,
        manager: &TermManager,
        fp_additions: &mut Vec<(TermId, TermId, TermId, TermId, RoundingMode)>,
        fp_divisions: &mut Vec<(TermId, TermId, TermId, TermId, RoundingMode)>,
        fp_multiplications: &mut Vec<(TermId, TermId, TermId, TermId, RoundingMode)>,
        fp_comparisons: &mut Vec<(TermId, TermId, bool)>,
        fp_equalities: &mut Vec<(TermId, TermId)>,
        fp_literals: &mut FxHashMap<TermId, f64>,
        rounding_add_results: &mut FxHashMap<(TermId, TermId, RoundingMode), TermId>,
        fp_is_zero: &mut FxHashSet<TermId>,
        fp_is_positive: &mut FxHashSet<TermId>,
        fp_is_negative: &mut FxHashSet<TermId>,
        fp_not_nan: &mut FxHashSet<TermId>,
        fp_gt_comparisons: &mut Vec<(TermId, TermId)>,
        fp_lt_comparisons: &mut Vec<(TermId, TermId)>,
        fp_conversions: &mut Vec<(TermId, u32, u32, TermId)>,
        real_to_fp_conversions: &mut Vec<(TermId, u32, u32, TermId)>,
        fp_subtractions: &mut Vec<(TermId, TermId, TermId)>,
        in_positive_context: bool,
    ) {
        let mut stack: Vec<WalkItem> = vec![WalkItem::Extended(term, in_positive_context)];

        while let Some(item) = stack.pop() {
            match item {
                WalkItem::Extended(term, in_positive_context) => {
                    let Some(term_data) = manager.get(term) else {
                        continue;
                    };

                    match &term_data.kind {
                        // FP predicates
                        TermKind::FpIsZero(arg) => {
                            if in_positive_context {
                                fp_is_zero.insert(*arg);
                            }
                            stack.push(WalkItem::Recurse(*arg));
                        }
                        TermKind::FpIsPositive(arg) => {
                            if in_positive_context {
                                fp_is_positive.insert(*arg);
                            }
                            stack.push(WalkItem::Recurse(*arg));
                        }
                        TermKind::FpIsNegative(arg) => {
                            if in_positive_context {
                                fp_is_negative.insert(*arg);
                            }
                            stack.push(WalkItem::Recurse(*arg));
                        }
                        TermKind::FpIsNaN(arg) => {
                            // If in negative context (under a Not), this means not(isNaN(arg))
                            if !in_positive_context {
                                fp_not_nan.insert(*arg);
                            }
                            stack.push(WalkItem::Recurse(*arg));
                        }
                        // FP comparisons
                        TermKind::FpLt(a, b) => {
                            if in_positive_context {
                                fp_comparisons.push((*a, *b, true));
                                fp_lt_comparisons.push((*a, *b));
                            }
                            // Reverse push: `a` must fully drain before `b`,
                            // matching the original left-to-right recursion.
                            stack.push(WalkItem::Recurse(*b));
                            stack.push(WalkItem::Recurse(*a));
                        }
                        TermKind::FpGt(a, b) => {
                            if in_positive_context {
                                fp_comparisons.push((*b, *a, true)); // a > b means b < a
                                fp_gt_comparisons.push((*a, *b)); // Track original direction: a > b
                            }
                            stack.push(WalkItem::Recurse(*b));
                            stack.push(WalkItem::Recurse(*a));
                        }
                        // Equality
                        TermKind::Eq(lhs, rhs) => {
                            // Equality-derived facts (a = b, literal assignments, operation
                            // results, conversions) only hold when the equality is asserted
                            // positively.  Under a `Not`, `(not (= a b))` is a DISequality and
                            // must NOT be recorded as `a = b`; treating it as an equality
                            // previously produced spurious UNSAT answers (e.g. Check 3 firing
                            // on a negated `y = fp.div 0 0`).
                            if in_positive_context {
                                fp_equalities.push((*lhs, *rhs));

                                // Check for FP literal assignment
                                if let Some(val) =
                                    self.get_fp_literal_value_from_eq(*rhs, manager, fp_equalities)
                                {
                                    fp_literals.insert(*lhs, val);
                                } else if let Some(val) =
                                    self.get_fp_literal_value_from_eq(*lhs, manager, fp_equalities)
                                {
                                    fp_literals.insert(*rhs, val);
                                }

                                // Check for FP operation results
                                if let Some(rhs_data) = manager.get(*rhs) {
                                    match &rhs_data.kind {
                                        TermKind::FpAdd(rm, x, y) => {
                                            fp_additions.push((*lhs, *x, *y, *lhs, *rm));
                                            rounding_add_results.insert((*x, *y, *rm), *lhs);
                                        }
                                        TermKind::FpDiv(rm, x, y) => {
                                            fp_divisions.push((*lhs, *x, *y, *lhs, *rm));
                                        }
                                        TermKind::FpMul(rm, x, y) => {
                                            fp_multiplications.push((*lhs, *x, *y, *lhs, *rm));
                                        }
                                        TermKind::FpSub(_, x, y) => {
                                            // Track: (lhs_operand, rhs_operand, result)
                                            fp_subtractions.push((*x, *y, *lhs));
                                        }
                                        TermKind::FpToFp { arg, eb, sb, .. } => {
                                            fp_conversions.push((*arg, *eb, *sb, *lhs));
                                        }
                                        TermKind::RealToFp { arg, eb, sb, .. } => {
                                            real_to_fp_conversions.push((*arg, *eb, *sb, *lhs));
                                        }
                                        _ => {}
                                    }
                                }
                                if let Some(lhs_data) = manager.get(*lhs) {
                                    match &lhs_data.kind {
                                        TermKind::FpAdd(rm, x, y) => {
                                            fp_additions.push((*rhs, *x, *y, *rhs, *rm));
                                            rounding_add_results.insert((*x, *y, *rm), *rhs);
                                        }
                                        TermKind::FpDiv(rm, x, y) => {
                                            fp_divisions.push((*rhs, *x, *y, *rhs, *rm));
                                        }
                                        TermKind::FpMul(rm, x, y) => {
                                            fp_multiplications.push((*rhs, *x, *y, *rhs, *rm));
                                        }
                                        TermKind::FpSub(_, x, y) => {
                                            fp_subtractions.push((*x, *y, *rhs));
                                        }
                                        TermKind::FpToFp { arg, eb, sb, .. } => {
                                            fp_conversions.push((*arg, *eb, *sb, *rhs));
                                        }
                                        TermKind::RealToFp { arg, eb, sb, .. } => {
                                            real_to_fp_conversions.push((*arg, *eb, *sb, *rhs));
                                        }
                                        _ => {}
                                    }
                                }
                            } // end `if in_positive_context`

                            stack.push(WalkItem::Recurse(*rhs));
                            stack.push(WalkItem::Recurse(*lhs));
                        }
                        // FP conversions (standalone, not in equality)
                        TermKind::FpToFp { arg, eb, sb, .. } => {
                            fp_conversions.push((*arg, *eb, *sb, term));
                            stack.push(WalkItem::Recurse(*arg));
                        }
                        TermKind::RealToFp { arg, eb, sb, .. } => {
                            real_to_fp_conversions.push((*arg, *eb, *sb, term));
                            // Also extract literal value
                            if let Some(arg_data) = manager.get(*arg) {
                                if let TermKind::RealConst(r) = &arg_data.kind {
                                    if let Some(val) = r.to_f64() {
                                        fp_literals.insert(term, val);
                                    }
                                }
                            }
                        }
                        // Compound terms.  `And` and `Not` are the only nodes that carry
                        // unconditional assertedness downwards, and `asserted_children` is
                        // the single place that decides which children qualify: an `And`
                        // hands out its conjuncts only at *positive* polarity, because
                        // `(not (and a b))` is `(or (not a) (not b))` and entails neither
                        // conjunct.  Passing `in_positive_context` straight through the
                        // `And` arm previously let `(not (and (fp.isNaN y) p))` record
                        // `y` as not-NaN and refuted a formula that is satisfiable with
                        // `p = false`.
                        TermKind::And(_) | TermKind::Not(_) => {
                            for &(child, child_positive) in
                                super::super::term_walk::asserted_children(
                                    &term_data.kind,
                                    in_positive_context,
                                )
                                .iter()
                                .rev()
                            {
                                stack.push(WalkItem::Extended(child, child_positive));
                            }
                        }
                        TermKind::Or(args) => {
                            // A disjunct asserts nothing, so this descends through the
                            // *discovery-only* mode, which may record the structural
                            // conversion terms it meets (`fp.to_fp` of a concrete real is
                            // that value no matter which branch is taken) but can never
                            // touch the predicate / equality / comparison fact maps.  This
                            // is the same sanctioned split as `check_array.rs`'s
                            // `collect_facts` flag.
                            for &arg in args.iter().rev() {
                                stack.push(WalkItem::Recurse(arg));
                            }
                        }
                        _ => {}
                    }
                }
                WalkItem::Recurse(term) => {
                    let Some(term_data) = manager.get(term) else {
                        continue;
                    };

                    // Only recurse into compound terms or collect conversion info
                    match &term_data.kind {
                        TermKind::FpToFp { arg, eb, sb, .. } => {
                            fp_conversions.push((*arg, *eb, *sb, term));
                            stack.push(WalkItem::Recurse(*arg));
                        }
                        TermKind::RealToFp { arg, eb, sb, .. } => {
                            real_to_fp_conversions.push((*arg, *eb, *sb, term));
                            if let Some(arg_data) = manager.get(*arg) {
                                if let TermKind::RealConst(r) = &arg_data.kind {
                                    if let Some(val) = r.to_f64() {
                                        fp_literals.insert(term, val);
                                    }
                                }
                            }
                        }
                        TermKind::And(args) | TermKind::Or(args) => {
                            for &arg in args.iter().rev() {
                                stack.push(WalkItem::Recurse(arg));
                            }
                        }
                        // Handle Apply terms that are to_fp conversions from parser
                        TermKind::Apply { func, args } => {
                            let func_name = manager.resolve_str(*func);
                            // Check for indexed to_fp like "(_ to_fp 8 24)"
                            if func_name.starts_with("(_ to_fp ")
                                || func_name.starts_with("(_to_fp ")
                            {
                                // Parse eb and sb from the function name: "(_ to_fp eb sb)"
                                if let Some((eb, sb)) = Self::parse_to_fp_indices(func_name) {
                                    if args.len() >= 2 {
                                        // Format: ((_ to_fp eb sb) rm arg)
                                        // args[0] is rounding mode, args[1] is the value/term to convert
                                        let arg = args[1];
                                        // Determine if this is RealToFp or FpToFp by checking arg's sort/type
                                        if let Some(arg_data) = manager.get(arg) {
                                            let is_real_arg = matches!(
                                                arg_data.kind,
                                                TermKind::RealConst(_) | TermKind::IntConst(_)
                                            );
                                            if is_real_arg {
                                                // RealToFp conversion
                                                real_to_fp_conversions.push((arg, eb, sb, term));
                                                // Also extract literal value
                                                if let TermKind::RealConst(r) = &arg_data.kind {
                                                    if let Some(val) = r.to_f64() {
                                                        fp_literals.insert(term, val);
                                                    }
                                                } else if let TermKind::IntConst(n) = &arg_data.kind
                                                {
                                                    if let Some(val) = n.to_i64() {
                                                        fp_literals.insert(term, val as f64);
                                                    }
                                                }
                                            } else {
                                                // FpToFp conversion (arg is a FP variable/term)
                                                fp_conversions.push((arg, eb, sb, term));
                                            }
                                        }
                                    }
                                }
                            }
                            // Recurse into args
                            for &arg in args.iter().rev() {
                                stack.push(WalkItem::Recurse(arg));
                            }
                        }
                        _ => {}
                    }
                }
            }
        }
    }

    /// Parse to_fp indices from function name like "(_ to_fp 8 24)" -> (8, 24)
    fn parse_to_fp_indices(func_name: &str) -> Option<(u32, u32)> {
        // Handle format: "(_ to_fp eb sb)"
        let trimmed = func_name
            .trim_start_matches("(_ to_fp")
            .trim_start_matches("(_to_fp")
            .trim();
        let trimmed = trimmed.trim_end_matches(')').trim();
        let parts: Vec<&str> = trimmed.split_whitespace().collect();
        if parts.len() >= 2 {
            let eb = parts[0].parse().ok()?;
            let sb = parts[1].parse().ok()?;
            Some((eb, sb))
        } else {
            None
        }
    }

    /// Get FP literal value from a term (for use in
    /// `collect_fp_constraints_extended`).
    fn get_fp_literal_value_from_eq(
        &self,
        term: TermId,
        manager: &TermManager,
        equalities: &[(TermId, TermId)],
    ) -> Option<f64> {
        // Check direct RealToFp
        if let Some(term_data) = manager.get(term) {
            if let TermKind::RealToFp { arg, .. } = &term_data.kind {
                if let Some(arg_data) = manager.get(*arg) {
                    if let TermKind::RealConst(r) = &arg_data.kind {
                        return r.to_f64();
                    }
                }
            }
            if let TermKind::RealConst(r) = &term_data.kind {
                return r.to_f64();
            }
            if let TermKind::IntConst(n) = &term_data.kind {
                return n.to_i64().map(|v| v as f64);
            }
        }
        // Check via equalities
        for &(eq_lhs, eq_rhs) in equalities {
            let to_check = if eq_lhs == term {
                eq_rhs
            } else if eq_rhs == term {
                eq_lhs
            } else {
                continue;
            };
            if let Some(term_data) = manager.get(to_check) {
                if let TermKind::RealToFp { arg, .. } = &term_data.kind {
                    if let Some(arg_data) = manager.get(*arg) {
                        if let TermKind::RealConst(r) = &arg_data.kind {
                            return r.to_f64();
                        }
                    }
                }
            }
        }
        None
    }
}
