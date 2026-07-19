//! Standalone bit-vector term bit-blasting helpers for the theory manager.
//!
//! These are pure free functions (no `TheoryManager` state) extracted from
//! `theory_manager.rs` to keep that file under the workspace 2000-line limit.
//! They recursively encode BV-sorted terms into a [`BvSolver`]'s bit-blasted
//! circuits so the embedded SAT solver can reason about them.

use crate::prelude::FxHashSet;
use oxiz_core::ast::{TermId, TermKind, TermManager};
use oxiz_theories::bv::BvSolver;

/// Post-order, memoised BV term encoding.
///
/// Bit-blast every BV-sorted operand reachable through a boolean condition
/// `cond` (the kind that appears as an `ite` selector). Walks the boolean
/// connective/comparison structure and bit-blasts the BV terms underneath the
/// `Eq`/comparison leaves, so that `BvSolver::encode_bool_node` can look them
/// up. Returns `false` if any BV operand fails to encode.
fn bit_blast_cond_operands(bv: &mut BvSolver, cond: TermId, mgr: &TermManager) -> bool {
    let term = match mgr.get(cond) {
        Some(t) => t,
        None => return false,
    };
    match &term.kind {
        // Boolean structure: recurse into operands.
        TermKind::Not(inner) => bit_blast_cond_operands(bv, *inner, mgr),
        TermKind::And(args) | TermKind::Or(args) => {
            args.iter().all(|&a| bit_blast_cond_operands(bv, a, mgr))
        }
        // Comparison/equality leaves: their operands are BV terms.
        TermKind::Eq(lhs, rhs)
        | TermKind::BvUlt(lhs, rhs)
        | TermKind::BvUle(lhs, rhs)
        | TermKind::BvSlt(lhs, rhs)
        | TermKind::BvSle(lhs, rhs) => {
            let mut encoded: FxHashSet<TermId> = FxHashSet::default();
            let lhs_ok = encode_bv_term_recursive(bv, *lhs, mgr, &mut encoded) || {
                if let Some(w) = mgr
                    .get(*lhs)
                    .and_then(|t| mgr.sorts.get(t.sort))
                    .and_then(|s| s.bitvec_width())
                {
                    bv.new_bv(*lhs, w);
                    true
                } else {
                    false
                }
            };
            let rhs_ok = encode_bv_term_recursive(bv, *rhs, mgr, &mut encoded) || {
                if let Some(w) = mgr
                    .get(*rhs)
                    .and_then(|t| mgr.sorts.get(t.sort))
                    .and_then(|s| s.bitvec_width())
                {
                    bv.new_bv(*rhs, w);
                    true
                } else {
                    false
                }
            };
            lhs_ok && rhs_ok
        }
        // A bare boolean variable / constant has no BV operands to blast.
        TermKind::Var(_) | TermKind::True | TermKind::False => true,
        // Anything else is outside the supported condition fragment.
        _ => false,
    }
}

/// If `tid` is a `BitVecConst` whose value is a positive power of two, return
/// the exponent (shift amount).  Returns `None` for zero, non-powers-of-two,
/// and non-constant terms.
fn bitvec_const_pow2_shift(mgr: &TermManager, tid: TermId) -> Option<u32> {
    let term = mgr.get(tid)?;
    if let TermKind::BitVecConst { value, .. } = &term.kind {
        let digits: Vec<u64> = value.iter_u64_digits().collect();
        let set_bits: u32 = digits.iter().map(|&d| d.count_ones()).sum();
        if set_bits != 1 {
            return None;
        }
        for (chunk, &d) in digits.iter().enumerate() {
            if d != 0 {
                return Some(chunk as u32 * 64 + d.trailing_zeros());
            }
        }
    }
    None
}

/// Recursively encodes every sub-term of `root` into the BV solver using an
/// explicit work-stack so that arbitrarily deep nesting is handled without
/// overflowing the call stack.  A `FxHashSet<TermId>` memo prevents duplicate
/// encoding when the same sub-term appears in multiple branches of the DAG.
///
/// Returns `true` when `root` was fully encoded, `false` when an unrecognised
/// TermKind is encountered.
pub(super) fn encode_bv_term_recursive(
    bv: &mut BvSolver,
    root: TermId,
    mgr: &TermManager,
    encoded: &mut FxHashSet<TermId>,
) -> bool {
    // Work-stack entry: (term_id, children_pushed)
    // We push a term twice: first time to push children, second time to
    // encode the term itself (post-order).
    let mut stack: Vec<(TermId, bool)> = vec![(root, false)];

    while let Some((tid, children_done)) = stack.pop() {
        if encoded.contains(&tid) {
            continue;
        }
        // If the BV solver already has a circuit for this term (encoded in a
        // previous call to encode_bv_term_recursive), skip both the child-push
        // and the encoding phases.  This makes the function globally idempotent:
        // calling it a second time for the same sub-tree is a no-op, which
        // prevents the adder/multiplier circuits from being duplicated across
        // CDCL restarts (each duplicate brings ~33 fresh carry SAT variables and
        // hundreds of new clauses, causing the embedded BV SAT to blow up).
        // Leaves (Var, BitVecConst) are already idempotent via `new_bv`'s
        // `or_insert_with`, so this guard is only strictly necessary for
        // compound operations, but checking unconditionally is correct and safe.
        if bv.get_bv(tid).is_some() {
            encoded.insert(tid);
            continue;
        }

        let term = match mgr.get(tid) {
            Some(t) => t,
            None => return false,
        };

        let width = match mgr.sorts.get(term.sort).and_then(|s| s.bitvec_width()) {
            Some(w) => w,
            None => return false,
        };

        if !children_done {
            // Re-push this node as "children done" so we encode it after children
            stack.push((tid, true));

            // Push children (they will be encoded first)
            match &term.kind {
                TermKind::BvAdd(a, b)
                | TermKind::BvMul(a, b)
                | TermKind::BvSub(a, b)
                | TermKind::BvAnd(a, b)
                | TermKind::BvOr(a, b)
                | TermKind::BvXor(a, b)
                | TermKind::BvUdiv(a, b)
                | TermKind::BvSdiv(a, b)
                | TermKind::BvUrem(a, b)
                | TermKind::BvSrem(a, b) => {
                    if !encoded.contains(a) {
                        stack.push((*a, false));
                    }
                    if !encoded.contains(b) {
                        stack.push((*b, false));
                    }
                }
                TermKind::BvNot(a) => {
                    if !encoded.contains(a) {
                        stack.push((*a, false));
                    }
                }
                // Shifts: value and shift-amount operands (same width).
                TermKind::BvShl(a, b) | TermKind::BvLshr(a, b) | TermKind::BvAshr(a, b) => {
                    if !encoded.contains(a) {
                        stack.push((*a, false));
                    }
                    if !encoded.contains(b) {
                        stack.push((*b, false));
                    }
                }
                // Concatenation: both operands (their own widths).
                TermKind::BvConcat(a, b) => {
                    if !encoded.contains(a) {
                        stack.push((*a, false));
                    }
                    if !encoded.contains(b) {
                        stack.push((*b, false));
                    }
                }
                // Extraction: single source operand (its own width).
                TermKind::BvExtract { arg, .. } => {
                    if !encoded.contains(arg) {
                        stack.push((*arg, false));
                    }
                }
                // ITE over BV: bit-blast both branches; the condition's BV
                // operands are bit-blasted separately just before encoding.
                TermKind::Ite(_cond, then_t, else_t) => {
                    if !encoded.contains(then_t) {
                        stack.push((*then_t, false));
                    }
                    if !encoded.contains(else_t) {
                        stack.push((*else_t, false));
                    }
                }
                // Leaves: Var, BitVecConst — no children to push
                TermKind::Var(_) | TermKind::BitVecConst { .. } => {}
                // Unknown term kind — cannot encode, abort
                _ => return false,
            }
        } else {
            // Encode this node (children already encoded)
            match &term.kind {
                TermKind::BvAdd(a, b) => {
                    bv.new_bv(*a, width);
                    bv.new_bv(*b, width);
                    bv.bv_add(tid, *a, *b);
                }
                TermKind::BvMul(a, b) => {
                    if let Some(shift) = bitvec_const_pow2_shift(mgr, *b) {
                        bv.new_bv(*a, width);
                        bv.bv_shl_const(tid, *a, shift, width);
                    } else if let Some(shift) = bitvec_const_pow2_shift(mgr, *a) {
                        bv.new_bv(*b, width);
                        bv.bv_shl_const(tid, *b, shift, width);
                    } else {
                        bv.new_bv(*a, width);
                        bv.new_bv(*b, width);
                        bv.bv_mul(tid, *a, *b);
                    }
                }
                TermKind::BvSub(a, b) => {
                    bv.new_bv(*a, width);
                    bv.new_bv(*b, width);
                    bv.bv_sub(tid, *a, *b);
                }
                TermKind::BvAnd(a, b) => {
                    bv.new_bv(*a, width);
                    bv.new_bv(*b, width);
                    bv.bv_and(tid, *a, *b);
                }
                TermKind::BvOr(a, b) => {
                    bv.new_bv(*a, width);
                    bv.new_bv(*b, width);
                    bv.bv_or(tid, *a, *b);
                }
                TermKind::BvXor(a, b) => {
                    bv.new_bv(*a, width);
                    bv.new_bv(*b, width);
                    bv.bv_xor(tid, *a, *b);
                }
                TermKind::BvNot(a) => {
                    bv.new_bv(*a, width);
                    bv.bv_not(tid, *a);
                }
                TermKind::BvShl(a, b) => {
                    // Operands and result share `width`.
                    bv.new_bv(*a, width);
                    bv.new_bv(*b, width);
                    bv.bv_shl(tid, *a, *b);
                }
                TermKind::BvLshr(a, b) => {
                    bv.new_bv(*a, width);
                    bv.new_bv(*b, width);
                    bv.bv_lshr(tid, *a, *b);
                }
                TermKind::BvAshr(a, b) => {
                    bv.new_bv(*a, width);
                    bv.new_bv(*b, width);
                    bv.bv_ashr(tid, *a, *b);
                }
                TermKind::BvConcat(a, b) => {
                    // Operands keep their own (possibly differing) widths; the
                    // result width is their sum (already `width` here).
                    let aw = match mgr
                        .get(*a)
                        .and_then(|t| mgr.sorts.get(t.sort))
                        .and_then(|s| s.bitvec_width())
                    {
                        Some(w) => w,
                        None => return false,
                    };
                    let bw = match mgr
                        .get(*b)
                        .and_then(|t| mgr.sorts.get(t.sort))
                        .and_then(|s| s.bitvec_width())
                    {
                        Some(w) => w,
                        None => return false,
                    };
                    bv.new_bv(*a, aw);
                    bv.new_bv(*b, bw);
                    // BvConcat(high, low) — `a` is the high (most-significant) part.
                    bv.concat(tid, *a, *b);
                }
                TermKind::BvExtract { high, low, arg } => {
                    let arg_w = match mgr
                        .get(*arg)
                        .and_then(|t| mgr.sorts.get(t.sort))
                        .and_then(|s| s.bitvec_width())
                    {
                        Some(w) => w,
                        None => return false,
                    };
                    bv.new_bv(*arg, arg_w);
                    bv.extract(tid, *arg, *high, *low);
                }
                TermKind::Ite(cond, then_t, else_t) => {
                    // Branches are already bit-blasted (pushed as children). The
                    // condition's BV operands must be bit-blasted before the
                    // condition itself is encoded inside `bv_ite`.
                    if !bit_blast_cond_operands(bv, *cond, mgr) {
                        return false;
                    }
                    bv.bv_ite(tid, *cond, *then_t, *else_t, mgr);
                }
                TermKind::BvUdiv(a, b) => {
                    bv.new_bv(*a, width);
                    bv.new_bv(*b, width);
                    bv.bv_udiv(tid, *a, *b);
                }
                TermKind::BvSdiv(a, b) => {
                    bv.new_bv(*a, width);
                    bv.new_bv(*b, width);
                    bv.bv_sdiv(tid, *a, *b);
                }
                TermKind::BvUrem(a, b) => {
                    bv.new_bv(*a, width);
                    bv.new_bv(*b, width);
                    bv.bv_urem(tid, *a, *b);
                }
                TermKind::BvSrem(a, b) => {
                    bv.new_bv(*a, width);
                    bv.new_bv(*b, width);
                    bv.bv_srem(tid, *a, *b);
                }
                TermKind::Var(_) => {
                    // Leaf variable: just ensure a BV variable exists.
                    bv.new_bv(tid, width);
                }
                TermKind::BitVecConst { value, .. } => {
                    // Leaf constant: create the BV variable AND pin its bits to
                    // the concrete value.  Without this the constant operand of a
                    // bit-blasted op (e.g. the `#x02` in `(bvmul #x02 x)`) would be
                    // an unconstrained free variable, silently weakening the
                    // encoding and causing false SAT for constant-folded identities.
                    let val_u64 = value.iter_u64_digits().next().unwrap_or(0);
                    bv.assert_const(tid, val_u64, width);
                }
                _ => return false,
            }
            encoded.insert(tid);
        }
    }

    true
}
