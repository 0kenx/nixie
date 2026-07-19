//! Generic structural term traversal helpers.
//!
//! These are theory-agnostic and are shared by the FP and string atom-presence
//! detectors (`check_fp.rs`, `check_string.rs`). Keeping the walker here avoids a
//! cross-file `Solver::` coupling between the FP-specific and string-specific
//! modules and keeps each theory file focused on its own reasoning.

use oxiz_core::ast::{TermId, TermKind};

/// Push every immediate sub-term of `kind` onto `out`.
///
/// This is a fully generic structural walk used by the FP and string
/// atom-presence detectors; it deliberately traverses through *all*
/// compound kinds (Boolean, arithmetic, bit-vector, array, datatype,
/// quantifier, FP, and string) so that a theory atom nested arbitrarily
/// deep is still discovered.
pub(super) fn collect_structural_children(kind: &TermKind, out: &mut Vec<TermId>) {
    match kind {
        // Single sub-term
        TermKind::Not(a)
        | TermKind::Neg(a)
        | TermKind::BvNot(a)
        | TermKind::StrLen(a)
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
        | TermKind::FpIsPositive(a)
        | TermKind::FpSqrt(_, a)
        | TermKind::FpRoundToIntegral(_, a) => out.push(*a),
        TermKind::BvExtract { arg, .. }
        | TermKind::DtTester { arg, .. }
        | TermKind::DtSelector { arg, .. }
        | TermKind::FpToFp { arg, .. }
        | TermKind::FpToSBV { arg, .. }
        | TermKind::FpToUBV { arg, .. }
        | TermKind::RealToFp { arg, .. }
        | TermKind::SBVToFp { arg, .. }
        | TermKind::UBVToFp { arg, .. } => out.push(*arg),
        // Two sub-terms
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
        | TermKind::BvSle(a, b)
        | TermKind::Select(a, b)
        | TermKind::StrConcat(a, b)
        | TermKind::StrAt(a, b)
        | TermKind::StrContains(a, b)
        | TermKind::StrPrefixOf(a, b)
        | TermKind::StrSuffixOf(a, b)
        | TermKind::StrInRe(a, b)
        | TermKind::FpRem(a, b)
        | TermKind::FpMin(a, b)
        | TermKind::FpMax(a, b)
        | TermKind::FpLeq(a, b)
        | TermKind::FpLt(a, b)
        | TermKind::FpGeq(a, b)
        | TermKind::FpGt(a, b)
        | TermKind::FpEq(a, b) => {
            out.push(*a);
            out.push(*b);
        }
        TermKind::FpAdd(_, a, b)
        | TermKind::FpSub(_, a, b)
        | TermKind::FpMul(_, a, b)
        | TermKind::FpDiv(_, a, b) => {
            out.push(*a);
            out.push(*b);
        }
        // Three sub-terms
        TermKind::Ite(a, b, c)
        | TermKind::Store(a, b, c)
        | TermKind::StrSubstr(a, b, c)
        | TermKind::StrIndexOf(a, b, c)
        | TermKind::StrReplace(a, b, c)
        | TermKind::StrReplaceAll(a, b, c) => {
            out.push(*a);
            out.push(*b);
            out.push(*c);
        }
        TermKind::FpFma(_, a, b, c) => {
            out.push(*a);
            out.push(*b);
            out.push(*c);
        }
        // Variadic
        TermKind::And(args)
        | TermKind::Or(args)
        | TermKind::Distinct(args)
        | TermKind::Add(args)
        | TermKind::Mul(args)
        | TermKind::Apply { args, .. }
        | TermKind::DtConstructor { args, .. } => {
            for &arg in args.iter() {
                out.push(arg);
            }
        }
        // Quantifiers / binders
        TermKind::Forall { body, .. } | TermKind::Exists { body, .. } => out.push(*body),
        TermKind::Let { bindings, body } => {
            for &(_, value) in bindings.iter() {
                out.push(value);
            }
            out.push(*body);
        }
        TermKind::Match { scrutinee, cases } => {
            out.push(*scrutinee);
            for case in cases.iter() {
                out.push(case.body);
            }
        }
        // Leaves (constants, variables, FP special values) — no sub-terms.
        _ => {}
    }
}
