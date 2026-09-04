//! Shape-extraction helpers shared by [`super::structural::structurally_equal`]
//! and [`super::alpha::alpha_equivalent`].
//!
//! Both functions dispatch their outer match on `lt.kind` alone (see
//! `structural.rs`'s module docs for why), which means that once inside an
//! arm for e.g. "some plain unary operator", they still need to pull the
//! matching payload back out of `rt.kind` -- which could be *any* member of
//! that shape family, not necessarily the same one as `lt.kind` (that's
//! exactly what the caller's `core::mem::discriminant` check guards against).
//! These helpers centralize that extraction so the shape (which fields, in
//! which order) is spelled out exactly once rather than twice per function.
//!
//! Each helper covers only the `TermKind` variants matching one particular
//! field shape and returns `None` for everything else; that `None` is *not*
//! a "not equal" verdict by itself; every call site pairs it with a
//! `core::mem::discriminant` check against `lt.kind` so the two together
//! prove "same specific variant on both sides", not merely "some variant of
//! this shape on each side" (which would wrongly let e.g. `And` compare
//! equal to `Or`).

use crate::ast::{RoundingMode, TermId, TermKind};
use smallvec::SmallVec;

/// Extract the single `TermId` operand from any `TermKind` whose only field
/// is the one term it applies to (`Not`, `FpAbs`, `StrLen`, ...).
pub(super) fn unary_arg(kind: &TermKind) -> Option<TermId> {
    match kind {
        TermKind::Not(a)
        | TermKind::Neg(a)
        | TermKind::BvNot(a)
        | TermKind::StrLen(a)
        | TermKind::StrToInt(a)
        | TermKind::IntToStr(a)
        | TermKind::StrToCode(a)
        | TermKind::StrFromCode(a)
        | TermKind::FpAbs(a)
        | TermKind::FpNeg(a)
        | TermKind::FpIsNormal(a)
        | TermKind::FpIsSubnormal(a)
        | TermKind::FpIsZero(a)
        | TermKind::FpIsInfinite(a)
        | TermKind::FpIsNaN(a)
        | TermKind::FpIsNegative(a)
        | TermKind::FpIsPositive(a)
        | TermKind::FpToReal(a) => Some(*a),
        _ => None,
    }
}

/// Extract `(rounding_mode, arg)` from `FpSqrt`/`FpRoundToIntegral`.
pub(super) fn unary_rm_arg(kind: &TermKind) -> Option<(RoundingMode, TermId)> {
    match kind {
        TermKind::FpSqrt(rm, a) | TermKind::FpRoundToIntegral(rm, a) => Some((*rm, *a)),
        _ => None,
    }
}

/// Extract `(a, b)` from any `TermKind` whose only fields are exactly two
/// terms (`Xor`, `Eq`, every plain `Bv*`/`Str*`/`Fp*` binary operator, ...).
pub(super) fn binary_args(kind: &TermKind) -> Option<(TermId, TermId)> {
    match kind {
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
        | TermKind::Select(a, b)
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
        | TermKind::StrConcat(a, b)
        | TermKind::StrAt(a, b)
        | TermKind::StrContains(a, b)
        | TermKind::StrPrefixOf(a, b)
        | TermKind::StrSuffixOf(a, b)
        | TermKind::StrInRe(a, b)
        | TermKind::StrLt(a, b)
        | TermKind::StrLe(a, b)
        | TermKind::FpRem(a, b)
        | TermKind::FpMin(a, b)
        | TermKind::FpMax(a, b)
        | TermKind::FpLeq(a, b)
        | TermKind::FpLt(a, b)
        | TermKind::FpGeq(a, b)
        | TermKind::FpGt(a, b)
        | TermKind::FpEq(a, b) => Some((*a, *b)),
        _ => None,
    }
}

/// Extract `(rounding_mode, a, b)` from `FpAdd`/`FpSub`/`FpMul`/`FpDiv`.
pub(super) fn binary_rm_args(kind: &TermKind) -> Option<(RoundingMode, TermId, TermId)> {
    match kind {
        TermKind::FpAdd(rm, a, b)
        | TermKind::FpSub(rm, a, b)
        | TermKind::FpMul(rm, a, b)
        | TermKind::FpDiv(rm, a, b) => Some((*rm, *a, *b)),
        _ => None,
    }
}

/// Extract `(a, b, c)` from any `TermKind` whose only fields are exactly
/// three terms (`Ite`, `Store`, every plain ternary `Str*` operator, ...).
pub(super) fn ternary_args(kind: &TermKind) -> Option<(TermId, TermId, TermId)> {
    match kind {
        TermKind::Ite(c, t, e)
        | TermKind::Store(c, t, e)
        | TermKind::StrSubstr(c, t, e)
        | TermKind::StrIndexOf(c, t, e)
        | TermKind::StrReplace(c, t, e)
        | TermKind::StrReplaceAll(c, t, e)
        | TermKind::StrReplaceRe(c, t, e)
        | TermKind::StrReplaceReAll(c, t, e) => Some((*c, *t, *e)),
        _ => None,
    }
}

/// Extract the n-ary argument list from `And`/`Or`/`Add`/`Mul`/`Distinct`.
pub(super) fn nary_args(kind: &TermKind) -> Option<&SmallVec<[TermId; 4]>> {
    match kind {
        TermKind::And(args)
        | TermKind::Or(args)
        | TermKind::Add(args)
        | TermKind::Mul(args)
        | TermKind::Distinct(args) => Some(args),
        _ => None,
    }
}
