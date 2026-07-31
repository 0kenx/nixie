//! [`structurally_equal`]: pure syntactic term comparison, no renaming.
//!
//! The outer match dispatches on `lt.kind` *alone*, with **no wildcard
//! arm**, so adding a new [`TermKind`] variant is a compile error right here
//! rather than a silent `false` from a `_` catch-all -- mirroring
//! `ast/manager/query/substitute.rs::rebuild_substituted`, which uses the
//! same "no `_`" discipline for the same reason. Each arm then checks `rt.kind`
//! against the *same* variant (or variant-group); a genuine kind mismatch
//! (e.g. `And` vs `Not`) falls through that *inner* check to `false`, which is
//! a correct "not equal" answer, not a dropped case. Variants that share an
//! identical field shape (e.g. every plain-unary operator, or `Forall`
//! /`Exists`) are grouped with `|` for brevity; since Rust's OR-patterns
//! cannot themselves distinguish *which* alternative fired, every grouped arm
//! re-checks `core::mem::discriminant(&lt.kind) == core::mem::discriminant(&rt.kind)`
//! before treating the pair as comparable, so e.g. `And([..])` is never
//! accidentally treated as comparable to `Or([..])` just because both are
//! "some n-ary op".
//!
//! `patterns` (the trigger/instantiation hints on `Forall`/`Exists`) are
//! deliberately **not** compared -- see the module-level docs in `mod.rs` for
//! the reasoning shared with [`super::alpha::alpha_equivalent`].

use super::shape;
use crate::ast::{TermId, TermKind, TermManager};
#[allow(unused_imports)]
use crate::prelude::*;

/// Check if two terms are structurally equal (identical syntax, no
/// alpha-renaming of bound variables permitted).
#[must_use]
pub fn structurally_equal(lhs: TermId, rhs: TermId, manager: &TermManager) -> bool {
    if lhs == rhs {
        return true;
    }

    let mut visited: FxHashSet<(TermId, TermId)> = FxHashSet::default();
    let mut stack: Vec<(TermId, TermId)> = vec![(lhs, rhs)];

    while let Some((l, r)) = stack.pop() {
        if l == r {
            continue;
        }
        if !visited.insert((l, r)) {
            continue;
        }

        let lhs_term = manager.get(l);
        let rhs_term = manager.get(r);

        match (lhs_term, rhs_term) {
            (None, None) => {}
            (Some(lt), Some(rt)) if lt.sort != rt.sort => return false,
            (Some(lt), Some(rt)) => {
                match &lt.kind {
                    TermKind::True => {
                        if !matches!(rt.kind, TermKind::True) {
                            return false;
                        }
                    }
                    TermKind::False => {
                        if !matches!(rt.kind, TermKind::False) {
                            return false;
                        }
                    }
                    TermKind::IntConst(a) => {
                        let TermKind::IntConst(b) = &rt.kind else {
                            return false;
                        };
                        if a != b {
                            return false;
                        }
                    }
                    TermKind::RealConst(a) => {
                        let TermKind::RealConst(b) = &rt.kind else {
                            return false;
                        };
                        if a != b {
                            return false;
                        }
                    }
                    TermKind::BitVecConst {
                        value: v1,
                        width: w1,
                    } => {
                        let TermKind::BitVecConst {
                            value: v2,
                            width: w2,
                        } = &rt.kind
                        else {
                            return false;
                        };
                        if v1 != v2 || w1 != w2 {
                            return false;
                        }
                    }
                    TermKind::StringLit(a) => {
                        let TermKind::StringLit(b) = &rt.kind else {
                            return false;
                        };
                        if a != b {
                            return false;
                        }
                    }
                    // Structural equality never permits renaming: two `Var`s
                    // are equal only if they are the exact same name.
                    TermKind::Var(a) => {
                        let TermKind::Var(b) = &rt.kind else {
                            return false;
                        };
                        if a != b {
                            return false;
                        }
                    }

                    // Every plain "one TermId, no other fields" operator.
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
                    | TermKind::FpToReal(a) => {
                        if core::mem::discriminant(&lt.kind) != core::mem::discriminant(&rt.kind) {
                            return false;
                        }
                        let Some(b) = shape::unary_arg(&rt.kind) else {
                            return false;
                        };
                        stack.push((*a, b));
                    }

                    TermKind::FpSqrt(rm1, a) | TermKind::FpRoundToIntegral(rm1, a) => {
                        if core::mem::discriminant(&lt.kind) != core::mem::discriminant(&rt.kind) {
                            return false;
                        }
                        let Some((rm2, b)) = shape::unary_rm_arg(&rt.kind) else {
                            return false;
                        };
                        if *rm1 != rm2 {
                            return false;
                        }
                        stack.push((*a, b));
                    }

                    TermKind::BvExtract {
                        high: h1,
                        low: l1,
                        arg: a1,
                    } => {
                        let TermKind::BvExtract {
                            high: h2,
                            low: l2,
                            arg: a2,
                        } = &rt.kind
                        else {
                            return false;
                        };
                        if h1 != h2 || l1 != l2 {
                            return false;
                        }
                        stack.push((*a1, *a2));
                    }

                    // Every plain "two TermIds, no other fields" operator.
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
                    | TermKind::FpEq(a, b) => {
                        if core::mem::discriminant(&lt.kind) != core::mem::discriminant(&rt.kind) {
                            return false;
                        }
                        let Some((x, y)) = shape::binary_args(&rt.kind) else {
                            return false;
                        };
                        stack.push((*a, x));
                        stack.push((*b, y));
                    }

                    TermKind::FpAdd(rm1, a, b)
                    | TermKind::FpSub(rm1, a, b)
                    | TermKind::FpMul(rm1, a, b)
                    | TermKind::FpDiv(rm1, a, b) => {
                        if core::mem::discriminant(&lt.kind) != core::mem::discriminant(&rt.kind) {
                            return false;
                        }
                        let Some((rm2, x, y)) = shape::binary_rm_args(&rt.kind) else {
                            return false;
                        };
                        if *rm1 != rm2 {
                            return false;
                        }
                        stack.push((*a, x));
                        stack.push((*b, y));
                    }

                    // Every plain "three TermIds, no other fields" operator.
                    TermKind::Ite(c, t, e)
                    | TermKind::Store(c, t, e)
                    | TermKind::StrSubstr(c, t, e)
                    | TermKind::StrIndexOf(c, t, e)
                    | TermKind::StrReplace(c, t, e)
                    | TermKind::StrReplaceAll(c, t, e)
                    | TermKind::StrReplaceRe(c, t, e)
                    | TermKind::StrReplaceReAll(c, t, e) => {
                        if core::mem::discriminant(&lt.kind) != core::mem::discriminant(&rt.kind) {
                            return false;
                        }
                        let Some((x, y, z)) = shape::ternary_args(&rt.kind) else {
                            return false;
                        };
                        stack.push((*c, x));
                        stack.push((*t, y));
                        stack.push((*e, z));
                    }

                    TermKind::FpFma(rm1, a, b, c) => {
                        let TermKind::FpFma(rm2, x, y, z) = &rt.kind else {
                            return false;
                        };
                        if rm1 != rm2 {
                            return false;
                        }
                        stack.push((*a, *x));
                        stack.push((*b, *y));
                        stack.push((*c, *z));
                    }

                    TermKind::And(a)
                    | TermKind::Or(a)
                    | TermKind::Add(a)
                    | TermKind::Mul(a)
                    | TermKind::Distinct(a) => {
                        if core::mem::discriminant(&lt.kind) != core::mem::discriminant(&rt.kind) {
                            return false;
                        }
                        let Some(b) = shape::nary_args(&rt.kind) else {
                            return false;
                        };
                        if a.len() != b.len() {
                            return false;
                        }
                        for (&x, &y) in a.iter().zip(b.iter()) {
                            stack.push((x, y));
                        }
                    }

                    TermKind::Apply { func: f1, args: a1 } => {
                        let TermKind::Apply { func: f2, args: a2 } = &rt.kind else {
                            return false;
                        };
                        if f1 != f2 || a1.len() != a2.len() {
                            return false;
                        }
                        for (&x, &y) in a1.iter().zip(a2.iter()) {
                            stack.push((x, y));
                        }
                    }

                    TermKind::DtConstructor {
                        constructor: c1,
                        args: a1,
                    } => {
                        let TermKind::DtConstructor {
                            constructor: c2,
                            args: a2,
                        } = &rt.kind
                        else {
                            return false;
                        };
                        if c1 != c2 || a1.len() != a2.len() {
                            return false;
                        }
                        for (&x, &y) in a1.iter().zip(a2.iter()) {
                            stack.push((x, y));
                        }
                    }

                    TermKind::DtTester {
                        constructor: c1,
                        arg: a1,
                    }
                    | TermKind::DtSelector {
                        selector: c1,
                        arg: a1,
                    } => {
                        if core::mem::discriminant(&lt.kind) != core::mem::discriminant(&rt.kind) {
                            return false;
                        }
                        let (c2, a2) = match &rt.kind {
                            TermKind::DtTester {
                                constructor: c,
                                arg: a,
                            }
                            | TermKind::DtSelector {
                                selector: c,
                                arg: a,
                            } => (c, *a),
                            _ => return false,
                        };
                        if c1 != c2 {
                            return false;
                        }
                        stack.push((*a1, a2));
                    }

                    TermKind::FpLit {
                        sign: s1,
                        exp: e1,
                        sig: g1,
                        eb: eb1,
                        sb: sb1,
                    } => {
                        let TermKind::FpLit {
                            sign: s2,
                            exp: e2,
                            sig: g2,
                            eb: eb2,
                            sb: sb2,
                        } = &rt.kind
                        else {
                            return false;
                        };
                        if s1 != s2 || e1 != e2 || g1 != g2 || eb1 != eb2 || sb1 != sb2 {
                            return false;
                        }
                    }

                    TermKind::FpPlusInfinity { eb: eb1, sb: sb1 }
                    | TermKind::FpMinusInfinity { eb: eb1, sb: sb1 }
                    | TermKind::FpPlusZero { eb: eb1, sb: sb1 }
                    | TermKind::FpMinusZero { eb: eb1, sb: sb1 }
                    | TermKind::FpNaN { eb: eb1, sb: sb1 } => {
                        if core::mem::discriminant(&lt.kind) != core::mem::discriminant(&rt.kind) {
                            return false;
                        }
                        let (eb2, sb2) = match &rt.kind {
                            TermKind::FpPlusInfinity { eb, sb }
                            | TermKind::FpMinusInfinity { eb, sb }
                            | TermKind::FpPlusZero { eb, sb }
                            | TermKind::FpMinusZero { eb, sb }
                            | TermKind::FpNaN { eb, sb } => (*eb, *sb),
                            _ => return false,
                        };
                        if *eb1 != eb2 || *sb1 != sb2 {
                            return false;
                        }
                    }

                    TermKind::FpToFp {
                        rm: rm1,
                        arg: a1,
                        eb: eb1,
                        sb: sb1,
                    }
                    | TermKind::RealToFp {
                        rm: rm1,
                        arg: a1,
                        eb: eb1,
                        sb: sb1,
                    }
                    | TermKind::SBVToFp {
                        rm: rm1,
                        arg: a1,
                        eb: eb1,
                        sb: sb1,
                    }
                    | TermKind::UBVToFp {
                        rm: rm1,
                        arg: a1,
                        eb: eb1,
                        sb: sb1,
                    } => {
                        if core::mem::discriminant(&lt.kind) != core::mem::discriminant(&rt.kind) {
                            return false;
                        }
                        let (rm2, a2, eb2, sb2) = match &rt.kind {
                            TermKind::FpToFp { rm, arg, eb, sb }
                            | TermKind::RealToFp { rm, arg, eb, sb }
                            | TermKind::SBVToFp { rm, arg, eb, sb }
                            | TermKind::UBVToFp { rm, arg, eb, sb } => (*rm, *arg, *eb, *sb),
                            _ => return false,
                        };
                        if *rm1 != rm2 || *eb1 != eb2 || *sb1 != sb2 {
                            return false;
                        }
                        stack.push((*a1, a2));
                    }

                    TermKind::FpToSBV {
                        rm: rm1,
                        arg: a1,
                        width: w1,
                    }
                    | TermKind::FpToUBV {
                        rm: rm1,
                        arg: a1,
                        width: w1,
                    } => {
                        if core::mem::discriminant(&lt.kind) != core::mem::discriminant(&rt.kind) {
                            return false;
                        }
                        let (rm2, a2, w2) = match &rt.kind {
                            TermKind::FpToSBV { rm, arg, width }
                            | TermKind::FpToUBV { rm, arg, width } => (*rm, *arg, *width),
                            _ => return false,
                        };
                        if *rm1 != rm2 || *w1 != w2 {
                            return false;
                        }
                        stack.push((*a1, a2));
                    }

                    // Quantifiers: structural equality permits *no* renaming,
                    // so the bound-variable list must match exactly --
                    // same names, same sorts, same order. (`patterns` is
                    // intentionally excluded -- see the module docs.)
                    TermKind::Forall {
                        vars: vars1,
                        body: body1,
                        patterns: _,
                    }
                    | TermKind::Exists {
                        vars: vars1,
                        body: body1,
                        patterns: _,
                    } => {
                        if core::mem::discriminant(&lt.kind) != core::mem::discriminant(&rt.kind) {
                            return false;
                        }
                        let (vars2, body2) = match &rt.kind {
                            TermKind::Forall {
                                vars,
                                body,
                                patterns: _,
                            }
                            | TermKind::Exists {
                                vars,
                                body,
                                patterns: _,
                            } => (vars, *body),
                            _ => return false,
                        };
                        if vars1 != vars2 {
                            return false;
                        }
                        stack.push((*body1, body2));
                    }

                    TermKind::Let {
                        bindings: b1,
                        body: body1,
                    } => {
                        let TermKind::Let {
                            bindings: b2,
                            body: body2,
                        } = &rt.kind
                        else {
                            return false;
                        };
                        if b1.len() != b2.len() {
                            return false;
                        }
                        for (&(n1, v1), &(n2, v2)) in b1.iter().zip(b2.iter()) {
                            if n1 != n2 {
                                return false;
                            }
                            stack.push((v1, v2));
                        }
                        stack.push((*body1, *body2));
                    }

                    TermKind::Match {
                        scrutinee: s1,
                        cases: c1,
                    } => {
                        let TermKind::Match {
                            scrutinee: s2,
                            cases: c2,
                        } = &rt.kind
                        else {
                            return false;
                        };
                        if c1.len() != c2.len() {
                            return false;
                        }
                        stack.push((*s1, *s2));
                        for (case1, case2) in c1.iter().zip(c2.iter()) {
                            if case1.constructor != case2.constructor
                                || case1.bindings != case2.bindings
                            {
                                return false;
                            }
                            stack.push((case1.body, case2.body));
                        }
                    }
                }
            }
            _ => return false,
        }
    }

    true
}
