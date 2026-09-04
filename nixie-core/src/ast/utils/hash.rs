//! Structural hashing of terms.
//!
//! [`structural_hash`] mirrors the original recursive `structural_hash_impl`
//! walk exactly, but drives it from an explicit heap-allocated stack instead
//! of the native call stack, so a term nested arbitrarily deep (constructible
//! directly through [`TermManager`]'s builder API, not just through the
//! SMT-LIB parser) cannot overflow the caller's stack. See
//! `smtlib/parser/terms.rs` for the precedent this mirrors, and Z3's
//! `ast.cpp` for the reference hashing scheme.
//!
//! The one subtlety that makes this conversion delicate: the original
//! function feeds every scalar field and every discriminant into *one
//! shared, order-sensitive [`Hasher`]* as it walks, rather than computing an
//! independent digest per subterm and combining digests. That means the
//! iterative version must reproduce the *exact same sequence* of
//! `hasher.write_*` calls in the exact same order, or the resulting `u64`
//! silently changes for every caller relying on it as a cache key or dedup
//! signature (this crate has none today -- `structural_hash`'s only other
//! caller is its own test -- but it is part of the public API surface, so a
//! silent drift would be a breaking change for any downstream user). Most
//! `TermKind` arms have no scalar field interleaved between their children,
//! so their children can simply be pushed onto the stack in reverse order (a
//! plain LIFO stack naturally reproduces left-to-right,
//! depth-first-complete-before-next-sibling recursion, exactly like
//! `traversal::traverse`). Exactly two arms -- `Let` and `Match` -- interleave
//! a scalar hash *between* children (a binding's name before its value, with
//! the next binding's name only hashed after the previous value's entire
//! subtree has been hashed; similarly a case's constructor/bindings before
//! its body, with the next case starting only after this one's body is done).
//! Those two need a resumable continuation ([`HashTask::LetBindings`] /
//! [`HashTask::MatchCases`]) that re-pushes itself with an advanced index
//! each time, so the interleaved scalar hash lands at the right point in the
//! byte stream.

use crate::ast::term::MatchCase;
use crate::ast::{TermId, TermKind, TermManager};
use crate::interner::Spur;
#[allow(unused_imports)]
use crate::prelude::*;
use core::hash::{BuildHasher, BuildHasherDefault, Hash, Hasher};
use rustc_hash::FxHasher;
use smallvec::SmallVec;

/// One pending step of the iterative structural-hash walk.
///
/// `Visit` is the ordinary case (mirrors one call to the old
/// `structural_hash_impl`). `LetBindings` / `MatchCases` are resumable
/// continuations for the two kinds whose hash sequence interleaves a scalar
/// field between children -- see the module docs for why they need this and
/// nothing else does.
enum HashTask {
    /// Hash this term (respecting DAG sharing): the ordinary case.
    Visit(TermId),
    /// Resume a `Let`'s binding loop. `index` names the next binding whose
    /// name/value pair has not yet been hashed; once `index == bindings.len()`
    /// only `body` remains.
    LetBindings {
        bindings: SmallVec<[(Spur, TermId); 2]>,
        index: usize,
        body: TermId,
    },
    /// Resume a `Match`'s case loop. `index` names the next case whose
    /// constructor/bindings/body have not yet been hashed.
    MatchCases {
        cases: SmallVec<[MatchCase; 4]>,
        index: usize,
    },
}

/// Compute a hash value for a term structure (not just the ID)
///
/// This is useful for structural equality checks and caching
#[must_use]
pub fn structural_hash(term_id: TermId, manager: &TermManager) -> u64 {
    let mut hasher = BuildHasherDefault::<FxHasher>::default().build_hasher();
    let mut visited: FxHashSet<TermId> = FxHashSet::default();
    let mut stack: Vec<HashTask> = vec![HashTask::Visit(term_id)];

    while let Some(task) = stack.pop() {
        match task {
            HashTask::Visit(id) => hash_visit(id, manager, &mut hasher, &mut visited, &mut stack),
            HashTask::LetBindings {
                bindings,
                index,
                body,
            } => hash_let_step(bindings, index, body, &mut hasher, &mut stack),
            HashTask::MatchCases { cases, index } => {
                hash_match_step(cases, index, &mut hasher, &mut stack)
            }
        }
    }

    hasher.finish()
}

/// Hash one term node, pushing whatever further [`HashTask`]s are needed to
/// hash its children in exactly the order the original recursion did.
fn hash_visit(
    id: TermId,
    manager: &TermManager,
    hasher: &mut FxHasher,
    visited: &mut FxHashSet<TermId>,
    stack: &mut Vec<HashTask>,
) {
    if !visited.insert(id) {
        // For DAG sharing, just hash the ID (matches the original's
        // `if visited.contains(&term_id) { term_id.hash(hasher); return; }`).
        id.hash(hasher);
        return;
    }

    let Some(term) = manager.get(id) else {
        // A dangling id contributes nothing (matches the original, which
        // only ever hashes anything inside `if let Some(term) = ... { }`
        // with no `else` arm).
        return;
    };

    core::mem::discriminant(&term.kind).hash(hasher);

    match &term.kind {
        TermKind::True | TermKind::False => {}
        TermKind::IntConst(n) => n.hash(hasher),
        TermKind::RealConst(r) => {
            r.numer().hash(hasher);
            r.denom().hash(hasher);
        }
        TermKind::BitVecConst { value, width } => {
            value.hash(hasher);
            width.hash(hasher);
        }
        TermKind::StringLit(s) => s.hash(hasher),
        TermKind::Var(spur) => spur.hash(hasher),

        TermKind::Not(a)
        | TermKind::Neg(a)
        | TermKind::BvNot(a)
        | TermKind::StrLen(a)
        | TermKind::StrToInt(a)
        | TermKind::IntToStr(a)
        | TermKind::StrToCode(a)
        | TermKind::StrFromCode(a) => stack.push(HashTask::Visit(*a)),

        TermKind::BvExtract { high, low, arg } => {
            high.hash(hasher);
            low.hash(hasher);
            stack.push(HashTask::Visit(*arg));
        }

        TermKind::And(args)
        | TermKind::Or(args)
        | TermKind::Add(args)
        | TermKind::Mul(args)
        | TermKind::Distinct(args) => {
            args.len().hash(hasher);
            for &arg in args.iter().rev() {
                stack.push(HashTask::Visit(arg));
            }
        }

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
        | TermKind::StrLe(a, b) => {
            // Original hashes `a` fully, then `b`: push in reverse so `a`
            // pops first.
            stack.push(HashTask::Visit(*b));
            stack.push(HashTask::Visit(*a));
        }

        TermKind::Ite(c, t, e)
        | TermKind::Store(c, t, e)
        | TermKind::StrSubstr(c, t, e)
        | TermKind::StrIndexOf(c, t, e)
        | TermKind::StrReplace(c, t, e)
        | TermKind::StrReplaceAll(c, t, e)
        | TermKind::StrReplaceRe(c, t, e)
        | TermKind::StrReplaceReAll(c, t, e) => {
            stack.push(HashTask::Visit(*e));
            stack.push(HashTask::Visit(*t));
            stack.push(HashTask::Visit(*c));
        }

        TermKind::Apply { func, args } => {
            func.hash(hasher);
            args.len().hash(hasher);
            for &arg in args.iter().rev() {
                stack.push(HashTask::Visit(arg));
            }
        }

        TermKind::Forall { vars, body, .. } | TermKind::Exists { vars, body, .. } => {
            vars.len().hash(hasher);
            for (var, sort) in vars {
                var.hash(hasher);
                sort.hash(hasher);
            }
            stack.push(HashTask::Visit(*body));
        }

        TermKind::Let { bindings, body } => {
            bindings.len().hash(hasher);
            stack.push(HashTask::LetBindings {
                bindings: bindings.clone(),
                index: 0,
                body: *body,
            });
        }

        // Floating-point literals and constants
        TermKind::FpLit {
            sign,
            exp,
            sig,
            eb,
            sb,
        } => {
            sign.hash(hasher);
            exp.hash(hasher);
            sig.hash(hasher);
            eb.hash(hasher);
            sb.hash(hasher);
        }
        TermKind::FpPlusInfinity { eb, sb }
        | TermKind::FpMinusInfinity { eb, sb }
        | TermKind::FpPlusZero { eb, sb }
        | TermKind::FpMinusZero { eb, sb }
        | TermKind::FpNaN { eb, sb } => {
            eb.hash(hasher);
            sb.hash(hasher);
        }

        // Unary FP operations
        TermKind::FpAbs(a)
        | TermKind::FpNeg(a)
        | TermKind::FpIsNormal(a)
        | TermKind::FpIsSubnormal(a)
        | TermKind::FpIsZero(a)
        | TermKind::FpIsInfinite(a)
        | TermKind::FpIsNaN(a)
        | TermKind::FpIsNegative(a)
        | TermKind::FpIsPositive(a)
        | TermKind::FpToReal(a) => stack.push(HashTask::Visit(*a)),

        TermKind::FpSqrt(rm, a) | TermKind::FpRoundToIntegral(rm, a) => {
            rm.hash(hasher);
            stack.push(HashTask::Visit(*a));
        }

        // Binary FP operations
        TermKind::FpRem(a, b)
        | TermKind::FpMin(a, b)
        | TermKind::FpMax(a, b)
        | TermKind::FpLeq(a, b)
        | TermKind::FpLt(a, b)
        | TermKind::FpGeq(a, b)
        | TermKind::FpGt(a, b)
        | TermKind::FpEq(a, b) => {
            stack.push(HashTask::Visit(*b));
            stack.push(HashTask::Visit(*a));
        }

        TermKind::FpAdd(rm, a, b)
        | TermKind::FpSub(rm, a, b)
        | TermKind::FpMul(rm, a, b)
        | TermKind::FpDiv(rm, a, b) => {
            rm.hash(hasher);
            stack.push(HashTask::Visit(*b));
            stack.push(HashTask::Visit(*a));
        }

        // Ternary FP operations
        TermKind::FpFma(rm, a, b, c) => {
            rm.hash(hasher);
            stack.push(HashTask::Visit(*c));
            stack.push(HashTask::Visit(*b));
            stack.push(HashTask::Visit(*a));
        }

        // FP conversions
        TermKind::FpToFp { rm, arg, eb, sb } => {
            rm.hash(hasher);
            eb.hash(hasher);
            sb.hash(hasher);
            stack.push(HashTask::Visit(*arg));
        }
        TermKind::FpToSBV { rm, arg, width } | TermKind::FpToUBV { rm, arg, width } => {
            rm.hash(hasher);
            width.hash(hasher);
            stack.push(HashTask::Visit(*arg));
        }
        TermKind::RealToFp { rm, arg, eb, sb }
        | TermKind::SBVToFp { rm, arg, eb, sb }
        | TermKind::UBVToFp { rm, arg, eb, sb } => {
            rm.hash(hasher);
            eb.hash(hasher);
            sb.hash(hasher);
            stack.push(HashTask::Visit(*arg));
        }

        // Algebraic datatypes
        TermKind::DtConstructor { constructor, args } => {
            constructor.hash(hasher);
            args.len().hash(hasher);
            for &arg in args.iter().rev() {
                stack.push(HashTask::Visit(arg));
            }
        }
        TermKind::DtTester { constructor, arg } => {
            constructor.hash(hasher);
            stack.push(HashTask::Visit(*arg));
        }
        TermKind::DtSelector { selector, arg } => {
            selector.hash(hasher);
            stack.push(HashTask::Visit(*arg));
        }

        // Match expressions
        TermKind::Match { scrutinee, cases } => {
            // Original hashes the scrutinee's *entire* subtree before even
            // hashing `cases.len()`, so the `MatchCases` continuation (which
            // performs that `cases.len()` hash on its first resume) must sit
            // *below* the scrutinee's `Visit` on the stack.
            stack.push(HashTask::MatchCases {
                cases: cases.clone(),
                index: 0,
            });
            stack.push(HashTask::Visit(*scrutinee));
        }
    }
}

/// Resume a `Let`'s binding loop: hash the next binding's name, then push a
/// task to hash its value, followed by a continuation for the remaining
/// bindings (or `body`, once none remain).
fn hash_let_step(
    bindings: SmallVec<[(Spur, TermId); 2]>,
    index: usize,
    body: TermId,
    hasher: &mut FxHasher,
    stack: &mut Vec<HashTask>,
) {
    let Some(&(name, value)) = bindings.get(index) else {
        // All bindings hashed; only `body` remains, matching the original's
        // `structural_hash_impl(*body, ...)` after the bindings loop.
        stack.push(HashTask::Visit(body));
        return;
    };

    name.hash(hasher);
    let next_index = index + 1;
    stack.push(HashTask::LetBindings {
        bindings,
        index: next_index,
        body,
    });
    stack.push(HashTask::Visit(value));
}

/// Resume a `Match`'s case loop: on the first call, hash `cases.len()`
/// (mirroring the original's placement of that hash immediately after the
/// scrutinee); then hash the next case's constructor/bindings and push a
/// task for its body, followed by a continuation for the remaining cases.
fn hash_match_step(
    cases: SmallVec<[MatchCase; 4]>,
    index: usize,
    hasher: &mut FxHasher,
    stack: &mut Vec<HashTask>,
) {
    if index == 0 {
        cases.len().hash(hasher);
    }

    let Some(case) = cases.get(index) else {
        // All cases hashed; nothing follows a `Match` (matches the original,
        // which has no statement after the `for case in cases` loop).
        return;
    };

    case.constructor.hash(hasher);
    case.bindings.len().hash(hasher);
    for binding in &case.bindings {
        binding.hash(hasher);
    }
    let body = case.body;
    let next_index = index + 1;
    stack.push(HashTask::MatchCases {
        cases,
        index: next_index,
    });
    stack.push(HashTask::Visit(body));
}
