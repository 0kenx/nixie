//! [`alpha_equivalent`]: term comparison up to renaming of bound variables.
//!
//! Structurally this mirrors `structural.rs` exactly -- same outer-match-on-
//! `lt.kind`-with-no-wildcard discipline, same `core::mem::discriminant`
//! guard on every grouped arm, same shared [`super::shape`] helpers for
//! extracting a same-shaped payload back out of `rt.kind` -- so see that
//! file's module docs for why the match is shaped this way. The differences
//! are confined to exactly the places alpha-equivalence itself differs from
//! plain structural equality: the `Var` arm consults [`AlphaEnv`] instead of
//! comparing raw names, and the four binder kinds (`Forall`/`Exists`/`Let`/
//! `Match`) *populate* that environment before descending into whatever they
//! scope, instead of requiring an exact name match.
//!
//! ## The bound-variable correspondence: what was broken, and the fix
//!
//! Before this fix, `alpha_equivalent` built an `env` map, cloned it down the
//! walk exactly as documented below, and **never inserted anything into it**:
//! no binder arm ever recorded a `lhs_name -> rhs_name` correspondence, so the
//! `Var` arm's lookup always missed and fell back to comparing raw `TermId`s
//! -- which, having already failed the `l == r` fast path to even reach this
//! point, was always `false`. The function's own doc example --
//! `(forall ((x Int)) (> x 0))` vs `(forall ((y Int)) (> y 0))` -- therefore
//! returned `false`, contrary to what "alpha-equivalent" means. [`AlphaEnv`]
//! is the fix: every binder arm now inserts its bound-variable correspondence
//! into a scoped copy of the environment before pushing whatever it scopes,
//! and the `Var` arm consults it.
//!
//! ## Why the environment is keyed by `Spur`, not `TermId`
//!
//! A `Forall`/`Exists`'s `vars: SmallVec<[(Spur, SortId); 2]>` gives a bound
//! variable's *name* and *sort* directly, but not the `TermId` of its
//! occurrences inside `body` -- getting that would mean asking `TermManager`
//! to look up (or, worse, intern) a `Var(name, sort)` term, which needs
//! `&mut TermManager` and this function only has `&TermManager`. It also
//! isn't needed: sort-correctness for *every* pair popped off the stack,
//! `Var` occurrences included, is already guaranteed generically by this
//! function's `lt.sort != rt.sort => return false` check before the `match`
//! ever runs, so the environment only has to track *names*, and a bound
//! variable's name is available directly from `vars`/`bindings` without any
//! manager lookup at all.
//!
//! ## Why the correspondence must be checked in *both* directions
//!
//! `env.fwd` alone (`lhs_name -> rhs_name`) is not enough: nothing would stop
//! two *different* still-in-scope lhs names from both mapping to the same rhs
//! name (e.g. an outer binder's `x -> y` surviving, unshadowed, into an inner
//! binder that independently maps a fresh `q -> y` too), which would wrongly
//! let two distinct lhs variables both compare equal to the same rhs
//! variable. `AlphaEnv::corresponds` therefore also maintains `rev`
//! (`rhs_name -> lhs_name`) in lockstep and requires *both* directions to
//! agree. Concretely, this rejects e.g.
//! `(forall ((x Int)) (forall ((q Int)) (= x q)))` vs
//! `(forall ((y Int)) (forall ((y Int)) (= y y)))`: naively, both `x` and `q`
//! would appear to correspond to `y` (the inner `y` shadows the outer one on
//! the rhs but the lhs has two genuinely distinct names), but `rev.get(y)`
//! reflects only the *most recent* binder (`q -> y`), so checking `x`'s
//! occurrence against it correctly fails (`rev.get(y) == Some(q) != x`) --
//! see `tests.rs` for this exact case pinned as a regression test. Both
//! `fwd` and `rev` use `BTreeMap`, not `FxHashMap`: `BTreeMap::insert`
//! overwrites on a repeated key (exactly the "innermost binder wins"
//! shadowing semantics a fresh binder needs, with no extra bookkeeping), and
//! `BTreeMap<Spur, Spur>` implements `Hash` (unlike `HashMap`, whose
//! unordered iteration cannot be hashed deterministically) because it always
//! iterates in sorted-key order -- which is exactly what lets `AlphaEnv`
//! itself be used as part of the `visited` cycle-guard's key below.
//!
//! ## Why the `visited` cycle-guard must be keyed on the environment too
//!
//! The module docs one level up (`super`, i.e. `equality/mod.rs`) explain why
//! memoizing "this `(TermId, TermId)` pair already concluded equal" is sound
//! for `structurally_equal`, where the answer for a given pair of ids can
//! never depend on anything outside those two subtrees. That argument
//! **stops applying** here, because once `Var` consults `env`, the answer for
//! the very same `(l, r)` pair of ids can legitimately differ depending on
//! what correspondence is in scope when it is reached -- and hash-consing
//! means the identical `(l, r)` pair genuinely can recur under two different
//! environments in one call (a shared sub-DAG referenced from two sibling
//! binders that establish different correspondences). Concretely:
//!
//! ```text
//! lhs: (and (forall ((x Int)) (= x w)) (forall ((z Int)) (= x w)))
//! rhs: (and (forall ((p Int)) (= p w)) (forall ((q Int)) (= p w)))
//! ```
//!
//! The first conjuncts bind `x <-> p` and correctly compare `(= x w)` against
//! `(= p w)` as equal. The *second* conjuncts' bodies are `(= x w)` (lhs,
//! `x` free relative to the vacuous `z`-binder) and `(= p w)` (rhs, `p` free
//! relative to the vacuous `q`-binder) -- **the exact same `(TermId, TermId)`
//! pair as the first conjuncts' bodies**, since hash-consing gives identical
//! subterms identical ids. But here `x` and `p` are *not* in any binder's
//! scope (`z <-> q`'s correspondence doesn't relate to them at all), so `x`
//! and `p` must be compared as free variables and correctly found unequal
//! (different raw names). A `(TermId, TermId)`-only `visited` set would have
//! already marked this exact pair "equal" while processing the first
//! conjunct and would skip re-checking it here, making the whole call
//! wrongly return `true` for two formulas that are not alpha-equivalent (the
//! lhs depends on free variable `x`, the rhs on the unrelated free variable
//! `p`). `visited` here is therefore keyed on `(TermId, TermId, AlphaEnv)`,
//! not just the id pair, closing exactly this gap; see `tests.rs` for this
//! example pinned as a regression test that fails without the environment in
//! the key.

use super::shape;
use crate::ast::{TermId, TermKind, TermManager};
use crate::interner::Spur;
#[allow(unused_imports)]
use crate::prelude::*;

/// The bound-variable correspondence accumulated while descending through
/// binders on an `alpha_equivalent` walk. See the module docs above for why
/// both directions are tracked and why `BTreeMap` (not `FxHashMap`) is used.
#[derive(Debug, Clone, Default, PartialEq, Eq, Hash)]
struct AlphaEnv {
    /// lhs bound name -> rhs bound name, for every binder currently in scope.
    fwd: BTreeMap<Spur, Spur>,
    /// rhs bound name -> lhs bound name; kept in lockstep with `fwd`.
    rev: BTreeMap<Spur, Spur>,
}

impl AlphaEnv {
    /// Return a scoped copy of `self` extended with one binder's pairwise
    /// name correspondence (`lhs_names[i]` corresponds to `rhs_names[i]`).
    /// A name reused from an enclosing binder is simply overwritten --
    /// exactly the shadowing semantics a fresh, innermost binder needs.
    fn bind<'a>(&self, pairs: impl IntoIterator<Item = (&'a Spur, &'a Spur)>) -> Self {
        let mut scoped = self.clone();
        for (&l, &r) in pairs {
            scoped.fwd.insert(l, r);
            scoped.rev.insert(r, l);
        }
        scoped
    }

    /// Whether bound-variable-occurrence `lhs_name` (from the left term)
    /// should be treated as corresponding to `rhs_name` (from the right
    /// term) at this point in the walk. Requires agreement in *both*
    /// directions -- see the module docs above for why `fwd` alone is not
    /// enough to stay bijective. Two names that are each unmapped (free
    /// relative to every binder currently in scope) correspond only if they
    /// are literally the same name: alpha-renaming applies to bound
    /// variables only.
    fn corresponds(&self, lhs_name: Spur, rhs_name: Spur) -> bool {
        let fwd_ok = match self.fwd.get(&lhs_name) {
            Some(&mapped) => mapped == rhs_name,
            None => lhs_name == rhs_name,
        };
        let rev_ok = match self.rev.get(&rhs_name) {
            Some(&mapped) => mapped == lhs_name,
            None => lhs_name == rhs_name,
        };
        fwd_ok && rev_ok
    }
}

/// Check if two terms are alpha-equivalent (equal modulo consistent renaming
/// of bound variables).
///
/// Alpha equivalence is important for comparing quantified formulas and
/// let-bindings that may use different variable names but represent the same
/// logical structure.
///
/// # Examples
///
/// `(forall ((x Int)) (> x 0))` and `(forall ((y Int)) (> y 0))` are
/// alpha-equivalent even though they use different variable names (`x` vs
/// `y`).
#[must_use]
pub fn alpha_equivalent(lhs: TermId, rhs: TermId, manager: &TermManager) -> bool {
    let mut visited: FxHashSet<(TermId, TermId, AlphaEnv)> = FxHashSet::default();
    let mut stack: Vec<(TermId, TermId, AlphaEnv)> = vec![(lhs, rhs, AlphaEnv::default())];

    while let Some((l, r, env)) = stack.pop() {
        if l == r {
            continue;
        }
        // Keyed on the environment too -- see the module docs above for why
        // `(TermId, TermId)` alone is not a sound memoization key here.
        if !visited.insert((l, r, env.clone())) {
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

                    // The key case for alpha equivalence: consult the
                    // environment instead of comparing raw names.
                    TermKind::Var(a) => {
                        let TermKind::Var(b) = &rt.kind else {
                            return false;
                        };
                        if !env.corresponds(*a, *b) {
                            return false;
                        }
                    }

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
                        stack.push((*a, b, env.clone()));
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
                        stack.push((*a, b, env.clone()));
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
                        stack.push((*a1, *a2, env.clone()));
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
                        stack.push((*a, x, env.clone()));
                        stack.push((*b, y, env.clone()));
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
                        stack.push((*a, x, env.clone()));
                        stack.push((*b, y, env.clone()));
                    }

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
                        stack.push((*c, x, env.clone()));
                        stack.push((*t, y, env.clone()));
                        stack.push((*e, z, env.clone()));
                    }

                    TermKind::FpFma(rm1, a, b, c) => {
                        let TermKind::FpFma(rm2, x, y, z) = &rt.kind else {
                            return false;
                        };
                        if rm1 != rm2 {
                            return false;
                        }
                        stack.push((*a, *x, env.clone()));
                        stack.push((*b, *y, env.clone()));
                        stack.push((*c, *z, env.clone()));
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
                            stack.push((x, y, env.clone()));
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
                            stack.push((x, y, env.clone()));
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
                            stack.push((x, y, env.clone()));
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
                        stack.push((*a1, a2, env.clone()));
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
                        stack.push((*a1, a2, env.clone()));
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
                        stack.push((*a1, a2, env.clone()));
                    }

                    // Quantifiers: pair the two sides' bound variables
                    // positionally (after checking arity and, pairwise,
                    // sort) and record the correspondence in a scoped copy
                    // of `env` before descending into `body` -- this is the
                    // actual fix for alpha-equivalence recognition. Not
                    // recorded for `patterns` -- see the module docs in
                    // `mod.rs`.
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
                        if vars1.len() != vars2.len() {
                            return false;
                        }
                        if !vars1
                            .iter()
                            .zip(vars2.iter())
                            .all(|((_, s1), (_, s2))| s1 == s2)
                        {
                            return false;
                        }
                        let scoped_env = env.bind(
                            vars1
                                .iter()
                                .map(|(n, _)| n)
                                .zip(vars2.iter().map(|(n, _)| n)),
                        );
                        stack.push((*body1, body2, scoped_env));
                    }

                    // Let bindings: value expressions are evaluated in the
                    // *outer* scope (SMT-LIB `let` is parallel/
                    // non-recursive -- bindings cannot see each other or the
                    // names being introduced), so they are pushed with the
                    // unmodified `env`; only `body` gets the scoped copy
                    // with the new correspondence recorded.
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
                        for (&(_, v1), &(_, v2)) in b1.iter().zip(b2.iter()) {
                            stack.push((v1, v2, env.clone()));
                        }
                        let scoped_env =
                            env.bind(b1.iter().map(|(n, _)| n).zip(b2.iter().map(|(n, _)| n)));
                        stack.push((*body1, *body2, scoped_env));
                    }

                    // Match expressions: each case's pattern bindings are
                    // scoped to that case's own body only -- a fresh clone
                    // per case, never accumulated across cases, so one
                    // case's bindings cannot leak into a sibling case.
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
                        stack.push((*s1, *s2, env.clone()));
                        for (case1, case2) in c1.iter().zip(c2.iter()) {
                            if case1.constructor != case2.constructor
                                || case1.bindings.len() != case2.bindings.len()
                            {
                                return false;
                            }
                            let scoped_env =
                                env.bind(case1.bindings.iter().zip(case2.bindings.iter()));
                            stack.push((case1.body, case2.body, scoped_env));
                        }
                    }
                }
            }
            _ => return false,
        }
    }

    true
}
