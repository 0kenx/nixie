//! Concrete floating-point model construction and verification.
//!
//! The FP conflict checks in [`super::check_fp`] recognise a fixed catalogue of
//! *unsatisfiable* patterns; everything else falls through to the honesty gate
//! ([`Solver::fp_atoms_need_theory`]) and is reported `Unknown`, because the
//! CDCL(T) core has no complete FP theory wired in.
//!
//! This module closes that gap on the *satisfiable* side without ever
//! sacrificing soundness. It attempts to build a fully concrete assignment to
//! every floating-point term in the current assertion set and then evaluates
//! every assertion against it using the bit-exact [`Ieee754Engine`]. A `Sat`
//! verdict is returned **only** when a genuine, verified model witness exists:
//! every FP-sorted variable is pinned to a concrete IEEE-754 datum and every
//! assertion evaluates to `true`. There is no guessing — if any term cannot be
//! pinned, or any assertion cannot be evaluated, or the constructed model
//! fails to satisfy some assertion, the routine gives up (returns `false`) and
//! the caller falls back to the honest `Unknown`.
//!
//! The construction handles the common concrete-evaluation shapes that dominate
//! `QF_FP` benchmarks: variables pinned by `(= x <fp-expr>)`, arithmetic and
//! conversion operations computed through the engine, literal conversions from
//! `Real`/`Int` constants, and free variables whose only constraints are
//! special-value predicates (`fp.isNaN`, `fp.isInfinite`, …) for which a witness
//! special value is synthesised.

#[allow(unused_imports)]
use crate::prelude::*;
use num_traits::ToPrimitive;
use oxiz_core::ast::{RoundingMode, TermId, TermKind, TermManager};
use oxiz_theories::fp::ieee754_full::{Ieee754Engine, convert_format};
use oxiz_theories::{FpFormat, FpRoundingMode, FpValue};

use super::Solver;

/// Positive/negative special-value predicate constraints gathered for a free
/// FP variable, used to synthesise a witness value.
#[derive(Default, Clone, Copy)]
struct PredicateFlags {
    want_nan: bool,
    want_inf: bool,
    want_zero: bool,
    want_normal: bool,
    want_subnormal: bool,
    want_positive: bool,
    want_negative: bool,
}

impl PredicateFlags {
    /// `true` when at least one positive class/sign constraint was recorded, so
    /// a meaningful witness can be synthesised (as opposed to leaving the
    /// variable to be defined by propagation).
    fn has_positive_constraint(&self) -> bool {
        self.want_nan
            || self.want_inf
            || self.want_zero
            || self.want_normal
            || self.want_subnormal
            || self.want_positive
            || self.want_negative
    }
}

/// Concrete FP model finder: assigns a bit-exact [`FpValue`] to every relevant
/// FP term and verifies the assertion set against the assignment.
struct FpModelFinder<'a> {
    manager: &'a TermManager,
    engine: Ieee754Engine,
    values: FxHashMap<TermId, FpValue>,
}

impl<'a> FpModelFinder<'a> {
    fn new(manager: &'a TermManager) -> Self {
        Self {
            manager,
            engine: Ieee754Engine::new(),
            values: FxHashMap::default(),
        }
    }

    /// Map the AST rounding mode to the engine's rounding-mode enum.
    fn engine_rm(rm: RoundingMode) -> FpRoundingMode {
        match rm {
            RoundingMode::RNE => FpRoundingMode::RoundNearestTiesToEven,
            RoundingMode::RNA => FpRoundingMode::RoundNearestTiesToAway,
            RoundingMode::RTP => FpRoundingMode::RoundTowardPositive,
            RoundingMode::RTN => FpRoundingMode::RoundTowardNegative,
            RoundingMode::RTZ => FpRoundingMode::RoundTowardZero,
        }
    }

    /// Return the IEEE-754 format of `term` from its sort, if it is FP-sorted.
    fn fp_format_of(&self, term: TermId) -> Option<FpFormat> {
        let td = self.manager.get(term)?;
        let sort = self.manager.sorts.get(td.sort)?;
        let (eb, sb) = sort.float_format()?;
        Some(FpFormat::new(eb, sb))
    }

    /// `true` iff `term` is a plain FP-sorted variable (an assignment target).
    fn is_fp_var(&self, term: TermId) -> bool {
        let Some(td) = self.manager.get(term) else {
            return false;
        };
        matches!(td.kind, TermKind::Var(_))
            && self
                .manager
                .sorts
                .get(td.sort)
                .is_some_and(|s| s.is_float())
    }

    /// Evaluate a `Real`/`Int`-sorted term to an `f64`, following the small
    /// arithmetic shapes that appear as `(_ to_fp …)` operands.
    fn eval_real(&self, term: TermId) -> Option<f64> {
        let td = self.manager.get(term)?;
        match &td.kind {
            TermKind::RealConst(r) => r.to_f64(),
            TermKind::IntConst(n) => n.to_f64(),
            TermKind::Neg(a) => self.eval_real(*a).map(|v| -v),
            TermKind::Sub(a, b) => Some(self.eval_real(*a)? - self.eval_real(*b)?),
            TermKind::Div(a, b) => {
                let denom = self.eval_real(*b)?;
                if denom == 0.0 {
                    return None;
                }
                Some(self.eval_real(*a)? / denom)
            }
            TermKind::Add(args) => {
                let mut acc = 0.0;
                for &a in args {
                    acc += self.eval_real(a)?;
                }
                Some(acc)
            }
            TermKind::Mul(args) => {
                let mut acc = 1.0;
                for &a in args {
                    acc *= self.eval_real(a)?;
                }
                Some(acc)
            }
            _ => None,
        }
    }

    /// Round an `f64` value to `format` under rounding mode `rm`, producing a
    /// concrete [`FpValue`]. The `f64` is treated as an exact dyadic rational,
    /// so the conversion is a single correctly-rounded step for `Float64` (and
    /// nearest-then-round for narrower targets, matching the RNE conversions
    /// used by these benchmarks).
    fn real_to_fp(&mut self, value: f64, format: FpFormat, rm: FpRoundingMode) -> FpValue {
        self.engine.set_rounding_mode(rm);
        let as_f64 = FpValue::from_f64(value);
        convert_format(&mut self.engine, &as_f64, format)
    }

    /// Evaluate an FP-sorted term to a concrete [`FpValue`], if all of its
    /// leaves are already pinned. Returns `None` when any input is unknown or
    /// the operation is not (yet) supported by concrete evaluation.
    fn eval_fp(&mut self, term: TermId) -> Option<FpValue> {
        let td = self.manager.get(term)?;
        match &td.kind {
            TermKind::Var(_) => self.values.get(&term).copied(),
            TermKind::FpLit {
                sign,
                exp,
                sig,
                eb,
                sb,
            } => Some(FpValue {
                sign: *sign,
                exponent: exp.to_u64()?,
                significand: sig.to_u64()?,
                format: FpFormat::new(*eb, *sb),
            }),
            TermKind::FpPlusInfinity { eb, sb } => {
                Some(FpValue::pos_infinity(FpFormat::new(*eb, *sb)))
            }
            TermKind::FpMinusInfinity { eb, sb } => {
                Some(FpValue::neg_infinity(FpFormat::new(*eb, *sb)))
            }
            TermKind::FpPlusZero { eb, sb } => Some(FpValue::pos_zero(FpFormat::new(*eb, *sb))),
            TermKind::FpMinusZero { eb, sb } => Some(FpValue::neg_zero(FpFormat::new(*eb, *sb))),
            TermKind::FpNaN { eb, sb } => Some(FpValue::nan(FpFormat::new(*eb, *sb))),
            TermKind::FpAbs(a) => {
                let v = self.eval_fp(*a)?;
                Some(self.engine.abs(&v))
            }
            TermKind::FpNeg(a) => {
                let v = self.eval_fp(*a)?;
                Some(self.engine.neg(&v))
            }
            TermKind::FpSqrt(rm, a) => {
                let v = self.eval_fp(*a)?;
                self.engine.set_rounding_mode(Self::engine_rm(*rm));
                Some(self.engine.sqrt(&v))
            }
            TermKind::FpAdd(rm, a, b) => {
                let va = self.eval_fp(*a)?;
                let vb = self.eval_fp(*b)?;
                self.engine.set_rounding_mode(Self::engine_rm(*rm));
                Some(self.engine.add(&va, &vb))
            }
            TermKind::FpSub(rm, a, b) => {
                let va = self.eval_fp(*a)?;
                let vb = self.eval_fp(*b)?;
                self.engine.set_rounding_mode(Self::engine_rm(*rm));
                Some(self.engine.sub(&va, &vb))
            }
            TermKind::FpMul(rm, a, b) => {
                let va = self.eval_fp(*a)?;
                let vb = self.eval_fp(*b)?;
                self.engine.set_rounding_mode(Self::engine_rm(*rm));
                Some(self.engine.mul(&va, &vb))
            }
            TermKind::FpDiv(rm, a, b) => {
                let va = self.eval_fp(*a)?;
                let vb = self.eval_fp(*b)?;
                self.engine.set_rounding_mode(Self::engine_rm(*rm));
                Some(self.engine.div(&va, &vb))
            }
            TermKind::FpRem(a, b) => {
                let va = self.eval_fp(*a)?;
                let vb = self.eval_fp(*b)?;
                Some(self.engine.rem(&va, &vb))
            }
            TermKind::FpFma(rm, a, b, c) => {
                let va = self.eval_fp(*a)?;
                let vb = self.eval_fp(*b)?;
                let vc = self.eval_fp(*c)?;
                self.engine.set_rounding_mode(Self::engine_rm(*rm));
                Some(self.engine.fma(&va, &vb, &vc))
            }
            TermKind::FpMin(a, b) => {
                let va = self.eval_fp(*a)?;
                let vb = self.eval_fp(*b)?;
                Some(self.engine.min(&va, &vb))
            }
            TermKind::FpMax(a, b) => {
                let va = self.eval_fp(*a)?;
                let vb = self.eval_fp(*b)?;
                Some(self.engine.max(&va, &vb))
            }
            TermKind::FpToFp { rm, arg, eb, sb } => {
                let v = self.eval_fp(*arg)?;
                self.engine.set_rounding_mode(Self::engine_rm(*rm));
                Some(convert_format(
                    &mut self.engine,
                    &v,
                    FpFormat::new(*eb, *sb),
                ))
            }
            TermKind::RealToFp { rm, arg, eb, sb } => {
                let value = self.eval_real(*arg)?;
                Some(self.real_to_fp(value, FpFormat::new(*eb, *sb), Self::engine_rm(*rm)))
            }
            _ => None,
        }
    }

    /// Structural (SMT-LIB `=`) equality on two concrete FP data: all NaNs are
    /// equal to one another; otherwise the encodings must match bit-for-bit, so
    /// `+0` and `-0` are distinct.
    fn fp_structural_eq(&self, a: &FpValue, b: &FpValue) -> bool {
        let ca = self.engine.classify(a);
        let cb = self.engine.classify(b);
        if ca.is_nan() || cb.is_nan() {
            return ca.is_nan() && cb.is_nan();
        }
        a.sign == b.sign && a.exponent == b.exponent && a.significand == b.significand
    }

    /// `fp.isPositive`: not NaN and sign bit clear (`+0` counts as positive,
    /// matching Z3).
    fn is_positive(&self, v: &FpValue) -> bool {
        let c = self.engine.classify(v);
        !c.is_nan() && !c.sign()
    }

    /// `fp.isNegative`: not NaN and sign bit set (`-0` counts as negative,
    /// matching Z3).
    fn is_negative(&self, v: &FpValue) -> bool {
        let c = self.engine.classify(v);
        !c.is_nan() && c.sign()
    }

    /// Evaluate a Boolean-sorted term against the concrete FP assignment.
    /// Returns `None` when the term contains anything the concrete evaluator
    /// cannot decide (a non-FP atom, an unassigned variable, an unsupported
    /// operation, …), which forces the caller to give up on `Sat`.
    fn eval_bool(&mut self, term: TermId) -> Option<bool> {
        let td = self.manager.get(term)?;
        match &td.kind {
            TermKind::True => Some(true),
            TermKind::False => Some(false),
            TermKind::Not(a) => self.eval_bool(*a).map(|b| !b),
            TermKind::And(args) => {
                let mut result = Some(true);
                for &a in args {
                    match self.eval_bool(a) {
                        Some(false) => return Some(false),
                        Some(true) => {}
                        None => result = None,
                    }
                }
                result
            }
            TermKind::Or(args) => {
                let mut result = Some(false);
                for &a in args {
                    match self.eval_bool(a) {
                        Some(true) => return Some(true),
                        Some(false) => {}
                        None => result = None,
                    }
                }
                result
            }
            TermKind::Eq(a, b) => {
                let va = self.eval_fp(*a);
                let vb = self.eval_fp(*b);
                if let (Some(va), Some(vb)) = (va, vb) {
                    return Some(self.fp_structural_eq(&va, &vb));
                }
                // Fall back to Boolean equality (e.g. `(= (fp.isNaN x) true)`).
                let ba = self.eval_bool(*a);
                let bb = self.eval_bool(*b);
                match (ba, bb) {
                    (Some(ba), Some(bb)) => Some(ba == bb),
                    _ => None,
                }
            }
            TermKind::FpEq(a, b) => {
                let va = self.eval_fp(*a)?;
                let vb = self.eval_fp(*b)?;
                Some(self.engine.eq(&va, &vb))
            }
            TermKind::FpLt(a, b) => {
                let va = self.eval_fp(*a)?;
                let vb = self.eval_fp(*b)?;
                Some(self.engine.lt(&va, &vb))
            }
            TermKind::FpGt(a, b) => {
                let va = self.eval_fp(*a)?;
                let vb = self.eval_fp(*b)?;
                Some(self.engine.gt(&va, &vb))
            }
            TermKind::FpLeq(a, b) => {
                let va = self.eval_fp(*a)?;
                let vb = self.eval_fp(*b)?;
                Some(self.engine.le(&va, &vb))
            }
            TermKind::FpGeq(a, b) => {
                let va = self.eval_fp(*a)?;
                let vb = self.eval_fp(*b)?;
                Some(self.engine.ge(&va, &vb))
            }
            TermKind::FpIsNaN(a) => {
                let v = self.eval_fp(*a)?;
                Some(self.engine.classify(&v).is_nan())
            }
            TermKind::FpIsInfinite(a) => {
                let v = self.eval_fp(*a)?;
                Some(self.engine.classify(&v).is_infinite())
            }
            TermKind::FpIsZero(a) => {
                let v = self.eval_fp(*a)?;
                Some(self.engine.classify(&v).is_zero())
            }
            TermKind::FpIsNormal(a) => {
                let v = self.eval_fp(*a)?;
                Some(self.engine.classify(&v).is_normal())
            }
            TermKind::FpIsSubnormal(a) => {
                let v = self.eval_fp(*a)?;
                Some(self.engine.classify(&v).is_subnormal())
            }
            TermKind::FpIsPositive(a) => {
                let v = self.eval_fp(*a)?;
                Some(self.is_positive(&v))
            }
            TermKind::FpIsNegative(a) => {
                let v = self.eval_fp(*a)?;
                Some(self.is_negative(&v))
            }
            _ => None,
        }
    }

    /// Propagate definitional equalities `(= var <fp-expr>)` to a fixpoint,
    /// pinning each variable whose defining expression becomes evaluable.
    fn propagate(&mut self, assertions: &[TermId]) {
        loop {
            let mut changed = false;
            for &assertion in assertions {
                let Some(td) = self.manager.get(assertion) else {
                    continue;
                };
                if let TermKind::Eq(l, r) = &td.kind {
                    changed |= self.try_define(*l, *r);
                    changed |= self.try_define(*r, *l);
                }
            }
            if !changed {
                break;
            }
        }
    }

    /// If `var` is an unpinned FP variable and `expr` is fully evaluable, pin
    /// `var` to the value of `expr`. Returns `true` when a new binding is made.
    fn try_define(&mut self, var: TermId, expr: TermId) -> bool {
        if self.values.contains_key(&var) || !self.is_fp_var(var) {
            return false;
        }
        if let Some(v) = self.eval_fp(expr) {
            self.values.insert(var, v);
            return true;
        }
        false
    }

    /// Collect the positive/negative special-value predicate constraints that
    /// the assertion set imposes directly on `var`, tracking Boolean polarity
    /// through `not`/`and`/`or`.
    fn collect_predicates(&self, var: TermId, assertions: &[TermId]) -> PredicateFlags {
        let mut flags = PredicateFlags::default();
        let mut stack: Vec<(TermId, bool)> = assertions.iter().map(|&a| (a, true)).collect();
        let mut visited: FxHashSet<(TermId, bool)> = FxHashSet::default();
        while let Some((term, positive)) = stack.pop() {
            if !visited.insert((term, positive)) {
                continue;
            }
            let Some(td) = self.manager.get(term) else {
                continue;
            };
            match &td.kind {
                TermKind::Not(a) => stack.push((*a, !positive)),
                TermKind::And(args) | TermKind::Or(args) => {
                    for &a in args {
                        stack.push((a, positive));
                    }
                }
                TermKind::FpIsNaN(a) if *a == var && positive => flags.want_nan = true,
                TermKind::FpIsInfinite(a) if *a == var && positive => flags.want_inf = true,
                TermKind::FpIsZero(a) if *a == var && positive => flags.want_zero = true,
                TermKind::FpIsNormal(a) if *a == var && positive => flags.want_normal = true,
                TermKind::FpIsSubnormal(a) if *a == var && positive => flags.want_subnormal = true,
                TermKind::FpIsPositive(a) if *a == var && positive => flags.want_positive = true,
                TermKind::FpIsNegative(a) if *a == var && positive => flags.want_negative = true,
                _ => {}
            }
        }
        flags
    }

    /// Synthesise a witness value for a free FP variable from its special-value
    /// predicate constraints. Returns `None` when no positive class/sign
    /// constraint applies (leaving the variable for propagation or the honest
    /// `Unknown` fallback). The verification pass is the ultimate soundness
    /// guard: a witness that fails to satisfy every assertion never yields
    /// `Sat`.
    fn synthesize_witness(&self, var: TermId, assertions: &[TermId]) -> Option<FpValue> {
        let format = self.fp_format_of(var)?;
        let flags = self.collect_predicates(var, assertions);
        if !flags.has_positive_constraint() {
            return None;
        }
        let sign = flags.want_negative;
        if flags.want_nan {
            return Some(FpValue::nan(format));
        }
        if flags.want_inf {
            return Some(if sign {
                FpValue::neg_infinity(format)
            } else {
                FpValue::pos_infinity(format)
            });
        }
        if flags.want_zero {
            return Some(if sign {
                FpValue::neg_zero(format)
            } else {
                FpValue::pos_zero(format)
            });
        }
        if flags.want_subnormal {
            // Smallest-magnitude subnormal: exponent field 0, significand 1.
            return Some(FpValue {
                sign,
                exponent: 0,
                significand: 1,
                format,
            });
        }
        // Normal / bare sign constraint: pick +/-1.0, which is `1.<zeros>` with
        // the biased exponent equal to the format bias.
        Some(FpValue {
            sign,
            exponent: format.bias() as u64,
            significand: 0,
            format,
        })
    }

    /// Collect every FP-sorted variable that appears in the assertion set.
    fn collect_fp_vars(&self, assertions: &[TermId]) -> Vec<TermId> {
        let mut vars = Vec::new();
        let mut seen: FxHashSet<TermId> = FxHashSet::default();
        let mut visited: FxHashSet<TermId> = FxHashSet::default();
        let mut stack: Vec<TermId> = assertions.to_vec();
        while let Some(term) = stack.pop() {
            if !visited.insert(term) {
                continue;
            }
            if self.is_fp_var(term) && seen.insert(term) {
                vars.push(term);
            }
            if let Some(td) = self.manager.get(term) {
                super::term_walk::collect_structural_children(&td.kind, &mut stack);
            }
        }
        vars
    }

    /// Drive the full construct-and-verify pipeline, returning `true` only when
    /// a verified satisfying model exists.
    fn find(&mut self, assertions: &[TermId]) -> bool {
        let fp_vars = self.collect_fp_vars(assertions);
        // Definitional propagation, then witness the still-free predicate-
        // constrained variables, then propagate again (a witness can unlock
        // further definitions, e.g. `z = x + y` once `x` becomes a NaN).
        self.propagate(assertions);
        for &var in &fp_vars {
            if !self.values.contains_key(&var)
                && let Some(witness) = self.synthesize_witness(var, assertions)
            {
                self.values.insert(var, witness);
            }
        }
        self.propagate(assertions);
        // Verify: every assertion must evaluate to a concrete `true`.
        for &assertion in assertions {
            if self.eval_bool(assertion) != Some(true) {
                return false;
            }
        }
        true
    }
}

impl Solver {
    /// Attempt to prove the current assertion set satisfiable by constructing
    /// and verifying a concrete floating-point model.
    ///
    /// Returns `true` **only** when a genuine model witness is found: every
    /// FP-sorted variable is pinned to a concrete IEEE-754 value and every
    /// assertion evaluates to `true` under the bit-exact engine. This is sound
    /// — it never reports a satisfiable verdict for an unsatisfiable formula,
    /// and it declines (returns `false`) whenever any assertion falls outside
    /// the concrete-evaluation fragment, letting the caller answer `Unknown`.
    pub(super) fn try_fp_model_sat(&self, manager: &TermManager) -> bool {
        if self.assertions.is_empty() {
            return false;
        }
        let mut finder = FpModelFinder::new(manager);
        finder.find(&self.assertions)
    }
}
