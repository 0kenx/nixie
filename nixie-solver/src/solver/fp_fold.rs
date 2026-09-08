//! Floating-point constant folding through EUF class pins.
//!
//! The FP theory's *defining* lemma family: for every ground `fp.*`
//! application whose operands' equivalence classes are pinned to concrete
//! literals, the operation's value is a bit-exact function of those literals,
//! computable once by the [`Ieee754Engine`].  The pass emits each fold as a
//! **guarded ground clause**
//!
//! ```text
//! (a = lit1) ∧ (b = lit2) → (fp.op(rm, a, b) = fold(lit1, lit2))
//!
//! (a = lit1) ∧ (b = lit2) → fp.pred(rm, a, b)          when it evaluates true
//! ```
//!
//! which is an *unconditionally valid* theory lemma — it is the operation's
//! defining property at concrete operands — so the pass's soundness never
//! depends on the e-graph state that guided the choice of fold; the EUF pins
//! only decide *which* lemmas are worth emitting.  The guard of an operand is
//! always the single atom `(operand = literal)`, never the transitive
//! justification of the pin, which keeps every clause valid independently of
//! how the pin was found.
//!
//! Together with the bit-pattern value marks on FP literals (see
//! [`nixie_theories::euf::EufSolver::declare_fp_const`], wired into the
//! constant-interning leaf path) this closes the unsat direction that the
//! pattern conflict checks and the concrete model builder leave open:
//!
//! ```text
//! x = c1 ∧ y = (fp.add RNE x x) ∧ y = c2        with fold(c1, c1) ≠ c2
//! ```
//!
//! refutes by unit propagation alone: the fold clause forces
//! `fp.add = fold(c1, c1)`, the asserted equalities merge `y` with both the
//! folded literal and `c2`, and the two distinct bit patterns collide in one
//! e-graph class (a distinguished-value conflict).
//!
//! Evaluation is exact and total on the folded shapes — the engine is the
//! same bit-exact core the concrete model builder trusts — and any operand
//! that cannot be resolved to a literal (free variable, a `to_fp` from a
//! Real, a subnormal field wider than 64 bits, …) simply leaves the operation
//! unfolded: no fold, no clause, no verdict risk.  Chains
//! (`z = (fp.mul y y)` where `y = (fp.add x x)`) iterate to a fixpoint inside
//! the pass: a folded operation pins its term (and every EUF-equal alias of
//! it) with the folded value, so downstream operations fold against it.
//!
//! All quantities are capped ([`MAX_FP_FOLD_OPS`]); a cap tripping defers the
//! remaining folds to the next `check` — it never fabricates a partial fold.
//! `fp.roundToIntegral` is not folded (the engine has no exact
//! implementation); those operations stay with the pattern checks and the
//! model builder.

use crate::prelude::*;
use nixie_core::ast::{RoundingMode, TermId, TermKind, TermManager};
use nixie_theories::fp::ieee754_full::{Ieee754Engine, convert_format};
use nixie_theories::{FpFormat, FpRoundingMode, FpValue};
use num_bigint::BigInt;
use num_traits::ToPrimitive;
use smallvec::SmallVec;

use super::Solver;

/// Cap on distinct operations folded per pass.  A cap trip defers the
/// remaining folds to the next `check`; it never half-folds an operation.
const MAX_FP_FOLD_OPS: usize = 512;

/// The bit-pattern key of an [`FpValue`]: `(eb, sb, sign, biased exponent,
/// significand)`.  Two floats are `=` — datum identity, the SMT-LIB `=` on
/// Floats — exactly when this tuple is equal.
pub(super) type FpConstKey = (u32, u32, bool, u64, u64);

/// One resolved pin: an exact value, the literal term that carries it (the
/// guard atoms' right-hand side), and the guard atoms that force the pinned
/// term to that value in the theory.
#[derive(Clone)]
struct FpPin {
    value: FpValue,
    witness: TermId,
    guards: Vec<TermId>,
}

/// Decode an FP literal term into its exact [`FpValue`].  `None` for any
/// non-literal kind (or a sort that is not a float format): those terms are
/// not constants and pin nothing.
pub(super) fn fp_const_value(term: TermId, manager: &TermManager) -> Option<FpValue> {
    let td = manager.get(term)?;
    match &td.kind {
        TermKind::FpLit {
            sign,
            exp,
            sig,
            eb,
            sb,
        } => {
            let (eb, sb) = (*eb, *sb);
            let format = FpFormat::new(eb, sb);
            // Raw biased exponent / significand fields.  A field wider than
            // 64 bits cannot occur in a format the engine supports, but the
            // term graph is untrusted input: refuse rather than truncate.
            let exponent = exp.to_u64()?;
            let significand = sig.to_u64()?;
            // NaN canonicalization: SMT-LIB `=` on floats treats every NaN
            // of a format as ONE datum (z3: `(= nan1 nan2)` over different
            // payloads is `sat`), and the payload-less `(_ NaN e s)` literal
            // carries no sign — so every NaN bit pattern decodes to the
            // same canonical value.  Without this, two NaN spellings got
            // distinct value keys and their equality was refuted (false
            // `unsat`).
            let emax = (1u64 << eb) - 1;
            if exponent == emax && significand != 0 {
                return Some(FpValue {
                    sign: false,
                    exponent: emax,
                    significand: 1,
                    format,
                });
            }
            let _ = sign;
            Some(FpValue {
                sign: *sign,
                exponent,
                significand,
                format,
            })
        }
        TermKind::FpPlusZero { eb, sb } => Some(FpValue::pos_zero(FpFormat::new(*eb, *sb))),
        TermKind::FpMinusZero { eb, sb } => Some(FpValue::neg_zero(FpFormat::new(*eb, *sb))),
        TermKind::FpPlusInfinity { eb, sb } => Some(FpValue::pos_infinity(FpFormat::new(*eb, *sb))),
        TermKind::FpMinusInfinity { eb, sb } => {
            Some(FpValue::neg_infinity(FpFormat::new(*eb, *sb)))
        }
        TermKind::FpNaN { eb, sb } => {
            // The payload-less NaN literal decodes to the canonical NaN of
            // its format — the one datum every NaN bit pattern shares (see
            // the FpLit arm).  Sign false: the literal carries no sign bit,
            // and `fp.isNegative` of it is false in the reference solvers.
            let format = FpFormat::new(*eb, *sb);
            Some(FpValue {
                sign: false,
                exponent: (1u64 << *eb) - 1,
                significand: 1,
                format,
            })
        }
        _ => None,
    }
}

/// The bit-pattern key of a decoded value.  Every spelling of one datum —
/// `FpLit` with those bits, the dedicated zero/infinity/NaN kinds, a literal
/// minted by this pass — decodes to the same key.
pub(super) fn fp_const_key(value: &FpValue) -> FpConstKey {
    (
        value.format.exponent_bits,
        value.format.significand_bits,
        value.sign,
        value.exponent,
        value.significand,
    )
}

/// Mint (intern) the canonical `FpLit` term of an exact value.  The caller
/// marks it via [`Solver::mark_fp_const`] before its first intern so it is
/// born carrying the bit pattern's shared distinctness id.
fn mint_fp_lit(value: &FpValue, manager: &mut TermManager) -> TermId {
    manager.mk_fp_lit(
        value.sign,
        BigInt::from(value.exponent),
        BigInt::from(value.significand),
        value.format.exponent_bits,
        value.format.significand_bits,
    )
}

/// Which operation a collected term is, with its operand terms copied out so
/// the term-data borrow ends before operand resolution (which needs
/// `&mut TermManager` to mint guard atoms).
#[derive(Clone, Copy)]
enum FpOpShape {
    Binary(RoundingMode, TermId, TermId, BinOp),
    Fma(RoundingMode, TermId, TermId, TermId),
    Unary(TermId, UnOp),
    ToFp(RoundingMode, u32, u32, TermId),
    Pred(TermId, TermId, PredOp),
    Classify(TermId, ClassOp),
}

#[derive(Clone, Copy)]
enum BinOp {
    Add,
    Sub,
    Mul,
    Div,
    Rem,
    Min,
    Max,
    /// `FpSqrt(rm, a)` rides the Binary shape with both operand slots = `a`
    /// so the rounding mode travels with it; only `vals[0]` participates.
    Sqrt,
}

#[derive(Clone, Copy)]
enum UnOp {
    Abs,
    Neg,
}

#[derive(Clone, Copy)]
enum PredOp {
    Eq,
    Lt,
    Leq,
    Gt,
    Geq,
}

#[derive(Clone, Copy)]
enum ClassOp {
    IsNormal,
    IsSubnormal,
    IsZero,
    IsInfinite,
    IsNaN,
    IsNegative,
    IsPositive,
}

impl FpOpShape {
    /// The operand terms of this operation, in declaration order.
    fn operands(&self) -> SmallVec<[TermId; 3]> {
        match *self {
            Self::Binary(_, a, b, _) => smallvec::smallvec![a, b],
            Self::Fma(_, a, b, c) => smallvec::smallvec![a, b, c],
            Self::Unary(a, _) => smallvec::smallvec![a],
            Self::ToFp(_, _, _, a) => smallvec::smallvec![a],
            Self::Pred(a, b, _) => smallvec::smallvec![a, b],
            Self::Classify(a, _) => smallvec::smallvec![a],
        }
    }

    /// The exact value/truth of the operation at concrete operand values.
    fn evaluate(&self, engine: &mut Ieee754Engine, vals: &[FpValue]) -> FpValueOrBool {
        match *self {
            Self::Binary(rm, _, _, op) => {
                engine.set_rounding_mode(engine_rm(rm));
                let value = match op {
                    BinOp::Add => engine.add(&vals[0], &vals[1]),
                    BinOp::Sub => engine.sub(&vals[0], &vals[1]),
                    BinOp::Mul => engine.mul(&vals[0], &vals[1]),
                    BinOp::Div => engine.div(&vals[0], &vals[1]),
                    BinOp::Rem => engine.rem(&vals[0], &vals[1]),
                    BinOp::Min => engine.min(&vals[0], &vals[1]),
                    BinOp::Max => engine.max(&vals[0], &vals[1]),
                    BinOp::Sqrt => engine.sqrt(&vals[0]),
                };
                FpValueOrBool::Value(value)
            }
            Self::Fma(rm, _, _, _) => {
                engine.set_rounding_mode(engine_rm(rm));
                FpValueOrBool::Value(engine.fma(&vals[0], &vals[1], &vals[2]))
            }
            Self::Unary(_, op) => {
                let value = match op {
                    UnOp::Abs => engine.abs(&vals[0]),
                    UnOp::Neg => engine.neg(&vals[0]),
                };
                FpValueOrBool::Value(value)
            }
            Self::ToFp(rm, eb, sb, _) => {
                engine.set_rounding_mode(engine_rm(rm));
                FpValueOrBool::Value(convert_format(engine, &vals[0], FpFormat::new(eb, sb)))
            }
            Self::Pred(_, _, op) => {
                // IEEE-754 comparisons: every ordering predicate is false
                // when either operand is NaN, and `±0` compare equal.
                let b = match op {
                    PredOp::Eq => engine.eq(&vals[0], &vals[1]),
                    PredOp::Lt => engine.lt(&vals[0], &vals[1]),
                    PredOp::Leq => engine.eq(&vals[0], &vals[1]) || engine.lt(&vals[0], &vals[1]),
                    PredOp::Gt => engine.gt(&vals[0], &vals[1]),
                    PredOp::Geq => engine.eq(&vals[0], &vals[1]) || engine.gt(&vals[0], &vals[1]),
                };
                FpValueOrBool::Bool(b)
            }
            Self::Classify(_, op) => {
                let class = engine.classify(&vals[0]);
                use nixie_theories::fp::ieee754_full::FpClass;
                let sign = vals[0].sign;
                let b = match op {
                    ClassOp::IsNormal => {
                        matches!(class, FpClass::NegativeNormal | FpClass::PositiveNormal)
                    }
                    ClassOp::IsSubnormal => {
                        matches!(
                            class,
                            FpClass::NegativeSubnormal | FpClass::PositiveSubnormal
                        )
                    }
                    ClassOp::IsZero => {
                        matches!(class, FpClass::NegativeZero | FpClass::PositiveZero)
                    }
                    ClassOp::IsInfinite => class.is_infinite(),
                    ClassOp::IsNaN => class.is_nan(),
                    // The sign bit.  NaN decodes with the canonical sign
                    // `false` above, so `isNegative (NaN)` is false and
                    // `isPositive (NaN)` is true — the reference semantics of
                    // the payload-less `(_ NaN e s)` literal.
                    ClassOp::IsNegative => sign && !class.is_nan(),
                    ClassOp::IsPositive => !sign && !class.is_nan(),
                };
                FpValueOrBool::Bool(b)
            }
        }
    }
}

enum FpValueOrBool {
    Value(FpValue),
    Bool(bool),
}

/// Classify a collected term into its foldable shape, or `None` for the
/// deliberately unfolded kinds (`FpRoundToIntegral` — no exact engine
/// implementation) and non-operations.
fn fp_op_shape(kind: &TermKind) -> Option<FpOpShape> {
    match kind {
        TermKind::FpAdd(rm, a, b) => Some(FpOpShape::Binary(*rm, *a, *b, BinOp::Add)),
        TermKind::FpSub(rm, a, b) => Some(FpOpShape::Binary(*rm, *a, *b, BinOp::Sub)),
        TermKind::FpMul(rm, a, b) => Some(FpOpShape::Binary(*rm, *a, *b, BinOp::Mul)),
        TermKind::FpDiv(rm, a, b) => Some(FpOpShape::Binary(*rm, *a, *b, BinOp::Div)),
        TermKind::FpRem(a, b) => {
            // `fp.rem` is exact: no rounding mode participates.
            Some(FpOpShape::Binary(RoundingMode::RNE, *a, *b, BinOp::Rem))
        }
        TermKind::FpMin(a, b) => Some(FpOpShape::Binary(RoundingMode::RNE, *a, *b, BinOp::Min)),
        TermKind::FpMax(a, b) => Some(FpOpShape::Binary(RoundingMode::RNE, *a, *b, BinOp::Max)),
        TermKind::FpFma(rm, a, b, c) => Some(FpOpShape::Fma(*rm, *a, *b, *c)),
        TermKind::FpAbs(a) => Some(FpOpShape::Unary(*a, UnOp::Abs)),
        TermKind::FpNeg(a) => Some(FpOpShape::Unary(*a, UnOp::Neg)),
        TermKind::FpSqrt(rm, a) => Some(FpOpShape::Binary(*rm, *a, *a, BinOp::Sqrt)),
        TermKind::FpToFp { rm, eb, sb, arg } => Some(FpOpShape::ToFp(*rm, *eb, *sb, *arg)),
        TermKind::FpEq(a, b) => Some(FpOpShape::Pred(*a, *b, PredOp::Eq)),
        TermKind::FpLt(a, b) => Some(FpOpShape::Pred(*a, *b, PredOp::Lt)),
        TermKind::FpLeq(a, b) => Some(FpOpShape::Pred(*a, *b, PredOp::Leq)),
        TermKind::FpGt(a, b) => Some(FpOpShape::Pred(*a, *b, PredOp::Gt)),
        TermKind::FpGeq(a, b) => Some(FpOpShape::Pred(*a, *b, PredOp::Geq)),
        TermKind::FpIsNormal(a) => Some(FpOpShape::Classify(*a, ClassOp::IsNormal)),
        TermKind::FpIsSubnormal(a) => Some(FpOpShape::Classify(*a, ClassOp::IsSubnormal)),
        TermKind::FpIsZero(a) => Some(FpOpShape::Classify(*a, ClassOp::IsZero)),
        TermKind::FpIsInfinite(a) => Some(FpOpShape::Classify(*a, ClassOp::IsInfinite)),
        TermKind::FpIsNaN(a) => Some(FpOpShape::Classify(*a, ClassOp::IsNaN)),
        TermKind::FpIsNegative(a) => Some(FpOpShape::Classify(*a, ClassOp::IsNegative)),
        TermKind::FpIsPositive(a) => Some(FpOpShape::Classify(*a, ClassOp::IsPositive)),
        _ => None,
    }
}

impl Solver {
    /// One round of FP constant folding (see the module doc).  Runs in the
    /// early `check_core` phase alongside the other theory-lemma
    /// instantiation passes; the clauses it asserts join the problem the
    /// upcoming search solves.  Nothing here can change a verdict unsoundly:
    /// every emitted clause is a valid theory implication.
    pub(super) fn instantiate_fp_folds(&mut self, manager: &mut TermManager) -> bool {
        // ======== collect the ground fp operations of the assertions ========
        // Iterative walk of the hash-consed DAG (the explicit-stack rule for
        // user-controlled nesting depth).  Quantifier bodies stay opaque:
        // their fp operations are not ground, and a lemma about a bound
        // variable's sub-terms belongs to the instantiation machinery, not
        // to this pass.
        let mut ops: Vec<TermId> = Vec::new();
        {
            let mut visited: FxHashSet<TermId> = FxHashSet::default();
            let mut stack: Vec<TermId> = self.assertions.clone();
            while let Some(term) = stack.pop() {
                if !visited.insert(term) {
                    continue;
                }
                let Some(td) = manager.get(term) else {
                    continue;
                };
                if matches!(td.kind, TermKind::Forall { .. } | TermKind::Exists { .. }) {
                    continue;
                }
                if fp_op_shape(&td.kind).is_some() {
                    ops.push(term);
                }
                super::term_walk::collect_structural_children(&td.kind, &mut stack);
            }
        }
        if ops.is_empty() {
            return false;
        }

        // ======== resolve operands and fold, iterating to a fixpoint ========
        // Pins come from three sources, in order: the *definitional*
        // assertions of this scope — `(= t lit)` conjuncts at positive
        // polarity, and `(= t op)` conjuncts whose op folds later in this
        // pass — a fold already recorded here, or (on re-checks after a
        // search has run) the e-graph class of the operand.  The first
        // source is what makes the pass work at `check_core` *entry*: the
        // early instantiation phase runs before any propagation, so the
        // level-0 units have not yet reached the e-graph as merges.  The
        // guard atoms keep the whole family valid regardless of source.
        let mut added_any = false;
        let mut engine = Ieee754Engine::new();
        let mut pinned: FxHashMap<TermId, FpPin> = FxHashMap::default();
        // Folded operations only — NOT `pinned.contains_key`: the define pass
        // legitimately pins an OPERATION term contextually (`(= y op)` with
        // `y` pinned equates them under the assertions), and that contextual
        // pin must not suppress folding the operation to its true value (the
        // fold's pin write then overwrites it).
        let mut folded: FxHashSet<TermId> = FxHashSet::default();
        let mut folded_ops = 0usize;
        loop {
            let mut progress = self.fp_define_pass(&mut pinned, manager);
            for &op in &ops {
                if folded.contains(&op) || folded_ops >= MAX_FP_FOLD_OPS {
                    continue;
                }
                // `None` = not foldable (skip); otherwise `(pin, added)`:
                // `pin` is the folded value to record for chains (`None`
                // for predicates), `added` whether a fresh clause reached
                // the SAT core.
                let Some((pin, added)) = self.fold_one(op, &mut engine, &pinned, manager) else {
                    continue;
                };
                progress = true;
                folded_ops += 1;
                folded.insert(op);
                added_any |= added;
                if let Some(pin) = pin {
                    pinned.insert(op, pin);
                }
            }
            if !progress || folded_ops >= MAX_FP_FOLD_OPS {
                break;
            }
        }
        added_any
    }

    /// Pin `(= term literal)` conjuncts of the assertion set: an equality
    /// reached at positive polarity whose one side decodes to an FP literal
    /// (or is already pinned) pins the other side.  Iterated by the caller's
    /// fixpoint loop, so an equality to an operation pins that side as soon
    /// as the operation folds.  Returns whether any new pin was made.
    fn fp_define_pass(
        &self,
        pinned: &mut FxHashMap<TermId, FpPin>,
        manager: &mut TermManager,
    ) -> bool {
        let mut progress = false;
        // Positive-polarity walk to equality leaves (iterative; `and`-spines
        // of an assertion are conjuncts, everything else — `or`, `ite`, `not`
        // — carries no definitional fact).
        let mut stack: Vec<TermId> = self.assertions.clone();
        let mut visited: FxHashSet<TermId> = FxHashSet::default();
        while let Some(term) = stack.pop() {
            if !visited.insert(term) {
                continue;
            }
            // Extract the structural step as owned ids so the immutable
            // term-data borrow ends before `fp_pin_of` takes `&mut` the
            // manager (it mints guard atoms).
            let step: Option<(TermId, TermId)> = {
                let Some(td) = manager.get(term) else {
                    continue;
                };
                match &td.kind {
                    TermKind::And(args) => {
                        stack.extend(args.iter().copied());
                        None
                    }
                    TermKind::Eq(l, r) => Some((*l, *r)),
                    _ => None,
                }
            };
            if let Some((l, r)) = step {
                {
                    // Pin each side from the other: a literal or already-
                    // pinned side transfers its value, adding the linking
                    // equality to the guard set (the pin then holds *in the
                    // theory* under `{that equality} ∪ {the source's
                    // guards}`, so downstream clauses stay valid standalone).
                    if !pinned.contains_key(&l)
                        && let Some(pin) = self.fp_pin_of(r, pinned, manager)
                    {
                        let mut guards = pin.guards;
                        guards.push(term);
                        pinned.insert(l, FpPin { guards, ..pin });
                        progress = true;
                    }
                    if !pinned.contains_key(&r)
                        && let Some(pin) = self.fp_pin_of(l, pinned, manager)
                    {
                        let mut guards = pin.guards;
                        guards.push(term);
                        pinned.insert(r, FpPin { guards, ..pin });
                        progress = true;
                    }
                }
            }
        }
        progress
    }

    /// The pin a term denotes right now (see [`Self::resolve_fp_operand`]).
    fn fp_pin_of(
        &self,
        term: TermId,
        pinned: &FxHashMap<TermId, FpPin>,
        manager: &mut TermManager,
    ) -> Option<FpPin> {
        self.resolve_fp_operand(term, pinned, manager)
    }

    /// Fold `op` under the current pins, emitting its guarded lemma when the
    /// operation and all its operands are foldable.  Returns the folded value
    /// for value-producing operations (to pin for downstream folds) or
    /// `None` for predicate folds (nothing to pin).
    fn fold_one(
        &mut self,
        op: TermId,
        engine: &mut Ieee754Engine,
        pinned: &FxHashMap<TermId, FpPin>,
        manager: &mut TermManager,
    ) -> Option<(Option<FpPin>, bool)> {
        let mut added_any = false;
        let shape = {
            let td = manager.get(op)?;
            fp_op_shape(&td.kind)?
        };
        // Resolve every operand to a concrete pin; the fold's guard set is
        // the union of the operands' justification atoms (deduplicated,
        // order-stable).  Literal operands contribute none.
        let mut values: SmallVec<[FpValue; 3]> = SmallVec::new();
        let mut guard_atoms: Vec<TermId> = Vec::new();
        for operand in shape.operands() {
            let pin = self.resolve_fp_operand(operand, pinned, manager)?;
            values.push(pin.value);
            for g in pin.guards {
                if !guard_atoms.contains(&g) {
                    guard_atoms.push(g);
                }
            }
        }
        // Exact evaluation at the concrete operands.
        let result = shape.evaluate(engine, &values);
        // The fold's own pin: value, its minted literal term, and the guard
        // set that justifies it (for downstream folds and define pins).
        let fold_pin = match result {
            FpValueOrBool::Value(value) => {
                let lit = mint_fp_lit(&value, manager);
                self.euf.declare_fp_const(lit, fp_const_key(&value));
                Some(FpPin {
                    value,
                    witness: lit,
                    guards: guard_atoms.clone(),
                })
            }
            FpValueOrBool::Bool(_) => None,
        };
        // Build the lemma: ¬g1 ∨ … ∨ ¬gk ∨ conclusion.
        let lemma = match result {
            FpValueOrBool::Value(_) => {
                let conclusion = manager.mk_eq(op, fold_pin.as_ref().map_or(op, |p| p.witness));
                build_fold_lemma(&guard_atoms, conclusion, manager)
            }
            FpValueOrBool::Bool(b) => {
                let conclusion = if b { op } else { manager.mk_not(op) };
                build_fold_lemma(&guard_atoms, conclusion, manager)
            }
        };
        if self.fp_fold_lemmas.insert(lemma) {
            added_any = true;
            // Journal the dedup entry so `pop` retracts it in lockstep with
            // the clause the SAT scope drops — a later scope re-emits the
            // (still valid) lemma if the shape is still there.
            self.trail
                .push(super::trail::TrailOp::FpFoldLemmaAdded { term: lemma });
            self.assert_ground_lemma(lemma, manager);
        }
        let _ = shape;
        Some((fold_pin, added_any))
    }

    /// Resolve `term` to a concrete pin: its exact value, the literal TERM
    /// that carries it (the guard atom's right-hand side), and the guard
    /// atoms that jointly force `term` to that value *in the theory* — so a
    /// downstream clause built from them is valid on its own, never leaning
    /// on another fold clause being present.
    ///
    /// Sources, in order: the term is itself a literal (no guards); a pin
    /// recorded in this pass (directly, or through an EUF-equal alias —
    /// `(= y (fp.add …))` puts `y` in the folded operation's class); or the
    /// distinguished FP constant of its e-graph class.  `None` = unpinned.
    fn resolve_fp_operand(
        &self,
        term: TermId,
        pinned: &FxHashMap<TermId, FpPin>,
        manager: &mut TermManager,
    ) -> Option<FpPin> {
        // A literal operand: its own witness, no guards.
        if let Some(value) = fp_const_value(term, manager) {
            return Some(FpPin {
                value,
                witness: term,
                guards: Vec::new(),
            });
        }
        if let Some(pin) = pinned.get(&term) {
            return Some(pin.clone());
        }
        // A pinned operation's EUF-equal alias resolves through the direct
        // pin (guard set unchanged — the link `(= alias op)` reaches the
        // pins through the define pass, which adds it explicitly).
        if !pinned.is_empty()
            && let Some(node) = self.euf.term_to_node(term)
        {
            for (other, pin) in pinned {
                if let Some(other_node) = self.euf.term_to_node(*other)
                    && self.euf.are_equal_immutable(other_node, node)
                {
                    return Some(pin.clone());
                }
            }
        }
        // The class's distinguished FP constant, if any.  A class pinned to
        // an Int/Bool/BV constant carries that term as its witness;
        // `fp_const_value` filters it (an FP-sorted operand's class can only
        // carry an FP constant or none).
        let witness = self.euf.class_const_witness(term)?;
        let value = fp_const_value(witness, manager)?;
        Some(FpPin {
            value,
            witness,
            guards: vec![manager.mk_eq(term, witness)],
        })
    }
}

/// Assemble `¬g1 ∨ … ∨ ¬gk ∨ conclusion` (just `conclusion` when no guard
/// survives — the operation's operands were all class-pinned constants).
fn build_fold_lemma(guards: &[TermId], conclusion: TermId, manager: &mut TermManager) -> TermId {
    if guards.is_empty() {
        return conclusion;
    }
    let mut disjuncts: Vec<TermId> = Vec::with_capacity(guards.len() + 1);
    for &g in guards {
        disjuncts.push(manager.mk_not(g));
    }
    disjuncts.push(conclusion);
    manager.mk_or(disjuncts)
}

fn engine_rm(rm: RoundingMode) -> FpRoundingMode {
    match rm {
        RoundingMode::RNE => FpRoundingMode::RoundNearestTiesToEven,
        RoundingMode::RNA => FpRoundingMode::RoundNearestTiesToAway,
        RoundingMode::RTP => FpRoundingMode::RoundTowardPositive,
        RoundingMode::RTN => FpRoundingMode::RoundTowardNegative,
        RoundingMode::RTZ => FpRoundingMode::RoundTowardZero,
    }
}
