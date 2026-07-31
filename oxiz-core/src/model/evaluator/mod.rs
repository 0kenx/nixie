//! Model Evaluator
//!
//! Evaluates terms under a given model assignment.
//!
//! Terms are evaluated **iteratively**, by an explicit frame stack held on the
//! heap, rather than by recursing once per nesting level. A term nested a
//! million levels deep therefore costs a million `Vec` entries and a constant
//! number of native stack frames, instead of a million native frames.
//!
//! That matters because a library cannot know how much stack its caller has.
//! The recursive version of this evaluator needed roughly 640 bytes of native
//! stack per nesting level, so a term only ~1700 levels deep killed the whole
//! process with `fatal runtime error: stack overflow` on the ~1 MiB stack an
//! embedder's worker thread typically gets — an abort, not an [`EvalResult`]
//! the caller could handle. Nothing bounded that depth either: the SMT-LIB
//! parser's own nesting limit does not apply to terms built directly through
//! [`TermManager`]'s builder API.
//!
//! The module is split along the seam between *driving* an evaluation and
//! *defining* what each operator computes:
//!
//! * this module — [`EvalResult`], [`EvalCache`], [`ModelEvaluator`] and the
//!   post-order driver, including the per-frame state that records how far a
//!   pending operator has got through its operands;
//! * [`combine`] — the ~60 pure operator implementations, each a function of
//!   already-evaluated operand [`Value`]s.
//!
//! Short-circuit semantics are a property of the *driver*, not of the
//! combiners: `ite` evaluates its condition and then only the taken branch,
//! and `and` / `or` / `distinct` / `+` / `*` stop at the first operand that
//! decides the result. Every other operator is eager — it evaluates all of its
//! operands even when an earlier one already failed, because the recursive
//! version matched on a tuple of `self.eval(..)` calls and so did the same.
//!
//! Reference: Z3's `model_evaluator.cpp`, which likewise separates the
//! rewriter loop from the per-operator reduction hooks.

mod combine;
#[cfg(test)]
mod tests;

use self::combine::{
    BvBinOp, EagerKind, arith_overflow, combine_distinct, combine_eager, finish_arith,
};
use super::{Model, Value};
use crate::ast::{TermId, TermKind, TermManager};
use crate::interner::Spur;
use crate::prelude::HashMap;
#[allow(unused_imports)]
use crate::prelude::*;
use num_rational::Rational64;
use num_traits::{CheckedAdd, CheckedMul};
use smallvec::SmallVec;

/// Result of evaluation
#[derive(Debug, Clone)]
pub enum EvalResult {
    /// Successful evaluation
    Ok(Value),
    /// Term has no value in model
    Undefined(TermId),
    /// Evaluation error
    Error(String),
}

impl EvalResult {
    /// Check if evaluation succeeded
    pub fn is_ok(&self) -> bool {
        matches!(self, EvalResult::Ok(_))
    }

    /// Get value if successful
    pub fn value(&self) -> Option<&Value> {
        match self {
            EvalResult::Ok(v) => Some(v),
            _ => None,
        }
    }

    /// Unwrap value or panic
    pub fn unwrap(self) -> Value {
        match self {
            EvalResult::Ok(v) => v,
            EvalResult::Undefined(t) => panic!("Term {:?} is undefined", t),
            EvalResult::Error(e) => panic!("Evaluation error: {}", e),
        }
    }
}

/// Cache for evaluated terms
#[derive(Debug, Default)]
pub struct EvalCache {
    cache: HashMap<TermId, Value>,
}

impl EvalCache {
    /// Create a new cache
    pub fn new() -> Self {
        Self::default()
    }

    /// Get cached value
    pub fn get(&self, term: TermId) -> Option<&Value> {
        self.cache.get(&term)
    }

    /// Insert value into cache
    pub fn insert(&mut self, term: TermId, value: Value) {
        self.cache.insert(term, value);
    }

    /// Clear the cache
    pub fn clear(&mut self) {
        self.cache.clear();
    }

    /// Number of cached entries
    pub fn len(&self) -> usize {
        self.cache.len()
    }

    /// Check if cache is empty
    pub fn is_empty(&self) -> bool {
        self.cache.is_empty()
    }
}

/// The widest fixed-arity operator the evaluator knows (`store`,
/// `str.substr`, `str.indexof`).
const MAX_EAGER_ARITY: usize = 3;

/// Which half of an `ite` the driver is working on.
#[derive(Debug, Clone, Copy)]
enum IteState {
    /// The condition has not produced a value yet.
    Cond,
    /// The condition selected this branch, which is being evaluated. The
    /// *other* branch is never evaluated, so an `Undefined` or `Error` hiding
    /// in it stays invisible.
    Branch(TermId),
}

/// A pending operator: its operand term ids plus whatever state distinguishes
/// "part-way through" from "ready to combine".
enum Op {
    /// A fixed-arity operator whose operands are *all* evaluated, left to
    /// right, before it combines them.
    ///
    /// Only `operands[..arity]` is meaningful; the tail is padding so that the
    /// frame needs no allocation for the overwhelmingly common unary and
    /// binary cases.
    Eager {
        /// Operand term ids in evaluation order.
        operands: [TermId; MAX_EAGER_ARITY],
        /// How many of `operands` this operator takes.
        arity: u8,
        /// What to compute once the operand values are available.
        kind: EagerKind,
    },
    /// `and` (`conjunction = true`) or `or`, which stop at the first operand
    /// that decides the result.
    Connective {
        /// Operand term ids in evaluation order.
        operands: SmallVec<[TermId; 4]>,
        /// `true` for `and`, `false` for `or`.
        conjunction: bool,
    },
    /// `distinct`, which needs every operand's value but stops at the first
    /// operand that fails.
    Distinct {
        /// Operand term ids in evaluation order.
        operands: SmallVec<[TermId; 4]>,
    },
    /// n-ary `+` (`product = false`) or `*`, folded into `acc` as each operand
    /// arrives so that the fold order — and therefore any arithmetic overflow
    /// it can provoke — matches the recursive version exactly.
    Arith {
        /// Operand term ids in evaluation order.
        operands: SmallVec<[TermId; 4]>,
        /// `true` for `*`, `false` for `+`.
        product: bool,
        /// The running sum or product.
        acc: Rational64,
    },
    /// `ite`, which evaluates the condition and then only the taken branch.
    Ite {
        /// The condition.
        cond: TermId,
        /// Branch taken when the condition is `true`.
        then_branch: TermId,
        /// Branch taken when the condition is `false`.
        else_branch: TermId,
        /// How far the `ite` has got.
        state: IteState,
    },
    /// `(func operands...)` — an uninterpreted function application, or a
    /// regex operator (`re.++`, `str.to_re`, ...), which lowers to `Apply`
    /// under the hood (see `TermManager::mk_regex_op`). Every operand is
    /// evaluated before `func` is looked up in the model, mirroring `Eager`'s
    /// "evaluate everything, remember the first failure" rule — there being
    /// no recursive predecessor to match here, since `Apply` was previously
    /// left entirely unhandled.
    Apply {
        /// The function symbol (`TermKind::Apply`'s interned `func`).
        func: Spur,
        /// Argument term ids in evaluation order.
        operands: SmallVec<[TermId; 4]>,
    },
}

/// One entry of the driver's explicit stack: a compound term whose operands
/// are still being evaluated.
struct Frame {
    /// The term this frame evaluates, and the key its result is cached under.
    term: TermId,
    /// The operator and its per-operator progress.
    op: Op,
    /// How many operands have been consumed so far.
    filled: usize,
    /// The first operand failure seen.
    ///
    /// `Undefined` outranks `Error` and the leftmost of each kind wins, which
    /// is exactly what the recursive version's tuple patterns did: the
    /// `(e @ Undefined(_), _) | (_, e @ Undefined(_)) => e` arm was matched
    /// before the corresponding `Error` arm, and within an arm the leftmost
    /// alternative binds first.
    failure: Option<EvalResult>,
    /// Where this frame's operand values start in the driver's value stack.
    base: usize,
}

/// What reading a term produced: either a value on the spot, or a frame whose
/// operands must be evaluated first.
enum Opened {
    /// A leaf, an unhandled term kind, or an unknown term id.
    Done(EvalResult),
    /// A compound term that now needs operands.
    Frame(Frame),
}

/// What the driver must do next for the frame on top of its stack.
enum Step {
    /// Evaluate this operand and hand the result back on the next turn.
    Need(TermId),
    /// The frame is finished; this is its result.
    Done(EvalResult),
}

impl Frame {
    /// A frame for a fixed-arity operator.
    fn eager(
        term: TermId,
        operands: [TermId; MAX_EAGER_ARITY],
        arity: u8,
        kind: EagerKind,
    ) -> Self {
        Self::new(
            term,
            Op::Eager {
                operands,
                arity,
                kind,
            },
        )
    }

    /// A frame for a one-operand operator.
    fn unary(term: TermId, a: TermId, kind: EagerKind) -> Self {
        Self::eager(term, [a, a, a], 1, kind)
    }

    /// A frame for a two-operand operator, evaluated `a` then `b`.
    fn binary(term: TermId, a: TermId, b: TermId, kind: EagerKind) -> Self {
        Self::eager(term, [a, b, b], 2, kind)
    }

    /// A frame for a three-operand operator, evaluated left to right.
    fn ternary(term: TermId, a: TermId, b: TermId, c: TermId, kind: EagerKind) -> Self {
        Self::eager(term, [a, b, c], 3, kind)
    }

    /// A frame for one of the binary bit-vector operators.
    fn bv_bin(term: TermId, a: TermId, b: TermId, op: BvBinOp) -> Self {
        Self::binary(term, a, b, EagerKind::BvBin(op))
    }

    /// A frame around an arbitrary [`Op`]. `base` is filled in by the driver
    /// when the frame is pushed, once the value stack's height is known.
    fn new(term: TermId, op: Op) -> Self {
        Self {
            term,
            op,
            filled: 0,
            failure: None,
            base: 0,
        }
    }

    /// Fold `incoming` (when there is one) into the frame, then say what the
    /// frame needs next. `model` is only consulted by `Op::Apply`, once all
    /// of its operands are in — see `request`.
    fn advance(
        &mut self,
        values: &mut Vec<Value>,
        incoming: Option<EvalResult>,
        model: &Model,
    ) -> Step {
        if let Some(result) = incoming
            && let Some(finished) = self.accept(values, result)
        {
            return Step::Done(finished);
        }
        self.request(values, model)
    }

    /// Fold one operand result into the frame.
    ///
    /// Returns `Some` when that operand ends the frame there and then — the
    /// short-circuiting arms, where the remaining operands must *not* be
    /// evaluated.
    fn accept(&mut self, values: &mut Vec<Value>, result: EvalResult) -> Option<EvalResult> {
        match &mut self.op {
            Op::Eager { .. } | Op::Apply { .. } => {
                // Eager operators (and `Apply`, which follows the same rule —
                // see its doc) evaluate every operand even after one has
                // failed, so a failure is remembered rather than returned.
                match result {
                    EvalResult::Ok(value) => values.push(value),
                    EvalResult::Undefined(t) => {
                        if !matches!(self.failure, Some(EvalResult::Undefined(_))) {
                            self.failure = Some(EvalResult::Undefined(t));
                        }
                    }
                    EvalResult::Error(message) => {
                        if self.failure.is_none() {
                            self.failure = Some(EvalResult::Error(message));
                        }
                    }
                }
                self.filled += 1;
                None
            }
            Op::Connective { conjunction, .. } => {
                let conjunction = *conjunction;
                match result {
                    EvalResult::Ok(Value::Bool(b)) if b == conjunction => {
                        self.filled += 1;
                        None
                    }
                    EvalResult::Ok(Value::Bool(b)) => Some(EvalResult::Ok(Value::Bool(b))),
                    EvalResult::Ok(_) => Some(EvalResult::Error(if conjunction {
                        "And: expected bool".to_string()
                    } else {
                        "Or: expected bool".to_string()
                    })),
                    e => Some(e),
                }
            }
            Op::Distinct { .. } => match result {
                EvalResult::Ok(value) => {
                    values.push(value);
                    self.filled += 1;
                    None
                }
                e => Some(e),
            },
            Op::Arith { product, acc, .. } => {
                let product = *product;
                let operand = match result {
                    EvalResult::Ok(Value::Int(n)) => Rational64::from_integer(n),
                    EvalResult::Ok(Value::Rational(r)) => r,
                    EvalResult::Ok(_) => {
                        return Some(EvalResult::Error(if product {
                            "Mul: expected number".to_string()
                        } else {
                            "Add: expected number".to_string()
                        }));
                    }
                    e => return Some(e),
                };
                // Checked, because `Rational64` is fixed width: an unchecked
                // fold aborts a debug build on overflow and silently wraps to
                // a wrong model value in release. See `combine::arith_overflow`.
                let folded = if product {
                    acc.checked_mul(&operand)
                } else {
                    acc.checked_add(&operand)
                };
                match folded {
                    Some(value) => *acc = value,
                    None => {
                        return Some(arith_overflow(if product { "Mul" } else { "Add" }));
                    }
                }
                self.filled += 1;
                None
            }
            Op::Ite {
                then_branch,
                else_branch,
                state,
                ..
            } => match state {
                IteState::Cond => match result {
                    EvalResult::Ok(Value::Bool(true)) => {
                        *state = IteState::Branch(*then_branch);
                        None
                    }
                    EvalResult::Ok(Value::Bool(false)) => {
                        *state = IteState::Branch(*else_branch);
                        None
                    }
                    EvalResult::Ok(_) => {
                        Some(EvalResult::Error("Ite: condition must be bool".to_string()))
                    }
                    e => Some(e),
                },
                // The taken branch's result *is* the `ite`'s result, verbatim,
                // including an `Undefined` or an `Error`.
                IteState::Branch(_) => Some(result),
            },
        }
    }

    /// The next operand to evaluate, or the frame's finished result. `model`
    /// is only read by `Op::Apply`, to look up `func`'s `FuncInterp` once
    /// every operand has a value.
    fn request(&mut self, values: &[Value], model: &Model) -> Step {
        match &self.op {
            Op::Eager {
                operands,
                arity,
                kind,
            } => {
                let arity = usize::from(*arity);
                if self.filled < arity {
                    return Step::Need(operands[self.filled]);
                }
                match self.failure.take() {
                    Some(failure) => Step::Done(failure),
                    None => Step::Done(combine_eager(
                        kind,
                        &operands[..arity],
                        &values[self.base..],
                    )),
                }
            }
            Op::Connective {
                operands,
                conjunction,
            } => {
                if self.filled < operands.len() {
                    Step::Need(operands[self.filled])
                } else {
                    Step::Done(EvalResult::Ok(Value::Bool(*conjunction)))
                }
            }
            Op::Distinct { operands } => {
                if self.filled < operands.len() {
                    Step::Need(operands[self.filled])
                } else {
                    Step::Done(combine_distinct(&values[self.base..]))
                }
            }
            Op::Arith { operands, acc, .. } => {
                if self.filled < operands.len() {
                    Step::Need(operands[self.filled])
                } else {
                    Step::Done(finish_arith(*acc))
                }
            }
            Op::Ite { cond, state, .. } => match state {
                IteState::Cond => Step::Need(*cond),
                IteState::Branch(branch) => Step::Need(*branch),
            },
            Op::Apply { func, operands } => {
                if self.filled < operands.len() {
                    Step::Need(operands[self.filled])
                } else {
                    match self.failure.take() {
                        Some(failure) => Step::Done(failure),
                        // `FuncInterp::evaluate` matches its entry table with
                        // `==`, which `Value`'s `PartialEq` bridges between
                        // `Int` and an integral `Rational` (see `Value`'s impl
                        // in `model/mod.rs`), so an Int-sorted argument still
                        // finds an entry keyed on the numerically equal Real
                        // literal, and vice versa.
                        None => Step::Done(match model.get_func_interp(*func) {
                            Some(interp) => {
                                EvalResult::Ok(interp.evaluate(&values[self.base..]).clone())
                            }
                            // No stored interpretation for this function —
                            // genuinely absent, not an error. This is also
                            // where every regex operator (`re.++`, `str.to_re`,
                            // ...) lands: they lower to `Apply` too (see
                            // `TermManager::mk_regex_op`), and a `FuncInterp`
                            // never exists for them, so they are honestly
                            // `Undefined` rather than silently treated as an
                            // uninterpreted function that happens to have no
                            // entries.
                            None => EvalResult::Undefined(self.term),
                        }),
                    }
                }
            }
        }
    }
}

/// Model evaluator with caching
#[derive(Debug)]
pub struct ModelEvaluator<'a> {
    model: &'a Model,
    cache: EvalCache,
    use_cache: bool,
}

impl<'a> ModelEvaluator<'a> {
    /// Create a new evaluator
    pub fn new(model: &'a Model) -> Self {
        Self {
            model,
            cache: EvalCache::new(),
            use_cache: true,
        }
    }

    /// Create evaluator without caching
    pub fn without_cache(model: &'a Model) -> Self {
        Self {
            model,
            cache: EvalCache::new(),
            use_cache: false,
        }
    }

    /// Evaluate a term.
    ///
    /// Runs the explicit frame stack described in the module documentation: a
    /// single loop that alternates between asking the innermost pending
    /// operator for its next operand and handing finished operand values back
    /// to it. Native stack usage is constant in the nesting depth of `term`.
    pub fn eval(&mut self, term: TermId, manager: &TermManager) -> EvalResult {
        if let Some(hit) = self.lookup(term) {
            return hit;
        }

        let mut frames: Vec<Frame> = Vec::new();
        // Operand values of every frame on the stack, concatenated; a frame
        // owns `values[frame.base..]` while it is the innermost one.
        let mut values: Vec<Value> = Vec::new();
        // A finished operand result travelling back to the frame that asked
        // for it.
        let mut carry: Option<EvalResult> = None;

        match self.open(term, manager) {
            Opened::Done(result) => return self.record(term, result),
            Opened::Frame(frame) => frames.push(frame),
        }

        loop {
            let step = match frames.last_mut() {
                Some(top) => top.advance(&mut values, carry.take(), self.model),
                // Only the `Step::Done` arm below empties the stack, and it
                // returns; reaching here would mean the driver lost its root.
                None => {
                    return EvalResult::Error("internal: evaluator stack underflow".to_string());
                }
            };

            match step {
                Step::Need(child) => {
                    if let Some(hit) = self.lookup(child) {
                        carry = Some(hit);
                        continue;
                    }
                    match self.open(child, manager) {
                        Opened::Done(result) => carry = Some(self.record(child, result)),
                        Opened::Frame(mut frame) => {
                            frame.base = values.len();
                            frames.push(frame);
                        }
                    }
                }
                Step::Done(result) => {
                    let Some(frame) = frames.pop() else {
                        return EvalResult::Error(
                            "internal: evaluator stack underflow".to_string(),
                        );
                    };
                    values.truncate(frame.base);
                    let result = self.record(frame.term, result);
                    if frames.is_empty() {
                        return result;
                    }
                    carry = Some(result);
                }
            }
        }
    }

    /// The two lookups every term goes through before any structural work: the
    /// evaluation cache, then the model's own assignment.
    fn lookup(&mut self, term: TermId) -> Option<EvalResult> {
        // Check cache first
        if self.use_cache
            && let Some(v) = self.cache.get(term)
        {
            return Some(EvalResult::Ok(v.clone()));
        }

        // Check model assignment
        if let Some(v) = self.model.get(term) {
            let v = v.clone();
            if self.use_cache {
                self.cache.insert(term, v.clone());
            }
            return Some(EvalResult::Ok(v));
        }

        None
    }

    /// Cache a structurally evaluated result. Only successful evaluations are
    /// cached; an `Undefined` or `Error` may become defined once the model
    /// grows, so it must not be remembered.
    fn record(&mut self, term: TermId, result: EvalResult) -> EvalResult {
        if self.use_cache
            && let EvalResult::Ok(ref v) = result
        {
            self.cache.insert(term, v.clone());
        }
        result
    }

    /// Read one term: either it has a value on its own, or it opens a frame.
    ///
    /// This is the former `eval_term`'s dispatch, minus the recursion: an arm
    /// that used to call `self.eval(..)` now describes its operands to the
    /// driver instead of evaluating them itself.
    fn open(&self, term: TermId, manager: &TermManager) -> Opened {
        let t = match manager.get(term) {
            Some(t) => t,
            None => return Opened::Done(EvalResult::Error(format!("Unknown term: {:?}", term))),
        };

        match &t.kind {
            // Constants
            TermKind::True => Opened::Done(EvalResult::Ok(Value::Bool(true))),
            TermKind::False => Opened::Done(EvalResult::Ok(Value::Bool(false))),
            TermKind::IntConst(n) => {
                // Convert BigInt to i64, without silently truncating out-of-range
                // values to 0. `Value::Int` is a fixed-width i64 representation
                // (see model/mod.rs); a BigInt that does not fit cannot be
                // represented faithfully, so surface an explicit error instead
                // of fabricating a wrong value.
                Opened::Done(match i64::try_from(n) {
                    Ok(val) => EvalResult::Ok(Value::Int(val)),
                    Err(_) => EvalResult::Error(format!(
                        "IntConst {n} does not fit in i64; wide integer model \
                         values are not yet representable by ModelEvaluator"
                    )),
                })
            }
            TermKind::RealConst(r) => Opened::Done(EvalResult::Ok(Value::Rational(*r))),
            TermKind::StringLit(s) => Opened::Done(EvalResult::Ok(Value::String(s.clone()))),
            TermKind::BitVecConst { value, width } => {
                // Convert BigInt to u64, without silently truncating out-of-range
                // values to 0. `Value::BitVec` stores its payload as a u64
                // magnitude alongside a (possibly >64) declared width — see
                // `Value`'s Display impl in model/mod.rs, which zero-extends
                // the u64 magnitude out to `width` bits. That representation
                // is exact as long as the constant's magnitude fits in u64;
                // when it does not (e.g. a >64-bit constant whose value
                // itself exceeds u64::MAX), surface an explicit error instead
                // of fabricating a wrong (truncated-to-something-else) value.
                Opened::Done(match u64::try_from(value) {
                    Ok(val) => EvalResult::Ok(Value::BitVec(*width, val)),
                    Err(_) => EvalResult::Error(format!(
                        "BitVecConst {value} (width {width}) does not fit in u64; \
                         wide bitvector model values with magnitude beyond u64::MAX \
                         are not yet representable by ModelEvaluator"
                    )),
                })
            }

            // Variables - look up in model
            TermKind::Var(_) => Opened::Done(match self.model.get(term) {
                Some(v) => EvalResult::Ok(v.clone()),
                None => EvalResult::Undefined(term),
            }),

            // Boolean operations
            TermKind::Not(inner) => Opened::Frame(Frame::unary(term, *inner, EagerKind::Not)),
            TermKind::And(args) => Opened::Frame(Frame::new(
                term,
                Op::Connective {
                    operands: args.clone(),
                    conjunction: true,
                },
            )),
            TermKind::Or(args) => Opened::Frame(Frame::new(
                term,
                Op::Connective {
                    operands: args.clone(),
                    conjunction: false,
                },
            )),
            TermKind::Xor(a, b) => Opened::Frame(Frame::binary(term, *a, *b, EagerKind::Xor)),
            TermKind::Implies(a, b) => {
                Opened::Frame(Frame::binary(term, *a, *b, EagerKind::Implies))
            }
            TermKind::Ite(cond, then_branch, else_branch) => Opened::Frame(Frame::new(
                term,
                Op::Ite {
                    cond: *cond,
                    then_branch: *then_branch,
                    else_branch: *else_branch,
                    state: IteState::Cond,
                },
            )),

            // Equality
            TermKind::Eq(a, b) => Opened::Frame(Frame::binary(term, *a, *b, EagerKind::Eq)),
            TermKind::Distinct(args) => Opened::Frame(Frame::new(
                term,
                Op::Distinct {
                    operands: args.clone(),
                },
            )),

            // Arithmetic
            TermKind::Add(args) => Opened::Frame(Frame::new(
                term,
                Op::Arith {
                    operands: args.clone(),
                    product: false,
                    acc: Rational64::from_integer(0),
                },
            )),
            TermKind::Sub(a, b) => Opened::Frame(Frame::binary(term, *a, *b, EagerKind::Sub)),
            TermKind::Mul(args) => Opened::Frame(Frame::new(
                term,
                Op::Arith {
                    operands: args.clone(),
                    product: true,
                    acc: Rational64::from_integer(1),
                },
            )),
            TermKind::Div(a, b) => {
                // The Int-vs-Real dispatch keys off the *sort* of the
                // numerator term, which is known before either operand has a
                // value, exactly as in the recursive version.
                let int_sorted = manager
                    .get(*a)
                    .and_then(|t| manager.sorts.get(t.sort))
                    .is_some_and(|s| s.is_int());
                Opened::Frame(Frame::binary(term, *a, *b, EagerKind::Div { int_sorted }))
            }
            TermKind::Mod(a, b) => Opened::Frame(Frame::binary(term, *a, *b, EagerKind::Mod)),
            TermKind::Neg(a) => Opened::Frame(Frame::unary(term, *a, EagerKind::Neg)),
            TermKind::Lt(a, b) => Opened::Frame(Frame::binary(term, *a, *b, EagerKind::Lt)),
            TermKind::Le(a, b) => Opened::Frame(Frame::binary(term, *a, *b, EagerKind::Le)),
            // `a > b` is `b < a`, and the recursive version passed the
            // operands to `eval_lt` in that swapped order — so the *right*
            // operand is evaluated first. Keep it: evaluation order is
            // observable through the cache.
            TermKind::Gt(a, b) => Opened::Frame(Frame::binary(term, *b, *a, EagerKind::Lt)),
            TermKind::Ge(a, b) => Opened::Frame(Frame::binary(term, *b, *a, EagerKind::Le)),

            // Bitvector operations
            TermKind::BvNot(a) => Opened::Frame(Frame::unary(term, *a, EagerKind::BvNot)),
            TermKind::BvAnd(a, b) => Opened::Frame(Frame::bv_bin(term, *a, *b, BvBinOp::And)),
            TermKind::BvOr(a, b) => Opened::Frame(Frame::bv_bin(term, *a, *b, BvBinOp::Or)),
            TermKind::BvXor(a, b) => Opened::Frame(Frame::bv_bin(term, *a, *b, BvBinOp::Xor)),
            TermKind::BvAdd(a, b) => Opened::Frame(Frame::bv_bin(term, *a, *b, BvBinOp::Add)),
            TermKind::BvSub(a, b) => Opened::Frame(Frame::bv_bin(term, *a, *b, BvBinOp::Sub)),
            TermKind::BvMul(a, b) => Opened::Frame(Frame::bv_bin(term, *a, *b, BvBinOp::Mul)),
            TermKind::BvUdiv(a, b) => Opened::Frame(Frame::bv_bin(term, *a, *b, BvBinOp::Udiv)),
            TermKind::BvSdiv(a, b) => Opened::Frame(Frame::bv_bin(term, *a, *b, BvBinOp::Sdiv)),
            TermKind::BvUrem(a, b) => Opened::Frame(Frame::bv_bin(term, *a, *b, BvBinOp::Urem)),
            TermKind::BvSrem(a, b) => Opened::Frame(Frame::bv_bin(term, *a, *b, BvBinOp::Srem)),
            TermKind::BvShl(a, b) => Opened::Frame(Frame::bv_bin(term, *a, *b, BvBinOp::Shl)),
            TermKind::BvLshr(a, b) => Opened::Frame(Frame::bv_bin(term, *a, *b, BvBinOp::Lshr)),
            TermKind::BvAshr(a, b) => Opened::Frame(Frame::bv_bin(term, *a, *b, BvBinOp::Ashr)),
            TermKind::BvUlt(a, b) => Opened::Frame(Frame::bv_bin(term, *a, *b, BvBinOp::Ult)),
            TermKind::BvUle(a, b) => Opened::Frame(Frame::bv_bin(term, *a, *b, BvBinOp::Ule)),
            TermKind::BvSlt(a, b) => Opened::Frame(Frame::bv_bin(term, *a, *b, BvBinOp::Slt)),
            TermKind::BvSle(a, b) => Opened::Frame(Frame::bv_bin(term, *a, *b, BvBinOp::Sle)),
            TermKind::BvConcat(a, b) => {
                Opened::Frame(Frame::binary(term, *a, *b, EagerKind::BvConcat))
            }
            TermKind::BvExtract { high, low, arg } => Opened::Frame(Frame::unary(
                term,
                *arg,
                EagerKind::BvExtract {
                    high: *high,
                    low: *low,
                },
            )),

            // Array operations
            TermKind::Select(array, index) => {
                Opened::Frame(Frame::binary(term, *array, *index, EagerKind::Select))
            }
            TermKind::Store(array, index, value) => Opened::Frame(Frame::ternary(
                term,
                *array,
                *index,
                *value,
                EagerKind::Store,
            )),

            // String operations
            TermKind::StrLen(arg) => Opened::Frame(Frame::unary(term, *arg, EagerKind::StrLen)),
            TermKind::StrConcat(a, b) => {
                Opened::Frame(Frame::binary(term, *a, *b, EagerKind::StrConcat))
            }
            TermKind::StrAt(s, i) => Opened::Frame(Frame::binary(term, *s, *i, EagerKind::StrAt)),
            TermKind::StrContains(s, sub) => {
                Opened::Frame(Frame::binary(term, *s, *sub, EagerKind::StrContains))
            }
            TermKind::StrSubstr(s, i, n) => {
                Opened::Frame(Frame::ternary(term, *s, *i, *n, EagerKind::StrSubstr))
            }
            TermKind::StrIndexOf(s, sub, offset) => Opened::Frame(Frame::ternary(
                term,
                *s,
                *sub,
                *offset,
                EagerKind::StrIndexOf,
            )),
            TermKind::StrLt(lhs, rhs) => Opened::Frame(Frame::binary(
                term,
                *lhs,
                *rhs,
                EagerKind::StrOrder { strict: true },
            )),
            TermKind::StrLe(lhs, rhs) => Opened::Frame(Frame::binary(
                term,
                *lhs,
                *rhs,
                EagerKind::StrOrder { strict: false },
            )),
            TermKind::StrToCode(s) => Opened::Frame(Frame::unary(term, *s, EagerKind::StrToCode)),
            TermKind::StrFromCode(n) => {
                Opened::Frame(Frame::unary(term, *n, EagerKind::StrFromCode))
            }

            // Uninterpreted function application (and, under the hood, every
            // regex operator — see `Op::Apply`'s doc comment).
            TermKind::Apply { func, args } => Opened::Frame(Frame::new(
                term,
                Op::Apply {
                    func: *func,
                    operands: args.clone(),
                },
            )),

            // Unhandled - return undefined for now
            _ => Opened::Done(EvalResult::Undefined(term)),
        }
    }

    /// Clear the evaluation cache
    pub fn clear_cache(&mut self) {
        self.cache.clear();
    }

    /// Get cache statistics
    pub fn cache_size(&self) -> usize {
        self.cache.len()
    }
}
