//! The evaluator behind the model-verification soundness gate.
//!
//! [`Solver::model_refutes_assertions`] is the last thing standing between a
//! candidate model and a reported `Sat`: it re-evaluates every top-level
//! assertion under the freshly built model and refuses the verdict when the
//! model does not hold up.  [`Solver::eval_in_model_outcome`] is the evaluator
//! it runs.
//!
//! Two properties of that evaluator are load-bearing and are the reason it
//! lives in its own module rather than inline in the solver:
//!
//! * **It is iterative.**  Terms are evaluated by an explicit frame stack held
//!   on the heap, so a term nested a million levels deep costs a million `Vec`
//!   entries and a constant number of native stack frames.  The recursive
//!   version spent one native frame per nesting level of the assertion, and a
//!   library cannot know how much stack its caller has: an embedder's worker
//!   thread typically gets ~1 MiB, and a `fatal runtime error: stack overflow`
//!   there is a process abort, not a verdict the caller can handle.  Nothing
//!   bounds that depth from the outside either — the SMT-LIB parser's nesting
//!   limit does not apply to terms built through [`TermManager`]'s builder API,
//!   nor to the lemmas the array-axiom refinement loop synthesises.
//! * **Its arithmetic is checked.**  [`EvalVal::Num`] is a fixed-width
//!   `Rational64`, so a sum, difference, product or negation of two
//!   representable model values need not itself be representable.  Every
//!   arithmetic step therefore goes through `checked_*` and reports
//!   [`EvalOutcome::Unrepresentable`] rather than overflowing — see that
//!   variant's documentation for why the unchecked version was a soundness bug
//!   and not merely a robustness one.
//!
//! Reference: Z3's `smt_model_checker.cpp` plays the same role — re-checking a
//! candidate model against the assertions before the verdict is trusted.

use super::types::Model;
use super::{ENCODE_DEPTH_LIMIT, EvalVal, Solver};
#[allow(unused_imports)]
use crate::prelude::*;
use num_rational::Rational64;
use num_traits::{CheckedAdd, CheckedMul, CheckedSub, ToPrimitive};
use oxiz_core::ast::{TermId, TermKind, TermManager};
use smallvec::SmallVec;

/// What evaluating a term under a candidate model produced.
///
/// The two non-value answers are deliberately *not* the same thing, and the
/// gate treats them differently — see [`Solver::model_refutes_assertions`].
#[derive(Debug, Clone, Copy, PartialEq)]
pub(super) enum EvalOutcome {
    /// A concrete value the model determines.
    Value(EvalVal),
    /// The model does not determine this term's value: an unconstrained
    /// arithmetic variable, an opaque application the model does not pin, an
    /// operator the gate deliberately declines to decide (`distinct`, a
    /// numeric equality collision, a strict comparison at its boundary), an
    /// ill-typed operand, or a term past the evaluator's depth budget.
    ///
    /// This is the ordinary, expected answer for large parts of any real
    /// formula, and it must never by itself downgrade a `Sat`: the arithmetic
    /// solver represents disequalities by case splitting and strict bounds by
    /// a symbolic delta, so `Undetermined` is what a *perfectly good* model
    /// looks like through this evaluator.
    Undetermined,
    /// The model pinned every operand, but the evaluator's own fixed-width
    /// arithmetic could not represent an intermediate result.
    ///
    /// This is a statement about the evaluator, not about the model, and it is
    /// kept apart from [`EvalOutcome::Undetermined`] because the gate cannot
    /// afford to shrug it off.  Before the arithmetic here was checked, an
    /// overflowing assertion aborted a debug build outright and, in release,
    /// wrapped: `(< (+ 2^62 2^62) 0)` — false under the model, i.e. a genuine
    /// violation — wrapped to `i64::MIN < 0` and reported `true`, so the gate
    /// waved the bad model through as `Sat`.  The mirror image
    /// `(>= (+ 2^62 2^62) 0)` — true under the model — wrapped to `false` and
    /// refuted a perfectly good one.
    Unrepresentable,
}

impl EvalOutcome {
    /// The outcome for a term whose value the model does not determine.
    const UNDETERMINED: EvalOutcome = EvalOutcome::Undetermined;

    /// A Boolean outcome.
    fn boolean(value: bool) -> Self {
        EvalOutcome::Value(EvalVal::Bool(value))
    }

    /// A numeric outcome.
    fn number(value: Rational64) -> Self {
        EvalOutcome::Value(EvalVal::Num(value))
    }

    /// The value this outcome carries, if any.
    fn value(self) -> Option<EvalVal> {
        match self {
            EvalOutcome::Value(v) => Some(v),
            _ => None,
        }
    }

    /// This outcome demoted to its non-value form: a `Value` the caller could
    /// not use (wrong type, or a sibling operand already failed) is no better
    /// than `Undetermined`, while `Unrepresentable` stays `Unrepresentable`.
    fn demote(self) -> Self {
        match self {
            EvalOutcome::Unrepresentable => EvalOutcome::Unrepresentable,
            _ => EvalOutcome::UNDETERMINED,
        }
    }

    /// The more cautious of two non-value outcomes: `Unrepresentable` wins,
    /// because it is the one the gate must act on.
    fn worse(self, other: Self) -> Self {
        if matches!(self, EvalOutcome::Unrepresentable)
            || matches!(other, EvalOutcome::Unrepresentable)
        {
            EvalOutcome::Unrepresentable
        } else {
            EvalOutcome::UNDETERMINED
        }
    }
}

/// A fixed-arity operator whose operands are evaluated left to right, stopping
/// at the first operand that does not produce a value.
///
/// The recursive version wrote each of these as `match (rec(a)?, rec(b)?)`, and
/// `?` on the left operand short-circuits before the right one is touched.
/// Evaluation here is pure — no cache, no model mutation — so the only thing
/// that short-circuit ever changed was the cost, and it is kept for that.
#[derive(Debug, Clone, Copy)]
enum EagerKind {
    /// `not`
    Not,
    /// `=`
    Eq,
    /// binary `-`
    Sub,
    /// unary `-`
    Neg,
    /// `<` (`strict_less`) or `>`; both soften at the boundary — see
    /// [`cmp_strict`].
    CmpStrict {
        /// `true` for `<`, `false` for `>`.
        less: bool,
    },
    /// `<=` (`or_equal_less`) or `>=`.
    CmpWeak {
        /// `true` for `<=`, `false` for `>=`.
        less: bool,
    },
}

/// How far an `ite` has got.
#[derive(Debug, Clone, Copy)]
enum IteState {
    /// The condition has not produced a value yet.
    Cond,
    /// The condition selected this branch; the other one is never evaluated.
    Branch(TermId),
}

/// How far an `=>` has got.
#[derive(Debug, Clone, Copy)]
enum ImpliesState {
    /// The antecedent has not produced a value yet.
    Antecedent,
    /// The antecedent is `true`, so the implication *is* its consequent.
    ConsequentDecides,
    /// The antecedent produced no usable truth value.  Only a `true`
    /// consequent can still decide the implication; anything else leaves the
    /// carried non-value outcome.
    ConsequentMayRescue(EvalOutcome),
}

/// A pending operator, plus whatever state distinguishes "part-way through"
/// from "ready to combine".
#[derive(Debug)]
enum Op {
    /// A fixed-arity operator; only `operands[..arity]` is meaningful.
    Eager {
        /// Operand term ids in evaluation order.
        operands: [TermId; 2],
        /// How many of `operands` this operator takes.
        arity: u8,
        /// What to compute from the operand values.
        kind: EagerKind,
    },
    /// `and` (`conjunction = true`) or `or`, which stop at the first operand
    /// that decides the result but keep scanning the rest otherwise.
    Connective {
        /// Operand term ids in evaluation order.
        operands: SmallVec<[TermId; 4]>,
        /// `true` for `and`, `false` for `or`.
        conjunction: bool,
    },
    /// n-ary `+` (`product = false`) or `*`, folded into `acc` as each operand
    /// arrives so the fold order matches the recursive version exactly.
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
    /// `=>`, whose antecedent decides whether the consequent is consulted at
    /// all and how its answer is used.
    Implies {
        /// The antecedent.
        antecedent: TermId,
        /// The consequent.
        consequent: TermId,
        /// How far the implication has got.
        state: ImpliesState,
    },
}

/// One entry of the driver's explicit stack.
#[derive(Debug)]
struct Frame {
    /// The operator and its per-operator progress.
    op: Op,
    /// How many operands have been consumed so far.
    filled: usize,
    /// Where this frame's operand values start in the driver's value stack.
    base: usize,
    /// The nesting depth of this frame's term, charged against
    /// [`ENCODE_DEPTH_LIMIT`].
    depth: u32,
    /// The most cautious non-value outcome any operand has produced, for the
    /// operators that keep scanning after one.
    carried: Option<EvalOutcome>,
}

/// What reading a term produced.
enum Opened {
    /// A leaf, an operator the gate declines to decide, or an unknown term id.
    Done(EvalOutcome),
    /// A compound term that now needs operands.
    Frame(Frame),
}

/// What the driver must do next for the frame on top of its stack.
enum Step {
    /// Evaluate this operand and hand the result back on the next turn.
    Need(TermId),
    /// The frame is finished; this is its result.
    Done(EvalOutcome),
}

impl Frame {
    /// A frame around an arbitrary [`Op`].  `base` is filled in by the driver
    /// when the frame is pushed, once the value stack's height is known.
    fn new(op: Op, depth: u32) -> Self {
        Self {
            op,
            filled: 0,
            base: 0,
            depth,
            carried: None,
        }
    }

    /// A frame for a one-operand operator.
    fn unary(a: TermId, kind: EagerKind, depth: u32) -> Self {
        Self::new(
            Op::Eager {
                operands: [a, a],
                arity: 1,
                kind,
            },
            depth,
        )
    }

    /// A frame for a two-operand operator, evaluated `a` then `b`.
    fn binary(a: TermId, b: TermId, kind: EagerKind, depth: u32) -> Self {
        Self::new(
            Op::Eager {
                operands: [a, b],
                arity: 2,
                kind,
            },
            depth,
        )
    }

    /// Fold `incoming` (when there is one) into the frame, then say what the
    /// frame needs next.
    fn advance(&mut self, values: &mut Vec<EvalVal>, incoming: Option<EvalOutcome>) -> Step {
        if let Some(result) = incoming
            && let Some(finished) = self.accept(values, result)
        {
            return Step::Done(finished);
        }
        self.request(values)
    }

    /// Fold one operand outcome into the frame.
    ///
    /// Returns `Some` when that operand ends the frame there and then — the
    /// short-circuiting cases, where the remaining operands must not be
    /// evaluated.
    fn accept(&mut self, values: &mut Vec<EvalVal>, result: EvalOutcome) -> Option<EvalOutcome> {
        match &mut self.op {
            // A fixed-arity operator gives up at the first operand it cannot
            // use, exactly as the recursive version's `rec(a)?` did.
            Op::Eager { .. } => match result.value() {
                Some(value) => {
                    values.push(value);
                    self.filled += 1;
                    None
                }
                None => Some(result.demote()),
            },
            Op::Connective { conjunction, .. } => {
                let conjunction = *conjunction;
                match result {
                    // The deciding truth value ends the connective outright and
                    // outranks anything an earlier operand carried: `false ∧ ?`
                    // really is `false`.
                    EvalOutcome::Value(EvalVal::Bool(b)) if b != conjunction => {
                        Some(EvalOutcome::boolean(b))
                    }
                    EvalOutcome::Value(EvalVal::Bool(_)) => {
                        self.filled += 1;
                        None
                    }
                    // A non-Boolean operand, or one with no value: remember the
                    // most cautious answer seen and keep scanning, because a
                    // later operand may still decide the connective.
                    other => {
                        let demoted = other.demote();
                        self.carried = Some(match self.carried {
                            Some(existing) => existing.worse(demoted),
                            None => demoted,
                        });
                        self.filled += 1;
                        None
                    }
                }
            }
            Op::Arith { product, acc, .. } => {
                let product = *product;
                let EvalOutcome::Value(EvalVal::Num(operand)) = result else {
                    return Some(result.demote());
                };
                // Checked, because `Rational64` is fixed width.  See
                // [`EvalOutcome::Unrepresentable`] for what the unchecked fold
                // did to the gate in each build profile.
                let folded = if product {
                    acc.checked_mul(&operand)
                } else {
                    acc.checked_add(&operand)
                };
                match folded {
                    Some(value) => *acc = value,
                    None => return Some(EvalOutcome::Unrepresentable),
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
                    EvalOutcome::Value(EvalVal::Bool(true)) => {
                        *state = IteState::Branch(*then_branch);
                        None
                    }
                    EvalOutcome::Value(EvalVal::Bool(false)) => {
                        *state = IteState::Branch(*else_branch);
                        None
                    }
                    other => Some(other.demote()),
                },
                // The taken branch's outcome *is* the `ite`'s outcome.
                IteState::Branch(_) => Some(result),
            },
            Op::Implies { state, .. } => match state {
                ImpliesState::Antecedent => match result {
                    // `false => _` is `true`, with no look at the consequent.
                    EvalOutcome::Value(EvalVal::Bool(false)) => Some(EvalOutcome::boolean(true)),
                    EvalOutcome::Value(EvalVal::Bool(true)) => {
                        *state = ImpliesState::ConsequentDecides;
                        None
                    }
                    other => {
                        *state = ImpliesState::ConsequentMayRescue(other.demote());
                        None
                    }
                },
                ImpliesState::ConsequentDecides => Some(match result {
                    EvalOutcome::Value(EvalVal::Bool(b)) => EvalOutcome::boolean(b),
                    other => other.demote(),
                }),
                // `_ => true` is `true` whatever the antecedent was.
                ImpliesState::ConsequentMayRescue(carried) => Some(match result {
                    EvalOutcome::Value(EvalVal::Bool(true)) => EvalOutcome::boolean(true),
                    other => carried.worse(other.demote()),
                }),
            },
        }
    }

    /// The next operand to evaluate, or the frame's finished outcome.
    fn request(&mut self, values: &[EvalVal]) -> Step {
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
                Step::Done(combine_eager(*kind, &values[self.base..]))
            }
            Op::Connective {
                operands,
                conjunction,
            } => {
                if self.filled < operands.len() {
                    Step::Need(operands[self.filled])
                } else {
                    // No operand decided the connective.  If every one agreed
                    // with it the connective holds; otherwise the most cautious
                    // outcome seen stands.
                    Step::Done(match self.carried {
                        Some(carried) => carried,
                        None => EvalOutcome::boolean(*conjunction),
                    })
                }
            }
            Op::Arith { operands, acc, .. } => {
                if self.filled < operands.len() {
                    Step::Need(operands[self.filled])
                } else {
                    Step::Done(EvalOutcome::number(*acc))
                }
            }
            Op::Ite { cond, state, .. } => match state {
                IteState::Cond => Step::Need(*cond),
                IteState::Branch(branch) => Step::Need(*branch),
            },
            Op::Implies {
                antecedent,
                consequent,
                state,
            } => match state {
                ImpliesState::Antecedent => Step::Need(*antecedent),
                _ => Step::Need(*consequent),
            },
        }
    }
}

/// Combine the operand values of a fixed-arity operator.
///
/// `values` holds exactly the operands the frame collected, in order; the
/// driver only reaches here once every one of them produced a value.
fn combine_eager(kind: EagerKind, values: &[EvalVal]) -> EvalOutcome {
    match (kind, values) {
        (EagerKind::Not, [EvalVal::Bool(b)]) => EvalOutcome::boolean(!b),
        (EagerKind::Eq, [a, b]) => combine_eq(*a, *b),
        (EagerKind::Sub, [EvalVal::Num(x), EvalVal::Num(y)]) => match x.checked_sub(y) {
            Some(d) => EvalOutcome::number(d),
            None => EvalOutcome::Unrepresentable,
        },
        // Negation is the one arithmetic operator that overflows on a *single*
        // operand: `-i64::MIN` has no `i64`.  Negating the numerator of an
        // already-reduced ratio keeps it reduced with a positive denominator,
        // so no re-reduction is needed.
        (EagerKind::Neg, [EvalVal::Num(n)]) => match n.numer().checked_neg() {
            Some(numer) => EvalOutcome::number(Rational64::new_raw(numer, *n.denom())),
            None => EvalOutcome::Unrepresentable,
        },
        (EagerKind::CmpStrict { less }, [EvalVal::Num(x), EvalVal::Num(y)]) => {
            cmp_strict(*x, *y, less)
        }
        (EagerKind::CmpWeak { less }, [EvalVal::Num(x), EvalVal::Num(y)]) => {
            EvalOutcome::boolean(if less { x <= y } else { x >= y })
        }
        // Ill-typed operands (a Bool where a number was wanted, or the other
        // way round).  The gate has nothing to say about such a term.
        _ => EvalOutcome::UNDETERMINED,
    }
}

/// Combine the operand values of `=`.
///
/// Booleans come straight from the SAT assignment and are reliable in both
/// directions.  Numeric equality is trustworthy only in the NEGATIVE direction:
/// distinct arithmetic values genuinely falsify the equality, but a *collision*
/// is not evidence — the LP model can assign two variables the same value even
/// when they were never asserted equal.  Reporting a collision as
/// `Undetermined` also keeps a negated equality (`distinct` / `not (= ..)`)
/// inconclusive there instead of a false violation.
fn combine_eq(a: EvalVal, b: EvalVal) -> EvalOutcome {
    match (a, b) {
        (EvalVal::Bool(x), EvalVal::Bool(y)) => EvalOutcome::boolean(x == y),
        (EvalVal::Num(x), EvalVal::Num(y)) => {
            if x == y {
                EvalOutcome::UNDETERMINED
            } else {
                EvalOutcome::boolean(false)
            }
        }
        _ => EvalOutcome::UNDETERMINED,
    }
}

/// Evaluate a STRICT comparison (`less` selects `<` over `>`).
///
/// STRICT comparisons are softened AT THE BOUNDARY: the arithmetic solver
/// represents `x > c` internally with a delta above `c` but `value()` reports
/// the boundary `c` itself, so a model value equal to the bound cannot
/// distinguish `x > c` (satisfiable) from a real violation.  Reporting
/// `Undetermined` there keeps the gate from falsely refuting a genuine
/// strict-inequality model; away from the boundary the comparison is concrete
/// and trustworthy.  Non-strict `<=` / `>=` have no such ambiguity.
fn cmp_strict(x: Rational64, y: Rational64, less: bool) -> EvalOutcome {
    if x == y {
        EvalOutcome::UNDETERMINED
    } else if less {
        EvalOutcome::boolean(x < y)
    } else {
        EvalOutcome::boolean(x > y)
    }
}

impl Solver {
    /// Soundness gate: may the freshly built model be reported as `Sat`?
    ///
    /// Returns `true` when it may not, for either of two reasons:
    ///
    /// * a top-level assertion evaluates to a concrete `false` under the model
    ///   — the model provably violates it (this is the case the name refers
    ///   to); or
    /// * a top-level assertion could not be evaluated *at all* because the
    ///   evaluator's fixed-width arithmetic could not represent an intermediate
    ///   result ([`EvalOutcome::Unrepresentable`]).
    ///
    /// The second reason is the conservative direction, and which direction is
    /// conservative here is worth spelling out.  A `false` answer from this
    /// function is consumed as "go ahead and report `Sat`"; a `true` answer
    /// costs only precision, because the caller then answers `Unknown`, which
    /// is always a legal verdict.  So when the gate cannot evaluate an
    /// assertion it must not conclude that the model satisfies it.  Doing the
    /// opposite is precisely the bug the checked arithmetic removes: an
    /// overflowing `(< (+ 2^62 2^62) 0)` wrapped to `true` in release, and the
    /// gate waved through a model that genuinely falsifies the assertion.
    ///
    /// [`EvalOutcome::Undetermined`] is emphatically *not* treated that way.
    /// The key to the gate's usefulness is where leaf numeric values come from:
    /// an Int/Real variable is read from the *arithmetic solver*
    /// (`arith.value`), which reports `None` for a variable it does not
    /// actually constrain.  That `None` propagates to `Undetermined` and never
    /// triggers a downgrade — so a `distinct` / comparison over variables that
    /// `build_model` merely *defaulted* to 0 (a genuinely satisfiable formula)
    /// is never mistaken for a violation.  Combined with the strict-inequality
    /// boundary softening (see [`cmp_strict`]), the gate only fires on a
    /// witness the theory genuinely determined yet the assignment falsifies —
    /// the signature of the SAT core committing an inconsistent trail (e.g. a
    /// clause reported satisfied whose every disjunct is false).  In that case
    /// the reported `Sat` is spurious and the solver answers `Unknown` instead.
    pub(super) fn model_refutes_assertions(&self, manager: &TermManager) -> bool {
        let Some(model) = self.model.as_ref() else {
            return false;
        };
        for &assertion in &self.assertions {
            match self.eval_in_model_outcome(assertion, model, manager, 0) {
                EvalOutcome::Value(EvalVal::Bool(false)) | EvalOutcome::Unrepresentable => {
                    return true;
                }
                _ => {}
            }
        }
        false
    }

    /// The value `model` determines for `term`, or `None` when it determines
    /// none.
    ///
    /// This is the *value-only* view of [`Self::eval_in_model_outcome`], for
    /// callers that act on a concrete value and treat every other answer alike
    /// — currently the array-axiom instantiator, which asks "does the candidate
    /// model already satisfy this axiom instance?" and re-asserts the instance
    /// whenever the answer is not a definite `true`.  Collapsing
    /// [`EvalOutcome::Unrepresentable`] into `None` is right for that caller:
    /// an axiom instance the evaluator could not fold is one it has not
    /// verified, so instantiating it again is the safe move.  The
    /// model-verification gate must *not* collapse the two and uses the outcome
    /// form directly.
    pub(super) fn eval_in_model(
        &self,
        term: TermId,
        model: &Model,
        manager: &TermManager,
        depth: u32,
    ) -> Option<EvalVal> {
        self.eval_in_model_outcome(term, model, manager, depth)
            .value()
    }

    /// Evaluate `term` under `model`.
    ///
    /// Runs the explicit frame stack described in the module documentation: a
    /// single loop that alternates between asking the innermost pending
    /// operator for its next operand and handing finished operand outcomes back
    /// to it.  Native stack usage is constant in the nesting depth of `term`.
    ///
    /// `depth` is the nesting depth `term` itself sits at, charged against
    /// [`ENCODE_DEPTH_LIMIT`].  Now that the walk is iterative that limit is no
    /// longer a stack bound — it is a plain *work* bound, with the visible
    /// outcome [`EvalOutcome::Undetermined`] for anything past it, which is the
    /// same answer the recursive version gave and therefore leaves the gate's
    /// verdict on deep terms unchanged.
    ///
    /// IMPORTANT: `model.get` is consulted only for *leaf* / opaque terms (the
    /// `Var` and fallback arms of [`Self::open_in_model`]).  Operator terms
    /// (`and` / `or` / `=` / `+` / …) are ALWAYS recomputed structurally from
    /// their children — never read back from the model cache.  `build_model`
    /// records the SAT core's Boolean value for every atom and gate, and when
    /// that core commits an inconsistent trail those cached values are exactly
    /// what must not be trusted (e.g. an `or` gate cached `true` while both
    /// disjuncts are `false`).  Recomputing from leaves is what makes this gate
    /// sound.
    pub(super) fn eval_in_model_outcome(
        &self,
        term: TermId,
        model: &Model,
        manager: &TermManager,
        depth: u32,
    ) -> EvalOutcome {
        let mut frames: Vec<Frame> = Vec::new();
        // Operand values of every frame on the stack, concatenated; a frame
        // owns `values[frame.base..]` while it is the innermost one.
        let mut values: Vec<EvalVal> = Vec::new();
        // A finished operand outcome travelling back to the frame that asked
        // for it.
        let mut carry: Option<EvalOutcome> = None;

        match self.open_in_model(term, model, manager, depth) {
            Opened::Done(outcome) => return outcome,
            Opened::Frame(frame) => frames.push(frame),
        }

        loop {
            let step = match frames.last_mut() {
                Some(top) => top.advance(&mut values, carry.take()),
                // Only the `Step::Done` arm below empties the stack, and it
                // returns; reaching here would mean the driver lost its root.
                None => return EvalOutcome::UNDETERMINED,
            };

            match step {
                Step::Need(child) => {
                    let child_depth = match frames.last() {
                        Some(top) => top.depth.saturating_add(1),
                        None => depth,
                    };
                    match self.open_in_model(child, model, manager, child_depth) {
                        Opened::Done(outcome) => carry = Some(outcome),
                        Opened::Frame(mut frame) => {
                            frame.base = values.len();
                            frames.push(frame);
                        }
                    }
                }
                Step::Done(outcome) => {
                    let Some(frame) = frames.pop() else {
                        return EvalOutcome::UNDETERMINED;
                    };
                    values.truncate(frame.base);
                    if frames.is_empty() {
                        return outcome;
                    }
                    carry = Some(outcome);
                }
            }
        }
    }

    /// Read one term: either it has an outcome on its own, or it opens a frame.
    ///
    /// This is the former recursive `eval_in_model`'s dispatch, minus the
    /// recursion: an arm that used to call itself now describes its operands to
    /// the driver instead of evaluating them.
    fn open_in_model(
        &self,
        term: TermId,
        model: &Model,
        manager: &TermManager,
        depth: u32,
    ) -> Opened {
        if depth > ENCODE_DEPTH_LIMIT {
            return Opened::Done(EvalOutcome::UNDETERMINED);
        }
        let Some(t) = manager.get(term) else {
            return Opened::Done(EvalOutcome::UNDETERMINED);
        };
        let sort = t.sort;
        match &t.kind {
            TermKind::True => Opened::Done(EvalOutcome::boolean(true)),
            TermKind::False => Opened::Done(EvalOutcome::boolean(false)),
            TermKind::IntConst(_) | TermKind::RealConst(_) => {
                Opened::Done(parse_value_term(term, manager))
            }
            TermKind::Var(_) => Opened::Done({
                // For a numeric variable, take the value from the ARITHMETIC
                // solver, not the built model.  `arith.value` returns `None` for
                // a variable the solver does not actually constrain, which makes
                // the whole evaluation inconclusive (never a false downgrade) —
                // exactly the variables `build_model` would have defaulted to 0.
                if sort == manager.sorts.int_sort || sort == manager.sorts.real_sort {
                    match self.arith.value(term) {
                        Some(n) => EvalOutcome::number(n),
                        None => EvalOutcome::UNDETERMINED,
                    }
                } else {
                    // Boolean / bit-vector / other: the model witness is fine
                    // (Booleans are exactly determined by the SAT assignment).
                    match model.get(term) {
                        Some(value_term) => parse_value_term(value_term, manager),
                        None => EvalOutcome::UNDETERMINED,
                    }
                }
            }),
            TermKind::Not(a) => Opened::Frame(Frame::unary(*a, EagerKind::Not, depth)),
            TermKind::And(args) => Opened::Frame(Frame::new(
                Op::Connective {
                    operands: args.clone(),
                    conjunction: true,
                },
                depth,
            )),
            TermKind::Or(args) => Opened::Frame(Frame::new(
                Op::Connective {
                    operands: args.clone(),
                    conjunction: false,
                },
                depth,
            )),
            TermKind::Implies(a, b) => Opened::Frame(Frame::new(
                Op::Implies {
                    antecedent: *a,
                    consequent: *b,
                    state: ImpliesState::Antecedent,
                },
                depth,
            )),
            TermKind::Ite(c, t, e) => Opened::Frame(Frame::new(
                Op::Ite {
                    cond: *c,
                    then_branch: *t,
                    else_branch: *e,
                    state: IteState::Cond,
                },
                depth,
            )),
            TermKind::Eq(a, b) => Opened::Frame(Frame::binary(*a, *b, EagerKind::Eq, depth)),
            // `distinct` is deliberately INCONCLUSIVE for the gate.  A model in
            // which two operands share a value does NOT reliably indicate a real
            // violation: the linear-arithmetic solver enforces disequalities by
            // case-splitting, not by pinning distinct witnesses in its LP model,
            // so `arith.value` routinely reports colliding integer values for a
            // genuinely satisfiable `distinct`.  Downgrading on that would turn
            // correct `Sat`s into spurious `Unknown`s; the gate targets violated
            // POSITIVE structure (a falsified equality or an all-false clause)
            // instead, which the arithmetic model represents faithfully.
            TermKind::Distinct(_) => Opened::Done(EvalOutcome::UNDETERMINED),
            TermKind::Add(args) => Opened::Frame(Frame::new(
                Op::Arith {
                    operands: args.clone(),
                    product: false,
                    acc: Rational64::from_integer(0),
                },
                depth,
            )),
            TermKind::Sub(a, b) => Opened::Frame(Frame::binary(*a, *b, EagerKind::Sub, depth)),
            TermKind::Mul(args) => Opened::Frame(Frame::new(
                Op::Arith {
                    operands: args.clone(),
                    product: true,
                    acc: Rational64::from_integer(1),
                },
                depth,
            )),
            TermKind::Neg(a) => Opened::Frame(Frame::unary(*a, EagerKind::Neg, depth)),
            TermKind::Lt(a, b) => Opened::Frame(Frame::binary(
                *a,
                *b,
                EagerKind::CmpStrict { less: true },
                depth,
            )),
            TermKind::Gt(a, b) => Opened::Frame(Frame::binary(
                *a,
                *b,
                EagerKind::CmpStrict { less: false },
                depth,
            )),
            TermKind::Le(a, b) => Opened::Frame(Frame::binary(
                *a,
                *b,
                EagerKind::CmpWeak { less: true },
                depth,
            )),
            TermKind::Ge(a, b) => Opened::Frame(Frame::binary(
                *a,
                *b,
                EagerKind::CmpWeak { less: false },
                depth,
            )),
            // Opaque leaves (uninterpreted applications, selects, …): the model
            // may pin a concrete value; otherwise inconclusive.
            _ => Opened::Done(match model.get(term) {
                Some(value_term) => parse_value_term(value_term, manager),
                None => EvalOutcome::UNDETERMINED,
            }),
        }
    }
}

/// Parse a constant value term (`IntConst` / `RealConst` / `True` / `False`)
/// into an outcome.
///
/// A non-constant term, or an integer constant outside `i64`, is
/// [`EvalOutcome::Undetermined`] rather than [`EvalOutcome::Unrepresentable`]:
/// a constant too wide for the evaluator's arithmetic is a property of the
/// *formula*, present before any model existed, and the recursive version has
/// always reported it inconclusive.  Treating it as a reason to downgrade would
/// make every formula that merely mentions a wide literal answer `Unknown`.
fn parse_value_term(term: TermId, manager: &TermManager) -> EvalOutcome {
    let Some(t) = manager.get(term) else {
        return EvalOutcome::UNDETERMINED;
    };
    match &t.kind {
        TermKind::True => EvalOutcome::boolean(true),
        TermKind::False => EvalOutcome::boolean(false),
        TermKind::IntConst(n) => match n.to_i64() {
            Some(v) => EvalOutcome::number(Rational64::from_integer(v)),
            None => EvalOutcome::UNDETERMINED,
        },
        TermKind::RealConst(r) => EvalOutcome::number(*r),
        _ => EvalOutcome::UNDETERMINED,
    }
}

#[cfg(test)]
mod tests {
    use super::{ENCODE_DEPTH_LIMIT, EvalOutcome, EvalVal};
    use crate::solver::Solver;
    use crate::solver::types::Model;
    use num_rational::Rational64;
    use oxiz_core::ast::{TermId, TermManager};

    /// `2^62` fits `i64`, but `2^62 + 2^62 = 2^63` does not — the smallest
    /// round number that makes `Rational64` addition overflow.
    const HALF_MAX: i64 = 1 << 62;

    /// The stack the in-budget regression tests in this module run their
    /// evaluation on.  1 MiB is what an embedder's worker thread typically
    /// gets, and a native stack overflow aborts the process — so "the closure
    /// returned at all" is itself part of each assertion.
    const WORKER_STACK: usize = 1 << 20;

    /// The stack the *past-the-budget* test below runs on.  It is an eighth of
    /// [`WORKER_STACK`], paired with an eighth of that test's depth, so the
    /// bytes-per-frame threshold the test really pins (~21 B per level) is
    /// unchanged while the term the test has to build — and keep interned —
    /// shrinks by 8x.  Never change one of the two without the other.
    const DEEP_WORKER_STACK: usize = 1 << 17;

    /// Run `body` on a fresh thread with `stack_size` bytes of stack.
    fn on_stack<T: Send + 'static>(
        stack_size: usize,
        body: impl FnOnce() -> T + Send + 'static,
    ) -> T {
        std::thread::Builder::new()
            .stack_size(stack_size)
            .spawn(body)
            .expect("spawn worker thread")
            .join()
            .expect("worker thread must return, not abort")
    }

    /// Run `body` on a fresh [`WORKER_STACK`] thread and return its result.
    fn on_worker_stack<T: Send + 'static>(body: impl FnOnce() -> T + Send + 'static) -> T {
        on_stack(WORKER_STACK, body)
    }

    /// A solver holding exactly `assertions`, with an empty (but present)
    /// model, ready for the gate.
    fn solver_with(assertions: Vec<TermId>) -> Solver {
        let mut solver = Solver::new();
        solver.assertions = assertions;
        solver.model = Some(Model::new());
        solver
    }

    /// The gate's answer for a single assertion.
    fn gate_refuses(manager: &TermManager, assertion: TermId) -> bool {
        solver_with(vec![assertion]).model_refutes_assertions(manager)
    }

    /// The evaluator's outcome for a single term.
    fn outcome(manager: &TermManager, term: TermId) -> EvalOutcome {
        let solver = solver_with(Vec::new());
        let model = Model::new();
        solver.eval_in_model_outcome(term, &model, manager, 0)
    }

    /// An overflowing `+` under an assertion the model genuinely **violates**.
    ///
    /// `(< (+ 2^62 2^62) 0)` is false — `2^63` is positive — so the gate must
    /// refuse the model.  Unchecked, this wrapped to `i64::MIN < 0` in release
    /// and reported `true`, hiding the violation; in debug it aborted with
    /// `attempt to add with overflow` before answering anything at all.
    #[test]
    fn overflowing_addition_never_hides_a_violated_assertion() {
        let mut manager = TermManager::new();
        let half = manager.mk_int(HALF_MAX);
        let sum = manager.mk_add([half, half]);
        let zero = manager.mk_int(0);
        let assertion = manager.mk_lt(sum, zero);

        assert_eq!(outcome(&manager, sum), EvalOutcome::Unrepresentable);
        assert!(gate_refuses(&manager, assertion));
    }

    /// The same overflow under an assertion the model **satisfies**.
    ///
    /// `(>= (+ 2^62 2^62) 0)` is true, so refusing the model costs precision —
    /// the caller answers `Unknown` for a formula it could have called `Sat`.
    /// That is the deliberate direction: a `false` answer from the gate is
    /// consumed as "report `Sat`", and an assertion the evaluator could not
    /// evaluate is no evidence that the model satisfies it.  Unchecked, this
    /// wrapped the other way and refuted the model on garbage.
    #[test]
    fn overflowing_addition_never_vouches_for_a_model() {
        let mut manager = TermManager::new();
        let half = manager.mk_int(HALF_MAX);
        let sum = manager.mk_add([half, half]);
        let zero = manager.mk_int(0);
        let assertion = manager.mk_ge(sum, zero);

        assert!(gate_refuses(&manager, assertion));
    }

    /// Every arithmetic operator the evaluator folds is checked, not just `+`.
    #[test]
    fn every_arithmetic_operator_reports_overflow() {
        let mut manager = TermManager::new();
        let half = manager.mk_int(HALF_MAX);
        let two = manager.mk_int(2);
        let min = manager.mk_int(i64::MIN);
        let max = manager.mk_int(i64::MAX);

        let product = manager.mk_mul([half, two]);
        let difference = manager.mk_sub(min, max);
        let negation = manager.mk_neg(min);

        for term in [product, difference, negation] {
            assert_eq!(outcome(&manager, term), EvalOutcome::Unrepresentable);
        }
    }

    /// An overflow the surrounding formula never depends on must not leak out.
    ///
    /// `(or true (< (+ 2^62 2^62) 0))` is decided by its first disjunct, and
    /// `(and false …)` by its first conjunct, so neither may be downgraded.
    /// This is what the three-valued outcome buys over a "saw an overflow
    /// anywhere" flag.
    #[test]
    fn short_circuited_overflow_does_not_downgrade() {
        let mut manager = TermManager::new();
        let half = manager.mk_int(HALF_MAX);
        let sum = manager.mk_add([half, half]);
        let zero = manager.mk_int(0);
        let overflowing = manager.mk_lt(sum, zero);
        // `mk_or` / `mk_and` drop a literal `true` / `false` operand outright,
        // so the deciding operand has to be a comparison the *evaluator*
        // folds rather than one the builder does.
        let one = manager.mk_int(1);
        let truth = manager.mk_lt(zero, one);

        let disjunction = manager.mk_or([truth, overflowing]);
        assert_eq!(
            outcome(&manager, disjunction),
            EvalOutcome::Value(EvalVal::Bool(true))
        );
        assert!(!gate_refuses(&manager, disjunction));

        // `(and <overflow> false)` is `false` whatever the overflow was: the
        // gate refuses, but as a genuine refutation rather than a shrug.
        let falsehood = manager.mk_lt(one, zero);
        let conjunction = manager.mk_and([overflowing, falsehood]);
        assert_eq!(
            outcome(&manager, conjunction),
            EvalOutcome::Value(EvalVal::Bool(false))
        );
        assert!(gate_refuses(&manager, conjunction));
    }

    /// An unevaluable term that is *not* an overflow stays inconclusive.
    ///
    /// `distinct`, a numeric equality collision and a strict comparison at its
    /// boundary are all `Undetermined`, and none of them may downgrade a `Sat`
    /// — that distinction is the whole reason the outcome is three-valued and
    /// not two.
    #[test]
    fn ordinary_inconclusiveness_never_downgrades() {
        let mut manager = TermManager::new();
        let one = manager.mk_int(1);
        let zero = manager.mk_int(0);
        // Terms are hash-consed, so `mk_int(1)` twice is the *same* term and
        // `mk_eq` would fold it to `true`.  `(+ 0 1)` is a distinct term with
        // the same value, which is exactly the collision the gate distrusts.
        let other_one = manager.mk_add([zero, one]);

        let collision = manager.mk_eq(one, other_one);
        let boundary = manager.mk_lt(one, other_one);
        let unconstrained = manager.mk_var("x", manager.sorts.int_sort);
        let opaque = manager.mk_ge(unconstrained, one);

        for term in [collision, boundary, opaque] {
            assert_eq!(outcome(&manager, term), EvalOutcome::Undetermined);
            assert!(!gate_refuses(&manager, term));
        }
    }

    /// The evaluator still computes what it always did for ordinary terms.
    #[test]
    fn arithmetic_and_comparisons_still_fold() {
        let mut manager = TermManager::new();
        let two = manager.mk_int(2);
        let three = manager.mk_int(3);
        let seven = manager.mk_int(7);

        let sum = manager.mk_add([two, three]);
        assert_eq!(
            outcome(&manager, sum),
            EvalOutcome::Value(EvalVal::Num(Rational64::from_integer(5)))
        );
        let product = manager.mk_mul([two, three]);
        assert_eq!(
            outcome(&manager, product),
            EvalOutcome::Value(EvalVal::Num(Rational64::from_integer(6)))
        );
        let difference = manager.mk_sub(three, seven);
        assert_eq!(
            outcome(&manager, difference),
            EvalOutcome::Value(EvalVal::Num(Rational64::from_integer(-4)))
        );
        let negated = manager.mk_neg(seven);
        assert_eq!(
            outcome(&manager, negated),
            EvalOutcome::Value(EvalVal::Num(Rational64::from_integer(-7)))
        );

        let less = manager.mk_lt(sum, product);
        assert_eq!(
            outcome(&manager, less),
            EvalOutcome::Value(EvalVal::Bool(true))
        );
        let at_least = manager.mk_ge(difference, seven);
        assert_eq!(
            outcome(&manager, at_least),
            EvalOutcome::Value(EvalVal::Bool(false))
        );
        let implication = manager.mk_implies(less, at_least);
        assert_eq!(
            outcome(&manager, implication),
            EvalOutcome::Value(EvalVal::Bool(false))
        );
        let choice = manager.mk_ite(less, difference, seven);
        assert_eq!(
            outcome(&manager, choice),
            EvalOutcome::Value(EvalVal::Num(Rational64::from_integer(-4)))
        );
    }

    /// A deeply nested assertion is evaluated on the heap, not the native
    /// stack, and still produces the *exact* right verdict.
    ///
    /// The chain is built with an iterative loop (a recursive test helper would
    /// move the overflow into the test itself) and evaluated on a 1 MiB thread.
    /// Each level is one `Sub` frame, which the recursive evaluator paid for
    /// with a native frame; 1900 of them are well inside the depth budget and
    /// were comfortably enough to exhaust that stack.
    #[test]
    fn deeply_nested_assertion_evaluates_on_a_worker_stack() {
        // Track the real budget so the pin survives future limit changes:
        // stay just inside ENCODE_DEPTH_LIMIT (the chain is DEPTH levels deep,
        // and the `(>= chain 1)` assertion adds one more).
        const DEPTH: i64 = ENCODE_DEPTH_LIMIT as i64 - 50;

        let refused = on_worker_stack(|| {
            let mut manager = TermManager::new();
            let one = manager.mk_int(1);
            let mut chain = manager.mk_int(0);
            for _ in 0..DEPTH {
                chain = manager.mk_sub(chain, one);
            }
            // `chain` is exactly `-DEPTH`, so `(>= chain 0)` is false: the gate
            // must refute, and refute for the right reason.
            let value = outcome(&manager, chain);
            let assertion = manager.mk_ge(chain, one);
            (value, gate_refuses(&manager, assertion))
        });

        assert_eq!(
            refused.0,
            EvalOutcome::Value(EvalVal::Num(Rational64::from_integer(-DEPTH)))
        );
        assert!(refused.1);
    }

    /// A chain past the evaluator's depth budget answers `Undetermined` — the
    /// same answer the recursive version gave — rather than aborting the
    /// process on the way there.
    ///
    /// Stack and depth scale together (1 MiB/50k -> 128 KiB/6.25k): the
    /// ~21 B-per-frame threshold is the pin, so never raise one alone.
    #[test]
    fn assertion_past_the_depth_budget_stays_inconclusive() {
        const DEPTH: usize = 6_250;

        let (value, refused) = on_stack(DEEP_WORKER_STACK, || {
            let mut manager = TermManager::new();
            let one = manager.mk_int(1);
            let mut chain = manager.mk_int(0);
            for _ in 0..DEPTH {
                chain = manager.mk_sub(chain, one);
            }
            let assertion = manager.mk_ge(chain, one);
            (outcome(&manager, chain), gate_refuses(&manager, assertion))
        });

        assert_eq!(value, EvalOutcome::Undetermined);
        assert!(!refused);
    }
}
