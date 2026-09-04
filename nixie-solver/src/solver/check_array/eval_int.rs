//! Ground evaluation of integer expressions modulo the array read-over-write
//! axiom, for the array/arithmetic ordering check.
//!
//! # Failure direction
//!
//! Unlike its bit-vector sibling, "not evaluable" here is *incompleteness* and
//! not unsoundness, because an Int-sorted `select` is a first-class arithmetic
//! variable rather than an opaque leaf: `encode` registers it in `arith_terms`
//! and parses `(< (select a i) 5)` as a linear atom, so when this check declines
//! an assertion two backstops still reach a sound verdict – the alias-aware
//! read-over-write lemmas in `array_axioms.rs`, whose Int-sorted equalities do
//! enter the tableau, and `propagate_euf_equalities_to_arith`, which carries
//! congruence-derived equalities between arith-registered terms across with an
//! explanation.
//!
//! That is a structural argument about the shapes reachable today, not a gate
//! that says "an ordering check was skipped, so answer `Unknown`".  It is
//! therefore worth keeping the coverage here honest rather than relying on it.
//!
//! # Semantics that are easy to get wrong
//!
//! * `div` and `mod` are **Euclidean** on integers: the unique `q` with
//!   `a = b*q + r` and `0 <= r < |b|`, so `(div -7 2) = -4` and `(mod -7 2) = 1`
//!   – not Rust's `/` and `%`, which truncate towards zero.  They go through
//!   [`CheckedEuclid`], matching `nixie_core`'s `rewrite::arith` and its model
//!   evaluator, which both use `checked_div_euclid`.
//! * Division and modulo **by zero are uninterpreted**, not total.  SMT-LIB
//!   leaves `(div a 0)` a fixed but unspecified value, so folding it to anything
//!   at all would claim a fact the theory does not state – and this evaluator's
//!   answer feeds a check that reports `Unsat`, so a fabricated value could
//!   refute a satisfiable formula.  [`CheckedEuclid`] returns `None` at a zero
//!   divisor, which is exactly the required answer.  (This is the opposite of the
//!   bit-vector division family, where SMT-LIB *does* specify a total result.)
//! * `Div` and `Mod` are folded only for an **Int-sorted** node.  The same
//!   `TermKind` means exact rational division when the operands are Real, and
//!   Euclidean folding would be wrong for it.
//!
//! # Why the walk is iterative
//!
//! It folds the two sides of every `<`/`<=`/`>`/`>=` assertion, so its depth is
//! input-controlled, and it runs on whatever stack `check_sat`'s caller has.
//! With `opt-level = 0` the recursive version's frame measured about 1 KiB, so a
//! 1 MiB worker overflowed at roughly 1 000 levels.
//!
//! This evaluator had a **second**, worse depth source, and it is the reason the
//! conversion mattered more here than the structural nesting did.  The `Select`
//! arm does not descend into a sub-term: it *rewrites* the read through the
//! read-over-write axiom and re-dispatches on the result, which may be an
//! entirely unrelated term reached through the array-variable alias map.  Two
//! consequences:
//!
//! * The chain length is bounded by the number of alias *assertions*, not by any
//!   term's depth, so
//!   [`Solver::term_exceeds_encode_depth`](super::Solver::term_exceeds_encode_depth)
//!   – which bounds structural depth at
//!   [`ENCODE_DEPTH_LIMIT`](crate::solver::ENCODE_DEPTH_LIMIT) before `check`
//!   reaches the array checks – does not bound it at all.  Each link
//!   `(= b_k (store a 0 (select b_(k-1) 0)))` nests only four deep.  Two thousand
//!   such assertions aborted the process with the depth gate reporting nothing
//!   wrong.
//! * The chain can **cycle**.  `(= b (store a 0 (select b 0)))` rewrites
//!   `(select b 0)` to itself, and the recursive version followed that rewrite
//!   forever – as an infinite loop wherever the tail call was optimised into one,
//!   and as a stack overflow where it was not.  Either way `check` never
//!   returned, on two well-sorted assertions.  [`Solver::open_number`] carries
//!   the set of reads it has already rewritten along the current chain and
//!   answers "not evaluable" on a repeat.
//!
//! The frame/cursor shape is the one `model_eval.rs` and `check_fp.rs` use; see
//! `eval_bv.rs` for the shared description, including why the walk is
//! *heterogeneous* (an `ite` condition produces a truth value, everything else a
//! number) and why [`Step::Tail`] is what makes `ite` visit only the taken
//! branch.  There is deliberately no memo table.

use crate::prelude::*;
use nixie_core::ast::{TermId, TermKind, TermManager};
use num_bigint::BigInt;
use num_traits::CheckedEuclid;
use smallvec::SmallVec;

use super::Solver;

#[cfg(test)]
mod tests;

/// The array-variable alias map, as `collect_array_var_aliases` builds it.
type Aliases = FxHashMap<TermId, TermId>;

/// The operand list of an n-ary operator, matching `TermKind`'s own inline
/// capacity so the common case does not spill to the heap.
type Operands = SmallVec<[TermId; 4]>;

/// Which kind of value a position must produce.
#[derive(Clone, Copy)]
enum Position {
    /// An integer expression.
    Number,
    /// A condition, i.e. the first operand of an `ite`.
    Truth,
}

/// A folded value on its way back to the frame that asked for it.
enum Value {
    /// An integer value.
    Number(BigInt),
    /// A truth value.
    Truth(bool),
}

impl Value {
    /// The integer payload.
    ///
    /// `None` when a truth value arrived instead.  That cannot happen: a frame
    /// names the [`Position`] each of its operands is opened in, and `open` only
    /// ever produces a value of the position it was given.  It is written as an
    /// `Option` rather than an assertion because "not evaluable" is the honest
    /// answer for a shape this evaluator cannot make sense of, and it is the
    /// conservative one – it can only cost a refutation, where a fabricated value
    /// could invent one.
    fn number(self) -> Option<BigInt> {
        match self {
            Value::Number(value) => Some(value),
            Value::Truth(_) => None,
        }
    }

    /// The truth payload; `None` when a number arrived instead.  See
    /// [`Value::number`] for why this is an `Option`.
    fn truth(self) -> Option<bool> {
        match self {
            Value::Truth(truth) => Some(truth),
            Value::Number(_) => None,
        }
    }
}

/// An n-ary fold: `+` accumulating from zero, or `*` accumulating from one.
#[derive(Clone, Copy)]
enum Fold {
    Sum,
    Product,
}

impl Fold {
    /// The value of the fold over no operands.
    fn identity(self) -> BigInt {
        match self {
            Fold::Sum => BigInt::ZERO,
            Fold::Product => BigInt::from(1u8),
        }
    }

    /// Fold one more operand into the accumulator.
    ///
    /// Operands are combined left to right, in operand order, exactly as the
    /// recursive `sum += …` / `product *= …` loops did.  The arithmetic is exact
    /// `BigInt`, so the order cannot change the result, and it is kept anyway so
    /// that stays true of any future accumulator.
    fn combine(self, accumulator: BigInt, operand: BigInt) -> BigInt {
        match self {
            Fold::Sum => accumulator + operand,
            Fold::Product => accumulator * operand,
        }
    }
}

/// A binary integer operator.
#[derive(Clone, Copy)]
enum Binary {
    Sub,
    /// Euclidean integer division; see the module docs.
    Div,
    /// Euclidean remainder; see the module docs.
    Mod,
}

/// A comparison between two integer operands, usable as an `ite` condition.
#[derive(Clone, Copy)]
enum Compare {
    Eq,
    Lt,
    Le,
    Gt,
    Ge,
}

/// One pending operator on the frame stack, with its resume state.
enum Frame {
    /// An n-ary `+` or `*`, part way through its operand list.
    Nary {
        /// Which fold, and therefore which accumulator rule.
        fold: Fold,
        /// The whole operand list; `operands[next..]` is what remains.
        operands: Operands,
        /// Index of the next operand to open.
        next: usize,
        /// The operands folded so far.
        accumulator: BigInt,
    },
    /// A binary operator waiting for its **left** operand.
    Left {
        /// The operator to apply once both operands are in hand.
        op: Binary,
        /// The right operand, still a term.
        right: TermId,
    },
    /// A binary operator waiting for its **right** operand.
    Right {
        /// The operator to apply once the right operand arrives.
        op: Binary,
        /// The already-folded left operand.
        left: BigInt,
    },
    /// Arithmetic negation, waiting for its operand.
    Negate,
    /// Boolean negation, waiting for the condition it negates.
    Not,
    /// A comparison waiting for its **left** operand.
    CompareLeft {
        /// The comparison to apply.
        cmp: Compare,
        /// The right operand, still a term.
        right: TermId,
    },
    /// A comparison waiting for its **right** operand.
    CompareRight {
        /// The comparison to apply.
        cmp: Compare,
        /// The already-folded left operand.
        left: BigInt,
    },
    /// `and` / `or`, part way through its operands.
    Connective {
        /// `true` for `and` – the value that lets the scan continue, and the
        /// value of the connective over no operands.
        all: bool,
        /// The whole operand list; `operands[next..]` is what remains.
        operands: Operands,
        /// Index of the next operand to open.
        next: usize,
    },
    /// `ite`, waiting for its condition.  Only the taken branch is ever opened.
    Branch {
        /// The branch taken when the condition holds.
        then_branch: TermId,
        /// The branch taken when it does not.
        else_branch: TermId,
    },
}

/// What a frame does with a finished operand.
enum Step {
    /// Open `term`, with the frame pushed back on to receive it.
    Need {
        /// The operand to open.
        term: TermId,
        /// The shape it must produce.
        position: Position,
        /// The frame, to be pushed back.
        frame: Frame,
    },
    /// Open `term` in the frame's *place*: the frame is finished and is not
    /// pushed back.  This is `ite`'s short-circuit.
    Tail {
        /// The term to open.
        term: TermId,
        /// The shape it must produce.
        position: Position,
    },
    /// The frame is finished and produced a value.
    Done(Value),
}

/// What one term turns into when it is opened.
enum Opened {
    /// The term folds on its own, with no operands to visit.
    Value(Value),
    /// The term is an operator: push `frame` and open `first` next.
    Operator {
        /// The pending operator.
        frame: Frame,
        /// Its first operand.
        first: TermId,
        /// The shape that operand must produce.
        position: Position,
    },
}

/// The driver's position: a term waiting to be opened in a given shape, or a
/// folded value on its way back to the frame that asked for it.
enum Cursor {
    Open(TermId, Position),
    Close(Value),
}

impl Solver {
    /// Evaluate an integer expression after reducing array selects through the
    /// read-over-write axiom.
    ///
    /// `None` means the expression does not fold – an unbound variable, an
    /// operator with no arm here, a read the axiom does not decide, a rewrite
    /// chain that cycles, a `div`/`mod` by zero (which SMT-LIB leaves
    /// uninterpreted), or an `ite` whose condition does not fold.  Every one of
    /// those aborts the whole walk rather than the arm that saw it, matching the
    /// recursive version, whose every arm propagated the failure with `?` to the
    /// root.  `check_int_ordering_conflict` skips an assertion it cannot fold both
    /// sides of, so `None` is never a value standing in for one.
    pub(super) fn evaluate_int_expr_with_array_axiom(
        &self,
        term: TermId,
        aliases: &Aliases,
        manager: &TermManager,
    ) -> Option<BigInt> {
        let mut frames: Vec<Frame> = Vec::new();
        let mut cursor = Cursor::Open(term, Position::Number);

        loop {
            match cursor {
                Cursor::Open(current, position) => {
                    match self.open(current, position, aliases, manager)? {
                        Opened::Value(value) => cursor = Cursor::Close(value),
                        Opened::Operator {
                            frame,
                            first,
                            position,
                        } => {
                            frames.push(frame);
                            cursor = Cursor::Open(first, position);
                        }
                    }
                }
                Cursor::Close(value) => {
                    // An empty stack means the root itself just folded.  The root
                    // was opened in `Number` position, so this is a number.
                    let Some(frame) = frames.pop() else {
                        return value.number();
                    };
                    match frame.resume(value)? {
                        Step::Need {
                            term,
                            position,
                            frame,
                        } => {
                            frames.push(frame);
                            cursor = Cursor::Open(term, position);
                        }
                        Step::Tail { term, position } => cursor = Cursor::Open(term, position),
                        Step::Done(value) => cursor = Cursor::Close(value),
                    }
                }
            }
        }
    }

    /// Read one term in a given position: either it folds on its own, or it opens
    /// a frame.
    fn open(
        &self,
        term: TermId,
        position: Position,
        aliases: &Aliases,
        manager: &TermManager,
    ) -> Option<Opened> {
        match position {
            Position::Number => self.open_number(term, aliases, manager),
            Position::Truth => open_truth(&manager.get(term)?.kind),
        }
    }

    /// Read a term that must produce an integer value.
    ///
    /// This is the former recursive evaluator's dispatch, minus the recursion.
    /// The `Select` arm's rewrite was a *tail* call there, so it becomes this
    /// function's own loop: keep rewriting the read while the axiom applies, and
    /// dispatch on whatever the rewriting lands on.
    ///
    /// `rewritten` is what makes that loop terminate.  It holds the reads already
    /// rewritten **on this chain** – a chain is one root-to-leaf path, so a
    /// per-call set is exactly the right scope: the same read reached again from a
    /// different operand position gets a fresh set and still folds.  A repeat
    /// within one chain can only mean the alias map sends the rewriting round in a
    /// circle, which no number of further steps will resolve.
    ///
    /// The catch-all is reached by `Var`, `RealConst`, a Real-sorted `div`/`mod`,
    /// and every string, datatype and floating-point kind.  It is a catch-all
    /// rather than an exhaustive listing because `TermKind` has well over a
    /// hundred variants.  Reaching it costs the ordering check a possible
    /// refutation and can never invent one.
    fn open_number(
        &self,
        term: TermId,
        aliases: &Aliases,
        manager: &TermManager,
    ) -> Option<Opened> {
        let mut current = term;
        let mut rewritten: FxHashSet<TermId> = FxHashSet::default();
        loop {
            let data = manager.get(current)?;
            // `div` and `mod` mean Euclidean integer division only at Int sort;
            // the same kinds at Real sort are exact rational division, which this
            // evaluator does not fold.
            let int_sorted = data.sort == manager.sorts.int_sort;
            let binary = |op: Binary, left: TermId, right: TermId| {
                Some(Opened::Operator {
                    frame: Frame::Left { op, right },
                    first: left,
                    position: Position::Number,
                })
            };
            match &data.kind {
                TermKind::IntConst(value) => {
                    return Some(Opened::Value(Value::Number(value.clone())));
                }
                TermKind::Add(args) => return Some(open_nary(Fold::Sum, args)),
                TermKind::Mul(args) => return Some(open_nary(Fold::Product, args)),
                TermKind::Sub(lhs, rhs) => return binary(Binary::Sub, *lhs, *rhs),
                TermKind::Div(lhs, rhs) if int_sorted => return binary(Binary::Div, *lhs, *rhs),
                TermKind::Mod(lhs, rhs) if int_sorted => return binary(Binary::Mod, *lhs, *rhs),
                TermKind::Neg(arg) => {
                    return Some(Opened::Operator {
                        frame: Frame::Negate,
                        first: *arg,
                        position: Position::Number,
                    });
                }
                TermKind::Ite(cond, then_branch, else_branch) => {
                    return Some(Opened::Operator {
                        frame: Frame::Branch {
                            then_branch: *then_branch,
                            else_branch: *else_branch,
                        },
                        first: *cond,
                        position: Position::Truth,
                    });
                }
                TermKind::Select(_, _) => {
                    if !rewritten.insert(current) {
                        return None;
                    }
                    current = self.resolve_read(current, aliases, manager)?;
                }
                _ => return None,
            }
        }
    }

    /// Apply the read-over-write axiom to one read, through the alias map when
    /// there is one.
    ///
    /// The alias-aware form is tried first and falls back to the plain axiom,
    /// which is what handles reads of a directly nested store.
    fn resolve_read(
        &self,
        read: TermId,
        aliases: &Aliases,
        manager: &TermManager,
    ) -> Option<TermId> {
        if aliases.is_empty() {
            self.evaluate_select_axiom(read, manager)
        } else {
            self.evaluate_select_axiom_with_alias(read, aliases, manager)
                .or_else(|| self.evaluate_select_axiom(read, manager))
        }
    }
}

impl Frame {
    /// Hand a finished operand to this frame and get its next step.
    fn resume(self, value: Value) -> Option<Step> {
        match self {
            Frame::Nary {
                fold,
                operands,
                next,
                accumulator,
            } => {
                let accumulator = fold.combine(accumulator, value.number()?);
                match operands.get(next).copied() {
                    Some(term) => Some(Step::Need {
                        term,
                        position: Position::Number,
                        frame: Frame::Nary {
                            fold,
                            operands,
                            next: next + 1,
                            accumulator,
                        },
                    }),
                    None => Some(Step::Done(Value::Number(accumulator))),
                }
            }
            Frame::Left { op, right } => Some(Step::Need {
                term: right,
                position: Position::Number,
                frame: Frame::Right {
                    op,
                    left: value.number()?,
                },
            }),
            Frame::Right { op, left } => Some(Step::Done(Value::Number(apply_binary(
                op,
                left,
                value.number()?,
            )?))),
            Frame::Negate => Some(Step::Done(Value::Number(-value.number()?))),
            Frame::Not => Some(Step::Done(Value::Truth(!value.truth()?))),
            Frame::CompareLeft { cmp, right } => Some(Step::Need {
                term: right,
                position: Position::Number,
                frame: Frame::CompareRight {
                    cmp,
                    left: value.number()?,
                },
            }),
            Frame::CompareRight { cmp, left } => Some(Step::Done(Value::Truth(apply_compare(
                cmp,
                &left,
                &value.number()?,
            )))),
            Frame::Connective {
                all,
                operands,
                next,
            } => {
                let truth = value.truth()?;
                if truth != all {
                    // A `false` conjunct or a `true` disjunct decides the whole
                    // connective; the remaining operands are never opened.
                    return Some(Step::Done(Value::Truth(truth)));
                }
                match operands.get(next).copied() {
                    Some(term) => Some(Step::Need {
                        term,
                        position: Position::Truth,
                        frame: Frame::Connective {
                            all,
                            operands,
                            next: next + 1,
                        },
                    }),
                    None => Some(Step::Done(Value::Truth(all))),
                }
            }
            Frame::Branch {
                then_branch,
                else_branch,
            } => {
                let taken = if value.truth()? {
                    then_branch
                } else {
                    else_branch
                };
                // The untaken branch is never opened, and this frame is done, so
                // the taken branch takes its place on the stack.
                Some(Step::Tail {
                    term: taken,
                    position: Position::Number,
                })
            }
        }
    }
}

/// Read a term that must produce a truth value, i.e. an `ite` condition.
///
/// The supported conditions are the ones decidable from ground integer
/// arithmetic alone: the two Boolean literals, `not`, `and`, `or`, and the five
/// integer relations.
///
/// A Boolean *variable* is deliberately absent: nothing here binds one, so it
/// could only be guessed.  `Eq` opens both sides in [`Position::Number`], so an
/// equality between two Boolean operands simply does not fold, which is the
/// conservative answer.
fn open_truth(kind: &TermKind) -> Option<Opened> {
    let compare = |cmp: Compare, left: TermId, right: TermId| {
        Some(Opened::Operator {
            frame: Frame::CompareLeft { cmp, right },
            first: left,
            position: Position::Number,
        })
    };
    match kind {
        TermKind::True => Some(Opened::Value(Value::Truth(true))),
        TermKind::False => Some(Opened::Value(Value::Truth(false))),
        TermKind::Not(a) => Some(Opened::Operator {
            frame: Frame::Not,
            first: *a,
            position: Position::Truth,
        }),
        TermKind::And(args) => Some(open_connective(true, args)),
        TermKind::Or(args) => Some(open_connective(false, args)),
        TermKind::Eq(a, b) => compare(Compare::Eq, *a, *b),
        TermKind::Lt(a, b) => compare(Compare::Lt, *a, *b),
        TermKind::Le(a, b) => compare(Compare::Le, *a, *b),
        TermKind::Gt(a, b) => compare(Compare::Gt, *a, *b),
        TermKind::Ge(a, b) => compare(Compare::Ge, *a, *b),
        _ => None,
    }
}

/// Open an n-ary `+` or `*`.
///
/// An empty operand list folds to the identity outright – the value the recursive
/// accumulator started from and never added to.
fn open_nary(fold: Fold, args: &Operands) -> Opened {
    match args.first().copied() {
        None => Opened::Value(Value::Number(fold.identity())),
        Some(first) => Opened::Operator {
            frame: Frame::Nary {
                fold,
                operands: args.clone(),
                next: 1,
                accumulator: fold.identity(),
            },
            first,
            position: Position::Number,
        },
    }
}

/// Open an `and` (`all = true`) or `or` (`all = false`).
///
/// An empty operand list folds to `all`, the identity of the connective.
fn open_connective(all: bool, args: &Operands) -> Opened {
    match args.first().copied() {
        None => Opened::Value(Value::Truth(all)),
        Some(first) => Opened::Operator {
            frame: Frame::Connective {
                all,
                operands: args.clone(),
                next: 1,
            },
            first,
            position: Position::Truth,
        },
    }
}

/// Compare two folded operands.  Total: every pair of integers is ordered.
fn apply_compare(cmp: Compare, left: &BigInt, right: &BigInt) -> bool {
    match cmp {
        Compare::Eq => left == right,
        Compare::Lt => left < right,
        Compare::Le => left <= right,
        Compare::Gt => left > right,
        Compare::Ge => left >= right,
    }
}

/// Apply a binary operator to two folded operands.
///
/// `div` and `mod` are Euclidean and are *not* folded at a zero divisor, which
/// [`CheckedEuclid`] reports as `None`; see the module docs for why inventing a
/// value there would be unsound.
fn apply_binary(op: Binary, left: BigInt, right: BigInt) -> Option<BigInt> {
    match op {
        Binary::Sub => Some(left - right),
        Binary::Div => left.checked_div_euclid(&right),
        Binary::Mod => left.checked_rem_euclid(&right),
    }
}
