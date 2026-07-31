//! Iterative `Clone`, `PartialEq` and [`std::hash::Hash`] for [`SeqExpr`]/[`IntExpr`].
//!
//! Split out of `sequence/mod.rs` to keep that file well under the
//! 2000-line limit -- see [`super::SeqExpr`]'s depth invariant for why these
//! three are hand-written here instead of derived.

use super::{IntExpr, SeqExpr};

/// One step of the iterative [`Clone`] walk for the mutually recursive
/// [`SeqExpr`]/[`IntExpr`] pair. `Enter` expands a node's operands; `Reduce`
/// rebuilds it once they are cloned. Both sides share one task stack, the
/// same shape as [`SeqEvalTask`].
enum SeqCloneTask<'a> {
    /// Clone this sequence node's operands.
    EnterSeq(&'a SeqExpr),
    /// Clone this integer node's operands.
    EnterInt(&'a IntExpr),
    /// Rebuild a sequence node from its already-cloned operands.
    ReduceSeq(&'a SeqExpr),
    /// Rebuild an integer node from its already-cloned operands.
    ReduceInt(&'a IntExpr),
}

/// Task stack plus the two heterogeneous result slots cloned operands land
/// in, mirroring [`SeqEvalState`].
#[derive(Default)]
struct SeqCloneState<'a> {
    /// Pending work, innermost operand on top.
    tasks: Vec<SeqCloneTask<'a>>,
    /// Cloned sequence operands, in evaluation order.
    seq_results: Vec<SeqExpr>,
    /// Cloned integer operands, in evaluation order.
    int_results: Vec<IntExpr>,
}

impl SeqCloneState<'_> {
    /// Detach the last `count` cloned sequence operands, oldest first.
    fn take_seq(&mut self, count: usize) -> Vec<SeqExpr> {
        let at = self.seq_results.len().saturating_sub(count);
        self.seq_results.split_off(at)
    }

    /// Detach the last `count` cloned integer operands, oldest first.
    fn take_int(&mut self, count: usize) -> Vec<IntExpr> {
        let at = self.int_results.len().saturating_sub(count);
        self.int_results.split_off(at)
    }
}

/// Queue `expr`'s operands for cloning, left to right -- the same order (and
/// the same operators) as [`push_seq_operands`].
fn push_seq_clone_operands<'a>(expr: &'a SeqExpr, tasks: &mut Vec<SeqCloneTask<'a>>) {
    match expr {
        SeqExpr::Var(_) | SeqExpr::Literal(_) => {}
        SeqExpr::Concat(parts) => {
            tasks.extend(parts.iter().rev().map(SeqCloneTask::EnterSeq));
        }
        SeqExpr::Extract(s, start, len) => {
            tasks.push(SeqCloneTask::EnterInt(len));
            tasks.push(SeqCloneTask::EnterInt(start));
            tasks.push(SeqCloneTask::EnterSeq(s));
        }
        SeqExpr::Replace(s, from, to) | SeqExpr::ReplaceAll(s, from, to) => {
            tasks.push(SeqCloneTask::EnterSeq(to));
            tasks.push(SeqCloneTask::EnterSeq(from));
            tasks.push(SeqCloneTask::EnterSeq(s));
        }
        SeqExpr::ReplaceRe(s, _, to) => {
            tasks.push(SeqCloneTask::EnterSeq(to));
            tasks.push(SeqCloneTask::EnterSeq(s));
        }
        SeqExpr::At(s, i) => {
            tasks.push(SeqCloneTask::EnterInt(i));
            tasks.push(SeqCloneTask::EnterSeq(s));
        }
        SeqExpr::Unit(code) => {
            tasks.push(SeqCloneTask::EnterInt(code));
        }
        SeqExpr::Reverse(s) => {
            tasks.push(SeqCloneTask::EnterSeq(s));
        }
    }
}

/// [`push_seq_clone_operands`] for the integer side.
fn push_int_clone_operands<'a>(expr: &'a IntExpr, tasks: &mut Vec<SeqCloneTask<'a>>) {
    match expr {
        IntExpr::Var(_) | IntExpr::Literal(_) => {}
        IntExpr::Length(s) | IntExpr::ToCode(s) | IntExpr::ToInt(s) => {
            tasks.push(SeqCloneTask::EnterSeq(s));
        }
        IntExpr::IndexOf(haystack, needle, start)
        | IntExpr::LastIndexOf(haystack, needle, start) => {
            tasks.push(SeqCloneTask::EnterInt(start));
            tasks.push(SeqCloneTask::EnterSeq(needle));
            tasks.push(SeqCloneTask::EnterSeq(haystack));
        }
        IntExpr::Add(terms) => {
            tasks.extend(terms.iter().rev().map(SeqCloneTask::EnterInt));
        }
        IntExpr::Sub(lhs, rhs) => {
            tasks.push(SeqCloneTask::EnterInt(rhs));
            tasks.push(SeqCloneTask::EnterInt(lhs));
        }
    }
}

/// Drain the task stack, leaving every cloned operand's value in `state`.
///
/// The root node itself is never pushed as a task: its reduction is
/// performed by the public entry point, which returns the value directly.
fn run_seq_clone(state: &mut SeqCloneState<'_>) {
    while let Some(task) = state.tasks.pop() {
        match task {
            SeqCloneTask::EnterSeq(expr) => {
                state.tasks.push(SeqCloneTask::ReduceSeq(expr));
                push_seq_clone_operands(expr, &mut state.tasks);
            }
            SeqCloneTask::EnterInt(expr) => {
                state.tasks.push(SeqCloneTask::ReduceInt(expr));
                push_int_clone_operands(expr, &mut state.tasks);
            }
            SeqCloneTask::ReduceSeq(expr) => {
                let value = reduce_seq_clone(expr, state);
                state.seq_results.push(value);
            }
            SeqCloneTask::ReduceInt(expr) => {
                let value = reduce_int_clone(expr, state);
                state.int_results.push(value);
            }
        }
    }
}

/// Rebuild one sequence node from its already-cloned operands.
fn reduce_seq_clone(expr: &SeqExpr, state: &mut SeqCloneState<'_>) -> SeqExpr {
    /// A childless stand-in for an operand that was, impossibly, absent.
    fn seq_placeholder() -> SeqExpr {
        SeqExpr::Var(0)
    }
    /// The integer-side stand-in.
    fn int_placeholder() -> IntExpr {
        IntExpr::Var(0)
    }
    match expr {
        SeqExpr::Var(v) => SeqExpr::Var(*v),
        SeqExpr::Literal(s) => SeqExpr::Literal(s.clone()),
        SeqExpr::Concat(parts) => SeqExpr::Concat(state.take_seq(parts.len())),
        SeqExpr::Extract(..) => {
            let mut seq = state.take_seq(1);
            let mut ints = state.take_int(2);
            let len = ints.pop().unwrap_or_else(int_placeholder);
            let start = ints.pop().unwrap_or_else(int_placeholder);
            let s = seq.pop().unwrap_or_else(seq_placeholder);
            SeqExpr::Extract(Box::new(s), Box::new(start), Box::new(len))
        }
        SeqExpr::Replace(..) | SeqExpr::ReplaceAll(..) => {
            let mut seq = state.take_seq(3);
            let to = seq.pop().unwrap_or_else(seq_placeholder);
            let from = seq.pop().unwrap_or_else(seq_placeholder);
            let s = seq.pop().unwrap_or_else(seq_placeholder);
            if matches!(expr, SeqExpr::Replace(..)) {
                SeqExpr::Replace(Box::new(s), Box::new(from), Box::new(to))
            } else {
                SeqExpr::ReplaceAll(Box::new(s), Box::new(from), Box::new(to))
            }
        }
        SeqExpr::ReplaceRe(_, regex_id, _) => {
            let mut seq = state.take_seq(2);
            let to = seq.pop().unwrap_or_else(seq_placeholder);
            let s = seq.pop().unwrap_or_else(seq_placeholder);
            SeqExpr::ReplaceRe(Box::new(s), *regex_id, Box::new(to))
        }
        SeqExpr::At(..) => {
            let mut seq = state.take_seq(1);
            let mut ints = state.take_int(1);
            let i = ints.pop().unwrap_or_else(int_placeholder);
            let s = seq.pop().unwrap_or_else(seq_placeholder);
            SeqExpr::At(Box::new(s), Box::new(i))
        }
        SeqExpr::Unit(_) => {
            let mut ints = state.take_int(1);
            let code = ints.pop().unwrap_or_else(int_placeholder);
            SeqExpr::Unit(Box::new(code))
        }
        SeqExpr::Reverse(_) => {
            let mut seq = state.take_seq(1);
            let s = seq.pop().unwrap_or_else(seq_placeholder);
            SeqExpr::Reverse(Box::new(s))
        }
    }
}

/// Rebuild one integer node from its already-cloned operands.
fn reduce_int_clone(expr: &IntExpr, state: &mut SeqCloneState<'_>) -> IntExpr {
    /// A childless stand-in for an operand that was, impossibly, absent.
    fn seq_placeholder() -> SeqExpr {
        SeqExpr::Var(0)
    }
    /// The integer-side stand-in.
    fn int_placeholder() -> IntExpr {
        IntExpr::Var(0)
    }
    match expr {
        IntExpr::Var(v) => IntExpr::Var(*v),
        IntExpr::Literal(n) => IntExpr::Literal(*n),
        IntExpr::Length(_) => {
            let mut seq = state.take_seq(1);
            IntExpr::Length(Box::new(seq.pop().unwrap_or_else(seq_placeholder)))
        }
        IntExpr::ToCode(_) => {
            let mut seq = state.take_seq(1);
            IntExpr::ToCode(Box::new(seq.pop().unwrap_or_else(seq_placeholder)))
        }
        IntExpr::ToInt(_) => {
            let mut seq = state.take_seq(1);
            IntExpr::ToInt(Box::new(seq.pop().unwrap_or_else(seq_placeholder)))
        }
        IntExpr::IndexOf(..) | IntExpr::LastIndexOf(..) => {
            let mut seq = state.take_seq(2);
            let mut ints = state.take_int(1);
            let start = ints.pop().unwrap_or_else(int_placeholder);
            let needle = seq.pop().unwrap_or_else(seq_placeholder);
            let haystack = seq.pop().unwrap_or_else(seq_placeholder);
            if matches!(expr, IntExpr::IndexOf(..)) {
                IntExpr::IndexOf(Box::new(haystack), Box::new(needle), Box::new(start))
            } else {
                IntExpr::LastIndexOf(Box::new(haystack), Box::new(needle), Box::new(start))
            }
        }
        IntExpr::Add(terms) => IntExpr::Add(state.take_int(terms.len())),
        IntExpr::Sub(..) => {
            let mut ints = state.take_int(2);
            let rhs = ints.pop().unwrap_or_else(int_placeholder);
            let lhs = ints.pop().unwrap_or_else(int_placeholder);
            IntExpr::Sub(Box::new(lhs), Box::new(rhs))
        }
    }
}

impl Clone for SeqExpr {
    /// Iterative clone.
    ///
    /// The derived recursive `Clone` walked the mutually recursive
    /// `SeqExpr`/`IntExpr` pair with one native call frame per nesting level
    /// -- the same hazard the [`Drop`] impls above exist to avoid, just
    /// triggered by a different standard-library entry point (`.clone()` /
    /// `#[derive(Clone)]` callers). Driven by the same explicit task stack
    /// shape as `SeqEvaluator::eval_seq`.
    fn clone(&self) -> Self {
        let mut state = SeqCloneState::default();
        push_seq_clone_operands(self, &mut state.tasks);
        run_seq_clone(&mut state);
        reduce_seq_clone(self, &mut state)
    }
}

impl Clone for IntExpr {
    /// Iterative for the same reason as [`SeqExpr`]'s.
    fn clone(&self) -> Self {
        let mut state = SeqCloneState::default();
        push_int_clone_operands(self, &mut state.tasks);
        run_seq_clone(&mut state);
        reduce_int_clone(self, &mut state)
    }
}

/// A pending comparison for the mutually recursive [`SeqExpr`]/[`IntExpr`]
/// pair's iterative [`PartialEq`].
enum SeqEqTask<'a> {
    /// Compare two sequence sub-expressions.
    Seq(&'a SeqExpr, &'a SeqExpr),
    /// Compare two integer sub-expressions.
    Int(&'a IntExpr, &'a IntExpr),
}

/// Drain an equality worklist, returning whether every queued pair compared
/// equal.
///
/// Shared by [`SeqExpr`]'s and [`IntExpr`]'s [`PartialEq`] impls, since a
/// comparison started on one side routinely needs to compare operands on the
/// other. Each inner `match` is exhaustive over its node's variants on
/// purpose, mirroring `InterpolantTerm` (`oxiz-proof/src/craig/term.rs`): a
/// new variant is a compile error here, not a silent "not equal".
fn drain_seq_eq_worklist(worklist: &mut Vec<SeqEqTask<'_>>) -> bool {
    /// Queue every positional sequence child pair, left to right.
    fn push_seq_pairs<'a>(
        worklist: &mut Vec<SeqEqTask<'a>>,
        lhs: &'a [SeqExpr],
        rhs: &'a [SeqExpr],
    ) {
        worklist.extend(
            lhs.iter()
                .zip(rhs.iter())
                .rev()
                .map(|(x, y)| SeqEqTask::Seq(x, y)),
        );
    }
    /// Queue every positional integer child pair, left to right.
    fn push_int_pairs<'a>(
        worklist: &mut Vec<SeqEqTask<'a>>,
        lhs: &'a [IntExpr],
        rhs: &'a [IntExpr],
    ) {
        worklist.extend(
            lhs.iter()
                .zip(rhs.iter())
                .rev()
                .map(|(x, y)| SeqEqTask::Int(x, y)),
        );
    }

    while let Some(task) = worklist.pop() {
        match task {
            SeqEqTask::Seq(a, b) => match a {
                SeqExpr::Var(x) => {
                    let SeqExpr::Var(y) = b else { return false };
                    if x != y {
                        return false;
                    }
                }
                SeqExpr::Literal(x) => {
                    let SeqExpr::Literal(y) = b else { return false };
                    if x != y {
                        return false;
                    }
                }
                SeqExpr::Concat(xs) => {
                    let SeqExpr::Concat(ys) = b else { return false };
                    if xs.len() != ys.len() {
                        return false;
                    }
                    push_seq_pairs(worklist, xs, ys);
                }
                SeqExpr::Extract(s1, start1, len1) => {
                    let SeqExpr::Extract(s2, start2, len2) = b else {
                        return false;
                    };
                    worklist.push(SeqEqTask::Int(len1, len2));
                    worklist.push(SeqEqTask::Int(start1, start2));
                    worklist.push(SeqEqTask::Seq(s1, s2));
                }
                SeqExpr::Replace(s1, from1, to1) => {
                    let SeqExpr::Replace(s2, from2, to2) = b else {
                        return false;
                    };
                    worklist.push(SeqEqTask::Seq(to1, to2));
                    worklist.push(SeqEqTask::Seq(from1, from2));
                    worklist.push(SeqEqTask::Seq(s1, s2));
                }
                SeqExpr::ReplaceAll(s1, from1, to1) => {
                    let SeqExpr::ReplaceAll(s2, from2, to2) = b else {
                        return false;
                    };
                    worklist.push(SeqEqTask::Seq(to1, to2));
                    worklist.push(SeqEqTask::Seq(from1, from2));
                    worklist.push(SeqEqTask::Seq(s1, s2));
                }
                SeqExpr::ReplaceRe(s1, id1, to1) => {
                    let SeqExpr::ReplaceRe(s2, id2, to2) = b else {
                        return false;
                    };
                    if id1 != id2 {
                        return false;
                    }
                    worklist.push(SeqEqTask::Seq(to1, to2));
                    worklist.push(SeqEqTask::Seq(s1, s2));
                }
                SeqExpr::At(s1, i1) => {
                    let SeqExpr::At(s2, i2) = b else { return false };
                    worklist.push(SeqEqTask::Int(i1, i2));
                    worklist.push(SeqEqTask::Seq(s1, s2));
                }
                SeqExpr::Unit(c1) => {
                    let SeqExpr::Unit(c2) = b else { return false };
                    worklist.push(SeqEqTask::Int(c1, c2));
                }
                SeqExpr::Reverse(s1) => {
                    let SeqExpr::Reverse(s2) = b else {
                        return false;
                    };
                    worklist.push(SeqEqTask::Seq(s1, s2));
                }
            },
            SeqEqTask::Int(a, b) => match a {
                IntExpr::Var(x) => {
                    let IntExpr::Var(y) = b else { return false };
                    if x != y {
                        return false;
                    }
                }
                IntExpr::Literal(x) => {
                    let IntExpr::Literal(y) = b else { return false };
                    if x != y {
                        return false;
                    }
                }
                IntExpr::Length(s1) => {
                    let IntExpr::Length(s2) = b else { return false };
                    worklist.push(SeqEqTask::Seq(s1, s2));
                }
                IntExpr::ToCode(s1) => {
                    let IntExpr::ToCode(s2) = b else { return false };
                    worklist.push(SeqEqTask::Seq(s1, s2));
                }
                IntExpr::ToInt(s1) => {
                    let IntExpr::ToInt(s2) = b else { return false };
                    worklist.push(SeqEqTask::Seq(s1, s2));
                }
                IntExpr::IndexOf(h1, n1, st1) => {
                    let IntExpr::IndexOf(h2, n2, st2) = b else {
                        return false;
                    };
                    worklist.push(SeqEqTask::Int(st1, st2));
                    worklist.push(SeqEqTask::Seq(n1, n2));
                    worklist.push(SeqEqTask::Seq(h1, h2));
                }
                IntExpr::LastIndexOf(h1, n1, st1) => {
                    let IntExpr::LastIndexOf(h2, n2, st2) = b else {
                        return false;
                    };
                    worklist.push(SeqEqTask::Int(st1, st2));
                    worklist.push(SeqEqTask::Seq(n1, n2));
                    worklist.push(SeqEqTask::Seq(h1, h2));
                }
                IntExpr::Add(xs) => {
                    let IntExpr::Add(ys) = b else { return false };
                    if xs.len() != ys.len() {
                        return false;
                    }
                    push_int_pairs(worklist, xs, ys);
                }
                IntExpr::Sub(l1, r1) => {
                    let IntExpr::Sub(l2, r2) = b else {
                        return false;
                    };
                    worklist.push(SeqEqTask::Int(r1, r2));
                    worklist.push(SeqEqTask::Int(l1, l2));
                }
            },
        }
    }

    true
}

impl PartialEq for SeqExpr {
    /// Iterative structural equality; see `drain_seq_eq_worklist`.
    fn eq(&self, other: &Self) -> bool {
        drain_seq_eq_worklist(&mut vec![SeqEqTask::Seq(self, other)])
    }
}

impl Eq for SeqExpr {}

impl PartialEq for IntExpr {
    /// Iterative structural equality; see `drain_seq_eq_worklist`.
    fn eq(&self, other: &Self) -> bool {
        drain_seq_eq_worklist(&mut vec![SeqEqTask::Int(self, other)])
    }
}

impl Eq for IntExpr {}

impl SeqExpr {
    /// Stable per-variant tag mixed into [`std::hash::Hash`], consistent
    /// with the [`PartialEq`] above. Written out rather than derived from
    /// `mem::discriminant` so the value is a fixed, exhaustively-checked
    /// constant per variant.
    const fn hash_tag(&self) -> u8 {
        match self {
            Self::Var(_) => 0,
            Self::Literal(_) => 1,
            Self::Concat(_) => 2,
            Self::Extract(..) => 3,
            Self::Replace(..) => 4,
            Self::ReplaceAll(..) => 5,
            Self::ReplaceRe(..) => 6,
            Self::At(..) => 7,
            Self::Unit(_) => 8,
            Self::Reverse(_) => 9,
        }
    }
}

impl IntExpr {
    /// [`SeqExpr::hash_tag`] for the integer side. The two tag spaces are
    /// independent (a `SeqExpr` and an `IntExpr` are never compared to each
    /// other), so overlapping numeric values are harmless.
    const fn hash_tag(&self) -> u8 {
        match self {
            Self::Var(_) => 0,
            Self::Literal(_) => 1,
            Self::Length(_) => 2,
            Self::IndexOf(..) => 3,
            Self::LastIndexOf(..) => 4,
            Self::ToCode(_) => 5,
            Self::ToInt(_) => 6,
            Self::Add(_) => 7,
            Self::Sub(..) => 8,
        }
    }
}

/// One pending node of the iterative [`std::hash::Hash`] walk for the
/// mutually recursive [`SeqExpr`]/[`IntExpr`] pair.
enum SeqHashNode<'a> {
    /// A sequence sub-expression.
    Seq(&'a SeqExpr),
    /// An integer sub-expression.
    Int(&'a IntExpr),
}

/// Hash `root` and everything reachable from it, in the same left-to-right
/// order `drain_seq_eq_worklist` compares in -- which is what keeps
/// `a == b` implying equal hashes.
fn hash_seq_or_int<H: std::hash::Hasher>(root: SeqHashNode<'_>, state: &mut H) {
    // Brings `.hash()` into method-call scope for the leaf field types below.
    use std::hash::Hash as _;

    let mut stack = vec![root];

    while let Some(node) = stack.pop() {
        match node {
            SeqHashNode::Seq(expr) => {
                state.write_u8(expr.hash_tag());
                match expr {
                    SeqExpr::Var(v) => v.hash(state),
                    SeqExpr::Literal(s) => s.hash(state),
                    SeqExpr::Concat(xs) => {
                        state.write_usize(xs.len());
                        stack.extend(xs.iter().rev().map(SeqHashNode::Seq));
                    }
                    SeqExpr::Extract(s, start, len) => {
                        stack.push(SeqHashNode::Int(len));
                        stack.push(SeqHashNode::Int(start));
                        stack.push(SeqHashNode::Seq(s));
                    }
                    SeqExpr::Replace(s, from, to) | SeqExpr::ReplaceAll(s, from, to) => {
                        stack.push(SeqHashNode::Seq(to));
                        stack.push(SeqHashNode::Seq(from));
                        stack.push(SeqHashNode::Seq(s));
                    }
                    SeqExpr::ReplaceRe(s, id, to) => {
                        id.hash(state);
                        stack.push(SeqHashNode::Seq(to));
                        stack.push(SeqHashNode::Seq(s));
                    }
                    SeqExpr::At(s, i) => {
                        stack.push(SeqHashNode::Int(i));
                        stack.push(SeqHashNode::Seq(s));
                    }
                    SeqExpr::Unit(code) => {
                        stack.push(SeqHashNode::Int(code));
                    }
                    SeqExpr::Reverse(s) => {
                        stack.push(SeqHashNode::Seq(s));
                    }
                }
            }
            SeqHashNode::Int(expr) => {
                state.write_u8(expr.hash_tag());
                match expr {
                    IntExpr::Var(v) => v.hash(state),
                    IntExpr::Literal(n) => n.hash(state),
                    IntExpr::Length(s) | IntExpr::ToCode(s) | IntExpr::ToInt(s) => {
                        stack.push(SeqHashNode::Seq(s));
                    }
                    IntExpr::IndexOf(haystack, needle, start)
                    | IntExpr::LastIndexOf(haystack, needle, start) => {
                        stack.push(SeqHashNode::Int(start));
                        stack.push(SeqHashNode::Seq(needle));
                        stack.push(SeqHashNode::Seq(haystack));
                    }
                    IntExpr::Add(xs) => {
                        state.write_usize(xs.len());
                        stack.extend(xs.iter().rev().map(SeqHashNode::Int));
                    }
                    IntExpr::Sub(lhs, rhs) => {
                        stack.push(SeqHashNode::Int(rhs));
                        stack.push(SeqHashNode::Int(lhs));
                    }
                }
            }
        }
    }
}

impl std::hash::Hash for SeqExpr {
    /// Iterative structural hashing, consistent with the [`PartialEq`]
    /// above; see `hash_seq_or_int`.
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        hash_seq_or_int(SeqHashNode::Seq(self), state);
    }
}

impl std::hash::Hash for IntExpr {
    /// Iterative for the same reason as [`SeqExpr`]'s.
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        hash_seq_or_int(SeqHashNode::Int(self), state);
    }
}
