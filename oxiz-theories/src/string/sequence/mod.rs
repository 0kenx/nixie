//! Sequence Operations for String Theory
//!
//! Implements SMT-LIB sequence operations for strings:
//! - seq.nth: Get character at index
//! - seq.extract: Get substring
//! - seq.replace: Replace first occurrence
//! - seq.replace_all: Replace all occurrences
//! - seq.at: Get single character
//! - seq.unit: Create singleton sequence
//! - seq.indexof: Find first occurrence
//! - seq.last_indexof: Find last occurrence

#[allow(unused_imports)]
use crate::prelude::*;

/// Sequence operation result
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum SeqResult {
    /// Concrete string result
    String(String),
    /// Concrete integer result
    Integer(i64),
    /// Symbolic expression
    Symbolic(SeqExpr),
    /// Error/undefined
    Undefined,
}

/// Symbolic sequence expression
///
/// # Depth invariant
///
/// There is deliberately no bound on how deep a `SeqExpr`/[`IntExpr`] may be:
/// the variants are public, so callers build values directly, and the two
/// types are mutually recursive. [`Clone`], [`PartialEq`] and
/// [`std::hash::Hash`] are therefore iterative -- see their impls below --
/// rather than derived, exactly like the [`Drop`] impl already in this file.
/// Do **not** replace any of them with a `derive` (`Hash` in particular must
/// stay consistent with the hand-written `PartialEq`, which clippy's
/// `derived_hash_with_manual_eq` enforces).
#[derive(Debug)]
pub enum SeqExpr {
    /// String variable
    Var(u32),
    /// String literal
    Literal(String),
    /// Concatenation
    Concat(Vec<SeqExpr>),
    /// Extract substring: extract(s, start, len)
    Extract(Box<SeqExpr>, Box<IntExpr>, Box<IntExpr>),
    /// Replace first: replace(s, from, to)
    Replace(Box<SeqExpr>, Box<SeqExpr>, Box<SeqExpr>),
    /// Replace all: replace_all(s, from, to)
    ReplaceAll(Box<SeqExpr>, Box<SeqExpr>, Box<SeqExpr>),
    /// Replace regex: replace_re(s, regex, replacement)
    ReplaceRe(Box<SeqExpr>, RegexId, Box<SeqExpr>),
    /// Character at index: at(s, i)
    At(Box<SeqExpr>, Box<IntExpr>),
    /// Single character sequence
    Unit(Box<IntExpr>),
    /// Reverse
    Reverse(Box<SeqExpr>),
}

/// Symbolic integer expression
///
/// See [`SeqExpr`]'s depth invariant: the same reasoning applies here, since
/// the two types are mutually recursive.
#[derive(Debug)]
pub enum IntExpr {
    /// Integer variable
    Var(u32),
    /// Integer literal
    Literal(i64),
    /// Length of string
    Length(Box<SeqExpr>),
    /// Index of substring: indexof(s, pattern, start)
    IndexOf(Box<SeqExpr>, Box<SeqExpr>, Box<IntExpr>),
    /// Last index of substring
    LastIndexOf(Box<SeqExpr>, Box<SeqExpr>, Box<IntExpr>),
    /// Character to code: to_code(s)
    ToCode(Box<SeqExpr>),
    /// String to int: to_int(s)
    ToInt(Box<SeqExpr>),
    /// Addition
    Add(Vec<IntExpr>),
    /// Subtraction
    Sub(Box<IntExpr>, Box<IntExpr>),
}

/// One owned node of the iterative dismantling of a [`SeqExpr`]/[`IntExpr`]
/// tree (the two are mutually recursive, so one stack carries both).
enum SeqDropNode {
    /// A sequence sub-expression.
    Seq(SeqExpr),
    /// An integer sub-expression.
    Int(IntExpr),
}

/// Move `expr`'s operands onto `out`, leaving a childless expression behind.
///
/// Operands are swapped out one field at a time: [`SeqExpr`] implements
/// [`Drop`], so its fields cannot be moved out wholesale.
fn take_seq_children(expr: &mut SeqExpr, out: &mut Vec<SeqDropNode>) {
    /// A childless stand-in, dropped immediately and never observed.
    fn seq_placeholder() -> Box<SeqExpr> {
        Box::new(SeqExpr::Var(0))
    }
    /// The integer-side stand-in.
    fn int_placeholder() -> Box<IntExpr> {
        Box::new(IntExpr::Var(0))
    }
    match expr {
        SeqExpr::Var(_) | SeqExpr::Literal(_) => {}
        SeqExpr::Concat(parts) => {
            out.extend(core::mem::take(parts).into_iter().map(SeqDropNode::Seq));
        }
        SeqExpr::Extract(s, start, len) => {
            out.push(SeqDropNode::Seq(*core::mem::replace(s, seq_placeholder())));
            out.push(SeqDropNode::Int(*core::mem::replace(
                start,
                int_placeholder(),
            )));
            out.push(SeqDropNode::Int(*core::mem::replace(
                len,
                int_placeholder(),
            )));
        }
        SeqExpr::Replace(s, from, to) | SeqExpr::ReplaceAll(s, from, to) => {
            out.push(SeqDropNode::Seq(*core::mem::replace(s, seq_placeholder())));
            out.push(SeqDropNode::Seq(*core::mem::replace(
                from,
                seq_placeholder(),
            )));
            out.push(SeqDropNode::Seq(*core::mem::replace(to, seq_placeholder())));
        }
        SeqExpr::ReplaceRe(s, _, to) => {
            out.push(SeqDropNode::Seq(*core::mem::replace(s, seq_placeholder())));
            out.push(SeqDropNode::Seq(*core::mem::replace(to, seq_placeholder())));
        }
        SeqExpr::At(s, i) => {
            out.push(SeqDropNode::Seq(*core::mem::replace(s, seq_placeholder())));
            out.push(SeqDropNode::Int(*core::mem::replace(i, int_placeholder())));
        }
        SeqExpr::Unit(code) => {
            out.push(SeqDropNode::Int(*core::mem::replace(
                code,
                int_placeholder(),
            )));
        }
        SeqExpr::Reverse(s) => {
            out.push(SeqDropNode::Seq(*core::mem::replace(s, seq_placeholder())));
        }
    }
}

/// [`take_seq_children`] for the integer side.
fn take_int_children(expr: &mut IntExpr, out: &mut Vec<SeqDropNode>) {
    /// A childless stand-in, dropped immediately and never observed.
    fn seq_placeholder() -> Box<SeqExpr> {
        Box::new(SeqExpr::Var(0))
    }
    /// The integer-side stand-in.
    fn int_placeholder() -> Box<IntExpr> {
        Box::new(IntExpr::Var(0))
    }
    match expr {
        IntExpr::Var(_) | IntExpr::Literal(_) => {}
        IntExpr::Length(s) | IntExpr::ToCode(s) | IntExpr::ToInt(s) => {
            out.push(SeqDropNode::Seq(*core::mem::replace(s, seq_placeholder())));
        }
        IntExpr::IndexOf(haystack, needle, start)
        | IntExpr::LastIndexOf(haystack, needle, start) => {
            out.push(SeqDropNode::Seq(*core::mem::replace(
                haystack,
                seq_placeholder(),
            )));
            out.push(SeqDropNode::Seq(*core::mem::replace(
                needle,
                seq_placeholder(),
            )));
            out.push(SeqDropNode::Int(*core::mem::replace(
                start,
                int_placeholder(),
            )));
        }
        IntExpr::Add(parts) => {
            out.extend(core::mem::take(parts).into_iter().map(SeqDropNode::Int));
        }
        IntExpr::Sub(lhs, rhs) => {
            out.push(SeqDropNode::Int(*core::mem::replace(
                lhs,
                int_placeholder(),
            )));
            out.push(SeqDropNode::Int(*core::mem::replace(
                rhs,
                int_placeholder(),
            )));
        }
    }
}

/// Drain a dismantling stack, taking each node's operands in turn.
fn drain_seq_drop_stack(stack: &mut Vec<SeqDropNode>) {
    while let Some(node) = stack.pop() {
        match node {
            SeqDropNode::Seq(mut e) => take_seq_children(&mut e, stack),
            SeqDropNode::Int(mut e) => take_int_children(&mut e, stack),
        }
    }
}

impl Drop for SeqExpr {
    /// Dismantle the operand tree iteratively.
    ///
    /// Compiler-generated drop glue recurses once per nesting level, so an
    /// expression deep enough to build is deep enough to abort the process at
    /// scope exit, after it has already been used successfully.
    fn drop(&mut self) {
        let mut stack: Vec<SeqDropNode> = Vec::new();
        take_seq_children(self, &mut stack);
        drain_seq_drop_stack(&mut stack);
    }
}

impl Drop for IntExpr {
    /// Iterative for the same reason as [`SeqExpr`]'s.
    fn drop(&mut self) {
        let mut stack: Vec<SeqDropNode> = Vec::new();
        take_int_children(self, &mut stack);
        drain_seq_drop_stack(&mut stack);
    }
}

/// Iterative `Clone`, `PartialEq` and [`std::hash::Hash`] for [`SeqExpr`]/
/// [`IntExpr`], split out to keep this file under the 2000-line limit.
mod derived_impls;

/// One step of the iterative [`SeqEvaluator`] evaluation.
///
/// `Enter` expands a node's operands; `Reduce` combines their values once they
/// are available. Both sides of the mutually recursive `SeqExpr`/`IntExpr` pair
/// share a single task stack.
enum SeqEvalTask<'a> {
    /// Expand a sequence node's operands.
    EnterSeq(&'a SeqExpr),
    /// Expand an integer node's operands.
    EnterInt(&'a IntExpr),
    /// Combine a sequence node's operand values.
    ReduceSeq(&'a SeqExpr),
    /// Combine an integer node's operand values.
    ReduceInt(&'a IntExpr),
}

/// Task stack plus the two heterogeneous result slots operands land in.
#[derive(Default)]
struct SeqEvalState<'a> {
    /// Pending work, innermost operand on top.
    tasks: Vec<SeqEvalTask<'a>>,
    /// Values of finished sequence operands, in evaluation order.
    seq_results: Vec<SeqResult>,
    /// Values of finished integer operands, in evaluation order.
    int_results: Vec<Option<i64>>,
}

impl SeqEvalState<'_> {
    /// Detach the last `count` sequence operand values, oldest first.
    fn take_seq(&mut self, count: usize) -> Vec<SeqResult> {
        let at = self.seq_results.len().saturating_sub(count);
        self.seq_results.split_off(at)
    }

    /// Detach the last `count` integer operand values, oldest first.
    fn take_int(&mut self, count: usize) -> Vec<Option<i64>> {
        let at = self.int_results.len().saturating_sub(count);
        self.int_results.split_off(at)
    }
}

/// Queue `expr`'s operands so they are evaluated left to right.
fn push_seq_operands<'a>(expr: &'a SeqExpr, tasks: &mut Vec<SeqEvalTask<'a>>) {
    match expr {
        SeqExpr::Var(_) | SeqExpr::Literal(_) => {}
        SeqExpr::Concat(parts) => {
            tasks.extend(parts.iter().rev().map(SeqEvalTask::EnterSeq));
        }
        SeqExpr::Extract(s, start, len) => {
            tasks.push(SeqEvalTask::EnterInt(len));
            tasks.push(SeqEvalTask::EnterInt(start));
            tasks.push(SeqEvalTask::EnterSeq(s));
        }
        SeqExpr::Replace(s, from, to) | SeqExpr::ReplaceAll(s, from, to) => {
            tasks.push(SeqEvalTask::EnterSeq(to));
            tasks.push(SeqEvalTask::EnterSeq(from));
            tasks.push(SeqEvalTask::EnterSeq(s));
        }
        // Regex replacement is symbolic: its operands are never evaluated.
        SeqExpr::ReplaceRe(_, _, _) => {}
        SeqExpr::At(s, i) => {
            tasks.push(SeqEvalTask::EnterInt(i));
            tasks.push(SeqEvalTask::EnterSeq(s));
        }
        SeqExpr::Unit(code) => {
            tasks.push(SeqEvalTask::EnterInt(code));
        }
        SeqExpr::Reverse(s) => {
            tasks.push(SeqEvalTask::EnterSeq(s));
        }
    }
}

/// [`push_seq_operands`] for the integer side.
fn push_int_operands<'a>(expr: &'a IntExpr, tasks: &mut Vec<SeqEvalTask<'a>>) {
    match expr {
        IntExpr::Var(_) | IntExpr::Literal(_) => {}
        IntExpr::Length(s) | IntExpr::ToCode(s) | IntExpr::ToInt(s) => {
            tasks.push(SeqEvalTask::EnterSeq(s));
        }
        IntExpr::IndexOf(haystack, needle, start)
        | IntExpr::LastIndexOf(haystack, needle, start) => {
            tasks.push(SeqEvalTask::EnterInt(start));
            tasks.push(SeqEvalTask::EnterSeq(needle));
            tasks.push(SeqEvalTask::EnterSeq(haystack));
        }
        IntExpr::Add(terms) => {
            tasks.extend(terms.iter().rev().map(SeqEvalTask::EnterInt));
        }
        IntExpr::Sub(lhs, rhs) => {
            tasks.push(SeqEvalTask::EnterInt(rhs));
            tasks.push(SeqEvalTask::EnterInt(lhs));
        }
    }
}

/// Regex identifier for symbolic expressions
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct RegexId(pub u32);

/// Sequence operations evaluator
#[derive(Debug)]
pub struct SeqEvaluator {
    /// String variable assignments
    string_vars: FxHashMap<u32, String>,
    /// Integer variable assignments
    int_vars: FxHashMap<u32, i64>,
    /// Evaluation cache for expressions
    cache: FxHashMap<u64, SeqResult>,
}

impl SeqEvaluator {
    /// Create a new evaluator
    pub fn new() -> Self {
        Self {
            string_vars: FxHashMap::default(),
            int_vars: FxHashMap::default(),
            cache: FxHashMap::default(),
        }
    }

    /// Set a string variable value
    pub fn set_string(&mut self, var: u32, value: String) {
        self.string_vars.insert(var, value);
    }

    /// Set an integer variable value
    pub fn set_int(&mut self, var: u32, value: i64) {
        self.int_vars.insert(var, value);
    }

    /// Get string value
    pub fn get_string(&self, var: u32) -> Option<&String> {
        self.string_vars.get(&var)
    }

    /// Get integer value
    pub fn get_int(&self, var: u32) -> Option<i64> {
        self.int_vars.get(&var).copied()
    }

    /// Evaluate a sequence expression
    ///
    /// Driven by an explicit task stack: [`SeqExpr`] and [`IntExpr`] are
    /// mutually recursive, so a natural-recursion evaluator would nest once per
    /// level of a caller-supplied expression tree. Semantics are unchanged --
    /// evaluation is side-effect free, so operands whose value the original
    /// short-circuited past are simply computed and discarded.
    pub fn eval_seq(&self, expr: &SeqExpr) -> SeqResult {
        let mut state = SeqEvalState::default();
        push_seq_operands(expr, &mut state.tasks);
        self.run_eval(&mut state);
        self.reduce_seq(expr, &mut state)
    }

    /// Evaluate an integer expression
    ///
    /// Iterative for the same reason as [`Self::eval_seq`].
    pub fn eval_int(&self, expr: &IntExpr) -> Option<i64> {
        let mut state = SeqEvalState::default();
        push_int_operands(expr, &mut state.tasks);
        self.run_eval(&mut state);
        self.reduce_int(expr, &mut state)
    }

    /// Drain the task stack, leaving every operand's value in `state`.
    ///
    /// The root node itself is never pushed as a task: its reduction is
    /// performed by the public entry point, which returns the value directly.
    /// That is what keeps "the result stack is empty at the end" unwritable.
    fn run_eval(&self, state: &mut SeqEvalState<'_>) {
        while let Some(task) = state.tasks.pop() {
            match task {
                SeqEvalTask::EnterSeq(expr) => {
                    state.tasks.push(SeqEvalTask::ReduceSeq(expr));
                    push_seq_operands(expr, &mut state.tasks);
                }
                SeqEvalTask::EnterInt(expr) => {
                    state.tasks.push(SeqEvalTask::ReduceInt(expr));
                    push_int_operands(expr, &mut state.tasks);
                }
                SeqEvalTask::ReduceSeq(expr) => {
                    let value = self.reduce_seq(expr, state);
                    state.seq_results.push(value);
                }
                SeqEvalTask::ReduceInt(expr) => {
                    let value = self.reduce_int(expr, state);
                    state.int_results.push(value);
                }
            }
        }
    }

    /// Combine the already-computed operand values of one sequence node.
    fn reduce_seq(&self, expr: &SeqExpr, state: &mut SeqEvalState<'_>) -> SeqResult {
        match expr {
            SeqExpr::Var(v) => {
                if let Some(s) = self.string_vars.get(v) {
                    SeqResult::String(s.clone())
                } else {
                    SeqResult::Symbolic(expr.clone())
                }
            }
            SeqExpr::Literal(s) => SeqResult::String(s.clone()),
            SeqExpr::Concat(parts) => {
                let values = state.take_seq(parts.len());
                let mut result = String::new();
                for value in values {
                    match value {
                        SeqResult::String(s) => result.push_str(&s),
                        _ => return SeqResult::Symbolic(expr.clone()),
                    }
                }
                SeqResult::String(result)
            }
            SeqExpr::Extract(_, _, _) => {
                let mut seq_values = state.take_seq(1);
                let mut int_values = state.take_int(2);
                let len = int_values.pop().flatten();
                let start = int_values.pop().flatten();
                if let (Some(SeqResult::String(s)), Some(start), Some(len)) =
                    (seq_values.pop(), start, len)
                {
                    let start = start.max(0) as usize;
                    let len = len.max(0) as usize;
                    if start >= s.len() {
                        SeqResult::String(String::new())
                    } else {
                        let end = (start + len).min(s.len());
                        SeqResult::String(s[start..end].to_string())
                    }
                } else {
                    SeqResult::Symbolic(expr.clone())
                }
            }
            SeqExpr::Replace(_, _, _) | SeqExpr::ReplaceAll(_, _, _) => {
                let mut values = state.take_seq(3);
                let to = values.pop();
                let from = values.pop();
                let subject = values.pop();
                if let (
                    Some(SeqResult::String(s)),
                    Some(SeqResult::String(from)),
                    Some(SeqResult::String(to)),
                ) = (subject, from, to)
                {
                    if matches!(expr, SeqExpr::Replace(_, _, _)) {
                        SeqResult::String(s.replacen(&from, &to, 1))
                    } else {
                        SeqResult::String(s.replace(&from, &to))
                    }
                } else {
                    SeqResult::Symbolic(expr.clone())
                }
            }
            SeqExpr::ReplaceRe(_, _, _) => {
                // Regex replacement requires regex engine
                SeqResult::Symbolic(expr.clone())
            }
            SeqExpr::At(_, _) => {
                let mut seq_values = state.take_seq(1);
                let mut int_values = state.take_int(1);
                if let (Some(SeqResult::String(s)), Some(Some(i))) =
                    (seq_values.pop(), int_values.pop())
                {
                    if i >= 0
                        && (i as usize) < s.len()
                        && let Some(c) = s.chars().nth(i as usize)
                    {
                        return SeqResult::String(c.to_string());
                    }
                    SeqResult::String(String::new())
                } else {
                    SeqResult::Symbolic(expr.clone())
                }
            }
            SeqExpr::Unit(_) => {
                let mut int_values = state.take_int(1);
                if let Some(Some(code)) = int_values.pop() {
                    if (0..=0x10FFFF).contains(&code)
                        && let Some(c) = char::from_u32(code as u32)
                    {
                        return SeqResult::String(c.to_string());
                    }
                    SeqResult::String(String::new())
                } else {
                    SeqResult::Symbolic(expr.clone())
                }
            }
            SeqExpr::Reverse(_) => {
                let mut seq_values = state.take_seq(1);
                if let Some(SeqResult::String(s)) = seq_values.pop() {
                    SeqResult::String(s.chars().rev().collect())
                } else {
                    SeqResult::Symbolic(expr.clone())
                }
            }
        }
    }

    /// Combine the already-computed operand values of one integer node.
    fn reduce_int(&self, expr: &IntExpr, state: &mut SeqEvalState<'_>) -> Option<i64> {
        match expr {
            IntExpr::Var(v) => self.int_vars.get(v).copied(),
            IntExpr::Literal(n) => Some(*n),
            IntExpr::Length(_) => match state.take_seq(1).pop() {
                Some(SeqResult::String(s)) => Some(s.len() as i64),
                _ => None,
            },
            IntExpr::IndexOf(_, _, _) | IntExpr::LastIndexOf(_, _, _) => {
                let mut seq_values = state.take_seq(2);
                let start = state.take_int(1).pop().flatten();
                let needle = seq_values.pop();
                let haystack = seq_values.pop();
                let (Some(SeqResult::String(h)), Some(SeqResult::String(n)), Some(start)) =
                    (haystack, needle, start)
                else {
                    return None;
                };
                let start = start.max(0) as usize;
                if matches!(expr, IntExpr::IndexOf(_, _, _)) {
                    if start >= h.len() {
                        return Some(-1);
                    }
                    if n.is_empty() {
                        return Some(start as i64);
                    }
                    h[start..].find(&n).map(|i| (i + start) as i64).or(Some(-1))
                } else {
                    if n.is_empty() {
                        return Some(start.min(h.len()) as i64);
                    }
                    let search_end = start.min(h.len());
                    if search_end < n.len() {
                        return Some(-1);
                    }
                    h[..search_end].rfind(&n).map(|i| i as i64).or(Some(-1))
                }
            }
            IntExpr::ToCode(_) => match state.take_seq(1).pop() {
                Some(SeqResult::String(s)) => {
                    if s.len() == 1 {
                        s.chars().next().map(|c| c as i64)
                    } else {
                        Some(-1)
                    }
                }
                _ => None,
            },
            IntExpr::ToInt(_) => match state.take_seq(1).pop() {
                Some(SeqResult::String(s)) => s.parse::<i64>().ok().or(Some(-1)),
                _ => None,
            },
            IntExpr::Add(terms) => {
                let values = state.take_int(terms.len());
                let mut sum = 0i64;
                for value in values {
                    sum = sum.saturating_add(value?);
                }
                Some(sum)
            }
            IntExpr::Sub(_, _) => {
                let mut values = state.take_int(2);
                let b = values.pop().flatten()?;
                let a = values.pop().flatten()?;
                Some(a.saturating_sub(b))
            }
        }
    }

    /// Clear all assignments
    pub fn clear(&mut self) {
        self.string_vars.clear();
        self.int_vars.clear();
        self.cache.clear();
    }
}

impl Default for SeqEvaluator {
    fn default() -> Self {
        Self::new()
    }
}

// ============================================================================
// Sequence Constraint Generation
// ============================================================================

/// Constraint generated from sequence operations
#[derive(Debug, Clone)]
pub enum SeqConstraint {
    /// String equality
    StringEq(SeqExpr, SeqExpr),
    /// Integer equality
    IntEq(IntExpr, IntExpr),
    /// Integer inequality
    IntLe(IntExpr, IntExpr),
    /// Integer less than
    IntLt(IntExpr, IntExpr),
    /// Non-negative constraint
    NonNeg(IntExpr),
    /// And of constraints
    And(Vec<SeqConstraint>),
    /// Or of constraints
    Or(Vec<SeqConstraint>),
    /// Implication
    Implies(Box<SeqConstraint>, Box<SeqConstraint>),
}

/// Constraint generator for sequence operations
#[derive(Debug)]
pub struct SeqConstraintGen {
    /// Generated constraints
    constraints: Vec<SeqConstraint>,
    /// Next fresh variable ID
    next_var: u32,
    /// Variable bounds (var -> (lower, upper))
    #[allow(dead_code)]
    bounds: FxHashMap<u32, (Option<i64>, Option<i64>)>,
}

impl SeqConstraintGen {
    /// Create a new constraint generator
    pub fn new() -> Self {
        Self {
            constraints: Vec::new(),
            next_var: 0,
            bounds: FxHashMap::default(),
        }
    }

    /// Create a fresh string variable
    pub fn fresh_string_var(&mut self) -> u32 {
        let var = self.next_var;
        self.next_var += 1;
        var
    }

    /// Create a fresh integer variable
    pub fn fresh_int_var(&mut self) -> u32 {
        let var = self.next_var;
        self.next_var += 1;
        var
    }

    /// Add a constraint
    pub fn add(&mut self, constraint: SeqConstraint) {
        self.constraints.push(constraint);
    }

    /// Generate constraints for extract operation
    /// extract(s, start, len) = result
    pub fn gen_extract(&mut self, s: &SeqExpr, start: &IntExpr, len: &IntExpr, result: &SeqExpr) {
        // Preconditions: start >= 0, len >= 0
        self.add(SeqConstraint::NonNeg(start.clone()));
        self.add(SeqConstraint::NonNeg(len.clone()));

        // Length constraint: |result| <= len
        let result_len = IntExpr::Length(Box::new(result.clone()));
        self.add(SeqConstraint::IntLe(result_len.clone(), len.clone()));

        // Length constraint: |result| <= |s| - start
        let s_len = IntExpr::Length(Box::new(s.clone()));
        let avail = IntExpr::Sub(Box::new(s_len.clone()), Box::new(start.clone()));
        self.add(SeqConstraint::IntLe(result_len.clone(), avail));

        // If start < |s|, then |result| >= min(len, |s| - start)
        // This is a complex constraint that requires case analysis
    }

    /// Generate constraints for indexof operation
    /// indexof(s, pattern, start) = result
    pub fn gen_indexof(
        &mut self,
        s: &SeqExpr,
        pattern: &SeqExpr,
        start: &IntExpr,
        result_var: u32,
    ) {
        let result = IntExpr::Var(result_var);

        // Preconditions
        self.add(SeqConstraint::NonNeg(start.clone()));

        // Result is either -1 or a valid index
        // result >= -1
        self.add(SeqConstraint::IntLe(IntExpr::Literal(-1), result.clone()));

        // If result != -1:
        // - result >= start
        // - result + |pattern| <= |s|
        // - s[result..result+|pattern|] = pattern
        let s_len = IntExpr::Length(Box::new(s.clone()));
        let pattern_len = IntExpr::Length(Box::new(pattern.clone()));

        // result + |pattern| <= |s| when result >= 0
        let end = IntExpr::Add(vec![result.clone(), pattern_len.clone()]);
        self.add(SeqConstraint::Or(vec![
            SeqConstraint::IntEq(result.clone(), IntExpr::Literal(-1)),
            SeqConstraint::IntLe(end, s_len),
        ]));
    }

    /// Generate constraints for replace operation
    /// replace(s, from, to) = result
    pub fn gen_replace(&mut self, s: &SeqExpr, from: &SeqExpr, to: &SeqExpr, result: &SeqExpr) {
        let from_len = IntExpr::Length(Box::new(from.clone()));
        let to_len = IntExpr::Length(Box::new(to.clone()));
        let s_len = IntExpr::Length(Box::new(s.clone()));
        let result_len = IntExpr::Length(Box::new(result.clone()));

        // Case 1: from not found -> result = s
        // Case 2: from found at index i -> result = s[0..i] ++ to ++ s[i+|from|..]
        // |result| = |s| - |from| + |to| (if found) or |result| = |s| (if not found)

        let found_len = IntExpr::Add(vec![
            IntExpr::Sub(Box::new(s_len.clone()), Box::new(from_len.clone())),
            to_len.clone(),
        ]);

        self.add(SeqConstraint::Or(vec![
            SeqConstraint::IntEq(result_len.clone(), s_len),
            SeqConstraint::IntEq(result_len, found_len),
        ]));
    }

    /// Get all generated constraints
    pub fn constraints(&self) -> &[SeqConstraint] {
        &self.constraints
    }

    /// Take all constraints
    pub fn take_constraints(&mut self) -> Vec<SeqConstraint> {
        core::mem::take(&mut self.constraints)
    }

    /// Clear all constraints
    pub fn clear(&mut self) {
        self.constraints.clear();
    }
}

impl Default for SeqConstraintGen {
    fn default() -> Self {
        Self::new()
    }
}

// ============================================================================
// String Builder for Model Generation
// ============================================================================

/// String builder for generating concrete values
#[derive(Debug)]
pub struct StringBuilder {
    /// Character alphabet for random generation
    alphabet: Vec<char>,
    /// Random seed
    seed: u64,
}

impl StringBuilder {
    /// Create a new string builder with default alphabet
    pub fn new() -> Self {
        Self {
            alphabet: ('a'..='z').collect(),
            seed: 42,
        }
    }

    /// Create with custom alphabet
    pub fn with_alphabet(alphabet: Vec<char>) -> Self {
        Self { alphabet, seed: 42 }
    }

    /// Set random seed
    pub fn set_seed(&mut self, seed: u64) {
        self.seed = seed;
    }

    /// Generate a random string of given length
    pub fn random_string(&mut self, len: usize) -> String {
        if self.alphabet.is_empty() {
            return String::new();
        }

        let mut result = String::with_capacity(len);
        for _ in 0..len {
            let idx = self.random() % self.alphabet.len();
            result.push(self.alphabet[idx]);
        }
        result
    }

    /// Generate string containing a pattern
    pub fn string_containing(&mut self, pattern: &str, min_len: usize) -> String {
        if pattern.is_empty() {
            return self.random_string(min_len);
        }

        let total_len = min_len.max(pattern.len());
        let prefix_len = if total_len > pattern.len() {
            self.random() % (total_len - pattern.len() + 1)
        } else {
            0
        };
        let suffix_len = total_len.saturating_sub(prefix_len + pattern.len());

        let mut result = self.random_string(prefix_len);
        result.push_str(pattern);
        result.push_str(&self.random_string(suffix_len));
        result
    }

    /// Generate string with given prefix
    pub fn string_with_prefix(&mut self, prefix: &str, total_len: usize) -> String {
        let suffix_len = total_len.saturating_sub(prefix.len());
        let mut result = prefix.to_string();
        result.push_str(&self.random_string(suffix_len));
        result
    }

    /// Generate string with given suffix
    pub fn string_with_suffix(&mut self, suffix: &str, total_len: usize) -> String {
        let prefix_len = total_len.saturating_sub(suffix.len());
        let mut result = self.random_string(prefix_len);
        result.push_str(suffix);
        result
    }

    /// Generate string NOT containing a pattern (best effort)
    pub fn string_avoiding(&mut self, pattern: &str, len: usize) -> Option<String> {
        if pattern.is_empty() {
            return None; // All strings contain empty pattern
        }

        // Try a few times to generate a string not containing pattern
        for _ in 0..100 {
            let s = self.random_string(len);
            if !s.contains(pattern) {
                return Some(s);
            }
        }

        // Fallback: construct a string that definitely doesn't contain pattern
        // Use a different character set
        let mut result = String::with_capacity(len);
        let c = if pattern.contains('_') { '-' } else { '_' };
        for _ in 0..len {
            result.push(c);
        }
        if result.contains(pattern) {
            None
        } else {
            Some(result)
        }
    }

    /// Simple xorshift random
    fn random(&mut self) -> usize {
        let mut x = self.seed;
        x ^= x << 13;
        x ^= x >> 7;
        x ^= x << 17;
        self.seed = x;
        x as usize
    }
}

impl Default for StringBuilder {
    fn default() -> Self {
        Self::new()
    }
}

// ============================================================================
// Sequence Rewriter
// ============================================================================

/// Rewriter for sequence expressions
#[derive(Debug)]
pub struct SeqRewriter {
    /// Rewrite rules cache
    cache: FxHashMap<u64, SeqExpr>,
}

/// How a [`SeqExpr`] node is rebuilt once its operands are simplified.
enum SimplifyBuild {
    /// `Concat`
    Concat,
    /// `Extract`, carrying its (unsimplified) integer operands.
    Extract(Box<IntExpr>, Box<IntExpr>),
    /// `Replace`
    Replace,
    /// `ReplaceAll`
    ReplaceAll,
    /// `At`, carrying its (unsimplified) index.
    At(Box<IntExpr>),
    /// `Reverse`
    Reverse,
}

/// One pending node of the iterative [`SeqRewriter::simplify`] walk.
struct SimplifyFrame {
    /// How to rebuild this node.
    build: SimplifyBuild,
    /// Operands still to simplify, reversed so `pop` yields them in order.
    pending: Vec<SeqExpr>,
    /// Operands simplified so far, in operand order.
    done: Vec<SeqExpr>,
}

/// What simplifying one expression needs: an answer already, or its operands.
enum SimplifyOpened {
    /// Already simplified.
    Done(SeqExpr),
    /// A compound whose operands must be simplified first.
    Frame(SimplifyFrame),
}

impl SeqRewriter {
    /// Create a new rewriter
    pub fn new() -> Self {
        Self {
            cache: FxHashMap::default(),
        }
    }

    /// Simplify a sequence expression
    ///
    /// Explicit post-order stack, not recursion: `SeqExpr` nests as deeply as
    /// the caller builds it, the recursive version consumed the expression by
    /// value (so every frame carried a whole subtree), and it returns a
    /// `SeqExpr` — no channel through which a depth limit could be reported.
    /// The rewrite rules and the order they are applied in are unchanged.
    pub fn simplify(&mut self, expr: SeqExpr) -> SeqExpr {
        let mut frames: Vec<SimplifyFrame> = match Self::open_simplify(expr) {
            SimplifyOpened::Done(e) => return e,
            SimplifyOpened::Frame(f) => vec![f],
        };
        // A simplified operand travelling back to the frame that asked for it.
        let mut carry: Option<SeqExpr> = None;

        while !frames.is_empty() {
            let next = match frames.last_mut() {
                Some(top) => {
                    if let Some(e) = carry.take() {
                        top.done.push(e);
                    }
                    top.pending.pop()
                }
                // Unreachable: the loop condition just checked non-emptiness.
                None => break,
            };
            match next {
                Some(child) => match Self::open_simplify(child) {
                    SimplifyOpened::Done(e) => carry = Some(e),
                    SimplifyOpened::Frame(f) => frames.push(f),
                },
                None => match frames.pop() {
                    Some(frame) => carry = Some(Self::finish_simplify(frame)),
                    // Unreachable for the same reason as above.
                    None => break,
                },
            }
        }

        carry.unwrap_or_else(|| SeqExpr::Literal(String::new()))
    }

    /// Classify one expression: either it is already simplified, or its
    /// operands must be simplified first.
    ///
    /// Operands are moved out one field at a time because [`SeqExpr`]
    /// implements [`Drop`] (see its iterative dismantler), so its fields
    /// cannot be moved out wholesale.
    fn open_simplify(mut expr: SeqExpr) -> SimplifyOpened {
        /// A childless stand-in left where an operand was taken from.
        fn placeholder() -> Box<SeqExpr> {
            Box::new(SeqExpr::Var(0))
        }
        /// The integer-side stand-in.
        fn int_placeholder() -> Box<IntExpr> {
            Box::new(IntExpr::Var(0))
        }
        let frame = |build: SimplifyBuild, pending: Vec<SeqExpr>| {
            SimplifyOpened::Frame(SimplifyFrame {
                build,
                pending,
                done: Vec::new(),
            })
        };
        match &mut expr {
            // `Var`, `Literal` and `ReplaceRe` were the recursive version's
            // `other => other` arm: returned untouched, operands included.
            SeqExpr::Var(_) | SeqExpr::Literal(_) | SeqExpr::ReplaceRe(_, _, _) => {
                SimplifyOpened::Done(expr)
            }
            SeqExpr::Concat(parts) => {
                let mut pending = core::mem::take(parts);
                pending.reverse();
                frame(SimplifyBuild::Concat, pending)
            }
            SeqExpr::Extract(s, start, len) => {
                let s = *core::mem::replace(s, placeholder());
                let start = core::mem::replace(start, int_placeholder());
                let len = core::mem::replace(len, int_placeholder());
                frame(SimplifyBuild::Extract(start, len), vec![s])
            }
            SeqExpr::Replace(..) | SeqExpr::ReplaceAll(..) => {
                let all = matches!(expr, SeqExpr::ReplaceAll(_, _, _));
                let (s, from, to) = match &mut expr {
                    SeqExpr::Replace(s, from, to) | SeqExpr::ReplaceAll(s, from, to) => (
                        *core::mem::replace(s, placeholder()),
                        *core::mem::replace(from, placeholder()),
                        *core::mem::replace(to, placeholder()),
                    ),
                    // Unreachable: the outer arm already matched one of these.
                    _ => return SimplifyOpened::Done(expr),
                };
                let build = if all {
                    SimplifyBuild::ReplaceAll
                } else {
                    SimplifyBuild::Replace
                };
                // Reversed so the pops yield `s`, `from`, `to` — the order the
                // recursive version simplified them in.
                frame(build, vec![to, from, s])
            }
            SeqExpr::At(s, i) => {
                let s = *core::mem::replace(s, placeholder());
                let i = core::mem::replace(i, int_placeholder());
                frame(SimplifyBuild::At(i), vec![s])
            }
            SeqExpr::Unit(code) => {
                if let IntExpr::Literal(c) = &**code {
                    if *c >= 0
                        && *c <= 0x10FFFF
                        && let Some(ch) = char::from_u32(*c as u32)
                    {
                        return SimplifyOpened::Done(SeqExpr::Literal(ch.to_string()));
                    }
                    return SimplifyOpened::Done(SeqExpr::Literal(String::new()));
                }
                SimplifyOpened::Done(expr)
            }
            SeqExpr::Reverse(s) => {
                let s = *core::mem::replace(s, placeholder());
                frame(SimplifyBuild::Reverse, vec![s])
            }
        }
    }

    /// Apply a node's rewrite rules to its simplified operands.
    fn finish_simplify(frame: SimplifyFrame) -> SeqExpr {
        /// Take the next simplified operand. Each frame's operand list is
        /// fixed when the frame is built, so the operand is always present;
        /// the empty literal keeps the impossible case from being written as
        /// an `expect`.
        fn operand(operands: &mut std::vec::IntoIter<SeqExpr>) -> SeqExpr {
            operands
                .next()
                .unwrap_or_else(|| SeqExpr::Literal(String::new()))
        }

        let mut operands = frame.done.into_iter();
        match frame.build {
            SimplifyBuild::Concat => {
                // Merge adjacent literals
                let mut result = Vec::new();
                let mut current_lit = String::new();

                for part in operands {
                    match part {
                        SeqExpr::Literal(ref s) => current_lit.push_str(s),
                        other => {
                            if !current_lit.is_empty() {
                                result.push(SeqExpr::Literal(core::mem::take(&mut current_lit)));
                            }
                            // Skip empty concats
                            if !matches!(&other, SeqExpr::Concat(v) if v.is_empty()) {
                                result.push(other);
                            }
                        }
                    }
                }

                if !current_lit.is_empty() {
                    result.push(SeqExpr::Literal(current_lit));
                }

                match result.len() {
                    0 => SeqExpr::Literal(String::new()),
                    1 => result
                        .pop()
                        .unwrap_or_else(|| SeqExpr::Literal(String::new())),
                    _ => SeqExpr::Concat(result),
                }
            }
            SimplifyBuild::Extract(start, len) => {
                let s = operand(&mut operands);
                // If s is a literal and start/len are literals, compute directly
                if let SeqExpr::Literal(s_str) = &s
                    && let (IntExpr::Literal(start_val), IntExpr::Literal(len_val)) =
                        (&*start, &*len)
                {
                    let start_idx = (*start_val).max(0) as usize;
                    let len_val = (*len_val).max(0) as usize;
                    if start_idx >= s_str.len() {
                        return SeqExpr::Literal(String::new());
                    }
                    let end_idx = (start_idx + len_val).min(s_str.len());
                    return SeqExpr::Literal(s_str[start_idx..end_idx].to_string());
                }
                SeqExpr::Extract(Box::new(s), start, len)
            }
            SimplifyBuild::Replace | SimplifyBuild::ReplaceAll => {
                let all = matches!(frame.build, SimplifyBuild::ReplaceAll);
                let s = operand(&mut operands);
                let from = operand(&mut operands);
                let to = operand(&mut operands);

                // If all are literals, compute directly
                if let (
                    SeqExpr::Literal(s_str),
                    SeqExpr::Literal(from_str),
                    SeqExpr::Literal(to_str),
                ) = (&s, &from, &to)
                {
                    return SeqExpr::Literal(if all {
                        s_str.replace(from_str, to_str)
                    } else {
                        s_str.replacen(from_str, to_str, 1)
                    });
                }

                // Replace with empty from is identity
                if matches!(&from, SeqExpr::Literal(f) if f.is_empty()) {
                    return s;
                }

                if all {
                    SeqExpr::ReplaceAll(Box::new(s), Box::new(from), Box::new(to))
                } else {
                    SeqExpr::Replace(Box::new(s), Box::new(from), Box::new(to))
                }
            }
            SimplifyBuild::At(i) => {
                let s = operand(&mut operands);
                if let (SeqExpr::Literal(s_str), IntExpr::Literal(i_val)) = (&s, &*i) {
                    if *i_val >= 0
                        && (*i_val as usize) < s_str.len()
                        && let Some(c) = s_str.chars().nth(*i_val as usize)
                    {
                        return SeqExpr::Literal(c.to_string());
                    }
                    return SeqExpr::Literal(String::new());
                }
                SeqExpr::At(Box::new(s), i)
            }
            SimplifyBuild::Reverse => {
                let mut s = operand(&mut operands);
                if let SeqExpr::Literal(s_str) = &s {
                    return SeqExpr::Literal(s_str.chars().rev().collect());
                }
                // Reverse of reverse is identity
                if let SeqExpr::Reverse(inner) = &mut s {
                    return *core::mem::replace(inner, Box::new(SeqExpr::Var(0)));
                }
                SeqExpr::Reverse(Box::new(s))
            }
        }
    }

    /// Clear the cache
    pub fn clear(&mut self) {
        self.cache.clear();
    }
}

impl Default for SeqRewriter {
    fn default() -> Self {
        Self::new()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    /// The stack the small-stack regressions below run on: a scaled-down model
    /// of an embedder's worker thread.
    ///
    /// This constant and [`DEEP_NESTING`] are scaled **together**, and only
    /// their ratio -- about 21 bytes of stack per nesting level -- decides what
    /// those tests detect. A recursive walk needs tens of bytes per frame at
    /// the very least, so it still overflows; an iterative one uses O(1) native
    /// stack, so it still returns. Never raise one without the other.
    const WORKER_STACK: usize = 1 << 17;

    /// Nesting depth paired with [`WORKER_STACK`].
    const DEEP_NESTING: usize = 6_250;

    #[test]
    fn test_eval_deeply_nested_alternating_chain_small_stack() {
        // `eval_seq` and `eval_int` are mutually recursive, so a chain that
        // alternates between the two sides nests one activation per level.
        // Both return concrete values (`SeqResult` / `Option<i64>`) with no
        // "too deep" variant, so the only correct fix is an explicit stack.
        // Run on a deliberately small (128 KiB) stack: a stack overflow aborts
        // the process, so "the thread returned at all" is part of the
        // assertion.
        let handle = std::thread::Builder::new()
            .stack_size(WORKER_STACK)
            .spawn(|| {
                let depth = DEEP_NESTING;

                // unit(len(unit(len(... "a" ...)))) -- `len` of a one-character
                // string is 1, and `unit(1)` is again a one-byte character, so
                // the value is stable at every level.
                let mut expr = SeqExpr::Literal("a".to_string());
                for _ in 0..depth {
                    expr = SeqExpr::Unit(Box::new(IntExpr::Length(Box::new(expr))));
                }

                let evaluator = SeqEvaluator::new();
                assert_eq!(
                    evaluator.eval_int(&IntExpr::Length(Box::new(expr))),
                    Some(1)
                );
            })
            .expect("spawning a thread with an explicit stack size must succeed");
        handle
            .join()
            .expect("a deeply nested sequence expression must not overflow a 128 KiB stack");
    }

    #[test]
    fn test_eval_deep_concat_chain_small_stack() {
        // The other shape: a left-leaning `concat` spine, evaluated for its
        // concrete string value.
        let handle = std::thread::Builder::new()
            .stack_size(WORKER_STACK)
            .spawn(|| {
                let depth = DEEP_NESTING;
                let mut expr = SeqExpr::Literal(String::new());
                for _ in 0..depth {
                    expr = SeqExpr::Concat(vec![expr, SeqExpr::Literal("x".to_string())]);
                }

                let evaluator = SeqEvaluator::new();
                match evaluator.eval_seq(&expr) {
                    SeqResult::String(s) => assert_eq!(s.len(), depth),
                    other => panic!("expected a concrete string, got {:?}", other),
                }
            })
            .expect("spawning a thread with an explicit stack size must succeed");
        handle
            .join()
            .expect("a deep concat spine must not overflow a 128 KiB stack");
    }

    #[test]
    fn test_deep_clone_eq_and_drop_small_stack() {
        // The derived recursive `Clone`/`PartialEq`/`Hash` were the last
        // remaining native-stack walks over this mutually recursive pair once
        // `Drop` was made iterative; each would overflow on an expression
        // deep enough to build. Run on a deliberately small (128 KiB) stack: a
        // stack overflow aborts the process, so "the thread returned at all"
        // is part of the assertion.
        let handle = std::thread::Builder::new()
            .stack_size(WORKER_STACK)
            .spawn(|| {
                let depth = DEEP_NESTING;

                // Alternates between the two sides, like
                // `test_eval_deeply_nested_alternating_chain_small_stack`
                // above, so both `SeqExpr::clone`/`eq` and
                // `IntExpr::clone`/`eq` are exercised at depth.
                let mut expr = SeqExpr::Literal("a".to_string());
                for _ in 0..depth {
                    expr = SeqExpr::Unit(Box::new(IntExpr::Length(Box::new(expr))));
                }

                let cloned = expr.clone();
                assert_eq!(expr, cloned);

                drop(expr);
                drop(cloned);
            })
            .expect("spawning a thread with an explicit stack size must succeed");
        handle.join().expect(
            "cloning, comparing and dropping a deeply nested sequence expression must not overflow a 128 KiB stack",
        );
    }

    #[test]
    fn test_eval_symbolic_operand_propagates() {
        // Semantic pin for the rewritten reducers: an unassigned variable makes
        // the whole enclosing expression symbolic rather than a wrong concrete
        // value, and operand order is preserved.
        let evaluator = SeqEvaluator::new();
        let expr = SeqExpr::Concat(vec![
            SeqExpr::Literal("a".to_string()),
            SeqExpr::Var(7),
            SeqExpr::Literal("b".to_string()),
        ]);
        assert_eq!(evaluator.eval_seq(&expr), SeqResult::Symbolic(expr.clone()));

        let mut assigned = SeqEvaluator::new();
        assigned.set_string(7, "MID".to_string());
        assert_eq!(
            assigned.eval_seq(&expr),
            SeqResult::String("aMIDb".to_string())
        );
    }

    #[test]
    fn test_eval_int_sub_operand_order() {
        // `sub(a, b)` must not be evaluated as `sub(b, a)`.
        let mut evaluator = SeqEvaluator::new();
        evaluator.set_int(0, 10);
        evaluator.set_int(1, 4);
        let expr = IntExpr::Sub(Box::new(IntExpr::Var(0)), Box::new(IntExpr::Var(1)));
        assert_eq!(evaluator.eval_int(&expr), Some(6));
    }

    #[test]
    fn test_eval_literal() {
        let eval = SeqEvaluator::new();
        let result = eval.eval_seq(&SeqExpr::Literal("hello".to_string()));
        assert_eq!(result, SeqResult::String("hello".to_string()));
    }

    #[test]
    fn test_eval_concat() {
        let eval = SeqEvaluator::new();
        let expr = SeqExpr::Concat(vec![
            SeqExpr::Literal("hello".to_string()),
            SeqExpr::Literal(" world".to_string()),
        ]);
        let result = eval.eval_seq(&expr);
        assert_eq!(result, SeqResult::String("hello world".to_string()));
    }

    #[test]
    fn test_eval_extract() {
        let eval = SeqEvaluator::new();
        let expr = SeqExpr::Extract(
            Box::new(SeqExpr::Literal("hello".to_string())),
            Box::new(IntExpr::Literal(1)),
            Box::new(IntExpr::Literal(3)),
        );
        let result = eval.eval_seq(&expr);
        assert_eq!(result, SeqResult::String("ell".to_string()));
    }

    #[test]
    fn test_eval_replace() {
        let eval = SeqEvaluator::new();
        let expr = SeqExpr::Replace(
            Box::new(SeqExpr::Literal("hello hello".to_string())),
            Box::new(SeqExpr::Literal("hello".to_string())),
            Box::new(SeqExpr::Literal("world".to_string())),
        );
        let result = eval.eval_seq(&expr);
        assert_eq!(result, SeqResult::String("world hello".to_string()));
    }

    #[test]
    fn test_eval_replace_all() {
        let eval = SeqEvaluator::new();
        let expr = SeqExpr::ReplaceAll(
            Box::new(SeqExpr::Literal("hello hello".to_string())),
            Box::new(SeqExpr::Literal("hello".to_string())),
            Box::new(SeqExpr::Literal("world".to_string())),
        );
        let result = eval.eval_seq(&expr);
        assert_eq!(result, SeqResult::String("world world".to_string()));
    }

    #[test]
    fn test_eval_at() {
        let eval = SeqEvaluator::new();
        let expr = SeqExpr::At(
            Box::new(SeqExpr::Literal("hello".to_string())),
            Box::new(IntExpr::Literal(1)),
        );
        let result = eval.eval_seq(&expr);
        assert_eq!(result, SeqResult::String("e".to_string()));
    }

    #[test]
    fn test_eval_reverse() {
        let eval = SeqEvaluator::new();
        let expr = SeqExpr::Reverse(Box::new(SeqExpr::Literal("hello".to_string())));
        let result = eval.eval_seq(&expr);
        assert_eq!(result, SeqResult::String("olleh".to_string()));
    }

    #[test]
    fn test_eval_length() {
        let eval = SeqEvaluator::new();
        let result = eval.eval_int(&IntExpr::Length(Box::new(SeqExpr::Literal(
            "hello".to_string(),
        ))));
        assert_eq!(result, Some(5));
    }

    #[test]
    fn test_eval_indexof() {
        let eval = SeqEvaluator::new();
        let result = eval.eval_int(&IntExpr::IndexOf(
            Box::new(SeqExpr::Literal("hello world".to_string())),
            Box::new(SeqExpr::Literal("world".to_string())),
            Box::new(IntExpr::Literal(0)),
        ));
        assert_eq!(result, Some(6));
    }

    #[test]
    fn test_eval_indexof_not_found() {
        let eval = SeqEvaluator::new();
        let result = eval.eval_int(&IntExpr::IndexOf(
            Box::new(SeqExpr::Literal("hello".to_string())),
            Box::new(SeqExpr::Literal("world".to_string())),
            Box::new(IntExpr::Literal(0)),
        ));
        assert_eq!(result, Some(-1));
    }

    #[test]
    fn test_eval_to_code() {
        let eval = SeqEvaluator::new();
        let result = eval.eval_int(&IntExpr::ToCode(Box::new(SeqExpr::Literal(
            "A".to_string(),
        ))));
        assert_eq!(result, Some(65));
    }

    #[test]
    fn test_eval_unit() {
        let eval = SeqEvaluator::new();
        let result = eval.eval_seq(&SeqExpr::Unit(Box::new(IntExpr::Literal(65))));
        assert_eq!(result, SeqResult::String("A".to_string()));
    }

    #[test]
    fn test_string_builder_random() {
        let mut builder = StringBuilder::new();
        let s = builder.random_string(10);
        assert_eq!(s.len(), 10);
    }

    #[test]
    fn test_string_builder_containing() {
        let mut builder = StringBuilder::new();
        let s = builder.string_containing("test", 20);
        assert!(s.contains("test"));
        assert!(s.len() >= 20);
    }

    #[test]
    fn test_string_builder_prefix() {
        let mut builder = StringBuilder::new();
        let s = builder.string_with_prefix("hello", 10);
        assert!(s.starts_with("hello"));
        assert_eq!(s.len(), 10);
    }

    #[test]
    fn test_string_builder_suffix() {
        let mut builder = StringBuilder::new();
        let s = builder.string_with_suffix("world", 10);
        assert!(s.ends_with("world"));
        assert_eq!(s.len(), 10);
    }

    #[test]
    fn test_rewriter_concat() {
        let mut rewriter = SeqRewriter::new();
        let expr = SeqExpr::Concat(vec![
            SeqExpr::Literal("hello".to_string()),
            SeqExpr::Literal(" ".to_string()),
            SeqExpr::Literal("world".to_string()),
        ]);
        let result = rewriter.simplify(expr);
        assert_eq!(result, SeqExpr::Literal("hello world".to_string()));
    }

    #[test]
    fn test_rewriter_extract() {
        let mut rewriter = SeqRewriter::new();
        let expr = SeqExpr::Extract(
            Box::new(SeqExpr::Literal("hello".to_string())),
            Box::new(IntExpr::Literal(1)),
            Box::new(IntExpr::Literal(3)),
        );
        let result = rewriter.simplify(expr);
        assert_eq!(result, SeqExpr::Literal("ell".to_string()));
    }

    #[test]
    fn test_rewriter_reverse_reverse() {
        let mut rewriter = SeqRewriter::new();
        let expr = SeqExpr::Reverse(Box::new(SeqExpr::Reverse(Box::new(SeqExpr::Var(1)))));
        let result = rewriter.simplify(expr);
        assert_eq!(result, SeqExpr::Var(1));
    }

    #[test]
    fn test_constraint_gen() {
        let mut cgen = SeqConstraintGen::new();
        let var_id = cgen.fresh_int_var();
        cgen.gen_indexof(
            &SeqExpr::Var(0),
            &SeqExpr::Literal("test".to_string()),
            &IntExpr::Literal(0),
            var_id,
        );
        assert!(!cgen.constraints().is_empty());
    }
}
