//! Interpolant term representation.

use super::partition::Symbol;
use num_rational::BigRational;
use rustc_hash::FxHashSet;
use std::fmt;

/// Default recursion-depth bound for [`InterpolantTerm::simplify`].
///
/// Reused by [`super::config::InterpolationConfig::default`]
/// (`max_simplify_depth`) so the crate-level default and this type's own
/// convenience entry point agree. An interpolant term is built directly from
/// a resolution proof's structure (see [`super::interpolator::CraigInterpolator`]),
/// whose depth is driven by the size of the UNSAT proof being interpolated,
/// not by anything this crate controls, so recursing over it without a bound
/// -- as `simplify` used to -- could overflow the native stack on a
/// pathologically large proof. Wire a different bound through
/// [`InterpolantTerm::simplify_bounded`] via
/// [`super::config::InterpolationConfig::max_simplify_depth`] when a
/// configured interpolator is available; [`super::interpolator::CraigInterpolator::extract`]
/// does exactly that.
pub(crate) const DEFAULT_SIMPLIFY_DEPTH: usize = 100;

/// An interpolant formula in a simple term representation
///
/// # Depth invariant
///
/// There is deliberately no bound on how deep an `InterpolantTerm` may be: the
/// variants are public, so callers build values directly, and
/// [`super::interpolator::CraigInterpolator`] builds them from a resolution
/// proof whose depth follows the input problem. Every walk over this type is
/// therefore iterative -- [`Clone`], [`Drop`], [`fmt::Display`], [`PartialEq`],
/// [`std::hash::Hash`], [`InterpolantTerm::collect_symbols`] and
/// `simplify_at_depth`. Do **not** replace any of them with a `derive`.
///
/// The one exception is the derived [`fmt::Debug`], which is still recursive:
/// it is a diagnostics-only formatter, is never invoked by this crate outside
/// tests, and hand-writing it would change `{:#?}` output. Prefer
/// [`fmt::Display`] when rendering a term whose depth is not known.
#[derive(Debug)]
pub enum InterpolantTerm {
    /// Boolean constant
    Bool(bool),
    /// Variable
    Var(Symbol),
    /// Negation
    Not(Box<InterpolantTerm>),
    /// Conjunction
    And(Vec<InterpolantTerm>),
    /// Disjunction
    Or(Vec<InterpolantTerm>),
    /// Implication
    Implies(Box<InterpolantTerm>, Box<InterpolantTerm>),
    /// Equality
    Eq(Box<InterpolantTerm>, Box<InterpolantTerm>),
    /// Less than
    Lt(Box<InterpolantTerm>, Box<InterpolantTerm>),
    /// Less than or equal
    Le(Box<InterpolantTerm>, Box<InterpolantTerm>),
    /// Integer/Rational constant
    Num(BigRational),
    /// Addition
    Add(Vec<InterpolantTerm>),
    /// Subtraction
    Sub(Box<InterpolantTerm>, Box<InterpolantTerm>),
    /// Multiplication
    Mul(Vec<InterpolantTerm>),
    /// Function application
    App(Symbol, Vec<InterpolantTerm>),
    /// Array select
    Select(Box<InterpolantTerm>, Box<InterpolantTerm>),
    /// Array store
    Store(
        Box<InterpolantTerm>,
        Box<InterpolantTerm>,
        Box<InterpolantTerm>,
    ),
}

impl InterpolantTerm {
    /// Create true
    #[must_use]
    pub fn true_val() -> Self {
        Self::Bool(true)
    }

    /// Create false
    #[must_use]
    pub fn false_val() -> Self {
        Self::Bool(false)
    }

    /// Create a variable
    #[must_use]
    pub fn var(name: impl Into<String>) -> Self {
        Self::Var(Symbol::var(name))
    }

    /// Create a negation
    #[must_use]
    #[allow(clippy::should_implement_trait)]
    pub fn not(mut term: Self) -> Self {
        // `mem::replace` rather than a by-value destructure: `InterpolantTerm`
        // has a manual `Drop` (see below), so its fields cannot be moved out.
        match &mut term {
            Self::Bool(b) => return Self::Bool(!*b),
            Self::Not(inner) => return std::mem::replace(inner.as_mut(), Self::Bool(false)),
            _ => {}
        }
        Self::Not(Box::new(term))
    }

    /// Create a conjunction
    #[must_use]
    pub fn and(terms: Vec<Self>) -> Self {
        let mut flat = Vec::new();
        for mut t in terms {
            match &t {
                Self::Bool(true) => continue,
                Self::Bool(false) => return Self::Bool(false),
                Self::And(_) => {
                    if let Self::And(inner) = &mut t {
                        flat.append(inner);
                    }
                }
                _ => flat.push(t),
            }
        }
        if flat.is_empty() {
            Self::Bool(true)
        } else if flat.len() == 1 {
            flat.pop().unwrap_or(Self::Bool(true))
        } else {
            Self::And(flat)
        }
    }

    /// Create a disjunction
    #[must_use]
    pub fn or(terms: Vec<Self>) -> Self {
        let mut flat = Vec::new();
        for mut t in terms {
            match &t {
                Self::Bool(false) => continue,
                Self::Bool(true) => return Self::Bool(true),
                Self::Or(_) => {
                    if let Self::Or(inner) = &mut t {
                        flat.append(inner);
                    }
                }
                _ => flat.push(t),
            }
        }
        if flat.is_empty() {
            Self::Bool(false)
        } else if flat.len() == 1 {
            flat.pop().unwrap_or(Self::Bool(false))
        } else {
            Self::Or(flat)
        }
    }

    /// Create an implication
    #[must_use]
    pub fn implies(lhs: Self, rhs: Self) -> Self {
        match (&lhs, &rhs) {
            (Self::Bool(false), _) => Self::Bool(true),
            (Self::Bool(true), _) => rhs,
            (_, Self::Bool(true)) => Self::Bool(true),
            (_, Self::Bool(false)) => Self::not(lhs),
            _ => Self::Implies(Box::new(lhs), Box::new(rhs)),
        }
    }

    /// Check if this term is true
    #[must_use]
    pub fn is_true(&self) -> bool {
        matches!(self, Self::Bool(true))
    }

    /// Check if this term is false
    #[must_use]
    pub fn is_false(&self) -> bool {
        matches!(self, Self::Bool(false))
    }

    /// Collect all symbols in the term.
    ///
    /// Iterative (explicit heap stack): an interpolant term's depth is set by
    /// the depth of the proof it was extracted from, and `-> ()` leaves no way
    /// to report a truncated walk, so a depth cap here could only produce a
    /// silently incomplete symbol set.
    pub fn collect_symbols(&self, symbols: &mut FxHashSet<Symbol>) {
        let mut stack: Vec<&Self> = vec![self];

        while let Some(term) = stack.pop() {
            match term {
                Self::Bool(_) | Self::Num(_) => {}
                Self::Var(s) => {
                    symbols.insert(s.clone());
                }
                Self::Not(t) => stack.push(t),
                Self::And(ts) | Self::Or(ts) | Self::Add(ts) | Self::Mul(ts) => {
                    stack.extend(ts.iter());
                }
                Self::Implies(a, b)
                | Self::Eq(a, b)
                | Self::Lt(a, b)
                | Self::Le(a, b)
                | Self::Sub(a, b)
                | Self::Select(a, b) => {
                    stack.push(a);
                    stack.push(b);
                }
                Self::App(f, args) => {
                    symbols.insert(f.clone());
                    stack.extend(args.iter());
                }
                Self::Store(a, i, v) => {
                    stack.push(a);
                    stack.push(i);
                    stack.push(v);
                }
            }
        }
    }

    /// Simplify the term, recursing at most `DEFAULT_SIMPLIFY_DEPTH` (an
    /// internal default, currently 100) levels before bailing out and
    /// returning the remaining subterm unsimplified.
    ///
    /// Prefer [`InterpolantTerm::simplify_bounded`] with
    /// [`super::config::InterpolationConfig::max_simplify_depth`] when a
    /// configured interpolator is available (see
    /// [`super::interpolator::CraigInterpolator::extract`], which does
    /// exactly that); this is the convenience entry point for callers that
    /// build an `InterpolantTerm` directly, with no configured depth budget
    /// of their own.
    #[must_use]
    pub fn simplify(&self) -> Self {
        self.simplify_bounded(DEFAULT_SIMPLIFY_DEPTH)
    }

    /// Simplify the term, recursing at most `max_depth` levels before
    /// bailing out and returning the remaining subterm unsimplified.
    ///
    /// Bailing out is sound: a subterm returned unprocessed is still a
    /// valid (if less-simplified) contribution to the overall result -- it
    /// is simply not rewritten any further below the cap.
    #[must_use]
    pub fn simplify_bounded(&self, max_depth: usize) -> Self {
        self.simplify_at_depth(0, max_depth)
    }

    /// Iterative (explicit heap stack) bottom-up simplification.
    ///
    /// Results are identical to the recursive formulation, `max_depth` bailout
    /// included; the difference is that the walk itself no longer consumes the
    /// native stack, so `max_depth` is a rewriting budget rather than a
    /// crash-avoidance device.
    fn simplify_at_depth(&self, depth: usize, max_depth: usize) -> Self {
        /// Work item for the iterative simplifier.
        enum SimplifyTask<'a> {
            /// Simplify this subterm at the given depth.
            Enter(&'a InterpolantTerm, usize),
            /// Rebuild a negation from the single result on top.
            BuildNot,
            /// Rebuild a conjunction from the top `n` results.
            BuildAnd(usize),
            /// Rebuild a disjunction from the top `n` results.
            BuildOr(usize),
            /// Rebuild an implication from the top two results.
            BuildImplies,
            /// Rebuild an equality from the top two results.
            BuildEq,
        }

        let mut tasks = vec![SimplifyTask::Enter(self, depth)];
        let mut results: Vec<Self> = Vec::new();

        /// Detach the top `n` results, preserving their original order.
        fn take_results(results: &mut Vec<InterpolantTerm>, n: usize) -> Vec<InterpolantTerm> {
            let start = results.len().saturating_sub(n);
            results.split_off(start)
        }

        while let Some(task) = tasks.pop() {
            match task {
                SimplifyTask::Enter(term, term_depth) => {
                    if term_depth >= max_depth {
                        results.push(term.clone());
                        continue;
                    }
                    match term {
                        Self::Bool(_) | Self::Num(_) | Self::Var(_) => results.push(term.clone()),
                        Self::Not(t) => {
                            tasks.push(SimplifyTask::BuildNot);
                            tasks.push(SimplifyTask::Enter(t, term_depth + 1));
                        }
                        Self::And(ts) => {
                            tasks.push(SimplifyTask::BuildAnd(ts.len()));
                            tasks.extend(
                                ts.iter()
                                    .rev()
                                    .map(|t| SimplifyTask::Enter(t, term_depth + 1)),
                            );
                        }
                        Self::Or(ts) => {
                            tasks.push(SimplifyTask::BuildOr(ts.len()));
                            tasks.extend(
                                ts.iter()
                                    .rev()
                                    .map(|t| SimplifyTask::Enter(t, term_depth + 1)),
                            );
                        }
                        Self::Implies(a, b) => {
                            tasks.push(SimplifyTask::BuildImplies);
                            tasks.push(SimplifyTask::Enter(b, term_depth + 1));
                            tasks.push(SimplifyTask::Enter(a, term_depth + 1));
                        }
                        Self::Eq(a, b) => {
                            tasks.push(SimplifyTask::BuildEq);
                            tasks.push(SimplifyTask::Enter(b, term_depth + 1));
                            tasks.push(SimplifyTask::Enter(a, term_depth + 1));
                        }
                        _ => results.push(term.clone()),
                    }
                }
                SimplifyTask::BuildNot => {
                    let mut operand = take_results(&mut results, 1);
                    match operand.pop() {
                        Some(t) => results.push(Self::not(t)),
                        None => return self.clone(),
                    }
                }
                SimplifyTask::BuildAnd(n) => {
                    let children = take_results(&mut results, n);
                    results.push(Self::and(children));
                }
                SimplifyTask::BuildOr(n) => {
                    let children = take_results(&mut results, n);
                    results.push(Self::or(children));
                }
                SimplifyTask::BuildImplies => {
                    let mut operands = take_results(&mut results, 2);
                    let rhs = operands.pop();
                    let lhs = operands.pop();
                    match (lhs, rhs) {
                        (Some(a), Some(b)) => results.push(Self::implies(a, b)),
                        _ => return self.clone(),
                    }
                }
                SimplifyTask::BuildEq => {
                    let mut operands = take_results(&mut results, 2);
                    let rhs = operands.pop();
                    let lhs = operands.pop();
                    match (lhs, rhs) {
                        (Some(sa), Some(sb)) => {
                            if sa == sb {
                                results.push(Self::Bool(true));
                            } else {
                                results.push(Self::Eq(Box::new(sa), Box::new(sb)));
                            }
                        }
                        _ => return self.clone(),
                    }
                }
            }
        }

        // Exactly one result is produced for the single root task; falling back
        // to the unsimplified term matches the documented bail-out semantics.
        results.pop().unwrap_or_else(|| self.clone())
    }
}

impl PartialEq for InterpolantTerm {
    /// Iterative structural equality.
    ///
    /// The derived `PartialEq` walked both terms with one native call frame per
    /// nesting level. Because `InterpolantTerm` has public variants and is also
    /// built from resolution proofs of unbounded depth (see the type-level depth
    /// invariant), that walk could overflow the stack on a plain `a == b` --
    /// including the `contains` scans inside [`InterpolantTerm::and`] and
    /// [`InterpolantTerm::or`]. The pairs still to be compared live on the heap
    /// instead; the relation itself is unchanged.
    ///
    /// The outer `match` is exhaustive over `self`'s variants on purpose: a new
    /// variant must be handled here explicitly rather than silently falling into
    /// a catch-all that reports "not equal".
    fn eq(&self, other: &Self) -> bool {
        /// Queue every positional child pair, left to right.
        fn push_all<'a>(
            worklist: &mut Vec<(&'a InterpolantTerm, &'a InterpolantTerm)>,
            lhs: &'a [InterpolantTerm],
            rhs: &'a [InterpolantTerm],
        ) {
            worklist.extend(lhs.iter().zip(rhs.iter()).rev());
        }

        let mut worklist = vec![(self, other)];

        while let Some((a, b)) = worklist.pop() {
            match a {
                Self::Bool(x) => {
                    let Self::Bool(y) = b else { return false };
                    if x != y {
                        return false;
                    }
                }
                Self::Var(x) => {
                    let Self::Var(y) = b else { return false };
                    if x != y {
                        return false;
                    }
                }
                Self::Num(x) => {
                    let Self::Num(y) = b else { return false };
                    if x != y {
                        return false;
                    }
                }
                Self::Not(x) => {
                    let Self::Not(y) = b else { return false };
                    worklist.push((x.as_ref(), y.as_ref()));
                }
                Self::And(xs) => {
                    let Self::And(ys) = b else { return false };
                    if xs.len() != ys.len() {
                        return false;
                    }
                    push_all(&mut worklist, xs, ys);
                }
                Self::Or(xs) => {
                    let Self::Or(ys) = b else { return false };
                    if xs.len() != ys.len() {
                        return false;
                    }
                    push_all(&mut worklist, xs, ys);
                }
                Self::Add(xs) => {
                    let Self::Add(ys) = b else { return false };
                    if xs.len() != ys.len() {
                        return false;
                    }
                    push_all(&mut worklist, xs, ys);
                }
                Self::Mul(xs) => {
                    let Self::Mul(ys) = b else { return false };
                    if xs.len() != ys.len() {
                        return false;
                    }
                    push_all(&mut worklist, xs, ys);
                }
                Self::App(f, xs) => {
                    let Self::App(g, ys) = b else { return false };
                    if f != g || xs.len() != ys.len() {
                        return false;
                    }
                    push_all(&mut worklist, xs, ys);
                }
                Self::Implies(x1, x2) => {
                    let Self::Implies(y1, y2) = b else {
                        return false;
                    };
                    worklist.push((x2.as_ref(), y2.as_ref()));
                    worklist.push((x1.as_ref(), y1.as_ref()));
                }
                Self::Eq(x1, x2) => {
                    let Self::Eq(y1, y2) = b else { return false };
                    worklist.push((x2.as_ref(), y2.as_ref()));
                    worklist.push((x1.as_ref(), y1.as_ref()));
                }
                Self::Lt(x1, x2) => {
                    let Self::Lt(y1, y2) = b else { return false };
                    worklist.push((x2.as_ref(), y2.as_ref()));
                    worklist.push((x1.as_ref(), y1.as_ref()));
                }
                Self::Le(x1, x2) => {
                    let Self::Le(y1, y2) = b else { return false };
                    worklist.push((x2.as_ref(), y2.as_ref()));
                    worklist.push((x1.as_ref(), y1.as_ref()));
                }
                Self::Sub(x1, x2) => {
                    let Self::Sub(y1, y2) = b else { return false };
                    worklist.push((x2.as_ref(), y2.as_ref()));
                    worklist.push((x1.as_ref(), y1.as_ref()));
                }
                Self::Select(x1, x2) => {
                    let Self::Select(y1, y2) = b else {
                        return false;
                    };
                    worklist.push((x2.as_ref(), y2.as_ref()));
                    worklist.push((x1.as_ref(), y1.as_ref()));
                }
                Self::Store(x1, x2, x3) => {
                    let Self::Store(y1, y2, y3) = b else {
                        return false;
                    };
                    worklist.push((x3.as_ref(), y3.as_ref()));
                    worklist.push((x2.as_ref(), y2.as_ref()));
                    worklist.push((x1.as_ref(), y1.as_ref()));
                }
            }
        }

        true
    }
}

impl Eq for InterpolantTerm {}

impl std::hash::Hash for InterpolantTerm {
    /// Iterative structural hashing, consistent with the [`PartialEq`] above.
    ///
    /// Same reason as `eq`: the derived `Hash` recursed once per nesting level,
    /// so hashing a deep term (e.g. inserting it into a set) could overflow the
    /// stack. Each node contributes a variant tag, then its non-child payload,
    /// then -- for the variable-arity variants -- its arity, so two terms that
    /// flatten to the same stream of leaves but differ in shape still hash
    /// differently. Children are visited in the same left-to-right order `eq`
    /// compares them in, which is what keeps `a == b` implying equal hashes.
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        /// Queue every child, left to right.
        fn push_all<'a>(stack: &mut Vec<&'a InterpolantTerm>, xs: &'a [InterpolantTerm]) {
            stack.extend(xs.iter().rev());
        }

        let mut stack = vec![self];

        while let Some(node) = stack.pop() {
            // Variant tag: distinguishes shapes that share a payload layout.
            state.write_u8(node.hash_tag());

            match node {
                Self::Bool(b) => b.hash(state),
                Self::Var(s) => s.hash(state),
                Self::Num(n) => n.hash(state),
                Self::Not(x) => stack.push(x.as_ref()),
                Self::And(xs) | Self::Or(xs) | Self::Add(xs) | Self::Mul(xs) => {
                    state.write_usize(xs.len());
                    push_all(&mut stack, xs);
                }
                Self::App(f, xs) => {
                    f.hash(state);
                    state.write_usize(xs.len());
                    push_all(&mut stack, xs);
                }
                Self::Implies(x1, x2)
                | Self::Eq(x1, x2)
                | Self::Lt(x1, x2)
                | Self::Le(x1, x2)
                | Self::Sub(x1, x2)
                | Self::Select(x1, x2) => {
                    stack.push(x2.as_ref());
                    stack.push(x1.as_ref());
                }
                Self::Store(x1, x2, x3) => {
                    stack.push(x3.as_ref());
                    stack.push(x2.as_ref());
                    stack.push(x1.as_ref());
                }
            }
        }
    }
}

impl InterpolantTerm {
    /// Stable per-variant tag mixed into [`std::hash::Hash`].
    ///
    /// Written out rather than derived from `mem::discriminant` so that the
    /// value is a fixed, exhaustively-checked constant per variant.
    const fn hash_tag(&self) -> u8 {
        match self {
            Self::Bool(_) => 0,
            Self::Var(_) => 1,
            Self::Not(_) => 2,
            Self::And(_) => 3,
            Self::Or(_) => 4,
            Self::Implies(_, _) => 5,
            Self::Eq(_, _) => 6,
            Self::Lt(_, _) => 7,
            Self::Le(_, _) => 8,
            Self::Num(_) => 9,
            Self::Add(_) => 10,
            Self::Sub(_, _) => 11,
            Self::Mul(_) => 12,
            Self::App(_, _) => 13,
            Self::Select(_, _) => 14,
            Self::Store(_, _, _) => 15,
        }
    }
}

/// The shape of a node being rebuilt by the iterative [`Clone`] impl: which
/// variant it is, plus anything that is not one of the cloned children.
enum CloneShape {
    /// `Not`, one child.
    Not,
    /// `And` with the given arity.
    And(usize),
    /// `Or` with the given arity.
    Or(usize),
    /// `Add` with the given arity.
    Add(usize),
    /// `Mul` with the given arity.
    Mul(usize),
    /// `App` with its function symbol and arity.
    App(Symbol, usize),
    /// `Implies`, two children.
    Implies,
    /// `Eq`, two children.
    Eq,
    /// `Lt`, two children.
    Lt,
    /// `Le`, two children.
    Le,
    /// `Sub`, two children.
    Sub,
    /// `Select`, two children.
    Select,
    /// `Store`, three children.
    Store,
}

/// Work item for the iterative [`Clone`] impl.
enum CloneTask<'a> {
    /// Clone this subterm.
    Visit(&'a InterpolantTerm),
    /// Rebuild a node from the already-cloned children on the result stack.
    Rebuild(CloneShape),
}

impl Clone for InterpolantTerm {
    /// Iterative clone.
    ///
    /// The derived recursive `Clone` was the last remaining native-stack walk
    /// over this type — and it is reached from `simplify`'s depth-budget
    /// bail-out, so it fired on exactly the deep terms the rest of this module
    /// was made safe for. The result is structurally identical: nodes are
    /// rebuilt with their plain variant constructors, never with the
    /// normalizing smart constructors.
    fn clone(&self) -> Self {
        /// Detach the top `n` results, preserving their original order.
        fn take(results: &mut Vec<InterpolantTerm>, n: usize) -> Vec<InterpolantTerm> {
            let start = results.len().saturating_sub(n);
            results.split_off(start)
        }

        /// Rebuild a two-child node, or fall back to `false` if starved.
        fn pair(
            results: &mut Vec<InterpolantTerm>,
        ) -> (Box<InterpolantTerm>, Box<InterpolantTerm>) {
            let mut operands = take(results, 2);
            let rhs = operands.pop().unwrap_or(InterpolantTerm::Bool(false));
            let lhs = operands.pop().unwrap_or(InterpolantTerm::Bool(false));
            (Box::new(lhs), Box::new(rhs))
        }

        let mut tasks = vec![CloneTask::Visit(self)];
        let mut results: Vec<Self> = Vec::new();

        while let Some(task) = tasks.pop() {
            match task {
                CloneTask::Visit(term) => match term {
                    Self::Bool(b) => results.push(Self::Bool(*b)),
                    Self::Var(s) => results.push(Self::Var(s.clone())),
                    Self::Num(n) => results.push(Self::Num(n.clone())),
                    Self::Not(inner) => {
                        tasks.push(CloneTask::Rebuild(CloneShape::Not));
                        tasks.push(CloneTask::Visit(inner));
                    }
                    Self::And(ts) | Self::Or(ts) | Self::Add(ts) | Self::Mul(ts) => {
                        let shape = match term {
                            Self::And(_) => CloneShape::And(ts.len()),
                            Self::Or(_) => CloneShape::Or(ts.len()),
                            Self::Add(_) => CloneShape::Add(ts.len()),
                            _ => CloneShape::Mul(ts.len()),
                        };
                        tasks.push(CloneTask::Rebuild(shape));
                        tasks.extend(ts.iter().rev().map(CloneTask::Visit));
                    }
                    Self::App(f, args) => {
                        tasks.push(CloneTask::Rebuild(CloneShape::App(f.clone(), args.len())));
                        tasks.extend(args.iter().rev().map(CloneTask::Visit));
                    }
                    Self::Implies(a, b)
                    | Self::Eq(a, b)
                    | Self::Lt(a, b)
                    | Self::Le(a, b)
                    | Self::Sub(a, b)
                    | Self::Select(a, b) => {
                        let shape = match term {
                            Self::Implies(..) => CloneShape::Implies,
                            Self::Eq(..) => CloneShape::Eq,
                            Self::Lt(..) => CloneShape::Lt,
                            Self::Le(..) => CloneShape::Le,
                            Self::Sub(..) => CloneShape::Sub,
                            _ => CloneShape::Select,
                        };
                        tasks.push(CloneTask::Rebuild(shape));
                        tasks.push(CloneTask::Visit(b));
                        tasks.push(CloneTask::Visit(a));
                    }
                    Self::Store(a, i, v) => {
                        tasks.push(CloneTask::Rebuild(CloneShape::Store));
                        tasks.push(CloneTask::Visit(v));
                        tasks.push(CloneTask::Visit(i));
                        tasks.push(CloneTask::Visit(a));
                    }
                },
                CloneTask::Rebuild(shape) => {
                    let rebuilt = match shape {
                        CloneShape::Not => {
                            let mut operand = take(&mut results, 1);
                            Self::Not(Box::new(
                                operand.pop().unwrap_or(InterpolantTerm::Bool(false)),
                            ))
                        }
                        CloneShape::And(n) => Self::And(take(&mut results, n)),
                        CloneShape::Or(n) => Self::Or(take(&mut results, n)),
                        CloneShape::Add(n) => Self::Add(take(&mut results, n)),
                        CloneShape::Mul(n) => Self::Mul(take(&mut results, n)),
                        CloneShape::App(f, n) => Self::App(f, take(&mut results, n)),
                        CloneShape::Implies => {
                            let (a, b) = pair(&mut results);
                            Self::Implies(a, b)
                        }
                        CloneShape::Eq => {
                            let (a, b) = pair(&mut results);
                            Self::Eq(a, b)
                        }
                        CloneShape::Lt => {
                            let (a, b) = pair(&mut results);
                            Self::Lt(a, b)
                        }
                        CloneShape::Le => {
                            let (a, b) = pair(&mut results);
                            Self::Le(a, b)
                        }
                        CloneShape::Sub => {
                            let (a, b) = pair(&mut results);
                            Self::Sub(a, b)
                        }
                        CloneShape::Select => {
                            let (a, b) = pair(&mut results);
                            Self::Select(a, b)
                        }
                        CloneShape::Store => {
                            let mut operands = take(&mut results, 3);
                            let v = operands.pop().unwrap_or(InterpolantTerm::Bool(false));
                            let i = operands.pop().unwrap_or(InterpolantTerm::Bool(false));
                            let a = operands.pop().unwrap_or(InterpolantTerm::Bool(false));
                            Self::Store(Box::new(a), Box::new(i), Box::new(v))
                        }
                    };
                    results.push(rebuilt);
                }
            }
        }

        results.pop().unwrap_or(Self::Bool(false))
    }
}

impl Drop for InterpolantTerm {
    /// Iterative drop.
    ///
    /// An interpolant term inherits the depth of the proof it was extracted
    /// from, and every walk over it in this module is now iterative — which
    /// would leave the compiler-generated recursive `drop_in_place` as the one
    /// remaining way to abort the process, at scope exit, with no diagnostic.
    /// Each node is dismantled into a shallow shell before being released.
    fn drop(&mut self) {
        /// Detach a node's children, leaving a shell that drops trivially.
        fn dismantle(node: &mut InterpolantTerm, out: &mut Vec<InterpolantTerm>) {
            /// Replace a boxed child with a leaf and hand the child over.
            fn take(slot: &mut Box<InterpolantTerm>, out: &mut Vec<InterpolantTerm>) {
                out.push(std::mem::replace(
                    slot.as_mut(),
                    InterpolantTerm::Bool(false),
                ));
            }

            match node {
                InterpolantTerm::Bool(_) | InterpolantTerm::Var(_) | InterpolantTerm::Num(_) => {}
                InterpolantTerm::Not(inner) => take(inner, out),
                InterpolantTerm::And(ts)
                | InterpolantTerm::Or(ts)
                | InterpolantTerm::Add(ts)
                | InterpolantTerm::Mul(ts)
                | InterpolantTerm::App(_, ts) => out.append(ts),
                InterpolantTerm::Implies(a, b)
                | InterpolantTerm::Eq(a, b)
                | InterpolantTerm::Lt(a, b)
                | InterpolantTerm::Le(a, b)
                | InterpolantTerm::Sub(a, b)
                | InterpolantTerm::Select(a, b) => {
                    take(a, out);
                    take(b, out);
                }
                InterpolantTerm::Store(a, i, v) => {
                    take(a, out);
                    take(i, out);
                    take(v, out);
                }
            }
        }

        let mut pending = Vec::new();
        dismantle(self, &mut pending);
        while let Some(mut node) = pending.pop() {
            dismantle(&mut node, &mut pending);
        }
    }
}

/// Work item for the iterative [`fmt::Display`] impl below.
enum FmtTask<'a> {
    /// Render this subterm.
    Term(&'a InterpolantTerm),
    /// Emit a structural token verbatim.
    Text(&'static str),
}

/// Schedule the operands of an n-ary form so each renders as ` <operand>`,
/// followed by the closing parenthesis.
fn push_operands<'a>(stack: &mut Vec<FmtTask<'a>>, ts: &'a [InterpolantTerm]) {
    stack.push(FmtTask::Text(")"));
    for t in ts.iter().rev() {
        stack.push(FmtTask::Term(t));
        stack.push(FmtTask::Text(" "));
    }
}

impl fmt::Display for InterpolantTerm {
    /// Iterative (explicit heap stack) rendering.
    ///
    /// A `Display` impl is the least expected place for a stack overflow, and
    /// interpolant terms inherit the depth of the proof they came from, so this
    /// walks the term with a heap stack rather than the call stack. The output
    /// is byte-identical to the recursive formulation.
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let mut stack = vec![FmtTask::Term(self)];

        while let Some(task) = stack.pop() {
            let term = match task {
                FmtTask::Text(text) => {
                    f.write_str(text)?;
                    continue;
                }
                FmtTask::Term(term) => term,
            };

            match term {
                Self::Bool(b) => write!(f, "{}", b)?,
                Self::Var(s) => write!(f, "{}", s.name)?,
                Self::Num(n) => write!(f, "{}", n)?,
                Self::Not(t) => {
                    f.write_str("(not ")?;
                    stack.push(FmtTask::Text(")"));
                    stack.push(FmtTask::Term(t));
                }
                Self::And(ts) => {
                    f.write_str("(and")?;
                    push_operands(&mut stack, ts);
                }
                Self::Or(ts) => {
                    f.write_str("(or")?;
                    push_operands(&mut stack, ts);
                }
                Self::Add(ts) => {
                    f.write_str("(+")?;
                    push_operands(&mut stack, ts);
                }
                Self::Mul(ts) => {
                    f.write_str("(*")?;
                    push_operands(&mut stack, ts);
                }
                Self::App(s, args) => {
                    write!(f, "({}", s.name)?;
                    push_operands(&mut stack, args);
                }
                Self::Implies(a, b)
                | Self::Eq(a, b)
                | Self::Lt(a, b)
                | Self::Le(a, b)
                | Self::Sub(a, b)
                | Self::Select(a, b) => {
                    let head = match term {
                        Self::Implies(..) => "(=> ",
                        Self::Eq(..) => "(= ",
                        Self::Lt(..) => "(< ",
                        Self::Le(..) => "(<= ",
                        Self::Sub(..) => "(- ",
                        _ => "(select ",
                    };
                    f.write_str(head)?;
                    stack.push(FmtTask::Text(")"));
                    stack.push(FmtTask::Term(b));
                    stack.push(FmtTask::Text(" "));
                    stack.push(FmtTask::Term(a));
                }
                Self::Store(a, i, v) => {
                    f.write_str("(store ")?;
                    stack.push(FmtTask::Text(")"));
                    stack.push(FmtTask::Term(v));
                    stack.push(FmtTask::Text(" "));
                    stack.push(FmtTask::Term(i));
                    stack.push(FmtTask::Text(" "));
                    stack.push(FmtTask::Term(a));
                }
            }
        }

        Ok(())
    }
}
