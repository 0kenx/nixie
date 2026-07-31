//! Explicit-stack backtracking core of [`super::PatternMatcher`]'s
//! E-matching.
//!
//! # What this replaces
//!
//! `PatternMatcher::match_recursive` used to be a *mutually recursive*
//! `bool`-returning walk: one native call frame per level of
//! pattern/ground-term nesting, with no guard of any kind. The nesting it
//! walks is user-supplied (a quantifier's `:pattern` annotation and the
//! ground terms collected from the goal), so a deep enough trigger term
//! overflowed the native stack and aborted the process. A depth cap could
//! not fix that here: the function's only channel is `bool`, so a cap could
//! only report "no match" for a pattern that does match -- a silently wrong
//! verdict rather than a diagnosable failure. The walk is therefore
//! converted to an explicit heap-allocated goal stack (the same treatment
//! `ast::manager::query::substitute` and `ast::normal_forms` received), so
//! depth is bounded by available memory rather than by the fixed native
//! stack.
//!
//! # Backtracking instead of nested re-entry
//!
//! The old `Eq` arm read
//!
//! ```text
//! (m(p1, g1) && m(p2, g2)) || (m(p1, g2) && m(p2, g1))
//! ```
//!
//! i.e. it re-entered the matcher four times per equality node, so a pattern
//! of nested equalities cost `4^depth`. Here the swapped orientation is not
//! a second traversal but a [`ChoicePoint`]: the alternative is recorded,
//! the first orientation is explored, and only if that fails is the machine
//! rewound and the alternative resumed. Every state the rewind must restore
//! is captured in O(1):
//!
//! * the goal list -- a *persistent* cons list in the [`GoalCell`] arena, so
//!   a choice point stores only its head index and pushing never mutates a
//!   cell another choice point still points at (a plain `Vec` goal stack
//!   would have to be cloned per choice point);
//! * the bindings -- a [`BacktrackMatcher::trail`] of the variable names
//!   inserted so far, truncated back to the choice point's mark, removing
//!   exactly the bindings made while exploring the failed alternative.
//!
//! ## Binding undo is a bug fix, not just a refactor
//!
//! The old recursion never undid bindings, because there was nowhere to undo
//! them *to*: the `&mut FxHashMap` was threaded straight through the `||`.
//! So a failed first orientation left its partial bindings behind and they
//! then constrained the second one. `try_match_term(Eq(X, a), Eq(a, b))`
//! bound `X := a` while failing orientation 1, and orientation 2 -- which
//! matches, with `X := b` -- was rejected by the stale `X := a`. Symmetrically,
//! bindings from a failed alternative could survive into a *successful*
//! match's result, so a variable never actually matched could come back
//! bound, and `PatternMatcher::match_against`'s "all bound variables are
//! assigned" gate would then accept it and instantiate the quantifier with
//! it. Undoing on backtrack fixes both directions; see this module's
//! `tests::eq_orientation_*` for the pins.
//!
//! # Residual worst case (no failure memo)
//!
//! Memoizing failed goals was considered and deliberately **not** done: a
//! goal's failure is not a function of `(pattern, ground)` alone. `f(X)` vs
//! `f(a)` fails or succeeds depending on whether `X` is already bound, and to
//! what. A sound key would have to be `(pattern, ground, restriction of the
//! current bindings to the pattern variables occurring in `pattern`)`, whose
//! computation is itself proportional to the pattern subtree being cached --
//! and triggers are small (a handful of nodes), so the memo would cost more
//! than it saves in every realistic case. Without it, an adversarial pattern
//! of nested equalities whose match fails only at the very bottom can still
//! explore `2^depth` orientation combinations -- an improvement on the old
//! `4^depth`, but still exponential. What removes it in practice is
//! [`BacktrackMatcher::may_match`]: a choice point is only pushed when the
//! swapped orientation is not already refuted at its own root (sorts,
//! top-level kind, and any existing binding of a pattern variable), which is
//! sound because it never rejects a pair the full matcher could accept.
//!
//! Reference: Z3's `smt_quantifier.cpp` / `mam.cpp` E-matching abstract
//! machine, which likewise backtracks over an explicit machine state rather
//! than recursing.

use crate::ast::{TermId, TermKind, TermManager};
use crate::interner::Spur;
#[allow(unused_imports)]
use crate::prelude::*;

/// One cell of the persistent goal list.
///
/// Cells are append-only: [`BacktrackMatcher::push_goal`] allocates a new
/// cell pointing at the current head and never mutates an existing one, so a
/// head index captured by a [`ChoicePoint`] keeps denoting the exact goal
/// list that was current when the choice point was created.
struct GoalCell {
    /// The `(pattern, ground)` pair still to be solved.
    pair: (TermId, TermId),
    /// Index of the next cell in this list, or `None` at its end.
    next: Option<usize>,
}

/// A pending alternative: the state to rewind to, plus the goals to try
/// instead.
struct ChoicePoint {
    /// Goal-list head to restore (index into [`BacktrackMatcher::cells`]).
    goals: Option<usize>,
    /// Length [`BacktrackMatcher::trail`] had when this point was created;
    /// bindings recorded past it are undone on rewind.
    trail_mark: usize,
    /// The two goals of the alternative orientation, in the order they
    /// should be solved.
    alt: [(TermId, TermId); 2],
}

/// The E-matching machine: a goal stack, a binding trail, and a choice-point
/// stack.
///
/// One instance matches one `(pattern, ground)` pair; see
/// [`BacktrackMatcher::run`].
pub(super) struct BacktrackMatcher<'a> {
    /// Names of the quantifier's bound variables -- the pattern variables
    /// this match may bind. A `Var` outside this set is a constant and must
    /// match structurally.
    bound_vars: &'a FxHashSet<Spur>,
    /// Bindings made along the currently explored path.
    bindings: FxHashMap<Spur, TermId>,
    /// Names inserted into `bindings`, in insertion order. A name is pushed
    /// only when it was previously unbound, so truncating the trail and
    /// removing the popped names restores the earlier binding state exactly.
    trail: Vec<Spur>,
    /// Arena backing the persistent goal list (see [`GoalCell`]).
    cells: Vec<GoalCell>,
    /// Head of the current goal list; `None` means every goal is solved.
    goals: Option<usize>,
    /// Alternatives not yet explored, innermost last.
    choices: Vec<ChoicePoint>,
}

impl<'a> BacktrackMatcher<'a> {
    /// Create a matcher for a quantifier whose bound variables are
    /// `bound_vars`.
    pub(super) fn new(bound_vars: &'a FxHashSet<Spur>) -> Self {
        Self {
            bound_vars,
            bindings: FxHashMap::default(),
            trail: Vec::new(),
            cells: Vec::new(),
            goals: None,
            choices: Vec::new(),
        }
    }

    /// Match `pattern` against `ground`, returning whether a consistent
    /// assignment of the pattern variables exists.
    ///
    /// On success the assignment is in [`Self::into_bindings`]; on failure
    /// the machine's state is meaningless (and dropped by the caller).
    pub(super) fn run(&mut self, pattern: TermId, ground: TermId, manager: &TermManager) -> bool {
        self.push_goal((pattern, ground));

        loop {
            let Some(head) = self.goals else {
                // No goals left: every conjunct of the currently explored
                // alternative succeeded.
                return true;
            };
            // `head` is an index this machine itself allocated, so the
            // lookup cannot miss; treating a miss as failure keeps the
            // structurally unreachable case total rather than panicking.
            let Some(cell) = self.cells.get(head) else {
                return false;
            };
            let pair = cell.pair;
            self.goals = cell.next;

            if !self.solve_goal(pair.0, pair.1, manager) && !self.backtrack() {
                return false;
            }
        }
    }

    /// Consume the machine, yielding the bindings of the successful match.
    pub(super) fn into_bindings(self) -> FxHashMap<Spur, TermId> {
        self.bindings
    }

    /// Push one goal onto the front of the current goal list.
    fn push_goal(&mut self, pair: (TermId, TermId)) {
        self.cells.push(GoalCell {
            pair,
            next: self.goals,
        });
        self.goals = Some(self.cells.len() - 1);
    }

    /// Push `pairs` so that they are solved left to right (the order the
    /// retired recursion's `&&` / `.all(..)` chains used, which decides
    /// which of several possible assignments is found first).
    fn push_pairs<const N: usize>(&mut self, pairs: [(TermId, TermId); N]) {
        for pair in pairs.into_iter().rev() {
            self.push_goal(pair);
        }
    }

    /// Push zipped argument pairs, solved left to right.
    fn push_zipped(&mut self, pattern_args: &[TermId], ground_args: &[TermId]) {
        for (&p, &g) in pattern_args.iter().zip(ground_args.iter()).rev() {
            self.push_goal((p, g));
        }
    }

    /// Undo every binding recorded after `mark`.
    fn undo_to(&mut self, mark: usize) {
        while self.trail.len() > mark {
            match self.trail.pop() {
                Some(name) => {
                    self.bindings.remove(&name);
                }
                // Unreachable while `len() > mark >= 0`; break rather than
                // spin.
                None => break,
            }
        }
    }

    /// Rewind to the innermost pending alternative and schedule it.
    ///
    /// Returns `false` when no alternative is left, i.e. the whole match
    /// has failed.
    fn backtrack(&mut self) -> bool {
        let Some(choice) = self.choices.pop() else {
            return false;
        };
        self.undo_to(choice.trail_mark);
        self.goals = choice.goals;
        self.push_pairs(choice.alt);
        true
    }

    /// Is `(pattern, ground)` refutable by looking only at the two nodes
    /// themselves?
    ///
    /// A conservative *over*-approximation of "this goal could succeed":
    /// every check here is one the full matcher performs at the same node,
    /// so a pair rejected here would fail its own goal immediately. Used
    /// only to decide whether an alternative is worth recording, never to
    /// decide a match, so it cannot change which matches exist.
    fn may_match(&self, pattern: TermId, ground: TermId, manager: &TermManager) -> bool {
        let (Some(pattern_term), Some(ground_term)) = (manager.get(pattern), manager.get(ground))
        else {
            return false;
        };
        if pattern_term.sort != ground_term.sort {
            return false;
        }
        match &pattern_term.kind {
            // A pattern variable matches anything of the right sort, unless
            // it is already bound to a different term. Bindings are read at
            // choice-point creation time, which is exactly the state
            // `undo_to(trail_mark)` restores before the alternative runs.
            TermKind::Var(name) if self.bound_vars.contains(name) => {
                match self.bindings.get(name) {
                    Some(&existing) => existing == ground,
                    None => true,
                }
            }
            // Everything else either matches structurally (`pattern ==
            // ground`, which implies equal discriminants) or decomposes,
            // which the full matcher only does for equal discriminants.
            _ => {
                pattern == ground
                    || core::mem::discriminant(&pattern_term.kind)
                        == core::mem::discriminant(&ground_term.kind)
            }
        }
    }

    /// Solve one goal, pushing whatever subgoals it decomposes into.
    ///
    /// Returns `false` if the goal is refuted (the caller then backtracks).
    /// Arm for arm this mirrors the retired `match_recursive`, including its
    /// gaps: kinds it never decomposed (`Mod`, `Distinct`, the bit-vector,
    /// string and floating-point operators, ...) still fall through to the
    /// structural `pattern == ground` test, so they match only an identical
    /// term. That is incomplete, never unsound -- a missed trigger match
    /// costs an instantiation, it does not admit a wrong one -- and widening
    /// it would change which matches exist, which this conversion
    /// deliberately does not do.
    #[allow(clippy::too_many_lines)]
    fn solve_goal(&mut self, pattern: TermId, ground: TermId, manager: &TermManager) -> bool {
        let (Some(pattern_term), Some(ground_term)) = (manager.get(pattern), manager.get(ground))
        else {
            return false;
        };

        // Check sort compatibility
        if pattern_term.sort != ground_term.sort {
            return false;
        }

        match &pattern_term.kind {
            // Pattern variable - bind it
            TermKind::Var(name) if self.bound_vars.contains(name) => {
                match self.bindings.get(name).copied() {
                    // Already bound - check consistency
                    Some(existing) => existing == ground,
                    // New binding, recorded on the trail so a later
                    // backtrack can take it back.
                    None => {
                        self.bindings.insert(*name, ground);
                        self.trail.push(*name);
                        true
                    }
                }
            }

            // Non-pattern variable or constant - must match exactly
            TermKind::Var(_)
            | TermKind::True
            | TermKind::False
            | TermKind::IntConst(_)
            | TermKind::RealConst(_)
            | TermKind::BitVecConst { .. }
            | TermKind::StringLit(_) => pattern == ground,

            // Function application - match head and arguments
            TermKind::Apply { func, args, .. } => {
                let TermKind::Apply {
                    func: ground_func,
                    args: ground_args,
                    ..
                } = &ground_term.kind
                else {
                    return false;
                };
                if func != ground_func || args.len() != ground_args.len() {
                    return false;
                }
                self.push_zipped(args, ground_args);
                true
            }

            // Equality - both orientations match, the swapped one as a
            // recorded alternative rather than a second traversal.
            TermKind::Eq(pattern_lhs, pattern_rhs) => {
                let TermKind::Eq(ground_lhs, ground_rhs) = &ground_term.kind else {
                    return false;
                };
                let (pattern_lhs, pattern_rhs) = (*pattern_lhs, *pattern_rhs);
                let (ground_lhs, ground_rhs) = (*ground_lhs, *ground_rhs);

                // Skip the alternative when it is the same search: either
                // side being self-equal makes the swap a permutation of the
                // very goals about to be pushed.
                let distinct = pattern_lhs != pattern_rhs && ground_lhs != ground_rhs;
                if distinct
                    && self.may_match(pattern_lhs, ground_rhs, manager)
                    && self.may_match(pattern_rhs, ground_lhs, manager)
                {
                    self.choices.push(ChoicePoint {
                        goals: self.goals,
                        trail_mark: self.trail.len(),
                        alt: [(pattern_lhs, ground_rhs), (pattern_rhs, ground_lhs)],
                    });
                }
                self.push_pairs([(pattern_lhs, ground_lhs), (pattern_rhs, ground_rhs)]);
                true
            }

            // N-ary operations - same operator, same arity, pairwise args
            TermKind::Add(args)
            | TermKind::Mul(args)
            | TermKind::And(args)
            | TermKind::Or(args) => {
                // Same operation type
                if core::mem::discriminant(&pattern_term.kind)
                    != core::mem::discriminant(&ground_term.kind)
                {
                    return false;
                }
                let (TermKind::Add(ground_args)
                | TermKind::Mul(ground_args)
                | TermKind::And(ground_args)
                | TermKind::Or(ground_args)) = &ground_term.kind
                else {
                    return false;
                };
                if args.len() != ground_args.len() {
                    return false;
                }
                self.push_zipped(args, ground_args);
                true
            }

            TermKind::Lt(pattern_lhs, pattern_rhs)
            | TermKind::Le(pattern_lhs, pattern_rhs)
            | TermKind::Gt(pattern_lhs, pattern_rhs)
            | TermKind::Ge(pattern_lhs, pattern_rhs)
            | TermKind::Sub(pattern_lhs, pattern_rhs)
            | TermKind::Div(pattern_lhs, pattern_rhs) => {
                if core::mem::discriminant(&pattern_term.kind)
                    != core::mem::discriminant(&ground_term.kind)
                {
                    return false;
                }
                let (TermKind::Lt(ground_lhs, ground_rhs)
                | TermKind::Le(ground_lhs, ground_rhs)
                | TermKind::Gt(ground_lhs, ground_rhs)
                | TermKind::Ge(ground_lhs, ground_rhs)
                | TermKind::Sub(ground_lhs, ground_rhs)
                | TermKind::Div(ground_lhs, ground_rhs)) = &ground_term.kind
                else {
                    return false;
                };
                self.push_pairs([(*pattern_lhs, *ground_lhs), (*pattern_rhs, *ground_rhs)]);
                true
            }

            TermKind::Not(pattern_arg) => {
                let TermKind::Not(ground_arg) = &ground_term.kind else {
                    return false;
                };
                self.push_goal((*pattern_arg, *ground_arg));
                true
            }

            TermKind::Neg(pattern_arg) => {
                let TermKind::Neg(ground_arg) = &ground_term.kind else {
                    return false;
                };
                self.push_goal((*pattern_arg, *ground_arg));
                true
            }

            TermKind::Select(array, index) => {
                let TermKind::Select(ground_array, ground_index) = &ground_term.kind else {
                    return false;
                };
                self.push_pairs([(*array, *ground_array), (*index, *ground_index)]);
                true
            }

            TermKind::Store(array, index, value) => {
                let TermKind::Store(ground_array, ground_index, ground_value) = &ground_term.kind
                else {
                    return false;
                };
                self.push_pairs([
                    (*array, *ground_array),
                    (*index, *ground_index),
                    (*value, *ground_value),
                ]);
                true
            }

            TermKind::Ite(cond, then_branch, else_branch) => {
                let TermKind::Ite(ground_cond, ground_then, ground_else) = &ground_term.kind else {
                    return false;
                };
                self.push_pairs([
                    (*cond, *ground_cond),
                    (*then_branch, *ground_then),
                    (*else_branch, *ground_else),
                ]);
                true
            }

            // Other terms - fallback to structural equality
            _ => pattern == ground,
        }
    }
}
