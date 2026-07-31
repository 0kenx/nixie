//! Explicit-stack backtracking matcher behind [`match_term`].
//!
//! # What this replaces
//!
//! `match_term` was a free function that recursed in lockstep over the
//! `(pattern, candidate)` structure, one native frame per level, through
//! helpers `match_binary` / `match_nary`. Both sides are user-supplied -- the
//! pattern comes from a quantifier's `:pattern` annotation, the candidate from
//! the term pool built out of the input formula -- so a deep enough trigger or
//! ground term overflowed the native stack and aborted the process. It is
//! called once per (pattern, candidate) pair from
//! [`super::EmatchEngine::match_single_pattern`], i.e. on the `Solver::check`
//! path. A depth cap was not an option: the function's only channel is `bool`,
//! so a cap could only answer "no match" for a pattern that does match.
//!
//! The walk is therefore a heap-allocated goal machine here, depth-bounded by
//! memory rather than by the fixed native stack.
//!
//! # Relationship to `tactic::quantifier::matching::backtrack`
//!
//! The tactic layer has a sibling machine, `BacktrackMatcher`, built for the
//! same reason. This module deliberately reuses its *design* -- persistent
//! cons-list goal stack in an arena, binding trail with undo, choice points
//! recording an O(1) rewind point -- but not the module itself, because the
//! two matchers do not agree on what matches:
//!
//! * **Bindings.** `BacktrackMatcher` owns a fresh `FxHashMap` per match; this
//!   one writes into a caller-supplied [`Substitution`] that may already carry
//!   bindings from an earlier pattern of a multi-pattern trigger (see
//!   [`super::EmatchEngine::match_multi_pattern`]), and those must constrain
//!   the match and survive it.
//! * **Sort prefilters.** `BacktrackMatcher` refuses any pair whose two sorts
//!   differ. This matcher never looked at sorts, and importing that check
//!   would silently drop matches the engine currently makes -- a behaviour
//!   change this conversion does not make. `may_match` therefore checks only
//!   what the full matcher below checks.
//! * **Node coverage.** This matcher decomposes `Implies`, which the sibling
//!   does not; the sibling has arms this one lacks. Sharing one implementation
//!   would have to widen one of them.
//!
//! # Backtracking on `Eq`
//!
//! Equality is symmetric, so the trigger `(= x a)` genuinely matches the
//! ground term `(= a b)` with `x := b`. The retired recursion only ever tried
//! the written orientation and reported no match; the sibling matcher already
//! tries both. That divergence is closed here, as a [`ChoicePoint`] rather
//! than a second traversal: the swapped orientation is recorded, the written
//! one explored, and only on failure is the machine rewound and the
//! alternative resumed. Finding *more* matches is sound for E-matching --
//! every grounding of the quantified variables yields a valid instantiation
//! lemma, so an extra match can only cost work, never admit a wrong answer.
//!
//! Rewinding restores two things in O(1):
//!
//! * the goal list -- a persistent cons list in the [`GoalCell`] arena, so a
//!   choice point stores only a head index and pushing never mutates a cell
//!   another choice point still points at;
//! * the bindings -- a [`MatchMachine::trail`] of the names inserted so far,
//!   truncated to the choice point's mark.
//!
//! ## Binding undo is also a fix
//!
//! The recursion threaded one `&mut Substitution` through its `&&` chains and
//! never took anything back, so a failed match left partial bindings in the
//! caller's substitution. With backtracking that would be fatal (a failed
//! orientation's bindings would constrain the alternative), and even without
//! it, it made `match_term`'s contract on failure meaningless. The machine now
//! unwinds its whole trail before reporting failure, so a failed match leaves
//! the caller's substitution exactly as it found it.
//!
//! # Residual worst case
//!
//! No failure memo: a goal's failure is not a function of `(pattern,
//! candidate)` alone -- it depends on which pattern variables are already
//! bound, and to what -- so a sound key would be as expensive to compute as
//! the subtree it caches, and triggers are small. What keeps the search flat
//! in practice is [`MatchMachine::may_match`]: a choice point is pushed only
//! when the swapped orientation is not already refuted at its own root, which
//! is sound because every check it makes is one the full matcher makes at the
//! same node.
//!
//! Reference: Z3's `mam.cpp` E-matching abstract machine, which likewise
//! backtracks over an explicit machine state rather than recursing.

use super::Substitution;
use crate::ast::{TermId, TermKind, TermManager};
use crate::interner::Spur;
#[allow(unused_imports)]
use crate::prelude::*;

/// One cell of the persistent goal list.
///
/// Cells are append-only: [`MatchMachine::push_goal`] allocates a new cell
/// pointing at the current head and never mutates an existing one, so a head
/// index captured by a [`ChoicePoint`] keeps denoting the exact goal list that
/// was current when the choice point was created.
struct GoalCell {
    /// The `(pattern, candidate)` pair still to be solved.
    pair: (TermId, TermId),
    /// Index of the next cell in this list, or `None` at its end.
    next: Option<usize>,
}

/// A pending alternative: the state to rewind to, plus the goals to try
/// instead.
struct ChoicePoint {
    /// Goal-list head to restore (index into [`MatchMachine::cells`]).
    goals: Option<usize>,
    /// Length [`MatchMachine::trail`] had when this point was created;
    /// bindings recorded past it are undone on rewind.
    trail_mark: usize,
    /// The two goals of the alternative orientation, in solving order.
    alt: [(TermId, TermId); 2],
}

/// The matching machine: a goal stack, a binding trail, and a choice-point
/// stack. One instance matches one `(pattern, candidate)` pair.
struct MatchMachine<'a> {
    /// Names of the quantifier's bound variables -- the pattern variables this
    /// match may bind. A `Var` outside this set is a constant and must match
    /// structurally.
    bound_vars: &'a FxHashSet<Spur>,
    /// Names this machine inserted into the caller's substitution, in
    /// insertion order. A name is pushed only when it was previously unbound,
    /// so truncating the trail and removing the popped names restores the
    /// earlier binding state exactly -- including bindings the caller supplied
    /// before the match started, which are never on the trail and so are never
    /// removed.
    trail: Vec<Spur>,
    /// Arena backing the persistent goal list (see [`GoalCell`]).
    cells: Vec<GoalCell>,
    /// Head of the current goal list; `None` means every goal is solved.
    goals: Option<usize>,
    /// Alternatives not yet explored, innermost last.
    choices: Vec<ChoicePoint>,
}

/// Match a pattern term against a candidate ground term.
///
/// Returns true if the match succeeds, and populates `subst` with the variable
/// bindings it made. On failure `subst` is restored to exactly the state it
/// had on entry -- the retired recursion instead left the partial bindings of
/// the failed branch behind.
pub(super) fn match_term(
    pattern: TermId,
    candidate: TermId,
    bound_vars: &FxHashSet<Spur>,
    subst: &mut Substitution,
    manager: &TermManager,
) -> bool {
    let mut machine = MatchMachine {
        bound_vars,
        trail: Vec::new(),
        cells: Vec::new(),
        goals: None,
        choices: Vec::new(),
    };
    machine.run(pattern, candidate, subst, manager)
}

impl MatchMachine<'_> {
    /// Drive the machine to a verdict.
    fn run(
        &mut self,
        pattern: TermId,
        candidate: TermId,
        subst: &mut Substitution,
        manager: &TermManager,
    ) -> bool {
        self.push_goal((pattern, candidate));

        loop {
            let Some(head) = self.goals else {
                // No goals left: every conjunct of the currently explored
                // alternative succeeded.
                return true;
            };
            // `head` is an index this machine itself allocated, so the lookup
            // cannot miss; treating a miss as failure keeps the structurally
            // unreachable case total rather than panicking.
            let Some(cell) = self.cells.get(head) else {
                self.undo_to(0, subst);
                return false;
            };
            let pair = cell.pair;
            self.goals = cell.next;

            if !self.solve_goal(pair.0, pair.1, subst, manager) && !self.backtrack(subst) {
                // Every alternative is exhausted: hand the caller back the
                // substitution it gave us, untouched.
                self.undo_to(0, subst);
                return false;
            }
        }
    }

    /// Push one goal onto the front of the current goal list.
    fn push_goal(&mut self, pair: (TermId, TermId)) {
        self.cells.push(GoalCell {
            pair,
            next: self.goals,
        });
        self.goals = Some(self.cells.len() - 1);
    }

    /// Push `pairs` so that they are solved left to right -- the order the
    /// retired recursion's `&&` chains and argument loops used, which decides
    /// which of several possible assignments is found first.
    fn push_pairs<const N: usize>(&mut self, pairs: [(TermId, TermId); N]) {
        for pair in pairs.into_iter().rev() {
            self.push_goal(pair);
        }
    }

    /// Push zipped argument pairs, solved left to right.
    fn push_zipped(&mut self, pattern_args: &[TermId], candidate_args: &[TermId]) {
        for (&p, &c) in pattern_args.iter().zip(candidate_args.iter()).rev() {
            self.push_goal((p, c));
        }
    }

    /// Undo every binding this machine recorded after `mark`.
    fn undo_to(&mut self, mark: usize, subst: &mut Substitution) {
        while self.trail.len() > mark {
            match self.trail.pop() {
                Some(name) => {
                    subst.remove(&name);
                }
                // Unreachable while `len() > mark >= 0`; break rather than
                // spin.
                None => break,
            }
        }
    }

    /// Rewind to the innermost pending alternative and schedule it.
    ///
    /// Returns `false` when no alternative is left, i.e. the whole match has
    /// failed.
    fn backtrack(&mut self, subst: &mut Substitution) -> bool {
        let Some(choice) = self.choices.pop() else {
            return false;
        };
        self.undo_to(choice.trail_mark, subst);
        self.goals = choice.goals;
        self.push_pairs(choice.alt);
        true
    }

    /// Is `(pattern, candidate)` refutable by looking only at the two nodes
    /// themselves?
    ///
    /// A conservative *over*-approximation of "this goal could succeed": every
    /// check here is one [`Self::solve_goal`] performs at the same node, so a
    /// pair rejected here would fail its own goal immediately. Used only to
    /// decide whether an alternative is worth recording, never to decide a
    /// match, so it cannot change which matches exist. In particular it does
    /// *not* compare sorts, because `solve_goal` does not either.
    fn may_match(
        &self,
        pattern: TermId,
        candidate: TermId,
        subst: &Substitution,
        manager: &TermManager,
    ) -> bool {
        let (Some(pattern_term), Some(candidate_term)) =
            (manager.get(pattern), manager.get(candidate))
        else {
            return false;
        };
        match &pattern_term.kind {
            // A pattern variable matches anything, unless it is already bound
            // to a different term. Bindings are read at choice-point creation
            // time, which is exactly the state `undo_to(trail_mark)` restores
            // before the alternative runs.
            TermKind::Var(name) if self.bound_vars.contains(name) => match subst.get(name) {
                Some(existing) => existing == candidate,
                None => true,
            },
            // Everything else either matches structurally (`pattern ==
            // candidate`, which implies equal discriminants) or decomposes,
            // which `solve_goal` only does for equal discriminants.
            _ => {
                pattern == candidate
                    || core::mem::discriminant(&pattern_term.kind)
                        == core::mem::discriminant(&candidate_term.kind)
            }
        }
    }

    /// Solve one goal, pushing whatever subgoals it decomposes into.
    ///
    /// Returns `false` if the goal is refuted (the caller then backtracks).
    /// Arm for arm this mirrors the retired recursion, including its gaps:
    /// kinds it never decomposed (`Mod`, `Distinct`, `Xor`, the bit-vector,
    /// string, floating-point and datatype operators, quantifiers, ...) still
    /// fall through to the structural `pattern == candidate` test, so they
    /// match only an identical term. That is incomplete, never unsound -- a
    /// missed trigger match costs an instantiation, it does not admit a wrong
    /// one.
    fn solve_goal(
        &mut self,
        pattern: TermId,
        candidate: TermId,
        subst: &mut Substitution,
        manager: &TermManager,
    ) -> bool {
        let (Some(pattern_term), Some(candidate_term)) =
            (manager.get(pattern), manager.get(candidate))
        else {
            return false;
        };

        match &pattern_term.kind {
            // Pattern variable: bind it, or check consistency with an existing
            // binding (which may predate this match, e.g. one carried over
            // from an earlier pattern of a multi-pattern trigger).
            TermKind::Var(name) if self.bound_vars.contains(name) => match subst.get(name) {
                Some(existing) => existing == candidate,
                None => {
                    subst.insert(*name, candidate);
                    self.trail.push(*name);
                    true
                }
            },

            // Function application: same symbol, same arity, pairwise args.
            TermKind::Apply {
                func: pattern_func,
                args: pattern_args,
            } => {
                let TermKind::Apply {
                    func: candidate_func,
                    args: candidate_args,
                } = &candidate_term.kind
                else {
                    return false;
                };
                if pattern_func != candidate_func || pattern_args.len() != candidate_args.len() {
                    return false;
                }
                self.push_zipped(pattern_args, candidate_args);
                true
            }

            // Equality: both orientations, the swapped one recorded as an
            // alternative rather than explored eagerly.
            TermKind::Eq(pattern_lhs, pattern_rhs) => {
                let TermKind::Eq(candidate_lhs, candidate_rhs) = &candidate_term.kind else {
                    return false;
                };
                let (pattern_lhs, pattern_rhs) = (*pattern_lhs, *pattern_rhs);
                let (candidate_lhs, candidate_rhs) = (*candidate_lhs, *candidate_rhs);

                // Skip the alternative when it is the same search: either side
                // being self-equal makes the swap a permutation of the goals
                // about to be pushed.
                let distinct = pattern_lhs != pattern_rhs && candidate_lhs != candidate_rhs;
                if distinct
                    && self.may_match(pattern_lhs, candidate_rhs, subst, manager)
                    && self.may_match(pattern_rhs, candidate_lhs, subst, manager)
                {
                    self.choices.push(ChoicePoint {
                        goals: self.goals,
                        trail_mark: self.trail.len(),
                        alt: [(pattern_lhs, candidate_rhs), (pattern_rhs, candidate_lhs)],
                    });
                }
                self.push_pairs([(pattern_lhs, candidate_lhs), (pattern_rhs, candidate_rhs)]);
                true
            }

            // Other binary operators: same operator, pairwise operands.
            TermKind::Lt(pattern_lhs, pattern_rhs)
            | TermKind::Le(pattern_lhs, pattern_rhs)
            | TermKind::Gt(pattern_lhs, pattern_rhs)
            | TermKind::Ge(pattern_lhs, pattern_rhs)
            | TermKind::Sub(pattern_lhs, pattern_rhs)
            | TermKind::Div(pattern_lhs, pattern_rhs)
            | TermKind::Implies(pattern_lhs, pattern_rhs) => {
                if core::mem::discriminant(&pattern_term.kind)
                    != core::mem::discriminant(&candidate_term.kind)
                {
                    return false;
                }
                let (TermKind::Lt(candidate_lhs, candidate_rhs)
                | TermKind::Le(candidate_lhs, candidate_rhs)
                | TermKind::Gt(candidate_lhs, candidate_rhs)
                | TermKind::Ge(candidate_lhs, candidate_rhs)
                | TermKind::Sub(candidate_lhs, candidate_rhs)
                | TermKind::Div(candidate_lhs, candidate_rhs)
                | TermKind::Implies(candidate_lhs, candidate_rhs)) = &candidate_term.kind
                else {
                    return false;
                };
                self.push_pairs([
                    (*pattern_lhs, *candidate_lhs),
                    (*pattern_rhs, *candidate_rhs),
                ]);
                true
            }

            // N-ary operators: same operator, same arity, pairwise args.
            TermKind::Add(pattern_args)
            | TermKind::Mul(pattern_args)
            | TermKind::And(pattern_args)
            | TermKind::Or(pattern_args) => {
                if core::mem::discriminant(&pattern_term.kind)
                    != core::mem::discriminant(&candidate_term.kind)
                {
                    return false;
                }
                let (TermKind::Add(candidate_args)
                | TermKind::Mul(candidate_args)
                | TermKind::And(candidate_args)
                | TermKind::Or(candidate_args)) = &candidate_term.kind
                else {
                    return false;
                };
                if pattern_args.len() != candidate_args.len() {
                    return false;
                }
                self.push_zipped(pattern_args, candidate_args);
                true
            }

            // Unary operators.
            TermKind::Not(pattern_arg) => {
                let TermKind::Not(candidate_arg) = &candidate_term.kind else {
                    return false;
                };
                self.push_goal((*pattern_arg, *candidate_arg));
                true
            }
            TermKind::Neg(pattern_arg) => {
                let TermKind::Neg(candidate_arg) = &candidate_term.kind else {
                    return false;
                };
                self.push_goal((*pattern_arg, *candidate_arg));
                true
            }

            TermKind::Ite(cond, then_branch, else_branch) => {
                let TermKind::Ite(candidate_cond, candidate_then, candidate_else) =
                    &candidate_term.kind
                else {
                    return false;
                };
                self.push_pairs([
                    (*cond, *candidate_cond),
                    (*then_branch, *candidate_then),
                    (*else_branch, *candidate_else),
                ]);
                true
            }

            TermKind::Select(array, index) => {
                let TermKind::Select(candidate_array, candidate_index) = &candidate_term.kind
                else {
                    return false;
                };
                self.push_pairs([(*array, *candidate_array), (*index, *candidate_index)]);
                true
            }

            TermKind::Store(array, index, value) => {
                let TermKind::Store(candidate_array, candidate_index, candidate_value) =
                    &candidate_term.kind
                else {
                    return false;
                };
                self.push_pairs([
                    (*array, *candidate_array),
                    (*index, *candidate_index),
                    (*value, *candidate_value),
                ]);
                true
            }

            // Ground terms (constants, free variables) and every kind this
            // matcher does not decompose: syntactic equality.
            _ => pattern == candidate,
        }
    }
}
