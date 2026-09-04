//! Tseitin (definitional) CNF conversion -- the *equisatisfiable*,
//! linear-size sibling of [`super::to_cnf`].
//!
//! Split out of `ast/normal_forms.rs`; see that module's doc comment for the
//! general iterative-conversion rationale, and [`to_cnf_tseitin`] for the
//! contract difference that makes this a separate entry point rather than a
//! replacement.
//!
//! # Why a fresh module rather than a flag on `to_cnf`
//!
//! The two conversions do not agree on *what they return*, only on the shape
//! of it: [`super::to_cnf`] returns a formula logically equivalent to its
//! input over the input's own variables; this one returns a formula that is
//! merely *equisatisfiable*, over a strictly larger variable set. Selecting
//! between them with a boolean parameter would leave one contract silently
//! attached to each call site; separate names make the choice (and the
//! obligation the caller takes on) visible at the call.
//!
//! Reference: Z3's `tseitin_cnf_tactic.cpp`, which likewise keeps
//! definitional CNF separate from its distribution-based counterpart.

use super::super::{TermId, TermKind, TermManager};
#[allow(unused_imports)]
use crate::prelude::*;
use smallvec::SmallVec;

#[cfg(test)]
mod tests;

/// Name prefix for the introduced definitional variables.
///
/// `!` cannot appear in an SMT-LIB simple symbol, so a parsed problem cannot
/// hand us a name of this shape; [`TseitinEncoder::fresh_var`] does not rely
/// on that, though -- it checks each candidate against the manager itself.
const FRESH_PREFIX: &str = "tseitin!";

/// Convert a boolean formula to an **equisatisfiable** CNF of linear size
/// (the Tseitin, or definitional, transformation).
///
/// # Contract: equisatisfiable, *not* equivalent
///
/// The result is *not* logically equivalent to `term_id`. It introduces one
/// fresh boolean variable per compound subformula, and the guarantee is:
///
/// * every model of `term_id` extends (uniquely) to a model of the result,
///   and
/// * every model of the result, restricted to the variables of `term_id`,
///   is a model of `term_id`.
///
/// So `term_id` and the result are satisfiable together or unsatisfiable
/// together, and a model of the result answers for `term_id` once the
/// `tseitin!*` variables are projected away. What the result is **not** safe
/// for is anything that reads it as a formula in its own right: it is not
/// valid to conclude the input is valid because the output is, to negate the
/// output, to substitute into it, or to feed it to an interpolation or
/// quantifier-elimination pass that assumes equivalence.
///
/// # Which one to use
///
/// * [`super::to_cnf`] -- when the caller needs an *equivalent* formula:
///   rewriting a subformula in place, negating the result, using it under a
///   quantifier, or handing it to a pass that assumes the variable set is
///   unchanged. Its cost is that naive `Or`-over-`And` distribution is
///   exponential in the worst case.
/// * `to_cnf_tseitin` -- when the caller only needs to decide
///   satisfiability, or to hand clauses to a SAT/SMT core, and can tolerate
///   auxiliary variables. Output size is linear in the input DAG's size.
///
/// # Coverage
///
/// `And`, `Or`, `Not`, `Implies`, `Xor`, `Ite` and `Eq`-between-booleans
/// (i.e. `Iff`) are given definitions. Everything else is an *atom*: it is
/// copied into the result unchanged and never descended into, which includes
/// boolean-sorted applications, arithmetic/bit-vector/string predicates,
/// quantifiers, and any boolean subterm sitting under a non-boolean operator
/// (the `Ite` condition inside an integer `Ite`, say). Treating a compound
/// term as an atom is sound for this contract precisely because the atom
/// appears verbatim in the output, so any interpretation scores it
/// identically on both sides.
///
/// This is a strictly wider connective coverage than [`super::to_cnf`],
/// which has no `Xor`, `Iff` or `Ite` arm at all and returns those nodes
/// as-is.
///
/// # Fresh variables
///
/// Definitional variables are minted through the [`TermManager`] itself, so
/// they are hash-consed like any other term and are genuinely new: each
/// candidate name is only accepted if interning it *grew* the manager, i.e.
/// no term of that name and sort existed (see this module's private
/// `TseitinEncoder::fresh_var`).
///
/// # Traversal
///
/// Explicit heap stack, no native recursion -- the input's nesting depth is
/// user-controlled, so it must not be able to overflow the call stack. Each
/// subformula is visited once (memoised by `TermId`), so a shared DAG node
/// gets one definitional variable no matter how many parents it has, which
/// is what keeps the output linear rather than merely polynomial.
pub fn to_cnf_tseitin(term_id: TermId, manager: &mut TermManager) -> TermId {
    let mut encoder = TseitinEncoder::default();
    encoder.encode(term_id, manager)
}

/// A boolean connective this pass gives a definition to, with its operands
/// already extracted.
///
/// Anything not classified here is an atom -- see [`classify`].
enum Connective {
    /// `Not(arg)`: needs no definitional variable, see
    /// [`TseitinEncoder::combine`].
    Not(TermId),
    /// `And(args)`.
    And(SmallVec<[TermId; 4]>),
    /// `Or(args)`.
    Or(SmallVec<[TermId; 4]>),
    /// `Implies(lhs, rhs)`.
    Implies(TermId, TermId),
    /// `Xor(lhs, rhs)`.
    Xor(TermId, TermId),
    /// `Eq(lhs, rhs)` between two boolean-sorted operands.
    Iff(TermId, TermId),
    /// `Ite(cond, then_branch, else_branch)`, all three boolean-sorted.
    Ite(TermId, TermId, TermId),
}

impl Connective {
    /// The operands that must be encoded before this node can be.
    fn operands(&self) -> SmallVec<[TermId; 4]> {
        match self {
            Self::Not(arg) => SmallVec::from_slice(&[*arg]),
            Self::And(args) | Self::Or(args) => args.clone(),
            Self::Implies(lhs, rhs) | Self::Xor(lhs, rhs) | Self::Iff(lhs, rhs) => {
                SmallVec::from_slice(&[*lhs, *rhs])
            }
            Self::Ite(cond, then_branch, else_branch) => {
                SmallVec::from_slice(&[*cond, *then_branch, *else_branch])
            }
        }
    }
}

/// Is `id` a boolean-sorted term?
fn is_bool(id: TermId, manager: &TermManager) -> bool {
    let bool_sort = manager.sorts.bool_sort;
    manager.get(id).is_some_and(|term| term.sort == bool_sort)
}

/// Classify `id` as a connective to define, or `None` for an atom.
///
/// The node's own sort must be boolean, and every operand a definition would
/// constrain must be boolean too: an `Ite` or `Eq` over a non-boolean sort
/// is a term-level operator whose clauses would be meaningless, so it stays
/// an atom.
fn classify(id: TermId, manager: &TermManager) -> Option<Connective> {
    let term = manager.get(id)?;
    if term.sort != manager.sorts.bool_sort {
        return None;
    }
    match &term.kind {
        TermKind::Not(arg) => Some(Connective::Not(*arg)),
        TermKind::And(args) => Some(Connective::And(args.clone())),
        TermKind::Or(args) => Some(Connective::Or(args.clone())),
        TermKind::Implies(lhs, rhs) => Some(Connective::Implies(*lhs, *rhs)),
        TermKind::Xor(lhs, rhs) => Some(Connective::Xor(*lhs, *rhs)),
        TermKind::Eq(lhs, rhs) if is_bool(*lhs, manager) && is_bool(*rhs, manager) => {
            Some(Connective::Iff(*lhs, *rhs))
        }
        TermKind::Ite(cond, then_branch, else_branch)
            if is_bool(*cond, manager)
                && is_bool(*then_branch, manager)
                && is_bool(*else_branch, manager) =>
        {
            Some(Connective::Ite(*cond, *then_branch, *else_branch))
        }
        _ => None,
    }
}

/// One pending step of the iterative Tseitin walk, mirroring the
/// `Expand`/`Combine` shape [`super::cnf`] and
/// `ast::manager::query::substitute` already use.
enum TseitinStep {
    /// Resolve `id`'s representative literal, scheduling its operands and
    /// its own [`TseitinStep::Combine`] first. A no-op if already resolved.
    Expand(TermId),
    /// Mint `id`'s definitional variable and emit its clauses, now that
    /// every operand has a representative.
    Combine(TermId),
}

/// Encoder state: the representative literal of each visited subformula, the
/// definitional clauses emitted so far, and the fresh-name counter.
#[derive(Default)]
struct TseitinEncoder {
    /// Subformula -> the literal standing for it. A literal here is always
    /// an atom, a boolean constant, a definitional variable, or the negation
    /// of one of those, which is why clause construction below can pass
    /// these straight to `mk_or` without any flattening surprises.
    reps: FxHashMap<TermId, TermId>,
    /// The definitional clauses, in emission order.
    clauses: Vec<TermId>,
    /// Next candidate suffix for [`Self::fresh_var`].
    counter: usize,
}

impl TseitinEncoder {
    /// Encode `root`, returning `root`'s representative conjoined with every
    /// definitional clause.
    fn encode(&mut self, root: TermId, manager: &mut TermManager) -> TermId {
        let mut work: Vec<TseitinStep> = vec![TseitinStep::Expand(root)];
        while let Some(step) = work.pop() {
            self.run_step(step, manager, &mut work);
        }

        // By now `work` is empty, so the root's own `Combine` has run and
        // its representative is recorded (`unwrap_or` covers only the
        // structurally unreachable case of a missing term).
        let root_literal = self.rep_of(root);
        let mut conjuncts: Vec<TermId> = Vec::with_capacity(self.clauses.len() + 1);
        conjuncts.push(root_literal);
        conjuncts.extend(self.clauses.iter().copied());
        manager.mk_and(conjuncts)
    }

    /// Dispatch one [`TseitinStep`].
    fn run_step(
        &mut self,
        step: TseitinStep,
        manager: &mut TermManager,
        work: &mut Vec<TseitinStep>,
    ) {
        match step {
            TseitinStep::Expand(id) => {
                if self.reps.contains_key(&id) {
                    return;
                }
                let Some(connective) = classify(id, manager) else {
                    // Atom (including `True`/`False`): it is its own literal.
                    self.reps.insert(id, id);
                    return;
                };
                let operands = connective.operands();
                work.push(TseitinStep::Combine(id));
                for &operand in operands.iter().rev() {
                    if !self.reps.contains_key(&operand) {
                        work.push(TseitinStep::Expand(operand));
                    }
                }
            }
            TseitinStep::Combine(id) => self.combine(id, manager),
        }
    }

    /// The literal standing for `id`; `id` itself if it was never expanded
    /// (structurally unreachable -- every operand is expanded before its
    /// parent combines -- but keeps this total without a panic).
    fn rep_of(&self, id: TermId) -> TermId {
        self.reps.get(&id).copied().unwrap_or(id)
    }

    /// Mint a boolean variable that does not already exist in `manager`.
    ///
    /// Freshness is checked, not assumed: interning is hash-consing, so a
    /// name already in use would silently hand back the *existing* term and
    /// the "definition" would constrain a user variable. A candidate is
    /// accepted only when interning it grew the manager's term table, which
    /// is exactly the condition "no `Var` of this name and sort existed".
    fn fresh_var(&mut self, manager: &mut TermManager) -> TermId {
        let bool_sort = manager.sorts.bool_sort;
        loop {
            let name = format!("{FRESH_PREFIX}{}", self.counter);
            self.counter += 1;
            let before = manager.len();
            let candidate = manager.mk_var(&name, bool_sort);
            if manager.len() > before {
                return candidate;
            }
        }
    }

    /// Record one clause, dropping it if it is trivially true.
    fn add_clause(
        &mut self,
        literals: impl IntoIterator<Item = TermId>,
        manager: &mut TermManager,
    ) {
        let clause = manager.mk_or(literals);
        if clause != manager.mk_true() {
            self.clauses.push(clause);
        }
    }

    /// Emit `id`'s definition and record its representative literal.
    fn combine(&mut self, id: TermId, manager: &mut TermManager) {
        let Some(connective) = classify(id, manager) else {
            self.reps.insert(id, id);
            return;
        };

        // `Not` needs no variable of its own: the negation of a literal is a
        // literal, so it is folded into the parent's clauses directly. This
        // is what keeps a chain of negations from costing a variable per
        // level.
        if let Connective::Not(arg) = connective {
            let arg_literal = self.rep_of(arg);
            let negated = manager.mk_not(arg_literal);
            self.reps.insert(id, negated);
            return;
        }

        let name = self.fresh_var(manager);
        match connective {
            // Handled above; listed so a future variant cannot fall through
            // silently.
            Connective::Not(_) => {}

            // name <-> AND(args)
            Connective::And(args) => {
                let literals: SmallVec<[TermId; 4]> =
                    args.iter().map(|&arg| self.rep_of(arg)).collect();
                let not_name = manager.mk_not(name);
                for &literal in &literals {
                    self.add_clause([not_name, literal], manager);
                }
                let mut big: Vec<TermId> = Vec::with_capacity(literals.len() + 1);
                big.push(name);
                for &literal in &literals {
                    big.push(manager.mk_not(literal));
                }
                self.add_clause(big, manager);
            }

            // name <-> OR(args)
            Connective::Or(args) => {
                let literals: SmallVec<[TermId; 4]> =
                    args.iter().map(|&arg| self.rep_of(arg)).collect();
                for &literal in &literals {
                    let not_literal = manager.mk_not(literal);
                    self.add_clause([name, not_literal], manager);
                }
                let mut big: Vec<TermId> = Vec::with_capacity(literals.len() + 1);
                big.push(manager.mk_not(name));
                big.extend(literals.iter().copied());
                self.add_clause(big, manager);
            }

            // name <-> (lhs -> rhs) == (!lhs | rhs)
            Connective::Implies(lhs, rhs) => {
                let (lhs, rhs) = (self.rep_of(lhs), self.rep_of(rhs));
                let (not_name, not_lhs, not_rhs) = (
                    manager.mk_not(name),
                    manager.mk_not(lhs),
                    manager.mk_not(rhs),
                );
                self.add_clause([not_name, not_lhs, rhs], manager);
                self.add_clause([name, lhs], manager);
                self.add_clause([name, not_rhs], manager);
            }

            // name <-> (lhs ^ rhs)
            Connective::Xor(lhs, rhs) => {
                let (lhs, rhs) = (self.rep_of(lhs), self.rep_of(rhs));
                let (not_name, not_lhs, not_rhs) = (
                    manager.mk_not(name),
                    manager.mk_not(lhs),
                    manager.mk_not(rhs),
                );
                self.add_clause([not_name, lhs, rhs], manager);
                self.add_clause([not_name, not_lhs, not_rhs], manager);
                self.add_clause([name, not_lhs, rhs], manager);
                self.add_clause([name, lhs, not_rhs], manager);
            }

            // name <-> (lhs <-> rhs)
            Connective::Iff(lhs, rhs) => {
                let (lhs, rhs) = (self.rep_of(lhs), self.rep_of(rhs));
                let (not_name, not_lhs, not_rhs) = (
                    manager.mk_not(name),
                    manager.mk_not(lhs),
                    manager.mk_not(rhs),
                );
                self.add_clause([not_name, not_lhs, rhs], manager);
                self.add_clause([not_name, lhs, not_rhs], manager);
                self.add_clause([name, lhs, rhs], manager);
                self.add_clause([name, not_lhs, not_rhs], manager);
            }

            // name <-> ite(cond, then_branch, else_branch)
            Connective::Ite(cond, then_branch, else_branch) => {
                let cond = self.rep_of(cond);
                let then_branch = self.rep_of(then_branch);
                let else_branch = self.rep_of(else_branch);
                let not_name = manager.mk_not(name);
                let not_cond = manager.mk_not(cond);
                let not_then = manager.mk_not(then_branch);
                let not_else = manager.mk_not(else_branch);
                self.add_clause([not_name, not_cond, then_branch], manager);
                self.add_clause([not_name, cond, else_branch], manager);
                self.add_clause([name, not_cond, not_then], manager);
                self.add_clause([name, cond, not_else], manager);
            }
        }

        self.reps.insert(id, name);
    }
}
