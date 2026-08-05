//! Grammar reduction for ground nonlinear problems (QF_ANIA, QF_AUFNIA-lite).
//!
//! Every engine has a grammar, and a term outside it is not merely awkward —
//! it is *invisible*. The polynomial translation has no production for
//! `select` or for an uninterpreted application, so an atom containing one is
//! dropped from the arithmetic problem entirely and the nonlinear engines then
//! reason about a strictly weaker formula, which they must refuse to answer
//! `sat` for. `(= (* (select A i) (select B i)) 6)` is not a hard problem; it
//! is a problem nobody was asked.
//!
//! This module is the purification step that asks it. Foreign subterms sitting
//! in arithmetic positions are replaced by arithmetic *unknowns*, so each
//! engine sees only its own grammar: the array and function structure moves
//! into the witness, and what reaches the polynomial search is a pure
//! polynomial system.
//!
//! ## Purification by abstraction, not by rewriting
//!
//! The textbook purification step rewrites the formula, introducing a fresh
//! constant and an interface equality `c = select(A, i)`. This module does the
//! same job by *declaring* `select(A, i)` an unknown and leaving the term
//! untouched — which is the same abstraction, minus the rewrite. That matters
//! for two reasons. First, `Solver`'s own assertion list keeps naming the
//! shapes the user wrote, so `(get-value ((select A i)))` still resolves and no
//! downstream pass has to be taught about interface constants. Second, and
//! decisively, the final check runs against those untouched assertions, so no
//! step here has to be trusted: an abstraction that lost a constraint produces
//! a candidate that fails the check, never a wrong answer. It also means this
//! module cannot collide with the encode-path purification in `oxiz-solver`'s
//! `encode::numeric_purification` — that one rewrites what the CDCL(T) core
//! encodes, this one only decides what the nonlinear search treats as a leaf,
//! and neither can see the other's output.
//!
//! Three reductions, in order:
//!
//! 1. **Read-over-write elimination.** `select(store(a, i, v), j)` is `v` when
//!    `i` and `j` are the same index and `select(a, j)` otherwise — McCarthy's
//!    axiom, applied as a rewrite rather than asserted as a lemma. This module
//!    applies it only where both indices fold to integer constants, so the
//!    choice between the two branches is decided outright and no case split is
//!    introduced. A store at a symbolic index leaves the rewrite undecided, and
//!    this module then declines the problem rather than guess.
//! 2. **Read abstraction.** What survives is `select(root, idx)` over free
//!    array symbols. Each such read becomes an arithmetic unknown, so
//!    `select(A, i) * select(B, j) = 6` is an ordinary nonlinear equation over
//!    two unknowns and the model-repair search can drive it.
//! 3. **Application abstraction.** A numeric uninterpreted application is an
//!    unknown too — its value is whatever the interpretation says, exactly like
//!    a variable. The one thing that distinguishes it from a variable is that
//!    an interpretation must be a *function* of the arguments, which
//!    [`crate::nl_eval::holds_under`] checks: two applications of one symbol
//!    whose arguments evaluate equal may not carry different values. The
//!    argument terms are ordinary arithmetic and their variables join the
//!    assignment, so that check has something to compare.
//!
//! ## Why the abstraction cannot lose the array axioms
//!
//! Abstracting reads as independent unknowns throws away exactly one thing:
//! that an array is a *function*, so two reads of the same symbol at the same
//! index must agree. Nothing in the abstracted problem says so, and a search
//! over it can happily assign them apart.
//!
//! That is caught rather than prevented. The witness this module builds records
//! each read as a **cell** of its array symbol, keyed by the *value* of the
//! index — so two reads that turn out to share an index are two writes to one
//! cell, and disagreeing values are rejected on the spot
//! (`ArrayWitness::build` returns `None`). Whatever survives is then checked
//! by [`crate::nl_eval::holds_under`] against the **original** assertions,
//! where `select` and `store` are evaluated by read-over-write from those very
//! cells. So neither reduction above has to be trusted: an unsound rewrite
//! would produce a candidate that fails the check, not a wrong answer.

use crate::nl_eval::{Interpretation, Value};
use crate::nl_repair_search::{Effort, Unknowns, WitnessBuilder};
use num_bigint::BigInt;
use num_rational::BigRational;
use num_traits::Zero;
use oxiz_core::ast::{TermId, TermKind, TermManager};
use oxiz_core::sort::SortKind;
use std::collections::{HashMap, HashSet};

/// Try to find a model for a ground array + nonlinear integer problem.
///
/// `None` means "no model found", never "unsatisfiable" — the reductions here
/// only ever make a satisfiable problem easier to witness.
#[must_use]
pub fn find_ground_model(
    assertions: &[TermId],
    manager: &mut TermManager,
    effort: Effort,
) -> Option<Interpretation> {
    if !mentions_foreign_arith(assertions, manager) {
        return None;
    }
    // Array-sorted equality is extensional: deciding it needs reasoning about
    // indices this reduction never enumerates, so it is out of scope. Refusing
    // keeps the answer honest.
    if has_array_equality(assertions, manager) {
        return None;
    }

    let mut rewriter = ReadOverWrite::new();
    let mut reduced: Vec<TermId> = Vec::with_capacity(assertions.len());
    for &assertion in assertions {
        reduced.push(rewriter.rewrite(assertion, manager)?);
    }

    // Collect the reads that survived. Each must be over a free array symbol
    // with a numeric element sort, or the abstraction below would be assigning
    // an integer to something that is not one.
    let mut reads: Vec<Read> = Vec::new();
    let mut unknowns = Unknowns::new();
    let mut applications: Vec<TermId> = Vec::new();
    collect_abstractions(
        &reduced,
        manager,
        &mut reads,
        &mut applications,
        &mut unknowns,
    )?;

    // Once a read or an application is abstracted, the terms *inside* it
    // vanish from the constraints — but the witness still has to say which
    // cell was read and which arguments were passed, so their variables must
    // be assigned regardless.
    let mut index_variables: Vec<TermId> = Vec::new();
    for read in &reads {
        collect_int_variables(read.index, manager, &mut index_variables);
    }
    for &application in &applications {
        collect_int_variables(application, manager, &mut index_variables);
    }

    // Read-over-write may have resolved every array term outright, leaving a
    // formula with no unknowns at all. Evaluating it is then the whole
    // decision procedure, and it is cheap enough to try before searching.
    let ground = Interpretation::empty();
    if crate::nl_eval::holds_under(assertions, manager, &ground) {
        return Some(ground);
    }

    let witness = ArrayWitness { reads };
    crate::nl_repair_search::search(
        &reduced,
        assertions,
        manager,
        effort,
        &unknowns,
        &index_variables,
        &witness,
    )
}

/// Collect the free Int-sorted variables of `term`.
///
/// Iterative, and only ever consulted for index expressions, which are
/// ordinary arithmetic.
fn collect_int_variables(term: TermId, manager: &TermManager, out: &mut Vec<TermId>) {
    let int_sort = manager.sorts.int_sort;
    let mut seen: HashSet<TermId> = HashSet::new();
    let mut stack = vec![term];
    while let Some(id) = stack.pop() {
        if !seen.insert(id) {
            continue;
        }
        let Some(node) = manager.get(id) else {
            continue;
        };
        if matches!(node.kind, TermKind::Var(_)) && node.sort == int_sort && !out.contains(&id) {
            out.push(id);
            continue;
        }
        push_children(&node.kind, &mut stack);
    }
}

/// One surviving array read.
#[derive(Debug, Clone)]
struct Read {
    /// The `select` term itself, which the search treats as an unknown.
    term: TermId,
    /// The free array symbol being read.
    root: TermId,
    /// The index expression.
    index: TermId,
}

/// Turns the search's raw assignment into an interpretation whose array cells
/// reproduce the reads.
struct ArrayWitness {
    reads: Vec<Read>,
}

impl WitnessBuilder for ArrayWitness {
    fn build(
        &self,
        assignment: &HashMap<TermId, BigInt>,
        manager: &TermManager,
    ) -> Option<Interpretation> {
        let mut interp = Interpretation::empty();
        for (&term, value) in assignment {
            interp.pin_int(term, value.clone());
        }
        // Unread cells need *some* value for the evaluator to be total; zero
        // is as good as any, and the check against the original assertions is
        // what decides whether the choice was acceptable.
        for read in &self.reads {
            interp.pin_fallback(read.root, Value::Num(BigRational::zero()));
        }

        let mut cells: HashMap<(TermId, BigRational), BigRational> = HashMap::new();
        for read in &self.reads {
            // The index is an ordinary arithmetic term over the assigned
            // unknowns, so it evaluates under the partial interpretation built
            // so far.
            let index = crate::nl_eval::evaluate(read.index, manager, &interp)?
                .as_num()?
                .clone();
            let value = assignment.get(&read.term)?;
            let value = BigRational::from_integer(value.clone());
            match cells.get(&(read.root, index.clone())) {
                // Two reads of one cell that disagree: the candidate is not a
                // function, so it is not a model of anything.
                Some(existing) if *existing != value => return None,
                Some(_) => {}
                None => {
                    cells.insert((read.root, index.clone()), value.clone());
                    interp.pin_cell(read.root, index, Value::Num(value));
                }
            }
        }
        Some(interp)
    }
}

/// Rewrites `select` over `store` away, where the indices decide it.
struct ReadOverWrite {
    memo: HashMap<TermId, Option<TermId>>,
}

impl ReadOverWrite {
    fn new() -> Self {
        Self {
            memo: HashMap::new(),
        }
    }

    /// Rewrite `root`, or `None` when some read-over-write could not be
    /// decided from constant indices alone.
    ///
    /// Iterative post-order over the hash-consed DAG with memoisation: nesting
    /// depth costs heap, not native stack, and a shared sub-term is rewritten
    /// once. A `select` whose base is itself rewritten into another `select`
    /// is re-opened rather than recursed into, so a store tower of any height
    /// collapses without the stack growing.
    fn rewrite(&mut self, root: TermId, manager: &mut TermManager) -> Option<TermId> {
        enum Task {
            Open(TermId),
            Close(TermId),
        }
        let mut work = vec![Task::Open(root)];
        let mut guard = 0u64;
        while let Some(task) = work.pop() {
            guard += 1;
            if guard > REWRITE_STEP_LIMIT {
                return None;
            }
            match task {
                Task::Open(id) => {
                    if self.memo.contains_key(&id) {
                        continue;
                    }
                    let kind = manager.get(id).map(|t| t.kind.clone())?;
                    let mut operands: Vec<TermId> = Vec::new();
                    push_children(&kind, &mut operands);
                    work.push(Task::Close(id));
                    for operand in operands {
                        work.push(Task::Open(operand));
                    }
                }
                Task::Close(id) => {
                    if self.memo.contains_key(&id) {
                        continue;
                    }
                    let rebuilt = self.rebuild(id, manager);
                    match rebuilt {
                        Rebuilt::Done(value) => {
                            self.memo.insert(id, value);
                        }
                        Rebuilt::Reopen(next) => {
                            // The rewrite produced a new term that itself
                            // needs rewriting (a `select` peeled off a store).
                            work.push(Task::Close(id));
                            work.push(Task::Open(next));
                            // Remember what `id` will become once `next` is
                            // resolved; `rebuild` re-reads it from the memo.
                            self.memo.remove(&id);
                        }
                    }
                }
            }
        }
        self.memo.get(&root).copied().flatten()
    }

    /// Rebuild one node from its already-rewritten children.
    fn rebuild(&mut self, id: TermId, manager: &mut TermManager) -> Rebuilt {
        let Some(node) = manager.get(id) else {
            return Rebuilt::Done(None);
        };
        let kind = node.kind.clone();
        let child = |slf: &Self, t: TermId| slf.memo.get(&t).copied().flatten();

        let TermKind::Select(base, index) = kind else {
            // Everything else is rebuilt structurally from its children.
            return Rebuilt::Done(rebuild_structural(id, manager, &self.memo));
        };
        let Some(base) = child(self, base) else {
            return Rebuilt::Done(None);
        };
        let Some(index) = child(self, index) else {
            return Rebuilt::Done(None);
        };

        let Some(base_node) = manager.get(base) else {
            return Rebuilt::Done(None);
        };
        let TermKind::Store(inner, written_at, written) = base_node.kind.clone() else {
            // A read of a free symbol: keep it, this is what gets abstracted.
            let rebuilt = manager.mk_select(base, index);
            return Rebuilt::Done(Some(rebuilt));
        };

        // Read over write. Both indices must fold to constants for the axiom
        // to pick a branch without a case split.
        let (Some(read_at), Some(store_at)) = (
            constant_integer(index, manager),
            constant_integer(written_at, manager),
        ) else {
            return Rebuilt::Done(None);
        };
        if read_at == store_at {
            return Rebuilt::Done(Some(written));
        }
        // Skip this write and read the array underneath — a fresh term that
        // must itself go through the rewrite.
        let peeled = manager.mk_select(inner, index);
        if self.memo.contains_key(&peeled) {
            return Rebuilt::Done(self.memo.get(&peeled).copied().flatten());
        }
        Rebuilt::Reopen(peeled)
    }
}

/// What [`ReadOverWrite::rebuild`] decided about a node.
enum Rebuilt {
    /// The node's rewrite is settled.
    Done(Option<TermId>),
    /// The node rewrote to a term that must itself be rewritten first.
    Reopen(TermId),
}

/// Total rewrite steps allowed, so a store tower that keeps peeling cannot
/// spin. Exceeding it declines the problem, which is always sound.
const REWRITE_STEP_LIMIT: u64 = 1_000_000;

/// Rebuild a non-`select` node from its rewritten children, preserving its
/// shape. `None` propagates: if any child could not be rewritten, neither can
/// this node.
fn rebuild_structural(
    id: TermId,
    manager: &mut TermManager,
    memo: &HashMap<TermId, Option<TermId>>,
) -> Option<TermId> {
    let kind = manager.get(id)?.kind.clone();
    let child = |t: TermId| memo.get(&t).copied().flatten();
    let children =
        |args: &[TermId]| -> Option<Vec<TermId>> { args.iter().map(|&a| child(a)).collect() };

    let rebuilt = match &kind {
        TermKind::Not(a) => manager.mk_not(child(*a)?),
        TermKind::And(args) => manager.mk_and(children(args)?),
        TermKind::Or(args) => manager.mk_or(children(args)?),
        TermKind::Xor(a, b) => {
            let (a, b) = (child(*a)?, child(*b)?);
            manager.mk_xor(a, b)
        }
        TermKind::Implies(a, b) => {
            let (a, b) = (child(*a)?, child(*b)?);
            manager.mk_implies(a, b)
        }
        TermKind::Ite(c, t, e) => {
            let (c, t, e) = (child(*c)?, child(*t)?, child(*e)?);
            manager.mk_ite(c, t, e)
        }
        TermKind::Eq(a, b) => {
            let (a, b) = (child(*a)?, child(*b)?);
            manager.mk_eq(a, b)
        }
        TermKind::Distinct(args) => manager.mk_distinct(children(args)?),
        TermKind::Neg(a) => manager.mk_neg(child(*a)?),
        TermKind::Add(args) => manager.mk_add(children(args)?),
        TermKind::Mul(args) => manager.mk_mul(children(args)?),
        TermKind::Sub(a, b) => {
            let (a, b) = (child(*a)?, child(*b)?);
            manager.mk_sub(a, b)
        }
        TermKind::Div(a, b) => {
            let (a, b) = (child(*a)?, child(*b)?);
            manager.mk_div(a, b)
        }
        TermKind::Mod(a, b) => {
            let (a, b) = (child(*a)?, child(*b)?);
            manager.mk_mod(a, b)
        }
        TermKind::Lt(a, b) => {
            let (a, b) = (child(*a)?, child(*b)?);
            manager.mk_lt(a, b)
        }
        TermKind::Le(a, b) => {
            let (a, b) = (child(*a)?, child(*b)?);
            manager.mk_le(a, b)
        }
        TermKind::Gt(a, b) => {
            let (a, b) = (child(*a)?, child(*b)?);
            manager.mk_gt(a, b)
        }
        TermKind::Ge(a, b) => {
            let (a, b) = (child(*a)?, child(*b)?);
            manager.mk_ge(a, b)
        }
        TermKind::Store(a, i, v) => {
            let (a, i, v) = (child(*a)?, child(*i)?, child(*v)?);
            manager.mk_store(a, i, v)
        }
        // Leaves keep their identity. An operator this reduction does not know
        // how to rebuild (a string or bit-vector op, an application) also
        // keeps it — safe, because any array structure underneath it would
        // have been rewritten into a term this node no longer references, and
        // the final check runs against the original assertions anyway.
        _ => id,
    };
    Some(rebuilt)
}

/// Immediate children to rewrite before a node can be rebuilt.
fn push_children(kind: &TermKind, out: &mut Vec<TermId>) {
    match kind {
        TermKind::Not(a) | TermKind::Neg(a) => out.push(*a),
        TermKind::And(args) | TermKind::Or(args) | TermKind::Add(args) | TermKind::Mul(args) => {
            out.extend(args.iter().copied());
        }
        TermKind::Distinct(args) => out.extend(args.iter().copied()),
        TermKind::Xor(a, b)
        | TermKind::Implies(a, b)
        | TermKind::Eq(a, b)
        | TermKind::Sub(a, b)
        | TermKind::Div(a, b)
        | TermKind::Mod(a, b)
        | TermKind::Lt(a, b)
        | TermKind::Le(a, b)
        | TermKind::Gt(a, b)
        | TermKind::Ge(a, b)
        | TermKind::Select(a, b) => {
            out.push(*a);
            out.push(*b);
        }
        TermKind::Ite(c, t, e) => {
            out.push(*c);
            out.push(*t);
            out.push(*e);
        }
        TermKind::Store(a, i, v) => {
            out.push(*a);
            out.push(*i);
            out.push(*v);
        }
        TermKind::Apply { args, .. } => out.extend(args.iter().copied()),
        _ => {}
    }
}

/// Gather the foreign terms to abstract, declining anything the abstraction
/// cannot represent.
fn collect_abstractions(
    assertions: &[TermId],
    manager: &TermManager,
    reads: &mut Vec<Read>,
    applications: &mut Vec<TermId>,
    unknowns: &mut Unknowns,
) -> Option<()> {
    let int_sort = manager.sorts.int_sort;
    let mut seen: HashSet<TermId> = HashSet::new();
    let mut stack: Vec<TermId> = assertions.to_vec();
    while let Some(id) = stack.pop() {
        if !seen.insert(id) {
            continue;
        }
        let node = manager.get(id)?;
        match &node.kind {
            TermKind::Select(base, index) => {
                // Only Int-sorted reads over a free array symbol are
                // abstractable: a read whose base is still a compound term
                // means step 1 left a read-over-write undecided.
                if node.sort != int_sort {
                    return None;
                }
                if !manager
                    .get(*base)
                    .is_some_and(|b| matches!(b.kind, TermKind::Var(_)))
                {
                    return None;
                }
                reads.push(Read {
                    term: id,
                    root: *base,
                    index: *index,
                });
                unknowns.insert(id);
            }
            TermKind::Apply { args, .. } => {
                // A numeric application is an unknown whose value the
                // congruence check ties to its arguments. A non-numeric one
                // has no arithmetic meaning to abstract.
                if node.sort != int_sort {
                    return None;
                }
                applications.push(id);
                unknowns.insert(id);
                // Arguments are still walked: a read nested inside one has to
                // be abstracted too, or the witness cannot evaluate it.
                stack.extend(args.iter().copied());
                continue;
            }
            _ => {}
        }
        push_children(&node.kind, &mut stack);
    }
    Some(())
}

/// Whether any assertion mentions a term this module would abstract — an
/// array operation or a numeric uninterpreted application. Without one there
/// is nothing to purify and the ordinary arithmetic search already sees the
/// whole problem.
fn mentions_foreign_arith(assertions: &[TermId], manager: &TermManager) -> bool {
    let mut seen: HashSet<TermId> = HashSet::new();
    let mut stack: Vec<TermId> = assertions.to_vec();
    while let Some(id) = stack.pop() {
        if !seen.insert(id) {
            continue;
        }
        let Some(node) = manager.get(id) else {
            continue;
        };
        match &node.kind {
            TermKind::Select(_, _) | TermKind::Store(_, _, _) => return true,
            TermKind::Apply { args, .. } => {
                if node.sort == manager.sorts.int_sort {
                    return true;
                }
                stack.extend(args.iter().copied());
            }
            _ => {}
        }
        push_children(&node.kind, &mut stack);
    }
    false
}

/// Whether any equality or `distinct` compares array-sorted operands.
fn has_array_equality(assertions: &[TermId], manager: &TermManager) -> bool {
    let is_array = |t: TermId| {
        manager
            .get(t)
            .and_then(|n| manager.sorts.get(n.sort))
            .is_some_and(|s| matches!(s.kind, SortKind::Array { .. }))
    };
    let mut seen: HashSet<TermId> = HashSet::new();
    let mut stack: Vec<TermId> = assertions.to_vec();
    while let Some(id) = stack.pop() {
        if !seen.insert(id) {
            continue;
        }
        let Some(node) = manager.get(id) else {
            continue;
        };
        match &node.kind {
            TermKind::Eq(a, b) if is_array(*a) || is_array(*b) => return true,
            TermKind::Distinct(args) if args.iter().copied().any(is_array) => return true,
            _ => {}
        }
        push_children(&node.kind, &mut stack);
    }
    false
}

/// Fold an integer-constant expression, or `None` if it is not constant.
///
/// Iterative, so a constant expression of any nesting depth folds without
/// native recursion.
fn constant_integer(term: TermId, manager: &TermManager) -> Option<BigInt> {
    let interp = Interpretation::empty();
    let value = crate::nl_eval::evaluate(term, manager, &interp)?;
    let rational = value.as_num()?;
    rational.is_integer().then(|| rational.to_integer())
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::nl_eval::holds_under;

    fn setup() -> (TermManager, TermId, TermId, TermId) {
        let mut tm = TermManager::new();
        let int_sort = tm.sorts.int_sort;
        let array_sort = tm.sorts.array(int_sort, int_sort);
        let a = tm.mk_var("arrA", array_sort);
        let b = tm.mk_var("arrB", array_sort);
        let i = tm.mk_var("idx", int_sort);
        (tm, a, b, i)
    }

    /// Two reads of free arrays multiplied together: after abstraction this is
    /// an ordinary `p*q = 6` over two unknowns.
    #[test]
    fn test_pr31_array_product_of_reads_is_sat() {
        let (mut tm, a, b, i) = setup();
        let read_a = tm.mk_select(a, i);
        let read_b = tm.mk_select(b, i);
        let product = tm.mk_mul(vec![read_a, read_b]);
        let thirty_five = tm.mk_int(35);
        let three = tm.mk_int(3);
        let assertions = vec![
            tm.mk_eq(product, thirty_five),
            tm.mk_ge(read_a, three),
            tm.mk_ge(read_b, three),
        ];
        let interp = find_ground_model(&assertions, &mut tm, Effort::default())
            .expect("select(A,i)*select(B,i) = 35 with both reads at least 3 has a model");
        assert!(holds_under(&assertions, &tm, &interp));
    }

    /// The same shape with an unreachable product: the search may not claim a
    /// model, because no assignment inside the box satisfies it.
    #[test]
    fn test_pr31_array_product_out_of_range_finds_no_model() {
        let (mut tm, a, b, i) = setup();
        let read_a = tm.mk_select(a, i);
        let read_b = tm.mk_select(b, i);
        let product = tm.mk_mul(vec![read_a, read_b]);
        let fifteen = tm.mk_int(15);
        let two = tm.mk_int(2);
        let four = tm.mk_int(4);
        let assertions = vec![
            tm.mk_eq(product, fifteen),
            tm.mk_ge(read_a, two),
            tm.mk_le(read_a, four),
            tm.mk_ge(read_b, two),
            tm.mk_le(read_b, four),
        ];
        let effort = Effort {
            moves: 3_000,
            restarts: 4,
            candidates_per_move: 10,
        };
        assert!(
            find_ground_model(&assertions, &mut tm, effort).is_none(),
            "15 needs a factor of 5, which the 2..4 box does not contain"
        );
    }

    /// Read-over-write at a constant index: the store decides the read, so a
    /// model must respect the stored value rather than treat the read as free.
    #[test]
    fn test_pr31_array_read_over_write_respects_stored_value() {
        let (mut tm, a, _b, _i) = setup();
        let three = tm.mk_int(3);
        let eight = tm.mk_int(8);
        let written = tm.mk_store(a, three, eight);
        let read_back = tm.mk_select(written, three);
        let square = tm.mk_mul(vec![read_back, read_back]);
        let sixty_four = tm.mk_int(64);
        let assertions = vec![tm.mk_eq(square, sixty_four)];
        let interp = find_ground_model(&assertions, &mut tm, Effort::default())
            .expect("the read is pinned to 8 by the store, and 8*8 = 64");
        assert!(holds_under(&assertions, &tm, &interp));
    }

    /// The unsatisfiable companion: the store pins the read to 8, so demanding
    /// its square be 65 cannot hold and no model may be produced.
    #[test]
    fn test_pr31_array_read_over_write_conflict_finds_no_model() {
        let (mut tm, a, _b, _i) = setup();
        let three = tm.mk_int(3);
        let eight = tm.mk_int(8);
        let written = tm.mk_store(a, three, eight);
        let read_back = tm.mk_select(written, three);
        let square = tm.mk_mul(vec![read_back, read_back]);
        let sixty_five = tm.mk_int(65);
        let assertions = vec![tm.mk_eq(square, sixty_five)];
        let effort = Effort {
            moves: 2_000,
            restarts: 3,
            candidates_per_move: 8,
        };
        assert!(find_ground_model(&assertions, &mut tm, effort).is_none());
    }

    /// A read at an index the store did not write must see through to the
    /// underlying array, not the stored value.
    #[test]
    fn test_pr31_array_read_past_write_sees_underlying_array() {
        let (mut tm, a, _b, _i) = setup();
        let three = tm.mk_int(3);
        let seven = tm.mk_int(7);
        let eight = tm.mk_int(8);
        let written = tm.mk_store(a, three, eight);
        let read_elsewhere = tm.mk_select(written, seven);
        let direct = tm.mk_select(a, seven);
        let product = tm.mk_mul(vec![read_elsewhere, direct]);
        let one_twenty_one = tm.mk_int(121);
        let assertions = vec![
            tm.mk_eq(product, one_twenty_one),
            tm.mk_ge(read_elsewhere, three),
        ];
        let interp = find_ground_model(&assertions, &mut tm, Effort::default())
            .expect("both terms denote the same cell of A, so the model sets it to 11");
        assert!(holds_under(&assertions, &tm, &interp));
    }

    /// Array-sorted equality is extensional and out of this reduction's scope;
    /// it must decline rather than answer on a fragment it does not model.
    #[test]
    fn test_pr31_array_equality_is_declined() {
        let (mut tm, a, b, i) = setup();
        let read_a = tm.mk_select(a, i);
        let square = tm.mk_mul(vec![read_a, read_a]);
        let four = tm.mk_int(4);
        let assertions = vec![tm.mk_eq(a, b), tm.mk_eq(square, four)];
        assert!(find_ground_model(&assertions, &mut tm, Effort::default()).is_none());
    }

    /// A product of two uninterpreted applications: outside this reduction the
    /// whole atom is invisible to the arithmetic engines, because `f(...)` has
    /// no polynomial translation.
    #[test]
    fn test_pr31_purified_application_product_is_sat() {
        let mut tm = TermManager::new();
        let int_sort = tm.sorts.int_sort;
        let x = tm.mk_var("ax", int_sort);
        let y = tm.mk_var("ay", int_sort);
        let f_of_x = tm.mk_apply("f", vec![x], int_sort);
        let f_of_y = tm.mk_apply("f", vec![y], int_sort);
        let product = tm.mk_mul(vec![f_of_x, f_of_y]);
        let twenty_one = tm.mk_int(21);
        let three = tm.mk_int(3);
        let assertions = vec![
            tm.mk_eq(product, twenty_one),
            tm.mk_ge(f_of_x, three),
            tm.mk_ge(f_of_y, three),
        ];
        let interp = find_ground_model(&assertions, &mut tm, Effort::default())
            .expect("f(x)*f(y) = 21 with both at least 3 has a model");
        assert!(holds_under(&assertions, &tm, &interp));
    }

    /// Congruence is the one array/function axiom abstraction throws away, and
    /// the witness check is what puts it back. Here the arguments are forced
    /// equal, so `f(x)` and `f(y)` are the same application and cannot take
    /// the two different values the product would need.
    #[test]
    fn test_pr31_purified_application_congruence_blocks_bad_model() {
        let mut tm = TermManager::new();
        let int_sort = tm.sorts.int_sort;
        let x = tm.mk_var("cx", int_sort);
        let y = tm.mk_var("cy", int_sort);
        let f_of_x = tm.mk_apply("f", vec![x], int_sort);
        let f_of_y = tm.mk_apply("f", vec![y], int_sort);
        let one = tm.mk_int(1);
        let two = tm.mk_int(2);
        let assertions = vec![tm.mk_eq(x, y), tm.mk_eq(f_of_x, one), tm.mk_eq(f_of_y, two)];
        let effort = Effort {
            moves: 3_000,
            restarts: 4,
            candidates_per_move: 10,
        };
        assert!(
            find_ground_model(&assertions, &mut tm, effort).is_none(),
            "x = y makes f(x) and f(y) one application; it cannot be both 1 and 2"
        );
    }

    /// Two reads of the *same* array symbol at the same index: abstraction
    /// gives them independent unknowns, and the cell-based witness is what
    /// refuses to let them disagree.
    #[test]
    fn test_pr31_array_same_cell_read_twice_cannot_disagree() {
        let (mut tm, a, _b, i) = setup();
        let int_sort = tm.sorts.int_sort;
        let j = tm.mk_var("idx2", int_sort);
        let read_i = tm.mk_select(a, i);
        let read_j = tm.mk_select(a, j);
        let one = tm.mk_int(1);
        let two = tm.mk_int(2);
        let assertions = vec![tm.mk_eq(i, j), tm.mk_eq(read_i, one), tm.mk_eq(read_j, two)];
        let effort = Effort {
            moves: 3_000,
            restarts: 4,
            candidates_per_move: 10,
        };
        assert!(
            find_ground_model(&assertions, &mut tm, effort).is_none(),
            "i = j makes both reads the same cell, which cannot hold 1 and 2"
        );
    }

    /// A store at a symbolic index leaves read-over-write undecided, so the
    /// reduction must decline instead of picking a branch.
    #[test]
    fn test_pr31_array_symbolic_store_index_is_declined() {
        let (mut tm, a, _b, i) = setup();
        let eight = tm.mk_int(8);
        let written = tm.mk_store(a, i, eight);
        let zero = tm.mk_int(0);
        let read_back = tm.mk_select(written, zero);
        let square = tm.mk_mul(vec![read_back, read_back]);
        let sixty_four = tm.mk_int(64);
        let assertions = vec![tm.mk_eq(square, sixty_four)];
        assert!(find_ground_model(&assertions, &mut tm, Effort::default()).is_none());
    }
}
