//! Structural invariant checks for the CDCL(T) SMT solver.
//!
//! This module is a read-only structural net over [`Solver`]'s bookkeeping:
//! the term <-> SAT-variable mapping, the theory-constraint side tables, the
//! Tseitin encoding memo, the push/pop context stack, and the assertion /
//! unsat-core registries. Every function here is pure, never mutates the
//! solver, and returns `Err(String)` describing the first violation found or
//! `Ok(())`.
//!
//! # Why this module was rewritten from scratch
//!
//! An earlier version of this file was never compiled (it was not declared in
//! `lib.rs`) and had drifted onto an API that this crate never had:
//! `Solver::trail_size()`, `Solver::get_trail_entry()`, `Solver::status()`,
//! `SolverStatus`, `Assignment`, `Solver::get_arith_theory()`,
//! `Solver::check_theory_model_validity()` — none of those exist. Several of
//! its checks were also nonsense against *any* API: it tested
//! `solver.trail_size() < 0` and `entry.decision_level < 0` on values that
//! were compared against `usize` elsewhere in the same function, i.e. they
//! could never fire. Rather than resurrect dead assertions, this file checks
//! properties that the *current* data model actually guarantees, mirroring
//! `oxiz_sat::invariants`.
//!
//! # Deliberately absent: CDCL-trail and model-validity checks
//!
//! Unlike the SAT core, this crate does not own an assignment trail or a
//! decision level — those live inside [`oxiz_sat::Solver`] and are already
//! covered by `oxiz_sat::invariants`. The `Solver::trail` field here is an
//! *undo journal* for `push`/`pop`, not a CDCL trail, so the only meaningful
//! invariants over it are the context-stack ones below.
//!
//! Model validity is likewise not checked here: verifying that a model
//! satisfies the assertions requires evaluating terms under a
//! `TermManager`, which the solver already does behind its own soundness
//! gate (`Solver::model_refutes_assertions`). Duplicating a weaker version of
//! that check here would add a second, less accurate answer to the same
//! question.
//!
//! Reference: Z3's `smt/smt_context_inv.cpp`.

#[allow(unused_imports)]
use crate::prelude::*;
use crate::solver::Solver;

/// Runs every structural invariant in this module, returning the first
/// violation found.
///
/// Cheap enough to call after any solver API entry point in a debug build:
/// the cost is linear in the number of encoded terms and assertions, with no
/// term traversal and no allocation beyond one variable-index set.
///
/// # Errors
///
/// Returns a human-readable description of the first violated invariant.
pub fn check_all_invariants(solver: &Solver) -> Result<(), String> {
    check_var_term_mapping(solver)?;
    check_side_table_vars(solver)?;
    check_encoded_terms(solver)?;
    check_context_stack(solver)?;
    check_assertion_registry(solver)?;
    check_unsat_core(solver)?;
    Ok(())
}

/// The term -> SAT-variable map and the variable -> term vector agree, and
/// the mapping is injective.
///
/// `Solver::get_or_create_var` allocates a fresh SAT variable per term and
/// writes both directions, and `Solver::pop` retracts the forward entry
/// (`TrailOp::VarCreated`) together with truncating the reverse vector to its
/// push-time length, so the two must stay in lockstep. A stale forward entry
/// surviving a `pop` would hand a later scope a SAT variable whose defining
/// clauses have already been retracted.
///
/// Note that the reverse direction is intentionally *not* required to be
/// total: `get_or_create_var` pads `var_to_term` with a placeholder whenever
/// the SAT core hands out a variable index above the current length, so an
/// index with no live term is legitimate.
///
/// # Errors
///
/// Returns a description of the first inconsistent or duplicated mapping.
pub fn check_var_term_mapping(solver: &Solver) -> Result<(), String> {
    let mut seen: FxHashSet<usize> = FxHashSet::default();
    for (&term, &var) in &solver.term_to_var {
        let idx = var.index();
        if idx >= solver.var_to_term.len() {
            return Err(format!(
                "term {term:?} maps to SAT variable {idx} but var_to_term only has {} entries",
                solver.var_to_term.len()
            ));
        }
        if solver.var_to_term[idx] != term {
            return Err(format!(
                "term {term:?} maps to SAT variable {idx}, but var_to_term[{idx}] is {:?}",
                solver.var_to_term[idx]
            ));
        }
        if !seen.insert(idx) {
            return Err(format!(
                "SAT variable {idx} is the image of more than one term (term_to_var is not injective)"
            ));
        }
    }
    Ok(())
}

/// Every SAT variable used as a key in a theory side table is a variable the
/// solver actually owns.
///
/// `var_to_constraint` and `var_to_parsed_arith` are retracted together by
/// `TrailOp::ConstraintAdded`; an entry naming a variable past the end of
/// `var_to_term` would mean a constraint outlived the scope that created its
/// variable, which feeds a retracted inequality back to the arithmetic
/// solver.
///
/// # Errors
///
/// Returns a description of the first out-of-range side-table key.
pub fn check_side_table_vars(solver: &Solver) -> Result<(), String> {
    let num_vars = solver.var_to_term.len();
    for var in solver.var_to_constraint.keys() {
        if var.index() >= num_vars {
            return Err(format!(
                "var_to_constraint holds SAT variable {} but the solver only has {num_vars} variables",
                var.index()
            ));
        }
    }
    for var in solver.var_to_parsed_arith.keys() {
        if var.index() >= num_vars {
            return Err(format!(
                "var_to_parsed_arith holds SAT variable {} but the solver only has {num_vars} variables",
                var.index()
            ));
        }
    }
    // A parsed linear constraint is only ever recorded alongside a
    // `Constraint` for the same variable, so the arithmetic map is a subset.
    for var in solver.var_to_parsed_arith.keys() {
        if !solver.var_to_constraint.contains_key(var) {
            return Err(format!(
                "SAT variable {} has a parsed arithmetic constraint but no Constraint entry",
                var.index()
            ));
        }
    }
    Ok(())
}

/// Every literal cached in the Tseitin memo names a live SAT variable.
///
/// `Solver::pop` retracts `encoded_terms` entry by entry, keeping the ones
/// written at an outer level because their backing clauses survive the scope.
/// A term's SAT variable is always created no later than its memo entry is
/// written, so a surviving entry must name a variable that also predates the
/// push and therefore survives `var_to_term.truncate`.  An entry pointing past
/// the end of `var_to_term` means the memo outlived a retraction it should
/// have been undone by.
///
/// # Errors
///
/// Returns a description of the first memo entry naming an unknown variable.
pub fn check_encoded_terms(solver: &Solver) -> Result<(), String> {
    let num_vars = solver.var_to_term.len();
    for (&term, &(lit, _polarity)) in &solver.encoded_terms {
        if lit.var().index() >= num_vars {
            return Err(format!(
                "encoded_terms maps {term:?} to a literal over SAT variable {} but the solver only has {num_vars} variables",
                lit.var().index()
            ));
        }
    }
    Ok(())
}

/// The push/pop context stack is a monotone chain of snapshots bounded by the
/// current state.
///
/// Each `push` records the *current* lengths, so going outwards-in the
/// recorded lengths can only grow, and the outermost recorded length can
/// never exceed what the solver holds now. A violation means a `pop` failed
/// to restore some length (leaking a retracted assertion into an outer
/// scope), or that a snapshot was taken out of order.
///
/// # Errors
///
/// Returns a description of the first non-monotone or out-of-range snapshot.
pub fn check_context_stack(solver: &Solver) -> Result<(), String> {
    let mut prev_assertions = 0usize;
    let mut prev_vars = 0usize;
    let mut prev_trail = 0usize;

    for (depth, state) in solver.context_stack.iter().enumerate() {
        if state.num_assertions < prev_assertions {
            return Err(format!(
                "context level {depth} snapshots {} assertions, fewer than the enclosing level's {prev_assertions}",
                state.num_assertions
            ));
        }
        if state.num_vars < prev_vars {
            return Err(format!(
                "context level {depth} snapshots {} SAT variables, fewer than the enclosing level's {prev_vars}",
                state.num_vars
            ));
        }
        if state.trail_position < prev_trail {
            return Err(format!(
                "context level {depth} snapshots undo-trail position {}, before the enclosing level's {prev_trail}",
                state.trail_position
            ));
        }
        prev_assertions = state.num_assertions;
        prev_vars = state.num_vars;
        prev_trail = state.trail_position;
    }

    if prev_assertions > solver.assertions.len() {
        return Err(format!(
            "innermost context snapshots {prev_assertions} assertions but the solver now holds {}",
            solver.assertions.len()
        ));
    }
    if prev_vars > solver.var_to_term.len() {
        return Err(format!(
            "innermost context snapshots {prev_vars} SAT variables but the solver now holds {}",
            solver.var_to_term.len()
        ));
    }
    if prev_trail > solver.trail.len() {
        return Err(format!(
            "innermost context snapshots undo-trail position {prev_trail} but the trail is only {} long",
            solver.trail.len()
        ));
    }
    Ok(())
}

/// Named-assertion bookkeeping points at assertions that still exist.
///
/// The registry is append-only within a scope and truncated by
/// `TrailOp::NamedAssertionAdded` on `pop`, with each entry's `index` field
/// being the position of the assertion it tracks. A dangling index would make
/// an unsat core name an assertion the user already retracted.
///
/// # Errors
///
/// Returns a description of the first dangling or duplicated entry.
pub fn check_assertion_registry(solver: &Solver) -> Result<(), String> {
    let num_assertions = solver.assertions.len();
    let mut seen: FxHashSet<u32> = FxHashSet::default();
    for (position, named) in solver.named_assertions.iter().enumerate() {
        if named.index as usize >= num_assertions {
            return Err(format!(
                "named assertion at position {position} tracks assertion #{} but only {num_assertions} assertions exist",
                named.index
            ));
        }
        if !seen.insert(named.index) {
            return Err(format!(
                "assertion #{} is tracked by more than one named-assertion entry",
                named.index
            ));
        }
    }
    Ok(())
}

/// A produced unsat core references real assertions and carries no more names
/// than indices.
///
/// `Solver::build_unsat_core` pushes one index per tracked assertion but only
/// pushes a name for the entries that actually have one, so `names` is a
/// (possibly shorter) companion of `indices` rather than a parallel array.
///
/// # Errors
///
/// Returns a description of the first malformed core entry.
pub fn check_unsat_core(solver: &Solver) -> Result<(), String> {
    let Some(core) = solver.unsat_core.as_ref() else {
        return Ok(());
    };
    let num_assertions = solver.assertions.len();
    let mut seen: FxHashSet<u32> = FxHashSet::default();
    for &index in &core.indices {
        if index as usize >= num_assertions {
            return Err(format!(
                "unsat core references assertion #{index} but only {num_assertions} assertions exist"
            ));
        }
        if !seen.insert(index) {
            return Err(format!("unsat core lists assertion #{index} twice"));
        }
    }
    if core.names.len() > core.indices.len() {
        return Err(format!(
            "unsat core carries {} names for only {} indices",
            core.names.len(),
            core.indices.len()
        ));
    }
    Ok(())
}

impl Solver {
    /// Release build: compiles away entirely.
    #[cfg(not(debug_assertions))]
    #[inline]
    pub fn debug_check_invariants(&self, _context: &str) {}

    /// Debug-build structural self-check: runs [`check_all_invariants`] and
    /// panics with `context` if any of them is violated.
    ///
    /// This is the hook to place next to any solver state transition you want
    /// guarded; it costs nothing in release builds because the whole body is
    /// compiled out.
    ///
    /// # Panics
    ///
    /// Panics (debug builds only) if any structural invariant is violated.
    #[cfg(debug_assertions)]
    pub fn debug_check_invariants(&self, context: &str) {
        if let Err(msg) = check_all_invariants(self) {
            panic!("SMT solver invariant violated ({context}): {msg}");
        }
    }
}

#[cfg(all(test, feature = "std"))]
mod tests {
    use super::*;
    use crate::SolverResult;
    use num_bigint::BigInt;
    use oxiz_core::ast::TermManager;

    #[test]
    fn fresh_solver_satisfies_all_invariants() {
        let solver = Solver::new();
        assert_eq!(check_all_invariants(&solver), Ok(()));
        solver.debug_check_invariants("fresh");
    }

    #[test]
    fn boolean_sat_run_satisfies_all_invariants() {
        let mut solver = Solver::new();
        let mut tm = TermManager::new();

        let p = tm.mk_var("p", tm.sorts.bool_sort);
        let q = tm.mk_var("q", tm.sorts.bool_sort);
        let formula = tm.mk_and(vec![p, q]);
        solver.assert(formula, &mut tm);

        assert_eq!(solver.check(&mut tm), SolverResult::Sat);
        assert_eq!(check_all_invariants(&solver), Ok(()));
        solver.debug_check_invariants("after sat check");
    }

    #[test]
    fn unsat_run_with_cores_satisfies_all_invariants() {
        let mut solver = Solver::new();
        solver.set_produce_unsat_cores(true);
        let mut tm = TermManager::new();

        let p = tm.mk_var("p", tm.sorts.bool_sort);
        let not_p = tm.mk_not(p);
        solver.assert(p, &mut tm);
        solver.assert(not_p, &mut tm);

        assert_eq!(solver.check(&mut tm), SolverResult::Unsat);
        assert_eq!(check_all_invariants(&solver), Ok(()));
    }

    #[test]
    fn arithmetic_run_satisfies_all_invariants() {
        let mut solver = Solver::new();
        let mut tm = TermManager::new();
        solver.set_logic("QF_LIA");

        let x = tm.mk_var("x", tm.sorts.int_sort);
        let five = tm.mk_int(BigInt::from(5));
        let ten = tm.mk_int(BigInt::from(10));
        let lower = tm.mk_ge(x, five);
        let upper = tm.mk_le(x, ten);
        solver.assert(lower, &mut tm);
        solver.assert(upper, &mut tm);

        assert_eq!(solver.check(&mut tm), SolverResult::Sat);
        assert_eq!(check_all_invariants(&solver), Ok(()));
    }

    #[test]
    fn push_pop_round_trip_satisfies_all_invariants() {
        let mut solver = Solver::new();
        let mut tm = TermManager::new();

        let p = tm.mk_var("p", tm.sorts.bool_sort);
        solver.assert(p, &mut tm);
        assert_eq!(check_all_invariants(&solver), Ok(()));

        for _ in 0..8 {
            solver.push();
            let q = tm.mk_var("q", tm.sorts.bool_sort);
            let both = tm.mk_and(vec![p, q]);
            solver.assert(both, &mut tm);
            assert_eq!(solver.check(&mut tm), SolverResult::Sat);
            assert_eq!(check_all_invariants(&solver), Ok(()));
        }

        for _ in 0..8 {
            solver.pop();
            assert_eq!(check_all_invariants(&solver), Ok(()));
        }

        assert_eq!(solver.context_level(), 0);
        assert_eq!(solver.check(&mut tm), SolverResult::Sat);
        assert_eq!(check_all_invariants(&solver), Ok(()));
    }

    /// Exercises the in-loop hooks on the array-axiom refinement path: a
    /// read-over-write candidate model is refuted, the SAT trail is dropped to
    /// root and the theory solvers are reset, and the search is replayed.  The
    /// term/variable tables survive that reset untouched and must still agree.
    #[test]
    fn array_refinement_run_satisfies_all_invariants() {
        let mut solver = Solver::new();
        let mut tm = TermManager::new();
        solver.set_logic("QF_ALIA");

        let int_sort = tm.sorts.int_sort;
        let array_sort = tm.sorts.array(int_sort, int_sort);
        let a = tm.mk_var("a", array_sort);
        let i = tm.mk_var("i", int_sort);
        let five = tm.mk_int(BigInt::from(5));
        let stored = tm.mk_store(a, i, five);
        let read_back = tm.mk_select(stored, i);
        let axiom = tm.mk_eq(read_back, five);
        solver.assert(axiom, &mut tm);

        // Whatever the verdict, every structural invariant must hold at the
        // end of a search that took the refinement path.
        let _ = solver.check(&mut tm);
        assert_eq!(check_all_invariants(&solver), Ok(()));
    }

    /// Exercises the MBQI round-boundary hook: each round encodes fresh
    /// instantiation lemmas, allocating SAT variables and extending the
    /// Tseitin memo mid-search.
    #[test]
    fn quantified_run_satisfies_all_invariants() {
        let mut solver = Solver::new();
        let mut tm = TermManager::new();

        let int_sort = tm.sorts.int_sort;
        let x = tm.mk_var("x", int_sort);
        let zero = tm.mk_int(BigInt::from(0));
        let fx = tm.mk_apply("f", [x], int_sort);
        let body = tm.mk_ge(fx, zero);
        let forall = tm.mk_forall([("x", int_sort)], body);
        solver.assert(forall, &mut tm);

        let k = tm.mk_var("k", int_sort);
        let fk = tm.mk_apply("f", [k], int_sort);
        let neg_one = tm.mk_int(BigInt::from(-1));
        let contradiction = tm.mk_eq(fk, neg_one);
        solver.assert(contradiction, &mut tm);

        let _ = solver.check(&mut tm);
        assert_eq!(check_all_invariants(&solver), Ok(()));
    }

    #[test]
    fn reset_satisfies_all_invariants() {
        let mut solver = Solver::new();
        let mut tm = TermManager::new();

        let p = tm.mk_var("p", tm.sorts.bool_sort);
        solver.assert(p, &mut tm);
        assert_eq!(solver.check(&mut tm), SolverResult::Sat);

        solver.reset();
        assert_eq!(check_all_invariants(&solver), Ok(()));
    }

    #[test]
    fn context_stack_check_rejects_a_non_monotone_snapshot() {
        // Build a solver with two nested scopes, then corrupt the outer
        // snapshot so that it claims more assertions than the inner one.
        let mut solver = Solver::new();
        let mut tm = TermManager::new();

        let p = tm.mk_var("p", tm.sorts.bool_sort);
        let q = tm.mk_var("q", tm.sorts.bool_sort);
        solver.assert(p, &mut tm);
        solver.push();
        solver.assert(q, &mut tm);
        solver.push();
        assert_eq!(check_all_invariants(&solver), Ok(()));
        assert_eq!(solver.context_stack.len(), 2);
        assert!(solver.context_stack[0].num_assertions >= 1);

        let inner = solver.context_stack.len() - 1;
        solver.context_stack[inner].num_assertions = 0;
        let err = check_context_stack(&solver).expect_err("corrupted stack must be rejected");
        assert!(err.contains("fewer than the enclosing level"), "{err}");
    }

    #[test]
    fn unsat_core_check_rejects_a_dangling_index() {
        let mut solver = Solver::new();
        solver.set_produce_unsat_cores(true);
        let mut tm = TermManager::new();

        let p = tm.mk_var("p", tm.sorts.bool_sort);
        let not_p = tm.mk_not(p);
        solver.assert(p, &mut tm);
        solver.assert(not_p, &mut tm);
        assert_eq!(solver.check(&mut tm), SolverResult::Unsat);

        let dangling = solver.assertions.len() as u32 + 7;
        if let Some(core) = solver.unsat_core.as_mut() {
            core.indices.push(dangling);
        }
        let err = check_unsat_core(&solver).expect_err("dangling core index must be rejected");
        assert!(err.contains("only"), "{err}");
    }
}
