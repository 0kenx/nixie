//! Regression: a theory conflict clause that still lists an UNASSIGNED literal
//! must not crash or corrupt the CDCL(T) trail.
//!
//! The MBQI / quantifier-instantiation layer builds its conflict clause from a
//! per-atom polarity map that is not pruned on every SAT backtrack (a restart in
//! particular). It can therefore report a "conflict" whose clause contains a
//! variable the SAT core has since unassigned – the literal is not falsified, so
//! the clause is really an *asserting lemma* (unit under the current assignment),
//! not a conflict. Feeding that into the all-false 1-UIP machinery used to
//! duplicate the asserting literal at the backtrack level, tripping the theory
//! trail-consistency `debug_assert` in `nixie-sat/src/solver/conflict.rs`
//! (panic in debug) and producing a wrong top-level UNSAT in release.
//!
//! These tests drive the real [`Solver::solve_with_theory`] loop with a mock
//! theory that reports exactly such a clause, and assert the solver survives and
//! returns a sound verdict.

use nixie_sat::{Lit, Solver, SolverResult, TheoryCallback, TheoryCheckResult, Var};

/// Mock theory that, on the very first Boolean assignment, reports a "conflict"
/// clause consisting of that (true, hence its negation false) literal plus a
/// second literal for a variable that is still unassigned – i.e. an asserting
/// lemma with one open literal. It fires only once; every later check is `Sat`.
struct StaleConflictTheory {
    vars: Vec<Var>,
    fired: bool,
}

impl TheoryCallback for StaleConflictTheory {
    fn on_assignment(&mut self, lit: Lit) -> TheoryCheckResult {
        if !self.fired {
            // This is the first assignment, so exactly one variable is on the
            // trail: any *other* declared variable is guaranteed unassigned and
            // makes the reported clause a one-open-literal asserting lemma.
            if let Some(&open) = self.vars.iter().find(|v| **v != lit.var()) {
                self.fired = true;
                // `lit` is true on the trail, so `lit.negate()` is false; the
                // `open` literal is unassigned. `collect()` infers the
                // `SmallVec<[Lit; 8]>` the `Conflict` variant expects.
                return TheoryCheckResult::Conflict(
                    [lit.negate(), Lit::pos(open)].into_iter().collect(),
                );
            }
        }
        TheoryCheckResult::Sat
    }

    fn final_check(&mut self) -> TheoryCheckResult {
        TheoryCheckResult::Sat
    }

    fn on_backtrack(&mut self, _level: u32) {}
}

#[test]
fn theory_conflict_with_unassigned_literal_does_not_panic() {
    let mut solver = Solver::new();
    let a = solver.new_var();
    let b = solver.new_var();
    let c = solver.new_var();

    // One satisfiable clause so the solver must make at least one decision, which
    // triggers the mock theory's (asserting-lemma) "conflict".
    solver.add_clause([Lit::pos(a), Lit::pos(b), Lit::pos(c)]);

    let mut theory = StaleConflictTheory {
        vars: vec![a, b, c],
        fired: false,
    };

    // Pre-fix this panicked at the theory trail-consistency assert. Post-fix the
    // asserting lemma is propagated and the search completes with a sound verdict.
    let result = solver.solve_with_theory(&mut theory);
    assert!(
        matches!(result, SolverResult::Sat | SolverResult::Unknown),
        "an asserting theory lemma must never yield a spurious UNSAT (got {result:?})"
    );
    assert!(theory.fired, "the mock theory must have reported its lemma");

    // The instance is genuinely satisfiable, so the honest verdict is Sat.
    assert_eq!(
        result,
        SolverResult::Sat,
        "the satisfiable instance must be solved as SAT"
    );
}

#[test]
fn theory_conflict_with_unassigned_literal_model_satisfies_clause() {
    // Same reproduction, but additionally confirm the returned model satisfies
    // the original clause – the asserting-lemma handling keeps the search sound.
    let mut solver = Solver::new();
    let a = solver.new_var();
    let b = solver.new_var();
    let c = solver.new_var();
    solver.add_clause([Lit::pos(a), Lit::pos(b), Lit::pos(c)]);

    let mut theory = StaleConflictTheory {
        vars: vec![a, b, c],
        fired: false,
    };
    let result = solver.solve_with_theory(&mut theory);
    assert_eq!(result, SolverResult::Sat);

    let satisfied = [a, b, c].iter().any(|&v| solver.model_value(v).is_true());
    assert!(satisfied, "the model must satisfy the clause (a ∨ b ∨ c)");
}
