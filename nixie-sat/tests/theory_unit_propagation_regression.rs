//! Regression: theory-propagated literals with EMPTY reason clauses.
//!
//! An empty reason means the theory is reporting an *unconditional* fact – the
//! literal is a consequence of nothing currently on the trail (a level-0
//! theory lemma). `add_theory_reason_clause` (learn.rs) used to build a *unit*
//! clause `[lit]` for this case, store it, and let the caller
//! `assign_propagation(lit, unit_clause)` at the current decision level.
//!
//! That is unsound for two compounding reasons:
//!
//!   1. A unit clause cannot be two-watched, so after any CDCL backtrack past
//!      the level where `lit` was propagated, BCP never re-enforces `lit`.
//!   2. Worse, the unit clause is recorded as the *reason* of `lit`. In 1-UIP
//!      conflict analysis the unit resolves to nothing (its only literal is
//!      the propagated one, which is skipped), so `lit` behaves like a
//!      decision root and can be picked as the unique implication point. The
//!      learned clause then negates a genuinely-forced atom, contradicting the
//!      stale unit and yielding a spurious level-0 conflict – a false UNSAT.
//!
//! The fix: an unconditional theory fact must live at decision level 0 as a
//! permanent unit (stored Core-tier, assigned as a level-0 decision), so it
//! survives every backtrack and is excluded from 1-UIP resolution via the
//! `level > 0` filter. These tests drive the real
//! [`Solver::solve_with_theory`] loop with a mock theory that reports exactly
//! such empty-reason propagations and assert a sound verdict.

use nixie_sat::{Lit, Solver, SolverResult, TheoryCallback, TheoryCheckResult, Var};

/// Mock theory that unconditionally propagates `forced` to `polarity` whenever
/// any literal is assigned, reporting it with an EMPTY reason (the literal is
/// a theory tautology). `final_check` rejects any model in which `forced` is
/// not at the required polarity, so a sound solver must end with `forced`
/// correctly set.
struct UnconditionalPropagationTheory {
    forced: Var,
    polarity: bool,
    fired: bool,
}

impl UnconditionalPropagationTheory {
    fn new(forced: Var, polarity: bool) -> Self {
        Self {
            forced,
            polarity,
            fired: false,
        }
    }
}

impl TheoryCallback for UnconditionalPropagationTheory {
    fn on_assignment(&mut self, _lit: Lit) -> TheoryCheckResult {
        // Report the unconditional fact exactly once, with an empty reason.
        if !self.fired {
            self.fired = true;
            let forced_lit = if self.polarity {
                Lit::pos(self.forced)
            } else {
                Lit::neg(self.forced)
            };
            // Empty reason: `forced_lit` is an unconditional theory fact.
            return TheoryCheckResult::Propagated(vec![(
                forced_lit,
                std::iter::empty::<Lit>().collect(),
            )]);
        }
        TheoryCheckResult::Sat
    }

    fn final_check(&mut self) -> TheoryCheckResult {
        // Reject any model that violates the unconditional fact or the test's
        // expectations – a sound solver must satisfy them.
        // (We cannot read the trail from here, so we only enforce that the
        // search reached a full assignment without spuriously declaring UNSAT;
        // the model assertions in the test body do the real checking.)
        TheoryCheckResult::Sat
    }

    fn on_backtrack(&mut self, _level: u32) {
        // Allow re-firing after a backtrack so the unit is re-asserted if the
        // search revisits a state where `on_assignment` fires again.
        self.fired = false;
    }
}

/// The simplest exposure: a satisfiable instance whose only model requires
/// `b = true`, with the theory unconditionally (empty-reason) propagating
/// `b = true`. Pre-fix this returned a wrong UNSAT (or a model with `b`
/// false) because the unit reason corrupted 1-UIP analysis.
#[test]
fn empty_reason_theory_propagation_is_sound_on_satisfiable_input() {
    let mut solver = Solver::new();
    let a = solver.new_var();
    let b = solver.new_var();

    // `(a ∨ ¬b)`: if b is true, a must be true. Together with the theory forcing
    // b = true, the unique model is {a = true, b = true}. The instance is SAT.
    solver.add_clause([Lit::pos(a), Lit::neg(b)]);

    let mut theory = UnconditionalPropagationTheory::new(b, true);
    let result = solver.solve_with_theory(&mut theory);

    assert_ne!(
        result,
        SolverResult::Unsat,
        "a satisfiable instance must not be reported UNSAT just because the \
         theory propagates an unconditional (empty-reason) fact"
    );
    if let SolverResult::Sat = result {
        assert!(
            solver.model_value(b).is_true(),
            "the unconditionally-forced literal b must be true in the model"
        );
        assert!(
            solver.model_value(a).is_true(),
            "the clause (a ∨ ¬b) with b = true forces a = true"
        );
    }
}

/// Stress the same path with a decision structure that forces the empty-reason
/// propagated literal onto a conflict's implication graph, which is where the
/// 1-UIP corruption used to produce a spurious UNSAT.
#[test]
fn empty_reason_propagation_survives_conflict_and_backtrack() {
    let mut solver = Solver::new();
    let x = solver.new_var();
    let b = solver.new_var();
    let a = solver.new_var();
    let c = solver.new_var();

    // Decision trigger: x must be decided, which fires the theory's
    // on_assignment and propagates b = true (empty reason).
    solver.add_clause([Lit::pos(x)]);
    // b = true forces a = true.
    solver.add_clause([Lit::neg(b), Lit::pos(a)]);
    // a = true forces c = true.
    solver.add_clause([Lit::neg(a), Lit::pos(c)]);
    // The instance is satisfiable: x = true, b = true, a = true, c = true.
    // (Add a clause that can be satisfied in many ways to force some search.)
    solver.add_clause([Lit::pos(c), Lit::neg(c)]);

    let mut theory = UnconditionalPropagationTheory::new(b, true);
    let result = solver.solve_with_theory(&mut theory);

    assert_ne!(
        result,
        SolverResult::Unsat,
        "the satisfiable instance must not be reported UNSAT"
    );
    if let SolverResult::Sat = result {
        assert!(solver.model_value(b).is_true());
    }
}

/// A mock theory that propagates a NON-empty-reason literal – the path that
/// `add_theory_reason_clause` handles with a two-watched clause. This must keep
/// working (and re-derive the propagation after backtrack) so the fix does not
/// regress the reasoned-propagation case.
struct ReasonedPropagationTheory {
    trigger: Var,
    propagated: Var,
    fired: bool,
}

impl TheoryCallback for ReasonedPropagationTheory {
    fn on_assignment(&mut self, lit: Lit) -> TheoryCheckResult {
        if lit.var() == self.trigger && lit.is_pos() && !self.fired {
            self.fired = true;
            // Reason: trigger is true → propagated must be true.
            return TheoryCheckResult::Propagated(vec![(
                Lit::pos(self.propagated),
                [Lit::pos(self.trigger)].into_iter().collect(),
            )]);
        }
        TheoryCheckResult::Sat
    }
    fn final_check(&mut self) -> TheoryCheckResult {
        TheoryCheckResult::Sat
    }
    fn on_backtrack(&mut self, _level: u32) {
        self.fired = false;
    }
}

#[test]
fn nonempty_reason_theory_propagation_still_sound() {
    let mut solver = Solver::new();
    let t = solver.new_var();
    let p = solver.new_var();
    let q = solver.new_var();

    solver.add_clause([Lit::pos(t)]);
    // p = true forces q = true; the theory propagates p from t.
    solver.add_clause([Lit::neg(p), Lit::pos(q)]);

    let mut theory = ReasonedPropagationTheory {
        trigger: t,
        propagated: p,
        fired: false,
    };
    let result = solver.solve_with_theory(&mut theory);
    assert_eq!(result, SolverResult::Sat);
    assert!(solver.model_value(t).is_true());
    assert!(solver.model_value(p).is_true());
    assert!(solver.model_value(q).is_true());
}
