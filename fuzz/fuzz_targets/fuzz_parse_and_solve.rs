//! Fuzz target for the parser-to-solver end-to-end path
//!
//! Parses arbitrary bytes as an SMT-LIB2 script and feeds the resulting
//! commands into the solver, exercising the same soundness oracles as
//! `fuzz_solver`'s structured-command fuzzing (see that target's module
//! docs for the full rationale). This target complements `fuzz_solver` by
//! driving the solver exclusively through `parse_script`, so parser bugs
//! that only manifest once their output reaches the solver (malformed
//! terms, wrong sorts, etc.) are exercised directly instead of only via
//! the structured `SmtCommand` generator.
//!
//! # Soundness oracles
//!
//! Discarding `check()`'s result only lets libFuzzer catch panics/crashes:
//! it can never find a *wrong* sat/unsat answer. This target therefore
//! keeps track of every assertion it feeds the solver and, whenever the
//! solver reports `Sat`, evaluates the returned model against those
//! assertions (`assert_model_satisfies`). A model that does not satisfy
//! the formula it was built from is a genuine soundness bug, not a mere
//! crash. `check()` is also required to be idempotent (repeating it with
//! no intervening mutation must reproduce the same verdict), and an empty
//! assertion set is known-satisfiable by construction, so `Unsat` on zero
//! assertions is always a bug.

#![no_main]

use libfuzzer_sys::fuzz_target;
use nixie::core::smtlib::{Command, parse_script};
use nixie::solver::{Model, SolverResult};
use nixie::{Solver, TermId, TermManager};

/// Soundness oracle: every assertion the solver was fed MUST evaluate to
/// `true` under a model the solver claims is satisfying. If it doesn't, the
/// solver returned `Sat` for an unsatisfiable formula (or built a model that
/// doesn't correspond to its own verdict) - a genuine soundness bug.
fn assert_model_satisfies(model: &Model, assertions: &[TermId], tm: &mut TermManager) {
    let true_term = tm.mk_true();
    for &assertion in assertions {
        let value = model.eval(assertion, tm);
        assert_eq!(
            value, true_term,
            "soundness oracle failed: solver returned Sat but the model does not \
             satisfy assertion {assertion:?} (evaluated to {value:?} instead of true)"
        );
    }
}

/// Re-running `check()` with no intervening assert/push/pop/reset must
/// reproduce the same verdict.
fn assert_check_idempotent(solver: &mut Solver, tm: &mut TermManager, first: SolverResult) {
    let second = solver.check(tm);
    assert_eq!(
        second, first,
        "check() is not idempotent: got {first:?} then {second:?} with no intervening mutation"
    );
}

/// Run the soundness oracles for a `CheckSat` result against the
/// assertions that are currently active (i.e. not popped off the scope
/// stack).
fn check_oracles(solver: &mut Solver, tm: &mut TermManager, active_assertions: &[TermId]) {
    let result = solver.check(tm);
    match result {
        SolverResult::Sat => {
            // Clone the model so the immutable borrow of `solver` doesn't
            // outlive the mutable borrow needed for the idempotency re-check.
            if let Some(model) = solver.model().cloned() {
                assert_model_satisfies(&model, active_assertions, tm);
            }
            assert_check_idempotent(solver, tm, result);
        }
        SolverResult::Unsat => {
            // The empty theory is satisfiable by construction (the trivial
            // model satisfies zero constraints), so Unsat on zero active
            // assertions is always a soundness bug, never a legitimate
            // "unknown-but-reported-as-unsat" corner case.
            assert!(
                !active_assertions.is_empty(),
                "soundness oracle failed: solver returned Unsat with zero active assertions"
            );
            assert_check_idempotent(solver, tm, result);
        }
        SolverResult::Unknown => {
            // Honest "I don't know" - nothing to check against a model.
        }
    }
}

fuzz_target!(|data: &[u8]| {
    let Ok(input) = std::str::from_utf8(data) else {
        return;
    };

    let mut tm = TermManager::new();

    let Ok(commands) = parse_script(input, &mut tm) else {
        return;
    };

    let mut solver = Solver::new();
    let mut scope_depth: u32 = 0;
    let mut assertion_frames: Vec<Vec<TermId>> = vec![Vec::new()];

    for cmd in commands {
        match cmd {
            Command::Assert(term) => {
                solver.assert(term, &mut tm);
                assertion_frames
                    .last_mut()
                    .expect("assertion_frames always has a base frame")
                    .push(term);
            }
            Command::CheckSat => {
                let active_assertions: Vec<TermId> =
                    assertion_frames.iter().flatten().copied().collect();
                check_oracles(&mut solver, &mut tm, &active_assertions);
            }
            Command::Push(n) => {
                for _ in 0..n.min(10) {
                    solver.push();
                    scope_depth += 1;
                    assertion_frames.push(Vec::new());
                }
            }
            Command::Pop(n) => {
                for _ in 0..n.min(10) {
                    if scope_depth > 0 {
                        solver.pop();
                        scope_depth -= 1;
                        assertion_frames.pop();
                    }
                }
            }
            Command::Reset => {
                solver.reset();
                scope_depth = 0;
                assertion_frames = vec![Vec::new()];
            }
            _ => {
                // Skip other commands
            }
        }
    }
});
