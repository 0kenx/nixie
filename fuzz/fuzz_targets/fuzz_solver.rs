//! Fuzz target for the SMT solver
//!
//! This fuzzer tests the solver with random valid SMT-LIB2 scripts using
//! structured fuzzing to generate well-formed commands.
//!
//! # Soundness oracles
//!
//! Discarding `check()`'s result (`let _ = solver.check(&mut tm)`) only lets
//! libFuzzer catch panics/crashes: it can never find a *wrong* sat/unsat
//! answer. This target therefore keeps track of every assertion it feeds the
//! solver and, whenever the solver reports `Sat`, evaluates the returned
//! model against those assertions (`assert_model_satisfies`). A model that
//! does not satisfy the formula it was built from is a genuine soundness
//! bug, not a mere crash, and is exactly the class of defect a "no oracle"
//! fuzzer can never detect. `check()` is also required to be idempotent
//! (repeating it with no intervening mutation must reproduce the same
//! verdict), and an empty assertion set is known-satisfiable by
//! construction, so `Unsat` on zero assertions is always a bug.
//!
//! The parser-to-solver end-to-end path (SMT-LIB2 text fed through
//! `parse_script` instead of this target's structured `SmtCommand`
//! generator) is fuzzed separately by the `fuzz_parse_and_solve` binary,
//! which applies the same oracles.

#![no_main]

use arbitrary::{Arbitrary, Unstructured};
use libfuzzer_sys::fuzz_target;
use num_bigint::BigInt;
use nixie::solver::{Model, SolverResult};
use nixie::{Solver, TermId, TermManager};

/// Represents a structured SMT command
#[derive(Debug, Arbitrary)]
enum SmtCommand {
    /// Declare a boolean constant
    DeclareBool { name_idx: u8 },
    /// Declare an integer constant
    DeclareInt { name_idx: u8 },
    /// Declare a real constant
    DeclareReal { name_idx: u8 },
    /// Assert a simple boolean constraint
    AssertBool { var_idx: u8, is_positive: bool },
    /// Assert an integer comparison
    AssertIntCmp {
        var_idx: u8,
        cmp_type: CmpType,
        value: i16,
    },
    /// Assert an arithmetic constraint
    AssertArith {
        lhs_var: u8,
        rhs_var: u8,
        op: ArithOp,
        result: i16,
    },
    /// Assert an equality between two variables
    AssertEq { lhs_var: u8, rhs_var: u8 },
    /// Check satisfiability
    CheckSat,
    /// Push a scope
    Push,
    /// Pop a scope
    Pop,
    /// Reset the solver
    Reset,
}

#[derive(Debug, Arbitrary, Clone, Copy)]
enum CmpType {
    Lt,
    Le,
    Gt,
    Ge,
    Eq,
}

#[derive(Debug, Arbitrary, Clone, Copy)]
enum ArithOp {
    Add,
    Sub,
    Mul,
}

/// Build a name from an index
fn make_name(prefix: &str, idx: u8) -> String {
    format!("{}_{}", prefix, idx % 8)
}

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
    let mut unstructured = Unstructured::new(data);

    // Limit the number of commands to prevent OOM and timeouts
    let max_commands = 50;

    let mut solver = Solver::new();
    let mut tm = TermManager::new();

    // Track declared variables
    let mut bool_vars: Vec<(String, TermId)> = Vec::new();
    let mut int_vars: Vec<(String, TermId)> = Vec::new();
    let mut real_vars: Vec<(String, TermId)> = Vec::new();

    // Track push/pop balance
    let mut scope_depth = 0;

    // Track every assertion currently in scope, one frame per push level
    // (frame 0 is the base/always-active scope), so the soundness oracle
    // knows exactly which assertions must hold in a satisfying model.
    let mut assertion_frames: Vec<Vec<TermId>> = vec![Vec::new()];

    // Generate and execute commands
    for _ in 0..max_commands {
        let cmd: Result<SmtCommand, _> = unstructured.arbitrary();
        let cmd = match cmd {
            Ok(cmd) => cmd,
            Err(_) => break,
        };

        match cmd {
            SmtCommand::DeclareBool { name_idx } => {
                let name = make_name("b", name_idx);
                // Only declare if not already declared
                if !bool_vars.iter().any(|(n, _)| n == &name) {
                    let var = tm.mk_var(&name, tm.sorts.bool_sort);
                    bool_vars.push((name, var));
                }
            }
            SmtCommand::DeclareInt { name_idx } => {
                let name = make_name("i", name_idx);
                if !int_vars.iter().any(|(n, _)| n == &name) {
                    let var = tm.mk_var(&name, tm.sorts.int_sort);
                    int_vars.push((name, var));
                }
            }
            SmtCommand::DeclareReal { name_idx } => {
                let name = make_name("r", name_idx);
                if !real_vars.iter().any(|(n, _)| n == &name) {
                    let var = tm.mk_var(&name, tm.sorts.real_sort);
                    real_vars.push((name, var));
                }
            }
            SmtCommand::AssertBool { var_idx, is_positive } => {
                if !bool_vars.is_empty() {
                    let (_, var) = &bool_vars[var_idx as usize % bool_vars.len()];
                    let term = if is_positive {
                        *var
                    } else {
                        tm.mk_not(*var)
                    };
                    solver.assert(term, &mut tm);
                    assertion_frames
                        .last_mut()
                        .expect("assertion_frames always has a base frame")
                        .push(term);
                }
            }
            SmtCommand::AssertIntCmp {
                var_idx,
                cmp_type,
                value,
            } => {
                if !int_vars.is_empty() {
                    let (_, var) = &int_vars[var_idx as usize % int_vars.len()];
                    let const_term = tm.mk_int(BigInt::from(value));
                    let cmp_term = match cmp_type {
                        CmpType::Lt => tm.mk_lt(*var, const_term),
                        CmpType::Le => tm.mk_le(*var, const_term),
                        CmpType::Gt => tm.mk_gt(*var, const_term),
                        CmpType::Ge => tm.mk_ge(*var, const_term),
                        CmpType::Eq => tm.mk_eq(*var, const_term),
                    };
                    solver.assert(cmp_term, &mut tm);
                    assertion_frames
                        .last_mut()
                        .expect("assertion_frames always has a base frame")
                        .push(cmp_term);
                }
            }
            SmtCommand::AssertArith {
                lhs_var,
                rhs_var,
                op,
                result,
            } => {
                if int_vars.len() >= 2 {
                    let (_, lhs) = &int_vars[lhs_var as usize % int_vars.len()];
                    let (_, rhs) = &int_vars[rhs_var as usize % int_vars.len()];
                    let arith_term = match op {
                        ArithOp::Add => tm.mk_add([*lhs, *rhs]),
                        ArithOp::Sub => tm.mk_sub(*lhs, *rhs),
                        ArithOp::Mul => tm.mk_mul([*lhs, *rhs]),
                    };
                    let result_term = tm.mk_int(BigInt::from(result));
                    let eq_term = tm.mk_eq(arith_term, result_term);
                    solver.assert(eq_term, &mut tm);
                    assertion_frames
                        .last_mut()
                        .expect("assertion_frames always has a base frame")
                        .push(eq_term);
                }
            }
            SmtCommand::AssertEq { lhs_var, rhs_var } => {
                if int_vars.len() >= 2 {
                    let (_, lhs) = &int_vars[lhs_var as usize % int_vars.len()];
                    let (_, rhs) = &int_vars[rhs_var as usize % int_vars.len()];
                    let eq_term = tm.mk_eq(*lhs, *rhs);
                    solver.assert(eq_term, &mut tm);
                    assertion_frames
                        .last_mut()
                        .expect("assertion_frames always has a base frame")
                        .push(eq_term);
                }
            }
            SmtCommand::CheckSat => {
                let active_assertions: Vec<TermId> =
                    assertion_frames.iter().flatten().copied().collect();
                check_oracles(&mut solver, &mut tm, &active_assertions);
            }
            SmtCommand::Push => {
                solver.push();
                scope_depth += 1;
                assertion_frames.push(Vec::new());
            }
            SmtCommand::Pop => {
                if scope_depth > 0 {
                    solver.pop();
                    scope_depth -= 1;
                    assertion_frames.pop();
                }
            }
            SmtCommand::Reset => {
                solver.reset();
                bool_vars.clear();
                int_vars.clear();
                real_vars.clear();
                scope_depth = 0;
                assertion_frames = vec![Vec::new()];
            }
        }
    }
});
