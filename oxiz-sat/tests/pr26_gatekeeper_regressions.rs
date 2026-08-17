//! ELS-half of the PR #26 gatekeeper review, ported from v0.3.2.
//!
//! SK-1 (soundness): a variable one-shot inprocessing already eliminated
//! could be *reintroduced* by a later `add_clause`/assumption with no guard.
//! `pick_branch_var` skips eliminated variables, so nothing assigns them
//! during search, and model reconstruction overwrote whatever the new clause
//! demanded – yielding a false `Sat`.
//!
//! Equivalent-literal substitution (ELS) has a sound rewrite (fold the
//! reintroduced literal through the substitution map), so a reintroduced ELS
//! variable is rewritten to its class representative rather than poisoned.
//! This file pins that rewrite on `add_clause`.
//!
//! The BVE half of the suite (poisoning via `SolverError`) is not ported:
//! main's BVE eliminates no variables under its sound literal-count bound,
//! so the BVE-reintroduction path is unreachable in practice. The
//! `solve_with_assumptions` variant additionally needs UNSAT-core
//! reverse-mapping through the rewrite and is deferred.

use oxiz_sat::{Lit, Solver, SolverConfig, SolverResult, Var};

fn els_enabled_solver() -> Solver {
    Solver::with_config(SolverConfig {
        enable_equiv_substitution: true,
        // Lucky pre-solving runs before every other pass (cadical
        // `luckyearly`) and would answer this trivially satisfiable
        // instance outright, so the ELS fold under test would never fire.
        enable_lucky: false,
        ..SolverConfig::default()
    })
}

/// Wire up `a ≡ b` (via `(¬a∨b)∧(¬b∨a)`) and run the first `solve()`, which
/// (with ELS enabled) folds one variable into the other. Returns the two
/// variables; the caller does not need to know which one ended up as the
/// canonical representative – the fix is symmetric in that choice.
fn solve_and_fold_equivalence(solver: &mut Solver) -> (Lit, Lit) {
    let a = solver.new_var();
    let b = solver.new_var();
    solver.add_clause([Lit::neg(a), Lit::pos(b)]);
    solver.add_clause([Lit::neg(b), Lit::pos(a)]);
    assert_eq!(solver.solve(), SolverResult::Sat);
    assert!(
        solver.var_eliminated(a) || solver.var_eliminated(b),
        "one of the two equivalent variables must be folded into the other"
    );
    (Lit::pos(a), Lit::pos(b))
}

#[test]
fn test_pr26_gatekeeper_sk1_els_add_clause_reintroduction_is_rewritten_soundly() {
    let mut solver = els_enabled_solver();
    let (a, b) = solve_and_fold_equivalence(&mut solver);

    // ¬a and b together with a≡b is unconditionally UNSAT: a≡b forces a==b
    // in every model, so ¬a implies ¬b, contradicting the unit clause b. The
    // second `add_clause` may catch this immediately (its own trivially_unsat
    // fast path, once b is rewritten to a's already-fixed representative) or
    // defer to `solve()` – either is correct; what must never happen is a
    // later `solve()` reporting `Sat`.
    assert!(solver.add_clause([a.negate()]));
    let _ = solver.add_clause([b]);

    assert_eq!(
        solver.solve(),
        SolverResult::Unsat,
        "a later add_clause naming an ELS-substituted variable must still be \
         checked against the equivalence, not silently ignored"
    );
    assert!(
        solver.error().is_none(),
        "ELS reintroduction has a sound rewrite; it must never poison the solver"
    );
}

#[test]
fn test_pr26_gatekeeper_sk1_els_add_clause_reintroduction_still_finds_sat_models() {
    // Positive control for the fix above: the rewrite must not turn every
    // reintroduction into a spurious UNSAT either. `b ∨ c` (c fresh) is
    // satisfiable together with a≡b; the reconstructed model must actually
    // satisfy it once translated back through b's substitution.
    let mut solver = els_enabled_solver();
    let (_a, b) = solve_and_fold_equivalence(&mut solver);
    let c: Var = solver.new_var();
    assert!(solver.add_clause([b, Lit::pos(c)]));

    assert_eq!(solver.solve(), SolverResult::Sat);
    let b_true = solver.model_value(b.var()) == oxiz_sat::LBool::True;
    let c_true = solver.model_value(c) == oxiz_sat::LBool::True;
    assert!(
        b_true || c_true,
        "reconstructed model must satisfy the clause that reintroduced b"
    );
}
