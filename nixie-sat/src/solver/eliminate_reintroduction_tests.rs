//! Elimination-reintroduction regressions (2026-09-15): a BVE-eliminated
//! variable re-mentioned by a later `add_clause` must have its retired
//! clauses resurrected and stay enforced — the extension-stack walk's
//! witness toggle alone can fabricate a model that violates a live clause
//! over the variable (the Rodin invalid-model class, layer 2).
use super::*;

/// Checks a total model against a list of original clauses (DIMACS).
fn assert_model_satisfies(solver: &Solver, clauses: &[&[i32]], ctx: &str) {
    for clause in clauses {
        let satisfied = clause.iter().any(|&d| {
            let lit = Lit::from_dimacs(d);
            match solver.model_value(lit.var()) {
                LBool::True => lit.is_pos(),
                LBool::False => lit.is_neg(),
                LBool::Undef => false,
            }
        });
        assert!(
            satisfied,
            "{ctx}: model violates original clause {clause:?}"
        );
    }
}

/// A theory callback that does nothing (mirrors tests.rs's `NullTheory`,
/// which is private to that module).
struct NullTheory;

impl TheoryCallback for NullTheory {
    fn on_assignment(&mut self, _lit: Lit) -> TheoryCheckResult {
        TheoryCheckResult::Sat
    }

    fn final_check(&mut self) -> TheoryCheckResult {
        TheoryCheckResult::Sat
    }

    fn on_backtrack(&mut self, _level: u32) {}
}

/// Layer 2 — BVE/ext-stack reintroduction. A BVE-eliminated variable's
/// retired clauses live only as extension-stack obligations; a later clause
/// over the variable constrains it, and the walk's witness toggle can then
/// falsify a live clause. The gatekeeper must resurrect the retired clauses
/// and make the variable branchable again. Parents are ternary on the
/// positive side so retirement leaves no binary-implication-graph edge
/// behind (a lingering edge would propagate the entailed literal and mask
/// the mechanism under test).
#[test]
fn bve_eliminated_var_remention_resurrects_its_retired_clauses() {
    let mut solver = Solver::new();
    solver.ensure_vars(4);
    solver.add_clause_dimacs(&[1, 2, 3]); // v ∨ a ∨ s
    solver.add_clause_dimacs(&[-1, 4]); // ¬v ∨ b
    // Eliminate v (var 0) directly, mirroring the eliminator's own tests.
    solver.elim_mark.resize(4, false);
    solver.elim_var_flag.resize(4, false);
    solver.bve_def.resize(4, Vec::new());
    solver.mark_elim_one(Var::new(0));
    let mut ticks = 64_000_000u64; // DEFINITION_PHASE_TICKS (private const)
    let (eliminated, _complete, _, _) = solver.elim_round_with_budget(10, &mut ticks);
    assert_eq!(eliminated, 1, "fixture must actually eliminate v");
    assert!(solver.var_eliminated(Var::new(0)));

    // Reintroduction (refinement-loop shape): a lemma mentions ¬v, and the
    // units force v = a = s = false — falsifying the retired (v ∨ a ∨ s).
    assert!(solver.add_clause_dimacs(&[-1, 5])); // ¬v ∨ c
    assert!(
        solver.ext_rementioned.contains(&Var::new(0)),
        "the mention must void v's extension-stack obligations"
    );
    assert!(
        solver.branchable(Var::new(0)),
        "a reintroduced variable must be branchable again"
    );
    assert!(solver.add_clause_dimacs(&[-5])); // ¬c ⇒ v = false
    assert!(solver.add_clause_dimacs(&[-2])); // ¬a
    assert!(solver.add_clause_dimacs(&[-3])); // ¬s

    let mut theory = NullTheory;
    assert_eq!(
        solver.solve_with_theory(&mut theory),
        SolverResult::Unsat,
        "(v ∨ a ∨ s) ∧ ¬v ∧ ¬a ∧ ¬s is unsatisfiable; a `Sat` here means the          retired clause was not restored"
    );
}

/// The satisfiable twin: only the ¬v constraint is reintroduced, so the
/// restored (v ∨ a ∨ s) is satisfied through a (or s), and the model must
/// carry v = false — the extension-stack walk must not toggle v back
/// against the live (¬v ∨ c) with c = false.
#[test]
fn bve_remention_model_keeps_the_reintroduced_constraint() {
    let mut solver = Solver::new();
    solver.ensure_vars(4);
    solver.add_clause_dimacs(&[1, 2, 3]); // v ∨ a ∨ s
    solver.add_clause_dimacs(&[-1, 4]); // ¬v ∨ b
    solver.elim_mark.resize(4, false);
    solver.elim_var_flag.resize(4, false);
    solver.bve_def.resize(4, Vec::new());
    solver.mark_elim_one(Var::new(0));
    let mut ticks = 64_000_000u64; // DEFINITION_PHASE_TICKS (private const)
    let _ = solver.elim_round_with_budget(10, &mut ticks);

    assert!(solver.add_clause_dimacs(&[-1, 5])); // ¬v ∨ c reintroduces v
    assert!(solver.add_clause_dimacs(&[-5])); // ¬c ⇒ v = false
    let mut theory = NullTheory;
    assert_eq!(solver.solve_with_theory(&mut theory), SolverResult::Sat);
    assert!(
        solver.model_value(Var::new(0)).is_false(),
        "v is forced false by (¬v ∨ c) ∧ ¬c; a true value here is the          extension-stack walk toggling v against a live clause"
    );
    let cs: [&[i32]; 4] = [&[1, 2, 3], &[-1, 4], &[-1, 5], &[-5]];
    assert_model_satisfies(&solver, &cs, "bve remention");
}
