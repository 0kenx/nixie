//! Contradictions present before push must survive pop even when the unit
//! insertion fast path did not retain a clause in the database.
use nixie_sat::{Lit, Solver, SolverResult};

#[test]
fn parent_empty_clause_survives_nested_scopes_without_solving() {
    let mut solver = Solver::new();
    solver.add_clause([]);
    solver.push();
    solver.push();
    solver.pop();
    assert_eq!(solver.solve(), SolverResult::Unsat);
    solver.pop();
    assert_eq!(solver.solve(), SolverResult::Unsat);
}

#[test]
fn parent_contradictory_units_survive_pop_without_solving() {
    let mut solver = Solver::new();
    let x = solver.new_var();
    solver.add_clause([Lit::pos(x)]);
    solver.add_clause([Lit::neg(x)]);
    solver.push();
    solver.pop();
    assert_eq!(solver.solve(), SolverResult::Unsat);
}

#[test]
fn derived_parent_contradiction_survives_pop() {
    let mut solver = Solver::new();
    let x = solver.new_var();
    let y = solver.new_var();
    for a in [Lit::pos(x), Lit::neg(x)] {
        for b in [Lit::pos(y), Lit::neg(y)] {
            solver.add_clause([a, b]);
        }
    }
    assert_eq!(solver.solve(), SolverResult::Unsat);
    solver.push();
    solver.pop();
    assert_eq!(solver.solve(), SolverResult::Unsat);
}

#[test]
fn scoped_contradiction_survives_inner_pop_but_not_outer_pop() {
    let mut solver = Solver::new();
    let x = solver.new_var();
    solver.add_clause([Lit::pos(x)]);
    assert_eq!(solver.solve(), SolverResult::Sat);
    solver.push();
    solver.add_clause([Lit::neg(x)]);
    assert_eq!(solver.solve(), SolverResult::Unsat);
    solver.push();
    solver.pop();
    assert_eq!(solver.solve(), SolverResult::Unsat);
    solver.pop();
    assert_eq!(solver.solve(), SolverResult::Sat);
}
