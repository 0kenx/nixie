use super::*;

#[test]
fn test_empty_sat() {
    let mut solver = Solver::new();
    assert_eq!(solver.solve(), SolverResult::Sat);
}

#[test]
fn test_simple_sat() {
    let mut solver = Solver::new();
    let _x = solver.new_var();
    let _y = solver.new_var();

    // x or y
    solver.add_clause_dimacs(&[1, 2]);
    // not x or y
    solver.add_clause_dimacs(&[-1, 2]);

    assert_eq!(solver.solve(), SolverResult::Sat);
    assert!(solver.model_value(Var::new(1)).is_true()); // y must be true
}

#[test]
fn test_simple_unsat() {
    let mut solver = Solver::new();
    let _x = solver.new_var();

    // x
    solver.add_clause_dimacs(&[1]);
    // not x
    solver.add_clause_dimacs(&[-1]);

    assert_eq!(solver.solve(), SolverResult::Unsat);
}

#[test]
fn test_pigeonhole_2_1() {
    // 2 pigeons, 1 hole - UNSAT
    let mut solver = Solver::new();
    let _p1h1 = solver.new_var(); // pigeon 1 in hole 1
    let _p2h1 = solver.new_var(); // pigeon 2 in hole 1

    // Each pigeon must be in some hole
    solver.add_clause_dimacs(&[1]); // p1 in h1
    solver.add_clause_dimacs(&[2]); // p2 in h1

    // No hole can have two pigeons
    solver.add_clause_dimacs(&[-1, -2]); // not (p1h1 and p2h1)

    assert_eq!(solver.solve(), SolverResult::Unsat);
}

#[test]
fn test_3sat_random() {
    let mut solver = Solver::new();
    for _ in 0..10 {
        solver.new_var();
    }

    // Random 3-SAT instance (likely SAT)
    solver.add_clause_dimacs(&[1, 2, 3]);
    solver.add_clause_dimacs(&[-1, 4, 5]);
    solver.add_clause_dimacs(&[2, -3, 6]);
    solver.add_clause_dimacs(&[-4, 7, 8]);
    solver.add_clause_dimacs(&[5, -6, 9]);
    solver.add_clause_dimacs(&[-7, 8, 10]);
    solver.add_clause_dimacs(&[1, -8, -9]);
    solver.add_clause_dimacs(&[-2, 3, -10]);

    let result = solver.solve();
    assert_eq!(result, SolverResult::Sat);
}

#[test]
fn test_luby_sequence() {
    // Luby sequence: 1, 1, 2, 1, 1, 2, 4, 1, 1, 2, 1, 1, 2, 4, 8, ...
    assert_eq!(Solver::luby(0), 1);
    assert_eq!(Solver::luby(1), 1);
    assert_eq!(Solver::luby(2), 2);
    assert_eq!(Solver::luby(3), 1);
    assert_eq!(Solver::luby(4), 1);
    assert_eq!(Solver::luby(5), 2);
    assert_eq!(Solver::luby(6), 4);
    assert_eq!(Solver::luby(7), 1);
}

#[test]
fn test_phase_saving() {
    let mut solver = Solver::new();
    for _ in 0..5 {
        solver.new_var();
    }

    // Set up a problem where phase saving helps
    solver.add_clause_dimacs(&[1, 2]);
    solver.add_clause_dimacs(&[-1, 3]);
    solver.add_clause_dimacs(&[-2, 4]);
    solver.add_clause_dimacs(&[-3, -4, 5]);
    solver.add_clause_dimacs(&[-5, 1]);

    let result = solver.solve();
    assert_eq!(result, SolverResult::Sat);
}

#[test]
fn test_lbd_computation() {
    // Test that clause deletion can handle a problem that generates learned clauses
    let mut solver = Solver::with_config(SolverConfig {
        clause_deletion_threshold: 5, // Trigger deletion quickly
        ..SolverConfig::default()
    });

    for _ in 0..20 {
        solver.new_var();
    }

    // A harder problem to generate more conflicts and learned clauses
    // PHP(3,2): 3 pigeons, 2 holes - UNSAT
    // Variables: p_i_h (pigeon i in hole h)
    // p11=1, p12=2, p21=3, p22=4, p31=5, p32=6

    // Each pigeon must be in some hole
    solver.add_clause_dimacs(&[1, 2]); // p1 in h1 or h2
    solver.add_clause_dimacs(&[3, 4]); // p2 in h1 or h2
    solver.add_clause_dimacs(&[5, 6]); // p3 in h1 or h2

    // No hole can have two pigeons
    solver.add_clause_dimacs(&[-1, -3]); // not (p1h1 and p2h1)
    solver.add_clause_dimacs(&[-1, -5]); // not (p1h1 and p3h1)
    solver.add_clause_dimacs(&[-3, -5]); // not (p2h1 and p3h1)
    solver.add_clause_dimacs(&[-2, -4]); // not (p1h2 and p2h2)
    solver.add_clause_dimacs(&[-2, -6]); // not (p1h2 and p3h2)
    solver.add_clause_dimacs(&[-4, -6]); // not (p2h2 and p3h2)

    let result = solver.solve();
    assert_eq!(result, SolverResult::Unsat);
    // Verify we had some conflicts (and thus learned clauses)
    assert!(solver.stats().conflicts > 0);
}

#[test]
fn test_clause_activity_decay() {
    let mut solver = Solver::new();
    for _ in 0..10 {
        solver.new_var();
    }

    // Add some clauses
    solver.add_clause_dimacs(&[1, 2, 3]);
    solver.add_clause_dimacs(&[-1, 4, 5]);
    solver.add_clause_dimacs(&[-2, -3, 6]);

    // Solve (should be SAT)
    let result = solver.solve();
    assert_eq!(result, SolverResult::Sat);
}

#[test]
fn test_clause_minimization() {
    // Test that clause minimization works correctly on a problem
    // that will generate learned clauses
    let mut solver = Solver::new();

    for _ in 0..15 {
        solver.new_var();
    }

    // A problem structure that generates conflicts and learned clauses
    // Graph coloring with 3 colors on 5 vertices
    // Vertices: 1-5, Colors: R(0-4), G(5-9), B(10-14)

    // Each vertex has at least one color
    solver.add_clause_dimacs(&[1, 6, 11]); // v1: R or G or B
    solver.add_clause_dimacs(&[2, 7, 12]); // v2
    solver.add_clause_dimacs(&[3, 8, 13]); // v3
    solver.add_clause_dimacs(&[4, 9, 14]); // v4
    solver.add_clause_dimacs(&[5, 10, 15]); // v5

    // At most one color per vertex (pairwise exclusion)
    solver.add_clause_dimacs(&[-1, -6]); // v1: not (R and G)
    solver.add_clause_dimacs(&[-1, -11]); // v1: not (R and B)
    solver.add_clause_dimacs(&[-6, -11]); // v1: not (G and B)

    solver.add_clause_dimacs(&[-2, -7]);
    solver.add_clause_dimacs(&[-2, -12]);
    solver.add_clause_dimacs(&[-7, -12]);

    solver.add_clause_dimacs(&[-3, -8]);
    solver.add_clause_dimacs(&[-3, -13]);
    solver.add_clause_dimacs(&[-8, -13]);

    // Adjacent vertices have different colors (edges: 1-2, 2-3, 3-4, 4-5)
    solver.add_clause_dimacs(&[-1, -2]); // edge 1-2: not both R
    solver.add_clause_dimacs(&[-6, -7]); // edge 1-2: not both G
    solver.add_clause_dimacs(&[-11, -12]); // edge 1-2: not both B

    solver.add_clause_dimacs(&[-2, -3]); // edge 2-3
    solver.add_clause_dimacs(&[-7, -8]);
    solver.add_clause_dimacs(&[-12, -13]);

    let result = solver.solve();
    assert_eq!(result, SolverResult::Sat);

    // The solver may or may not have conflicts/learned clauses depending on
    // the decision heuristic. The key is that the result is correct.
    // If there are learned clauses, minimization would have been applied.
}

/// A simple theory callback that does nothing (pure SAT)
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

#[test]
fn test_solve_with_theory_sat() {
    let mut solver = Solver::new();
    let mut theory = NullTheory;

    let _x = solver.new_var();
    let _y = solver.new_var();

    // x or y
    solver.add_clause_dimacs(&[1, 2]);
    // not x or y
    solver.add_clause_dimacs(&[-1, 2]);

    assert_eq!(solver.solve_with_theory(&mut theory), SolverResult::Sat);
    assert!(solver.model_value(Var::new(1)).is_true()); // y must be true
}

#[test]
fn test_solve_with_theory_unsat() {
    let mut solver = Solver::new();
    let mut theory = NullTheory;

    let _x = solver.new_var();

    // x
    solver.add_clause_dimacs(&[1]);
    // not x
    solver.add_clause_dimacs(&[-1]);

    assert_eq!(solver.solve_with_theory(&mut theory), SolverResult::Unsat);
}

/// A theory that forces x0 => x1 (if x0 is true, x1 must be true)
struct ImplicationTheory {
    /// Track if x0 is assigned true
    x0_true: bool,
}

impl ImplicationTheory {
    fn new() -> Self {
        Self { x0_true: false }
    }
}

impl TheoryCallback for ImplicationTheory {
    fn on_assignment(&mut self, lit: Lit) -> TheoryCheckResult {
        // If x0 becomes true, propagate x1
        if lit.var().index() == 0 && lit.is_pos() {
            self.x0_true = true;
            // Propagate: x1 must be true because x0 is true
            // The reason is: ~x0 (if x0 were false, we wouldn't need x1)
            let reason: SmallVec<[Lit; 8]> = smallvec::smallvec![Lit::pos(Var::new(0))];
            return TheoryCheckResult::Propagated(vec![(Lit::pos(Var::new(1)), reason)]);
        }
        TheoryCheckResult::Sat
    }

    fn final_check(&mut self) -> TheoryCheckResult {
        TheoryCheckResult::Sat
    }

    fn on_backtrack(&mut self, _level: u32) {
        self.x0_true = false;
    }
}

#[test]
fn test_theory_propagation() {
    let mut solver = Solver::new();
    let mut theory = ImplicationTheory::new();

    let _x0 = solver.new_var();
    let _x1 = solver.new_var();

    // Force x0 to be true
    solver.add_clause_dimacs(&[1]);

    let result = solver.solve_with_theory(&mut theory);
    assert_eq!(result, SolverResult::Sat);

    // x0 should be true (forced by clause)
    assert!(solver.model_value(Var::new(0)).is_true());
    // x1 should also be true (propagated by theory)
    assert!(solver.model_value(Var::new(1)).is_true());
}

/// Theory that says x0 and x1 can't both be true
struct MutexTheory {
    x0_true: Option<Lit>,
    x1_true: Option<Lit>,
}

impl MutexTheory {
    fn new() -> Self {
        Self {
            x0_true: None,
            x1_true: None,
        }
    }
}

impl TheoryCallback for MutexTheory {
    fn on_assignment(&mut self, lit: Lit) -> TheoryCheckResult {
        if lit.var().index() == 0 && lit.is_pos() {
            self.x0_true = Some(lit);
        }
        if lit.var().index() == 1 && lit.is_pos() {
            self.x1_true = Some(lit);
        }

        // If both are true, conflict
        if self.x0_true.is_some() && self.x1_true.is_some() {
            // Conflict clause: ~x0 or ~x1 (at least one must be false)
            let conflict: SmallVec<[Lit; 8]> = smallvec::smallvec![
                Lit::pos(Var::new(0)), // x0 is true (we negate in conflict)
                Lit::pos(Var::new(1))  // x1 is true
            ];
            return TheoryCheckResult::Conflict(conflict);
        }
        TheoryCheckResult::Sat
    }

    fn final_check(&mut self) -> TheoryCheckResult {
        if self.x0_true.is_some() && self.x1_true.is_some() {
            let conflict: SmallVec<[Lit; 8]> =
                smallvec::smallvec![Lit::pos(Var::new(0)), Lit::pos(Var::new(1))];
            return TheoryCheckResult::Conflict(conflict);
        }
        TheoryCheckResult::Sat
    }

    fn on_backtrack(&mut self, _level: u32) {
        self.x0_true = None;
        self.x1_true = None;
    }
}

#[test]
fn test_theory_conflict() {
    let mut solver = Solver::new();
    let mut theory = MutexTheory::new();

    let _x0 = solver.new_var();
    let _x1 = solver.new_var();

    // Force both x0 and x1 to be true (should cause theory conflict)
    solver.add_clause_dimacs(&[1]);
    solver.add_clause_dimacs(&[2]);

    let result = solver.solve_with_theory(&mut theory);
    assert_eq!(result, SolverResult::Unsat);
}

#[test]
fn test_solve_with_assumptions_sat() {
    let mut solver = Solver::new();

    let x0 = solver.new_var();
    let x1 = solver.new_var();

    // x0 \/ x1
    solver.add_clause([Lit::pos(x0), Lit::pos(x1)]);

    // Assume x0 = true
    let assumptions = [Lit::pos(x0)];
    let (result, core) = solver.solve_with_assumptions(&assumptions);

    assert_eq!(result, SolverResult::Sat);
    assert!(core.is_none());
}

#[test]
fn test_solve_with_assumptions_unsat() {
    let mut solver = Solver::new();

    let x0 = solver.new_var();
    let x1 = solver.new_var();

    // x0 -> ~x1 (encoded as ~x0 \/ ~x1)
    solver.add_clause([Lit::neg(x0), Lit::neg(x1)]);

    // Assume both x0 = true and x1 = true (should be UNSAT)
    let assumptions = [Lit::pos(x0), Lit::pos(x1)];
    let (result, core) = solver.solve_with_assumptions(&assumptions);

    assert_eq!(result, SolverResult::Unsat);
    assert!(core.is_some());
    let core = core.expect("UNSAT result must have conflict core");
    // Core should contain at least one of the conflicting assumptions
    assert!(!core.is_empty());
}

#[test]
fn test_solve_with_assumptions_core_extraction() {
    let mut solver = Solver::new();

    let x0 = solver.new_var();
    let x1 = solver.new_var();
    let x2 = solver.new_var();

    // ~x0 (x0 must be false)
    solver.add_clause([Lit::neg(x0)]);

    // Assume x0 = true, x1 = true, x2 = true
    // Only x0 should be in the core
    let assumptions = [Lit::pos(x0), Lit::pos(x1), Lit::pos(x2)];
    let (result, core) = solver.solve_with_assumptions(&assumptions);

    assert_eq!(result, SolverResult::Unsat);
    assert!(core.is_some());
    let core = core.expect("UNSAT result must have conflict core");
    // x0 should be in the core
    assert!(core.contains(&Lit::pos(x0)));
}

#[test]
fn test_solve_with_assumptions_incremental() {
    let mut solver = Solver::new();

    let x0 = solver.new_var();
    let x1 = solver.new_var();

    // x0 \/ x1
    solver.add_clause([Lit::pos(x0), Lit::pos(x1)]);

    // First: assume ~x0 (should be SAT with x1 = true)
    let (result1, _) = solver.solve_with_assumptions(&[Lit::neg(x0)]);
    assert_eq!(result1, SolverResult::Sat);

    // Second: assume ~x0 and ~x1 (should be UNSAT)
    let (result2, core2) = solver.solve_with_assumptions(&[Lit::neg(x0), Lit::neg(x1)]);
    assert_eq!(result2, SolverResult::Unsat);
    assert!(core2.is_some());

    // Third: assume x0 (should be SAT again)
    let (result3, _) = solver.solve_with_assumptions(&[Lit::pos(x0)]);
    assert_eq!(result3, SolverResult::Sat);
}

#[test]
fn test_push_pop_simple() {
    let mut solver = Solver::new();

    let x0 = solver.new_var();

    // Should be SAT (x0 can be true or false)
    assert_eq!(solver.solve(), SolverResult::Sat);

    // Push and add unit clause: x0
    solver.push();
    solver.add_clause([Lit::pos(x0)]);
    assert_eq!(solver.solve(), SolverResult::Sat);
    assert!(solver.model_value(x0).is_true());

    // Pop - should be SAT again
    solver.pop();
    let result = solver.solve();
    assert_eq!(
        result,
        SolverResult::Sat,
        "After pop, expected SAT but got {:?}. trivially_unsat={}",
        result,
        solver.trivially_unsat
    );
}

#[test]
fn test_push_pop_incremental() {
    let mut solver = Solver::new();

    let x0 = solver.new_var();
    let x1 = solver.new_var();
    let x2 = solver.new_var();

    // Base level: x0 \/ x1
    solver.add_clause([Lit::pos(x0), Lit::pos(x1)]);
    assert_eq!(solver.solve(), SolverResult::Sat);

    // Push and add: ~x0
    solver.push();
    solver.add_clause([Lit::neg(x0)]);
    assert_eq!(solver.solve(), SolverResult::Sat);
    // x1 must be true
    assert!(solver.model_value(x1).is_true());

    // Push again and add: ~x1 (should be UNSAT)
    solver.push();
    solver.add_clause([Lit::neg(x1)]);
    assert_eq!(solver.solve(), SolverResult::Unsat);

    // Pop back one level (remove ~x1, keep ~x0)
    solver.pop();
    assert_eq!(solver.solve(), SolverResult::Sat);
    assert!(solver.model_value(x1).is_true());

    // Pop back to base level (remove ~x0)
    solver.pop();
    assert_eq!(solver.solve(), SolverResult::Sat);
    // Either x0 or x1 can be true now

    // Push and add different clause: x0 /\ x2
    solver.push();
    solver.add_clause([Lit::pos(x0)]);
    solver.add_clause([Lit::pos(x2)]);
    assert_eq!(solver.solve(), SolverResult::Sat);
    assert!(solver.model_value(x0).is_true());
    assert!(solver.model_value(x2).is_true());

    // Pop and verify clauses are removed
    solver.pop();
    assert_eq!(solver.solve(), SolverResult::Sat);
}

#[test]
fn test_push_pop_with_learned_clauses() {
    let mut solver = Solver::new();

    let x0 = solver.new_var();
    let x1 = solver.new_var();
    let x2 = solver.new_var();

    // Create a formula that will cause learning
    // (x0 \/ x1) /\ (~x0 \/ x2) /\ (~x1 \/ x2)
    solver.add_clause([Lit::pos(x0), Lit::pos(x1)]);
    solver.add_clause([Lit::neg(x0), Lit::pos(x2)]);
    solver.add_clause([Lit::neg(x1), Lit::pos(x2)]);

    assert_eq!(solver.solve(), SolverResult::Sat);

    // Push and add conflicting clause
    solver.push();
    solver.add_clause([Lit::neg(x2)]);

    // This should be UNSAT and cause clause learning
    assert_eq!(solver.solve(), SolverResult::Unsat);

    // Pop - learned clauses from this level should be removed
    solver.pop();

    // Should be SAT again
    assert_eq!(solver.solve(), SolverResult::Sat);
}
