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
fn deterministic_theory_phase_ignores_randomization_and_rephasing() {
    let mut solver = Solver::with_config(SolverConfig {
        random_polarity_prob: 1.0,
        ..SolverConfig::default()
    });
    let positive = solver.new_var();
    let negative = solver.new_var();
    solver.set_deterministic_phase(positive, true);
    solver.set_deterministic_phase(negative, false);
    solver.phase_inverted = true;

    // Repeated calls also advance the PRNG in the generic path.  A theory's
    // coherent candidate phases must remain stable regardless.
    for _ in 0..64 {
        assert!(solver.decision_polarity(positive));
        assert!(!solver.decision_polarity(negative));
    }
}

#[test]
fn test_lbd_computation() {
    // Test that clause deletion can handle a problem that generates learned clauses.
    // Lucky is disabled: it can refute small pigeonhole formulas (PHP(3,2))
    // without entering search, which would defeat the point of exercising the
    // clause-deletion path here.
    let mut solver = Solver::with_config(SolverConfig {
        clause_deletion_threshold: 5, // Trigger deletion quickly
        enable_lucky: false,
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

/// Reproduces the residual bug the coordinator flagged in
/// `Solver::add_clause`: forcing an effective-unit clause's implied literal
/// with `Trail::assign_propagation` (current decision level) instead of
/// `Trail::assign_propagation_at` (the correct dependency level -- here, the
/// falsifying literal's own level) over-approximates the implication's
/// dependency set. Before the fix, adding `(x0 ∨ x1)` while `x0` is a
/// *permanent* (level-0) fact but the search sits at some unrelated higher
/// decision level (exactly the state `solve()` leaves behind on a plain
/// `Sat`, since it does not backtrack to root the way
/// `solve_with_assumptions` does) recorded `x1` at that higher level. A
/// later backtrack below it then discarded `x1` while `x0`'s permanent
/// falsity survived -- silently reopening the clause, with no live watcher
/// able to notice (the falsifying literal's watcher event already happened,
/// long before the rollback).
///
/// Deliberately white-box (direct `solver.trail` / `propagate()` manipulation,
/// in the spirit of this module's other internal-state tests): the point is
/// to pin the exact levels involved, which a heuristic-driven `solve()` call
/// cannot deterministically control.
#[test]
fn add_clause_binary_effective_unit_is_forced_at_the_falsifying_literals_level_not_current() {
    let mut solver = Solver::new();
    let x0 = solver.new_var();

    // x0 is a genuine, permanent level-0 fact.
    assert!(solver.add_clause([Lit::neg(x0)]));
    assert_eq!(solver.trail.level(x0), 0);

    // Advance the search to an unrelated decision level > 0 -- exactly the
    // "solve() returned Sat at level > 0" scenario: `solve()` does not
    // backtrack to root on a plain `Sat` (unlike `solve_with_assumptions`),
    // so a caller adding a clause afterward can find the trail sitting at
    // any level, with nothing at all to do with x0.
    let extra1 = solver.new_var();
    let extra2 = solver.new_var();
    let extra3 = solver.new_var();
    solver.trail.new_decision_level(); // level 1
    solver.trail.assign_decision(Lit::pos(extra1));
    solver.trail.new_decision_level(); // level 2
    solver.trail.assign_decision(Lit::pos(extra2));
    solver.trail.new_decision_level(); // level 3
    solver.trail.assign_decision(Lit::pos(extra3));
    assert!(solver.propagate().is_none());
    assert_eq!(solver.trail.decision_level(), 3);

    // x1 is a brand-new variable, introduced by the clause below.
    let x1 = Var::new(4);

    // Add (x0 ∨ x1): x0 is false (permanently, level 0), x1 undefined ->
    // effective unit. THE BUG (pre-fix): x1 was forced via
    // `Trail::assign_propagation`, recording the search's *current* level
    // (3) instead of the correct dependency level (0 -- x0's level, the only
    // thing this implication actually depends on).
    assert!(solver.add_clause([Lit::pos(x0), Lit::pos(x1)]));
    assert!(solver.trail.value(x1).is_true());
    assert_eq!(
        solver.trail.level(x1),
        0,
        "x1's implication depends only on x0's permanent level-0 falsity, so it \
         must be recorded at level 0, not the search's current level (3)"
    );

    // Confirm the fix actually matters, not just the level bookkeeping:
    // backtracking to a level *below* the search's current level at
    // attach-time (1, well below the old, wrongly-recorded level of 3) must
    // NOT discard x1, now that it is correctly pinned at level 0.
    solver.backtrack_with_phase_saving(1);
    assert!(
        solver.trail.value(x1).is_true(),
        "the implication must survive a backtrack now that it is correctly \
         recorded at level 0 (pre-fix, this would have unassigned x1 while \
         x0 stayed permanently false, silently reopening the clause)"
    );
    assert!(
        crate::invariants::check_unit_propagation_complete(&solver).is_ok(),
        "(x0 v x1) must not be a hanging unit after this backtrack"
    );
}

/// Companion to the test above: when the *falsifying* literal is itself
/// **not** permanent (assigned above level 0), `add_clause` must backtrack
/// to root and re-evaluate -- per `pre_check_effective_unit`'s doc comment --
/// rather than forcing anything. After the rollback both literals are
/// undefined, and ordinary two-watched-literal propagation is sufficient and
/// correct: there is nothing left to force, since the falsifying literal
/// itself does not survive.
#[test]
fn add_clause_binary_backtracks_and_reevaluates_when_falsifying_literal_is_not_permanent() {
    let mut solver = Solver::new();
    let x0 = solver.new_var();
    let extra1 = solver.new_var();

    solver.trail.new_decision_level(); // level 1
    solver.trail.assign_decision(Lit::pos(extra1));
    solver.trail.new_decision_level(); // level 2
    solver.trail.assign_decision(Lit::neg(x0)); // x0 = false @ level 2 (not permanent)
    assert!(solver.propagate().is_none());

    let x1 = Var::new(2);

    // Add (x0 ∨ x1): x0 is false only at level 2, x1 undefined.
    assert!(solver.add_clause([Lit::pos(x0), Lit::pos(x1)]));

    // The fix must backtrack to root (x0's falsity is not permanent), after
    // which both x0 and x1 are undefined -- there is nothing to force.
    assert_eq!(solver.trail.decision_level(), 0);
    assert!(!solver.trail.is_assigned(x0));
    assert!(!solver.trail.is_assigned(x1));
    assert!(crate::invariants::check_all_sat_invariants(&solver).is_ok());
}

/// General (3+ literal) analogue of
/// `add_clause_binary_effective_unit_is_forced_at_the_falsifying_literals_level_not_current`:
/// the same wrong-level hazard, and the same fix, apply identically when the
/// clause has more than two literals.
#[test]
fn add_clause_general_effective_unit_is_forced_at_the_falsifying_literals_level_not_current() {
    let mut solver = Solver::new();
    let x0 = solver.new_var();
    let x_extra_permanent = solver.new_var();

    // Two genuine, permanent level-0 facts.
    assert!(solver.add_clause([Lit::neg(x0)]));
    assert!(solver.add_clause([Lit::neg(x_extra_permanent)]));

    // Advance to an unrelated decision level > 0.
    let extra1 = solver.new_var();
    solver.trail.new_decision_level(); // level 1
    solver.trail.assign_decision(Lit::pos(extra1));
    assert!(solver.propagate().is_none());
    assert_eq!(solver.trail.decision_level(), 1);

    let x1 = Var::new(3);

    // Add (x0 ∨ x_extra_permanent ∨ x1): both x0 and x_extra_permanent are
    // permanently false (level 0); x1 is undefined -> effective unit.
    assert!(solver.add_clause([Lit::pos(x0), Lit::pos(x_extra_permanent), Lit::pos(x1)]));
    assert!(solver.trail.value(x1).is_true());
    assert_eq!(
        solver.trail.level(x1),
        0,
        "x1's implication depends only on permanent level-0 facts"
    );

    solver.backtrack_with_phase_saving(0);
    assert!(
        solver.trail.value(x1).is_true(),
        "the implication must survive a backtrack to root"
    );
}

/// Answers the coordinator's explicit question about the 3+-literal path: a
/// clause that is fully false at attach time, with its falsifying literals
/// at a *mix* of level 0 (permanent) and a higher level (not permanent),
/// must resolve via backtrack-and-re-evaluate into a forced implication --
/// it is not yet a genuine conflict, because undoing the non-permanent
/// falsity leaves an open (forceable) clause, not a contradiction.
#[test]
fn add_clause_general_all_false_with_mixed_levels_forces_rather_than_conflicts() {
    let mut solver = Solver::new();
    let a = solver.new_var();
    let b = solver.new_var();
    let c = solver.new_var();

    // a, b permanently false (level 0).
    assert!(solver.add_clause([Lit::neg(a)]));
    assert!(solver.add_clause([Lit::neg(b)]));

    // c false only at level 2 (a decision, not permanent).
    let filler = solver.new_var();
    solver.trail.new_decision_level(); // level 1
    solver.trail.assign_decision(Lit::pos(filler));
    solver.trail.new_decision_level(); // level 2
    solver.trail.assign_decision(Lit::neg(c)); // c = false @ level 2
    assert!(solver.propagate().is_none());

    // (a ∨ b ∨ c): all three literals are false right now, but c's falsity
    // is not permanent, so this is not a genuine conflict.
    assert!(solver.add_clause([Lit::pos(a), Lit::pos(b), Lit::pos(c)]));
    assert!(
        !solver.trivially_unsat,
        "undoing c's non-permanent falsity leaves an open, forceable clause, \
         not a real conflict"
    );
    assert!(solver.trail.value(c).is_true());
    assert_eq!(solver.trail.level(c), 0);
}

/// Answers the other half of the coordinator's question: when *every*
/// falsifying literal genuinely is permanent (level 0), the 3+-literal path
/// must still report an unconditional conflict rather than silently
/// dropping it.
#[test]
fn add_clause_general_all_false_at_level_zero_is_a_genuine_conflict() {
    let mut solver = Solver::new();
    let a = solver.new_var();
    let b = solver.new_var();
    let c = solver.new_var();

    assert!(solver.add_clause([Lit::neg(a)]));
    assert!(solver.add_clause([Lit::neg(b)]));
    assert!(solver.add_clause([Lit::neg(c)]));

    // (a ∨ b ∨ c): every literal is permanently false -- a genuine,
    // unconditional conflict.
    assert!(!solver.add_clause([Lit::pos(a), Lit::pos(b), Lit::pos(c)]));
    assert_eq!(solver.solve(), SolverResult::Unsat);
}
