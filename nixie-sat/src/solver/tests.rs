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
    // The cadical-faithful rephase strategies mutate `phase` in place; a
    // global inversion flag no longer exists. Flip every saved phase instead
    // (the `flipping` strategy) and check the deterministic phases survive.
    for p in &mut solver.phase {
        *p = !*p;
    }
    for p in &mut solver.target_phase {
        *p = !*p;
    }

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

/// The CDCL(T) restart gate: every clause-learning path must feed the cadical
/// glue EMAs (`note_learned_lbd`), so that `handle_clause_deletion_and_restart`
/// can consult them for the Glucose strategy instead of restarting on the bare
/// conflict-count threshold.  The previous wiring left the EMAs at zero in
/// `solve_with_theory` (whose learning goes through `learn_clause`), so the
/// Glucose arm there only ever enforced the `restart_interval` minimum gap – an
/// unconditional restart every 100 conflicts, which wiped the trail on
/// structured inputs and cost ~45× more conflicts than Z3 on QF_UF quasigroup
/// problems.
#[test]
fn learned_clauses_feed_glue_emas_and_gate_restarts() {
    let mut solver = Solver::new();
    let a = solver.new_var();
    let b = solver.new_var();
    let _ = (a, b);

    assert_eq!(solver.glue_current.fast.value(), 0.0);
    // The EMA input is the analysis-walk glue (cadical `levels.size() - 1`),
    // set by the analysis itself; the clause LBD argument feeds LocalLbd/stats.
    solver.analysis_walk_glue = 3;
    solver.note_learned_lbd(5);
    assert!(
        (solver.glue_current.fast.value() - 3.0).abs() < 1e-9,
        "a walk glue of 3 moves the (freshly-initialised, unbiased) fast EMA to 3"
    );
    assert!((solver.glue_current.slow.value() - 3.0).abs() < 1e-9);
}

/// With a *healthy* (non-degrading) glue signal, the conflict handler must not
/// restart merely because the bare conflict count crossed the interval: the
/// Glucose decision belongs to the EMA comparison, not the threshold.
#[test]
fn healthy_glue_ema_suppresses_glucose_restart() {
    let mut solver = Solver::with_config(SolverConfig {
        restart_strategy: RestartStrategy::Glucose,
        restart_interval: 1,
        ..SolverConfig::default()
    });
    let a = solver.new_var();
    assert!(solver.add_clause([Lit::pos(a), Lit::neg(a)]));

    // Simulate a stable learning history: fast EMA strictly below the slow
    // EMA's 10% margin, so the degradation condition is false.  The EMAs are
    // moved to their target by repeated samples (an EMA converges towards its
    // input, it is not assigned by one update).
    for _ in 0..1000 {
        solver.glue_current.fast.update(1.0);
        solver.glue_current.slow.update(10.0);
    }
    solver.stats.conflicts = solver.restart_threshold + 5;

    let restarts_before = solver.stats.restarts;
    solver.handle_clause_deletion_and_restart();
    assert_eq!(
        solver.stats.restarts, restarts_before,
        "fast=1.0 < 1.1*slow=11.0 must not restart past the bare threshold"
    );

    // A degraded signal (fast 20% above slow) restarts.  Advance the conflict
    // count past the every-2-conflicts check gate first.
    solver.stats.conflicts += 2;
    for _ in 0..1000 {
        solver.glue_current.fast.update(12.0);
    }
    solver.handle_clause_deletion_and_restart();
    assert_eq!(
        solver.stats.restarts,
        restarts_before + 1,
        "fast=12.0 >= 1.1*slow=11.0 must restart"
    );
}

/// A theory propagation explained **lazily** (`assign_theory_propagation`)
/// must produce the *same* learned clause as the materialized design when a
/// conflict resolves *through* it: the stored tail is exactly the literal
/// tail of the reason clause `add_theory_reason_clause` would have added.
///
/// Setup: x@1, y@2 decided; at level 3, w is decided and then z is
/// theory-propagated from x ∧ y.  The clause (¬x ∨ ¬y ∨ ¬z ∨ ¬w) conflicts
/// with two level-3 literals (z, w), so 1-UIP must resolve through z's
/// antecedents and learn over x, y, w only – in either design.
#[test]
fn lazy_theory_reason_resolves_like_a_materialized_clause() {
    let build = |lazy: bool| -> SmallVec<[Lit; 32]> {
        let mut solver = Solver::new();
        let x = solver.new_var();
        let y = solver.new_var();
        let z = solver.new_var();
        let w = solver.new_var();
        // Original clause: (¬x ∨ ¬y ∨ ¬z ∨ ¬w) – falsified once all are true.
        assert!(solver.add_clause([Lit::neg(x), Lit::neg(y), Lit::neg(z), Lit::neg(w),]));

        solver.trail.new_decision_level();
        solver.trail.assign_decision(Lit::pos(x));
        solver.trail.new_decision_level();
        solver.trail.assign_decision(Lit::pos(y));
        assert!(solver.propagate().is_none());

        solver.trail.new_decision_level();
        solver.trail.assign_decision(Lit::pos(w));
        let reasons: SmallVec<[Lit; 8]> = SmallVec::from_iter([Lit::pos(x), Lit::pos(y)]);
        if lazy {
            // Arm the adaptive switch so the lazy path is taken.
            solver.theory_reason_clauses = super::learn::THEORY_LAZY_SWITCH_AFTER;
            assert!(solver.theory_lazy_reasons_enabled());
            solver.assign_theory_propagation(Lit::pos(z), reasons);
        } else {
            let cid = solver.add_theory_reason_clause(&reasons, Lit::pos(z));
            solver.trail.assign_propagation(Lit::pos(z), cid);
        }
        assert!(solver.trail.lit_value(Lit::pos(z)).is_true());

        // Propagation visits z's watch, finds the clause falsified, and
        // returns the conflict id – exactly the flow the search uses.
        let conflict = solver.propagate().expect("clause must be falsified");
        let (level, learnt) = solver.analyze(conflict);
        // Backtrack level = highest level among the non-asserting literals
        // (x@1, y@2), not the asserting literal's own level.
        assert_eq!(level, 2);
        learnt
    };

    let materialized = build(false);
    let lazy = build(true);
    assert_eq!(
        materialized, lazy,
        "lazy and materialized theory reasons must learn the same clause"
    );
    // z was resolved out through its antecedents; x, y (the reasons) and w
    // (the asserting literal) are what remain.
    let vars: std::collections::HashSet<u32> = lazy.iter().map(|l| l.var().0).collect();
    assert!(
        vars.contains(&0) && vars.contains(&1) && vars.contains(&3),
        "learnt = {lazy:?}"
    );
    assert!(
        !vars.contains(&2),
        "the theory-propagated literal must be resolved out"
    );
}

/// The adaptive switch: below [`THEORY_LAZY_SWITCH_AFTER`] materialized
/// reason clauses, propagations are materialized; at or above it, lazy.
#[test]
fn theory_lazy_switch_flips_at_the_configured_count() {
    let mut solver = Solver::new();
    let a = solver.new_var();
    assert!(solver.add_clause([Lit::pos(a), Lit::neg(a)]));
    assert!(!solver.theory_lazy_reasons_enabled());

    solver.theory_reason_clauses = super::learn::THEORY_LAZY_SWITCH_AFTER;
    assert!(solver.theory_lazy_reasons_enabled());
}

// ===== cadical-faithful rephase / target-phase machinery ====================
//
// These tests pin the parts of the port that matter for search behaviour:
// `no_conflict_until` tracking, `update_target_and_best` from *every*
// phase-saving backtrack (not just restarts), the mode-dependent strategy
// schedule, and the target-phase fallback order in `decision_polarity`.

/// A clean propagation fixpoint records the whole trail as conflict-free;
/// a conflict records only the prefix before the current decision level.
#[test]
fn rephase_no_conflict_until_tracks_prefixes() {
    let mut solver = Solver::new();
    let a = solver.new_var();
    let b = solver.new_var();
    solver.add_clause([Lit::pos(a), Lit::neg(a)]); // keep a busy
    solver.add_clause([Lit::pos(a), Lit::pos(b)]);
    solver.propagate();
    assert_eq!(solver.no_conflict_until, solver.trail.size());

    // Decide a = false at level 1 → propagates b at level 1 → conflict with
    // the tautology-watch clause... instead force a real conflict: clause
    // (a ∨ b) with a=false,b=false requires both decisions.
    let c = solver.new_var();
    solver.backtrack_with_phase_saving(0);
    solver.trail.new_decision_level();
    solver.trail.assign_decision(Lit::neg(a));
    solver.trail.new_decision_level();
    solver.trail.assign_decision(Lit::neg(b));
    // Now (a ∨ b) is falsified: propagate must report it and record only the
    // level-0 prefix as conflict-free.
    let _ = c;
    assert!(solver.propagate().is_some());
    assert_eq!(
        solver.no_conflict_until,
        solver.trail.level_start(solver.trail.decision_level())
    );
}

/// `update_target_and_best` fires from ordinary conflict backjumps (no
/// restart involved) and snapshots the conflict-free prefix's polarities.
#[test]
fn rephase_target_and_best_update_on_backtrack() {
    let mut solver = Solver::with_config(SolverConfig {
        enable_lucky: false,
        ..SolverConfig::default()
    });
    // (a ∨ b) ∧ (¬a ∨ b) ∧ (¬b ∨ c) ∧ (¬c) → UNSAT, with conflicts above
    // level 0 so backjumps (and thus update_target_and_best) must fire.
    let a = solver.new_var();
    let b = solver.new_var();
    let c = solver.new_var();
    solver.add_clause([Lit::pos(a), Lit::pos(b)]);
    solver.add_clause([Lit::neg(a), Lit::pos(b)]);
    solver.add_clause([Lit::neg(b), Lit::pos(c)]);
    solver.add_clause([Lit::neg(c)]);

    let result = solver.solve();
    assert_eq!(result, SolverResult::Unsat);
    assert!(
        solver.best_assigned > 0 || solver.stats.conflicts == 0,
        "best_assigned must be established from a conflict-free prefix \
         (conflicts: {}, best_assigned: {})",
        solver.stats.conflicts,
        solver.best_assigned
    );
    assert_eq!(solver.best_assigned, solver.target_assigned);
}

/// The per-mode strategy schedule matches cadical's stable-mode cycle:
/// original, inverted, (best, original, best, inverted)^ω with walk off,
/// and the walk variants with walk on.
#[test]
fn rephase_schedule_matches_cadical_stable_cycle() {
    // stable && !walk: original,inverted,(best,original,best,inverted)^ω
    let mut solver = Solver::with_config(SolverConfig {
        enable_stabilize: true,
        walk: false,
        rephase_interval: 1,
        ..SolverConfig::default()
    });
    let _a = solver.new_var();
    solver.stable = true;
    let kinds = [
        RephaseKind::Original,
        RephaseKind::Inverted,
        RephaseKind::Best,
        RephaseKind::Original,
        RephaseKind::Best,
        RephaseKind::Inverted,
        RephaseKind::Best,
        RephaseKind::Original,
    ];
    for expected in kinds {
        solver.rephase();
        assert_eq!(solver.rephased, Some(expected));
    }

    // stable && walk: original,inverted,(best,walk,original,best,walk,inverted)^ω
    let mut solver = Solver::with_config(SolverConfig {
        enable_stabilize: true,
        walk: true,
        rephase_interval: 1,
        ..SolverConfig::default()
    });
    let _a = solver.new_var();
    solver.stable = true;
    let kinds = [
        RephaseKind::Original,
        RephaseKind::Inverted,
        RephaseKind::Best,
        RephaseKind::Walk,
        RephaseKind::Original,
        RephaseKind::Best,
        RephaseKind::Walk,
        RephaseKind::Inverted,
    ];
    for expected in kinds {
        solver.rephase();
        assert_eq!(solver.rephased, Some(expected));
    }
}

/// The focused-mode schedule (stabilization on, walk on – cadical defaults):
/// original,(random,best,walk,flipping,best,walk)^ω, matching cadical's
/// *code* (its comment claims a leading `flipping`).
#[test]
fn rephase_schedule_matches_cadical_focused_cycle() {
    let mut solver = Solver::with_config(SolverConfig {
        enable_stabilize: true,
        walk: true,
        walk_nonstable: true,
        rephase_interval: 1,
        ..SolverConfig::default()
    });
    let _a = solver.new_var();
    solver.stable = false;
    let kinds = [
        RephaseKind::Original,
        RephaseKind::Random,
        RephaseKind::Best,
        RephaseKind::Walk,
        RephaseKind::Flipping,
        RephaseKind::Best,
        RephaseKind::Walk,
        RephaseKind::Random,
    ];
    for expected in kinds {
        solver.rephase();
        assert_eq!(solver.rephased, Some(expected));
    }
}

/// A `best` rephase replays the recorded best phases into the saved array,
/// and the next conflict re-arms `best_assigned` for a fresh best.
#[test]
fn rephase_best_replays_and_rearms() {
    let mut solver = Solver::with_config(SolverConfig {
        rephase_interval: 1,
        walk: false,
        enable_stabilize: true,
        ..SolverConfig::default()
    });
    let a = solver.new_var();
    let b = solver.new_var();
    solver.stable = true;
    // round 0 = original (all false)
    solver.rephase();
    assert_eq!(solver.rephased, Some(RephaseKind::Original));
    assert!(!solver.phase[a.index()] && !solver.phase[b.index()]);

    // Record a best phase: assign a trail, let propagate succeed, backtrack.
    solver.trail.new_decision_level();
    solver.trail.assign_decision(Lit::pos(a));
    solver.propagate();
    solver.backtrack_with_phase_saving(0);
    assert!(solver.best_phase[a.index()]);
    assert!(solver.best_assigned > 0);

    // round 1 = inverted (all true), round 2 = best → replays a = true.
    solver.rephase();
    solver.rephase();
    assert_eq!(solver.rephased, Some(RephaseKind::Best));
    assert!(solver.phase[a.index()]);

    // After the rephase, the first conflict (conflicts advanced past
    // last_rephase_conflicts) resets best_assigned via update_target_and_best.
    solver.stats.conflicts += 1;
    let armed_best = solver.best_assigned;
    solver.update_target_and_best();
    assert_eq!(solver.best_assigned, 0);
    assert_eq!(solver.target_assigned, 0);
    assert_eq!(solver.rephased, None);
    let _ = armed_best;
}

/// Target phases are consulted in stable mode (target = 1) and ignored in
/// focused mode; `target = 2` uses them in both modes; forced (theory)
/// phases always win.
#[test]
fn rephase_target_phase_decision_fallback() {
    let mut solver = Solver::with_config(SolverConfig {
        random_polarity_prob: 0.0,
        ..SolverConfig::default()
    });
    let a = solver.new_var();
    let b = solver.new_var();
    solver.phase[a.index()] = false;
    solver.target_phase[a.index()] = true;
    solver.phase[b.index()] = false;
    solver.target_phase[b.index()] = true;
    solver.set_deterministic_phase(b, false);

    // Focused (stable = false): saved phase wins for a, forced for b.
    solver.stable = false;
    assert!(!solver.decision_polarity(a));
    assert!(!solver.decision_polarity(b));

    // Stable: target phase for a, forced still wins for b.
    solver.stable = true;
    assert!(solver.decision_polarity(a));
    assert!(!solver.decision_polarity(b));
}

/// Rephasing fires from the search loop on the arithmetic conflict schedule
/// (interval × round) and the stats count every strategy used.
#[test]
fn rephase_fires_from_search_on_conflict_schedule() {
    let mut solver = Solver::with_config(SolverConfig {
        rephase: 1,
        rephase_interval: 2,
        walk: false,
        enable_stabilize: false,
        enable_lucky: false,
        ..SolverConfig::default()
    });
    // UNSAT pigeonhole PHP(4,3): 4 pigeons, 3 holes – small enough to run
    // instantly, big enough that unit propagation alone cannot refute it, so
    // the conflict counter (and the rephase schedule) actually advances.
    let pigeons = 4;
    let holes = 3;
    let mut p = Vec::new();
    for _ in 0..pigeons * holes {
        p.push(solver.new_var());
    }
    let at = |i: usize, j: usize| Lit::pos(p[i * holes + j]);
    // Every pigeon in some hole.
    for i in 0..pigeons {
        let clause = (0..holes).map(|j| at(i, j));
        solver.add_clause(clause);
    }
    // No two pigeons share a hole.
    for j in 0..holes {
        for i1 in 0..pigeons {
            for i2 in i1 + 1..pigeons {
                solver.add_clause([at(i1, j).negate(), at(i2, j).negate()]);
            }
        }
    }

    assert_eq!(solver.solve(), SolverResult::Unsat);
    assert!(
        solver.stats.rephased.total > 0,
        "the arithmetic schedule (base 2) must fire within the PHP(4,3) \
         refutation (conflicts: {})",
        solver.stats.conflicts
    );
    // `single` schedule (stabilization off): inverted,best,flipping,best,...
    assert_eq!(solver.stats.rephased.inverted, 1);
}

/// The walk writes back an assignment that satisfies every original clause
/// when it finds one (broken count reaches zero), and never flips fixed
/// (level-0) variables.
#[test]
fn rephase_walk_satisfies_original_clauses_and_respects_fixed() {
    let mut solver = Solver::new();
    let a = solver.new_var();
    let b = solver.new_var();
    let c = solver.new_var();
    // (¬a ∨ b): a=true forces b. (c) fixed true at level 0.
    solver.add_clause([Lit::neg(a), Lit::pos(b)]);
    solver.add_clause([Lit::pos(a), Lit::pos(b), Lit::neg(c)]);
    solver.add_clause([Lit::pos(c)]);
    assert_eq!(solver.solve(), SolverResult::Sat);

    // Run a walk with a generous budget from a bad phase (both false).
    solver.backtrack_with_phase_saving(0);
    solver.phase[a.index()] = false;
    solver.phase[b.index()] = false;
    solver.last_walk_ticks = 0;
    solver.ticks_focused = 100_000; // budget = 8000 ticks
    solver.walk();

    // The walk must have repaired the phases: (¬a ∨ b) satisfied and the
    // fixed variable c untouched by the flip loop (its value is forced).
    let a_true = solver.phase[a.index()];
    let b_true = solver.phase[b.index()];
    assert!(a_true == b_true || !a_true, "phase a={a_true} b={b_true}");
}

/// Incremental scope consistency: rephase state survives push/pop without
/// corrupting later answers (phases are heuristic-only, but the machinery's
/// bookkeeping must not wedge the search).
#[test]
fn rephase_incremental_push_pop_stays_consistent() {
    let mut solver = Solver::new();
    let a = solver.new_var();
    let b = solver.new_var();
    solver.add_clause([Lit::pos(a), Lit::pos(b)]);
    assert_eq!(solver.solve(), SolverResult::Sat);

    solver.push();
    solver.add_clause([Lit::neg(a)]);
    assert_eq!(solver.solve(), SolverResult::Sat);
    solver.pop();
    // Model restored: both rounds SAT with the original clauses only.
    assert_eq!(solver.solve(), SolverResult::Sat);
    let _ = solver.rephase_rounds;
}

/// Pins the `inprocess()` soundness defect CLOSED.  `config_presets`' module
/// doc historically cited exactly this shape — pigeonhole(7,6) with
/// `inprocessing_interval: 1` — as returning `Sat` on an UNSAT instance
/// ("hanging unit at a propagation fixpoint" from missing watch rebuilds),
/// and every preset shipped inprocessing off because of it.  The intervening
/// clause-management fixes (retire reason fixups + binary-edge purge, DRAT
/// deletion completion, subsumption promotion, deletion-aware arena reads)
/// closed it; the doc was re-verified 2026-08-25 (see
/// `docs/studies/2026-08-inprocessing-soundness-recheck.md`).  If this test
/// ever fails, presets must be re-audited before anything else ships.
#[test]
fn pigeonhole_inprocessing_interval_1_stays_unsat() {
    let mut solver = Solver::with_config(SolverConfig {
        enable_inprocessing: true,
        inprocessing_interval: 1,
        ..SolverConfig::default()
    });
    let (pigeons, holes) = (7usize, 6usize);
    let mut p = Vec::new();
    for _ in 0..pigeons * holes {
        p.push(solver.new_var());
    }
    let at = |i: usize, j: usize| Lit::pos(p[i * holes + j]);
    for i in 0..pigeons {
        solver.add_clause((0..holes).map(|j| at(i, j)));
    }
    for j in 0..holes {
        for i1 in 0..pigeons {
            for i2 in i1 + 1..pigeons {
                solver.add_clause([at(i1, j).negate(), at(i2, j).negate()]);
            }
        }
    }
    assert_eq!(solver.solve(), SolverResult::Unsat);
}

/// Pins the 2026-09-05 one-shot-latch fix CLOSED: the conflict-scheduled
/// ELS slot used to set `did_equiv_subst` *before* calling
/// `substitute_equivalent_literals`, whose first line is exactly that
/// one-shot guard — so whenever `enable_equiv_substitution` was set the
/// scheduled pass (and the gate-congruence augmentation it hosts)
/// silently no-op'd (`58df118`..2026-09-05; the `0ed8543` "BVE + ELS
/// default-on" measurement had therefore measured BVE alone).  With the
/// fix the latch-free `_round` variant runs and folds equivalences.
#[test]
fn scheduled_els_executes_when_enabled() {
    let mut solver = Solver::with_config(SolverConfig {
        enable_equiv_substitution: true,
        // Fire the one-shot right after the first conflict (php(3,2) needs
        // several, so the slot is guaranteed to be reached mid-search).
        elim_interval: 1,
        ..SolverConfig::default()
    });
    // Pigeonhole(7,6): UNSAT after many conflicts, and (unlike php(3,2))
    // not binary-refutable at the first conflict, so the round folds the
    // equivalence below instead of returning Unsat from the SCC
    // contradiction check outright.
    let (pigeons, holes) = (7usize, 6usize);
    let mut p = Vec::new();
    for _ in 0..pigeons * holes {
        p.push(solver.new_var());
    }
    let at = |i: usize, j: usize| Lit::pos(p[i * holes + j]);
    for i in 0..pigeons {
        solver.add_clause((0..holes).map(|j| at(i, j)));
    }
    for j in 0..holes {
        for i1 in 0..pigeons {
            for i2 in i1 + 1..pigeons {
                solver.add_clause([at(i1, j).negate(), at(i2, j).negate()]);
            }
        }
    }
    // An explicit equivalence x ≡ y (both binary implications) on vars the
    // pigeonhole part never assigns, so a non-trivial SCC exists for the
    // round to fold when it runs.
    let x = solver.new_var();
    let y = solver.new_var();
    solver.add_clause([Lit::neg(x), Lit::pos(y)]);
    solver.add_clause([Lit::pos(x), Lit::neg(y)]);
    assert_eq!(solver.solve(), SolverResult::Unsat);
    assert!(
        solver.stats().substitutions > 0,
        "scheduled ELS folded no equivalences — the one-shot latch regression is back"
    );
}

// ---------------------------------------------------------------------------
// BIG-authoritative BCP (2026-09): binaries live in the binary implication
// graph only; the watch lists carry length >= 3 clauses and a phantom tick
// count. See studies/2026-09-big-authoritative-bcp.md.
// ---------------------------------------------------------------------------

#[test]
fn big_authoritative_binaries_have_no_watch_entries() {
    // A pure binary formula: every clause registers in the BIG, none in the
    // watch lists; the phantom counts match the old scheme's entry count
    // (one per clause per direction).
    let mut solver = Solver::new();
    for _ in 0..6 {
        let _ = solver.new_var();
    }
    // (¬x0 ∨ x1) ∧ (¬x1 ∨ x2) ∧ (x0 ∨ x3) ∧ (¬x2 ∨ x4): a chain forcing x1,
    // x2, x4 true once x0 is false; x3 covers the x0-true branch.
    solver.add_clause_dimacs(&[-1, 2]);
    solver.add_clause_dimacs(&[-2, 3]);
    solver.add_clause_dimacs(&[1, 4]);
    solver.add_clause_dimacs(&[-3, 5]);

    assert_eq!(solver.solve(), SolverResult::Sat);

    // No live clause of len 2 may carry watch entries.
    for cid in solver.clauses.iter_ids() {
        let Some(c) = solver.clauses.get(cid) else {
            continue;
        };
        if c.lits.len() == 2 {
            let (a, b) = (c.lits[0], c.lits[1]);
            assert!(
                !solver
                    .watches
                    .get(a.negate())
                    .iter()
                    .any(|w| w.clause == cid)
                    && !solver
                        .watches
                        .get(b.negate())
                        .iter()
                        .any(|w| w.clause == cid),
                "binary clause {cid:?} carries watch entries"
            );
        }
    }
    // Both BIG edges per binary clause (spot-check the chain edge ¬x1 ∨ x2:
    // x1 => x2 and ¬x2 => ¬x1).
    let from = Lit::from_code(2); // x1 (Var 0, positive)
    assert!(
        solver
            .binary_graph
            .get(from)
            .iter()
            .any(|&(l, _)| l.code() == 2 * 2)
    );
}

#[test]
fn big_authoritative_invariant_catches_purged_edge() {
    // Tripwire for the new load-bearing invariant: remove one BIG edge of a
    // live binary and the backing check must fire (a missing edge is a lost
    // implication, i.e. a wrong answer, not a slowdown).
    let mut solver = Solver::new();
    for _ in 0..3 {
        let _ = solver.new_var();
    }
    solver.add_clause_dimacs(&[1, 2]);
    solver.add_clause_dimacs(&[-1, 3]);
    assert_eq!(solver.solve(), SolverResult::Sat);

    // Purge both edges of clause 0 behind the API's back (simulating a
    // missed purge/attach site): the checker must now report the clause as
    // missing its edges.
    let cid = crate::clause::ClauseId::new(0);
    let (a, b) = {
        let c = solver.clauses.get(cid).expect("clause 0 live");
        (c.lits[0], c.lits[1])
    };
    solver.binary_graph.remove_clause_edges(a.negate(), cid);
    solver.binary_graph.remove_clause_edges(b.negate(), cid);
    assert!(
        crate::invariants::check_binary_registration(&solver).is_err(),
        "purged BIG edges must trip the structural registration invariant"
    );
    assert!(
        crate::invariants::check_all_sat_invariants(&solver).is_err(),
        "purged BIG edges must trip the full invariant set"
    );
}

#[test]
fn big_authoritative_phantom_tick_parity_counters() {
    // The phantom counters exist to keep the tick-driven schedules
    // bit-identical to the old binary-watch-entry accounting. Pin their
    // semantics: bump per attach direction, reset+refill at rebuild, and
    // read-back through phantom_len.
    let mut solver = Solver::new();
    for _ in 0..4 {
        let _ = solver.new_var();
    }
    solver.add_clause_dimacs(&[1, 2]);
    solver.add_clause_dimacs(&[-1, 3]);
    solver.add_clause_dimacs(&[2, 4]);
    solver.add_clause_dimacs(&[-2, -3]);

    // DIMACS x_k is Var::new(k-1); ¬x2 = Lit::neg(Var::new(1)).
    let neg1 = Lit::neg(Var::new(0));
    let neg2 = Lit::neg(Var::new(1));
    // Old scheme: one watch entry per clause direction — under ¬x2 the
    // clauses (1∨2) and (2∨4) each held an entry (2); under ¬x1 only (1∨2)
    // (the clause (¬1∨3) keys under x1 and ¬x3, not ¬x1).
    assert_eq!(solver.watches.phantom_len(neg2), 2);
    assert_eq!(solver.watches.phantom_len(neg1), 1);

    // The rebuild resets and refills identically.
    solver.rebuild_watches_and_binary_graph();
    assert_eq!(solver.watches.phantom_len(neg2), 2);
    assert_eq!(solver.watches.phantom_len(neg1), 1);
}

/// Pins the `els_presearch` wiring: with the flag (plus
/// `enable_equiv_substitution`) the ELS round folds equivalences *before*
/// search starts.  php(7,6) + an explicit x≡y pair with `elim_interval`
/// far above php(7,6)'s conflict count: the conflict-scheduled one-shot
/// can never fire, so any recorded substitutions must come from the
/// pre-search fixpoint (which also consumes `did_equiv_subst`).
#[test]
fn els_presearch_folds_before_search() {
    let mut solver = Solver::with_config(SolverConfig {
        enable_equiv_substitution: true,
        els_presearch: true,
        elim_interval: 50_000,
        ..SolverConfig::default()
    });
    let (pigeons, holes) = (7usize, 6usize);
    let mut p = Vec::new();
    for _ in 0..pigeons * holes {
        p.push(solver.new_var());
    }
    let at = |i: usize, j: usize| Lit::pos(p[i * holes + j]);
    for i in 0..pigeons {
        solver.add_clause((0..holes).map(|j| at(i, j)));
    }
    for j in 0..holes {
        for i1 in 0..pigeons {
            for i2 in i1 + 1..pigeons {
                solver.add_clause([at(i1, j).negate(), at(i2, j).negate()]);
            }
        }
    }
    let x = solver.new_var();
    let y = solver.new_var();
    solver.add_clause([Lit::neg(x), Lit::pos(y)]);
    solver.add_clause([Lit::pos(x), Lit::neg(y)]);
    assert_eq!(solver.solve(), SolverResult::Unsat);
    assert!(
        solver.stats().substitutions > 0,
        "no equivalences folded before search — els_presearch wiring is broken"
    );
}

// ---------------------------------------------------------------------------
// Binary-chain factoring (2026-09-05, solver/factor.rs) — soundness pins.
// ---------------------------------------------------------------------------

/// Build `(f ∨ q_i)` and `(q_i ∨ g)` for i = 1..k on fresh vars and run
/// one factoring pass; returns (introduced, solver).  The witness polarity
/// `(q_i ∨ g)` is the sound direction (see `solver/factor.rs`).
fn factoring_fixture(k: usize) -> (usize, Solver) {
    let mut solver = Solver::new();
    let f = solver.new_var();
    let g = solver.new_var();
    let qs: Vec<_> = (0..k).map(|_| solver.new_var()).collect();
    for &q in &qs {
        solver.add_clause([Lit::pos(f), Lit::pos(q)]);
        solver.add_clause([Lit::pos(q), Lit::pos(g)]);
    }
    let (introduced, _reduction) = solver.factor_binaries();
    (introduced, solver)
}

#[test]
fn factor_fires_on_shared_implication_binaries() {
    // With incremental BIG maintenance the fixpoint compounds: round 1
    // factors `(f v q_i)` against witnesses `(q_i v g)`; round 2 factors
    // the kept witnesses themselves (candidate `g`, quotients `(g v q_i)`,
    // witnesses `(q_i v not-x)` — the round-1 quotients, now visible to
    // the adjacency scan).  Both applications use the same verified
    // transformation.
    let (introduced, _) = factoring_fixture(5);
    assert_eq!(introduced, 2, "k=5: quotient + witness-compounding rounds");
    let (introduced, _) = factoring_fixture(3);
    assert_eq!(
        introduced, 2,
        "k=3 is the firing threshold (reduction k-2 > 0)"
    );
    let (introduced, _) = factoring_fixture(2);
    assert_eq!(introduced, 0, "k=2 must not fire (no occurrence reduction)");
}

#[test]
fn factor_preserves_verdict_both_ways() {
    // SAT: f=T (or g=T with all q_i) satisfies everything.
    let (i, mut s) = factoring_fixture(5);
    assert!(i >= 1);
    assert_eq!(s.solve(), SolverResult::Sat);
    // UNSAT variant: force ¬f, ¬q_1 and ... originals (f∨q_i) with ¬f
    // force q_i, so ¬q_1 contradicts; witnesses irrelevant.
    let (i, mut s) = factoring_fixture(5);
    assert!(i >= 1);
    let f = Var::new(0);
    let g = Var::new(1);
    let q1 = Var::new(2);
    s.add_clause([Lit::neg(f)]);
    s.add_clause([Lit::neg(g)]);
    s.add_clause([Lit::neg(q1)]);
    assert_eq!(s.solve(), SolverResult::Unsat);
}

/// Differential: factoring must never change the verdict on random
/// binary-heavy formulas, and a `Sat` model must satisfy the ORIGINAL
/// clauses (restricted to the original variables).
#[test]
fn factor_differential_random_binaries() {
    let mut rng: u64 = 0x243F_6A88_85A3_08D3;
    let mut next = move || {
        rng ^= rng << 13;
        rng ^= rng >> 7;
        rng ^= rng << 17;
        rng
    };
    for trial in 0..300 {
        let n = 4 + (next() % 6) as usize; // 4..=9 vars
        let m = 6 + (next() % 10) as usize; // 6..=15 clauses
        let lit = |v: usize, rng: u64| -> Lit {
            let var = Var::new((v % n) as u32);
            if rng & 1 == 0 {
                Lit::pos(var)
            } else {
                Lit::neg(var)
            }
        };
        // Build the formula, solve WITHOUT factoring.
        let mut base = Solver::new();
        let mut ref_solver = Solver::new();
        for _ in (0..n).map(|_| base.new_var()) {}
        for _ in (0..n).map(|_| ref_solver.new_var()) {}
        let mut clauses: Vec<SmallVec<[Lit; 4]>> = Vec::new();
        for c in 0..m {
            let sz = if next() % 3 == 0 { 3 } else { 2 };
            let mut cl: SmallVec<[Lit; 4]> = SmallVec::new();
            for j in 0..sz {
                let l = lit((next() % n as u64) as usize, next());
                if !cl.contains(&l) && !cl.contains(&l.negate()) {
                    cl.push(l);
                }
                let _ = j;
            }
            if !cl.is_empty() {
                base.add_clause(cl.iter().copied());
                ref_solver.add_clause(cl.iter().copied());
                clauses.push(cl);
            }
            let _ = c;
        }
        let expected = ref_solver.solve();
        let (introduced, _) = base.factor_binaries();
        let got = base.solve();
        assert_eq!(
            expected, got,
            "verdict changed by factoring (trial {trial}, introduced {introduced})"
        );
        if got == SolverResult::Sat {
            let model = base.model();
            // Every original clause must be satisfied by the restriction.
            for cl in &clauses {
                let sat = cl.iter().any(|l| {
                    let vi = l.var().index();
                    model.get(vi).is_some_and(|v| {
                        *v == if l.is_pos() {
                            crate::literal::LBool::True
                        } else {
                            crate::literal::LBool::False
                        }
                    })
                });
                assert!(sat, "model violates an original clause (trial {trial})");
            }
        }
    }
}

/// The witness-polarity regression (2026-09-05): with the witness read as
/// `(¬g ∨ q)` instead of `(q ∨ g)`, the model `f = T, g = F, q_1 = F`
/// satisfies every original and witness but has NO `x` extension — the
/// rewrite flips satisfiable formulas to UNSAT (caught on the corpus A/B
/// as 18 sat→unsat flips before anything landed).  This fixture builds
/// that exact shape and requires the verdict to stay `Sat` with factoring
/// enabled.
#[test]
fn factor_witness_polarity_regression() {
    let mut base = Solver::new();
    let mut factored = Solver::new();
    let mut vars = Vec::new();
    for _ in 0..4 {
        vars.push(base.new_var());
        factored.new_var();
    }
    let [f, g, q1, q2] = [vars[0], vars[1], vars[2], vars[3]];
    // Quotients (f ∨ q_i) and witnesses in the polarity that fooled the
    // first port: clauses `(¬g ∨ q_i)`.
    for q in [q1, q2] {
        for s in [&mut base, &mut factored] {
            s.add_clause([Lit::pos(f), Lit::pos(q)]);
            s.add_clause([Lit::neg(g), Lit::pos(q)]);
        }
    }
    // Make it satisfiable with q_1 free to be false only when f holds:
    // units pin `g = F`; `f` and the `q_i` are then forced by the
    // witnesses only through `q_i` — the model `f=T, q_i=T` satisfies
    // everything.  `q_1 = F, f = T` satisfies the QUOTIENTS but not the
    // witnesses — the direction a wrong rewrite would flip.
    for s in [&mut base, &mut factored] {
        s.add_clause([Lit::neg(g)]);
    }
    assert_eq!(base.solve(), SolverResult::Sat);
    let (introduced, _) = factored.factor_binaries();
    // The witnesses `(¬g ∨ q_i)` legitimately match with candidate
    // `¬g` (the adjacency entry `¬q → ¬g` IS the clause `(q ∨ ¬g)`), so
    // factoring may fire — but must preserve the verdict either way.
    let got = factored.solve();
    assert_eq!(
        got,
        SolverResult::Sat,
        "factoring flipped the verdict (introduced={introduced}) — witness polarity regressed"
    );
}

// ---------------------------------------------------------------------------
// XOR (parity) extraction + GF(2) solve (2026-09-05, solver/xor.rs).
// ---------------------------------------------------------------------------

/// Strict detection: a full parity class is an XOR constraint; an
/// implication pair (mixed parities) and duplicated clauses are not.
#[test]
fn xor_detection_is_strict() {
    let mut s = Solver::new();
    let a = s.new_var();
    let b = s.new_var();
    let c = s.new_var();
    // XOR(a,b) = 0: (a ∨ b) ∧ (¬a ∨ ¬b).
    s.add_clause([Lit::pos(a), Lit::pos(b)]);
    s.add_clause([Lit::neg(a), Lit::neg(b)]);
    // Mixed pair over (a,c): (a ∨ c) ∧ (¬a ∨ c) — implies c, NOT an XOR.
    s.add_clause([Lit::pos(a), Lit::pos(c)]);
    s.add_clause([Lit::neg(a), Lit::pos(c)]);
    // Duplicate clause over (b,c) — not a complete class.
    s.add_clause([Lit::pos(b), Lit::pos(c)]);
    s.add_clause([Lit::pos(b), Lit::pos(c)]);
    let cs = s.detect_xor_constraints();
    assert_eq!(cs.len(), 1, "exactly the (a,b) parity class");
    assert_eq!(cs[0].vars.len(), 2);
    // (a ∨ b) ∧ (¬a ∨ ¬b) = exactly-one-true = ⊕(a,b) = 1.
    assert!(cs[0].rhs, "p=0 class encodes odd true-parity");
}

/// Full 3-var parity class (o ↔ a ⊕ b style) with odd parity.
#[test]
fn xor_detection_three_vars() {
    let mut s = Solver::new();
    let vs: Vec<_> = (0..3).map(|_| s.new_var()).collect();
    // Odd-negation-parity class (p=1): excludes odd-|T| assignments, so
    // the constraint is ⊕(v1,v2,v3) = 0 (even true-parity).
    s.add_clause(vs.iter().map(|&v| Lit::neg(v)));
    for i in 0..3 {
        s.add_clause((0..3).map(|j| {
            if j == i {
                Lit::neg(vs[j])
            } else {
                Lit::pos(vs[j])
            }
        }));
    }
    let cs = s.detect_xor_constraints();
    assert_eq!(cs.len(), 1);
    assert!(!cs[0].rhs, "p=1 class encodes even true-parity");
}

/// GE: a small consistent system solves; every returned assignment
/// satisfies every constraint; an inconsistent one is rejected.
#[test]
fn xor_gaussian_solve_and_consistency() {
    let mut s = Solver::new();
    let vs: Vec<_> = (0..6).map(|_| s.new_var()).collect();
    let idx = |v: usize| vs[v].index() as u32;
    let cons = vec![
        super::xor::XorConstraint {
            vars: smallvec::smallvec![idx(0), idx(1), idx(2)],
            rhs: false,
        },
        super::xor::XorConstraint {
            vars: smallvec::smallvec![idx(2), idx(3)],
            rhs: true,
        },
        super::xor::XorConstraint {
            vars: smallvec::smallvec![idx(4), idx(5)],
            rhs: true,
        },
    ];
    let assign = s.solve_xor_system(&cons).expect("consistent system");
    for c in &cons {
        let parity = c.vars.iter().filter(|v| assign[v]).count() % 2 == 1;
        assert_eq!(parity, c.rhs, "constraint over {:?} violated", c.vars);
    }
    // Inconsistent: x ⊕ y = 0 and x ⊕ y = 1.
    let bad = vec![
        super::xor::XorConstraint {
            vars: smallvec::smallvec![idx(0), idx(1)],
            rhs: false,
        },
        super::xor::XorConstraint {
            vars: smallvec::smallvec![idx(0), idx(1)],
            rhs: true,
        },
    ];
    assert!(s.solve_xor_system(&bad).is_err());
}

/// End-to-end: a formula whose clauses are exactly parity classes is
/// solved with zero conflicts under the seeded phases (the model-descent
/// theorem: UP never conflicts under model-consistent decisions).
#[test]
fn xor_phase_seed_gives_model_descent() {
    let mut s = Solver::with_config(SolverConfig {
        enable_xor_reasoning: true,
        random_polarity_prob: 0.0, // keep the descent pure for the test
        ..SolverConfig::default()
    });
    let vs: Vec<_> = (0..8).map(|_| s.new_var()).collect();
    // Three complete parity classes: a 3-var odd-negation class (⊕=0),
    // a 2-var even-negation class (⊕=1), a 2-var odd-negation class
    // (⊕=0) — the system pins x0..=x4.
    let mut cls3 = |neg: &[usize]| {
        s.add_clause((0..3).map(|i| {
            if neg.contains(&i) {
                Lit::neg(vs[i])
            } else {
                Lit::pos(vs[i])
            }
        }));
    };
    cls3(&[]);
    cls3(&[0, 1]);
    cls3(&[0, 2]);
    cls3(&[1, 2]);
    s.add_clause([Lit::pos(vs[3]), Lit::pos(vs[4])]);
    s.add_clause([Lit::neg(vs[3]), Lit::neg(vs[4])]);
    s.add_clause([Lit::neg(vs[5]), Lit::pos(vs[6])]);
    s.add_clause([Lit::pos(vs[5]), Lit::neg(vs[6])]);
    let (n, seeded, inconsistent) = s.xor_phase_seed();
    assert_eq!(n, 3);
    assert!(seeded >= 5, "the system pins at least the 5 XOR vars");
    assert!(!inconsistent);
    assert_eq!(s.solve(), SolverResult::Sat);
    assert_eq!(s.stats().conflicts, 0, "model-descent under seeded phases");
}

#[test]
fn xor_matrix_build_speed_at_mdp_scale() {
    use crate::xor::GF2Matrix;
    let t0 = std::time::Instant::now();
    let mut m = GF2Matrix::new();
    let mut rng: u64 = 0xDEAD_BEEF;
    let mut next = move || {
        rng ^= rng << 13;
        rng ^= rng >> 7;
        rng ^= rng << 17;
        rng
    };
    for i in 0..373 {
        let base = (next() % 700) as u32;
        let vars: Vec<crate::literal::Var> = (0..5)
            .map(|j| crate::literal::Var::new(base + j * 3 + (next() % 3) as u32))
            .collect();
        let _ = m.add_constraint(&vars, next() % 2 == 0, 0);
        if i % 100 == 0 {
            eprintln!("build i={i} t={:?}", t0.elapsed());
        }
    }
    let el = t0.elapsed();
    eprintln!("total build time: {el:?}");
    assert!(el.as_millis() < 500, "373-constraint build took {el:?}");
}

/// The probing pass derives forced units from a system that pins
/// variables: with `a ⊕ b = 1` and `a ⊕ b ⊕ c = 0`, subtracting gives
/// `c = 1` (an add-time unit); a probe of `d` against
/// `(¬d ∨ e)(d ∨ ¬e)`-style CNF glue forces nothing unless a polarity
/// conflicts.  This fixture pins via matrix reduction only.
#[test]
fn xor_probe_forces_pinned_units() {
    let mut s = Solver::new();
    let a = s.new_var();
    let b = s.new_var();
    let c = s.new_var();
    // a ⊕ b = 1: (a ∨ b) ∧ (¬a ∨ ¬b).
    s.add_clause([Lit::pos(a), Lit::pos(b)]);
    s.add_clause([Lit::neg(a), Lit::neg(b)]);
    // a ⊕ b ⊕ c = 0: the even-negation 3-var class.
    s.add_clause([Lit::neg(a), Lit::neg(b), Lit::neg(c)]);
    s.add_clause([Lit::neg(a), Lit::pos(b), Lit::pos(c)]);
    s.add_clause([Lit::pos(a), Lit::neg(b), Lit::pos(c)]);
    s.add_clause([Lit::pos(a), Lit::pos(b), Lit::neg(c)]);
    let (n, forced, inconsistent) = s.xor_probe();
    assert_eq!(n, 2);
    assert!(!inconsistent);
    // c = 1 pinned by the difference of the two rows; a, b stay free
    // (the system pins only their parity).
    assert!(forced >= 1, "the row difference must pin c");
    assert!(s.trail.is_assigned(c));
    assert_eq!(s.trail.lit_value(Lit::pos(c)), crate::literal::LBool::True);
}

/// Mid-search XOR propagation must fire where CNF-UP cannot: a parity
/// chain `a ⊕ b ⊕ c = 1`, `c ⊕ d ⊕ e = 1` whose interior variable `c` is
/// only determined once `a` and `b` are assigned — unit propagation over
/// the CNF classes cannot derive it (parity needs counting).  With the
/// integration on, deciding `a` and `b` cascades `c` through the matrix
/// with a materialized reason.
#[test]
fn xor_search_propagates_parity_midsearch() {
    let mk = |on: bool| -> (Solver, usize) {
        let mut s = Solver::with_config(SolverConfig {
            enable_xor_reasoning: on,
            ..SolverConfig::default()
        });
        let vars: Vec<_> = (0..5).map(|_| s.new_var()).collect();
        // a ⊕ b ⊕ c = 1 (odd true-parity class = even negation parity).
        let cls3 = |s: &mut Solver, neg: &[usize]| {
            s.add_clause((0..3).map(|i| {
                if neg.contains(&i) {
                    Lit::neg(vars[i])
                } else {
                    Lit::pos(vars[i])
                }
            }));
        };
        cls3(&mut s, &[]);
        cls3(&mut s, &[0, 1]);
        cls3(&mut s, &[0, 2]);
        cls3(&mut s, &[1, 2]);
        // c ⊕ d ⊕ e = 1.
        let cls3b = |s: &mut Solver, neg: &[usize]| {
            s.add_clause((2..5).map(|i| {
                if neg.contains(&i) {
                    Lit::neg(vars[i])
                } else {
                    Lit::pos(vars[i])
                }
            }));
        };
        cls3b(&mut s, &[]);
        cls3b(&mut s, &[0, 1]);
        cls3b(&mut s, &[0, 2]);
        cls3b(&mut s, &[1, 2]);
        // Glue: pin nothing at level 0 (so the parity cascade must come
        // from decisions), just forbid one corner.
        s.add_clause([Lit::neg(vars[3]), Lit::neg(vars[4])]);
        (s, vars.len())
    };
    // The integration is env-gated at solve(); exercise the step directly.
    let (mut s, _) = mk(true);
    let installed = s.xor_search_init();
    assert_eq!(installed, 0, "nothing pinned at level 0");
    assert!(s.xor_search_active());
    // Decide a=true, b=true at levels 1 and 2 (as the search would).
    let a = Var::new(0);
    let b = Var::new(1);
    let c = Var::new(2);
    s.trail.new_decision_level();
    s.trail.assign_decision(Lit::pos(a));
    assert!(s.propagate().is_none());
    assert!(s.xor_search_step().is_none(), "row still has two free vars");
    s.trail.new_decision_level();
    s.trail.assign_decision(Lit::pos(b));
    assert!(s.propagate().is_none());
    // Now the row a⊕b⊕c=1 folds to single-var: 1⊕1⊕c = c, so c is
    // FORCED true (the parity is odd and a=b=true contribute none), with
    // a materialized reason clause.
    assert!(s.xor_search_step().is_none(), "unit assigned, no conflict");
    assert!(
        s.trail.is_assigned(c),
        "the matrix must propagate c once a and b are assigned"
    );
    assert_eq!(
        s.trail.lit_value(Lit::pos(c)),
        crate::literal::LBool::True,
        "a=b=true forces c=true under odd parity (1 xor 1 xor c = c = 1)"
    );
    // And the cascade continues into the second row: c=true ⇒ d⊕e=0 — not
    // single-var yet (two free), so stop here.
    s.backtrack(0);
    // Rollback restored the matrix: re-folding the same decisions must
    // re-derive the same unit.
    s.trail.new_decision_level();
    s.trail.assign_decision(Lit::pos(a));
    let _ = s.propagate();
    let _ = s.xor_search_step();
    s.trail.new_decision_level();
    s.trail.assign_decision(Lit::pos(b));
    let _ = s.propagate();
    let _ = s.xor_search_step();
    assert_eq!(s.trail.lit_value(Lit::pos(c)), crate::literal::LBool::True);
}

/// Differential: random parity-class + glue formulas; with the matrix
/// installed the search's verdict must match a plain solver's, and Sat
/// models must satisfy the original clauses (the materialized XOR reasons
/// are entailed, so they can never flip satisfiability).
#[test]
fn xor_search_differential_random() {
    let mut rng: u64 = 0xB502_6F5A_A9D1_9A5B;
    let mut next = move || {
        rng ^= rng << 13;
        rng ^= rng >> 7;
        rng ^= rng << 17;
        rng
    };
    for trial in 0..200 {
        let n = 6 + (next() % 4) as usize;
        let mut base = Solver::new();
        let mut withxor = Solver::new();
        for _ in 0..n {
            base.new_var();
            withxor.new_var();
        }
        let mut clauses: Vec<Vec<Lit>> = Vec::new();
        // Two random 3-var parity classes + random glue clauses.
        for _ in 0..2 {
            let vs: Vec<usize> = {
                let mut v: Vec<usize> = (0..n).collect();
                v.sort_by_key(|_| next());
                v.truncate(3);
                v
            };
            for neg in [&[][..], &[0usize, 1], &[0, 2], &[1, 2]] {
                let cl: Vec<Lit> = vs
                    .iter()
                    .enumerate()
                    .map(|(i, &v)| {
                        if neg.contains(&i) {
                            Lit::neg(Var::new(v as u32))
                        } else {
                            Lit::pos(Var::new(v as u32))
                        }
                    })
                    .collect();
                clauses.push(cl);
            }
        }
        for _ in 0..(2 + next() % 3) {
            let k = 2 + (next() % 2) as usize;
            let mut cl: Vec<Lit> = Vec::new();
            for _ in 0..k {
                let v = (next() % n as u64) as u32;
                let l = if next() & 1 == 0 {
                    Lit::pos(Var::new(v))
                } else {
                    Lit::neg(Var::new(v))
                };
                if !cl.contains(&l) && !cl.contains(&l.negate()) {
                    cl.push(l);
                }
            }
            if !cl.is_empty() {
                clauses.push(cl);
            }
        }
        for cl in &clauses {
            base.add_clause(cl.iter().copied());
            withxor.add_clause(cl.iter().copied());
        }
        let expected = base.solve();
        let _ = withxor.xor_search_init();
        let got = withxor.solve();
        assert_eq!(
            expected, got,
            "verdict changed by in-search XOR propagation (trial {trial})"
        );
        if got == SolverResult::Sat {
            let m = withxor.model();
            for cl in &clauses {
                let sat = cl.iter().any(|l| {
                    let vi = l.var().index();
                    m.get(vi).is_some_and(|v| {
                        *v == if l.is_pos() {
                            crate::literal::LBool::True
                        } else {
                            crate::literal::LBool::False
                        }
                    })
                });
                assert!(sat, "model violates an original clause (trial {trial})");
            }
        }
    }
}

/// Reference model for the CSR binary implication graph's combined-view
/// semantics (`solver/mod.rs`): a `Vec<Vec<(Lit, ClauseId)>>` shaped exactly
/// like the historical per-literal lists. Every randomized op sequence below
/// is applied to both, and the per-literal sequences must match after every
/// step — this is the BIG-side twin of `round_occs_matches_vec_semantics`
/// (the eliminator CSR's guard) and pins the same contract the walk's
/// by-id merge and propagation's scan order depend on.
#[test]
fn binary_graph_matches_vec_semantics() {
    let mut rng: u64 = 0x243F6A8885A308D3;
    let mut next = || {
        rng ^= rng << 13;
        rng ^= rng >> 7;
        rng ^= rng << 17;
        rng
    };
    for round in 0..30u64 {
        let vars = 6 + (next() % 10) as usize;
        let mut big = BinaryImplicationGraph::new(vars);
        let mut model: Vec<Vec<(Lit, ClauseId)>> = vec![Vec::new(); vars * 2];

        // Phase A: full rebuild via the two-phase builder (count, layout,
        // fill) — must reproduce the same per-literal order as pushing the
        // same edges into the reference.
        let mut built: Vec<(Lit, Lit, ClauseId)> = Vec::new();
        for _ in 0..vars * 2 {
            if next() % 3 != 0 {
                let a = Lit::from_code((next() % (vars as u64 * 2)) as u32);
                let b = Lit::from_code((next() % (vars as u64 * 2)) as u32);
                built.push((a, b, ClauseId::new((next() % 1000) as u32)));
            }
        }
        big.build_reset(vars);
        for &(a, b, _) in &built {
            big.build_count(a);
            big.build_count(b);
        }
        big.build_layout();
        for &(a, b, cid) in &built {
            big.build_edge(a, b, cid);
            big.build_edge(b, a, cid);
            model[a.code() as usize].push((b, cid));
            model[b.code() as usize].push((a, cid));
        }
        big.shrink();

        // Phase B: interleaved incremental adds, order-preserving
        // deletions, and mid-content variable growth (the `new_var`
        // mid-search shape: new codes' spans must stay empty and start
        // past every existing span — a 0-fill here would alias code 0's
        // span, misreading its edges as the new code's).
        // Clause ids are unique per (trigger, clause) in the real solver
        // (one edge per binary per trigger); the randomized model needs the
        // same uniqueness or "remove first occurrence" is ambiguous.
        let mut next_cid = 1000u32;
        let mut cur_vars = vars;
        for step in 0..200 {
            if step % 37 == 5 {
                cur_vars += 1 + (next() % 3) as usize;
                big.resize(cur_vars);
                model.resize(cur_vars * 2, Vec::new());
            }
            let code = (next() % (cur_vars as u64 * 2)) as u32;
            let lit = Lit::from_code(code);
            match next() % 4 {
                0 | 1 => {
                    let to = Lit::from_code((next() % (cur_vars as u64 * 2)) as u32);
                    let cid = ClauseId::new(next_cid);
                    next_cid += 1;
                    big.add(lit, to, cid);
                    model[code as usize].push((to, cid));
                }
                2 => {
                    let list = model[code as usize].clone();
                    if let Some(&(_, cid)) = list.get((next() as usize) % list.len().max(1))
                        && !list.is_empty()
                    {
                        big.remove_clause_edges(lit, cid);
                        let pos = model[code as usize]
                            .iter()
                            .position(|&(_, c)| c == cid)
                            .unwrap_or(0);
                        if pos < model[code as usize].len() {
                            model[code as usize].remove(pos);
                        }
                    }
                }
                _ => {}
            }
        }

        // The contract: every literal's combined view (primary span then
        // overflow) equals the reference list in content AND order.
        for (code, reference) in model.iter().enumerate() {
            let lit = Lit::from_code(code as u32);
            let got: Vec<(Lit, ClauseId)> = big.get(lit).iter().copied().collect();
            assert_eq!(
                got, *reference,
                "round {round}: BIG view diverged at code {code}"
            );
            assert_eq!(big.get(lit).len(), reference.len());
        }
        let (edges, _) = big.edge_accounting();
        assert_eq!(
            edges,
            model.iter().map(Vec::len).sum::<usize>(),
            "edge accounting must count the combined view"
        );
    }
}

/// The bulk-load deferral pair must materialize a graph identical to the one
/// incremental `attach_watchers` calls build: the DIMACS parse path's
/// trajectory-neutrality contract, at unit scale. Both solvers get the same
/// clause stream; one attaches immediately, the other defers and flushes.
#[test]
fn deferred_big_materializes_incremental_attach() {
    let mut rng: u64 = 0x13198A2E03707344;
    let mut next = || {
        rng ^= rng << 13;
        rng ^= rng >> 7;
        rng ^= rng << 17;
        rng
    };
    for _ in 0..25 {
        let vars = 8 + (next() % 12) as usize;
        let mut a = Solver::new();
        let mut b = Solver::new();
        for s in [&mut a, &mut b] {
            s.ensure_vars(vars);
        }
        b.begin_deferred_big();
        for _ in 0..120 {
            let len = 2 + (next() % 3) as usize;
            let lits: Vec<Lit> = (0..len)
                .map(|_| {
                    let v = Var::new((next() % vars as u64) as u32);
                    if next() % 2 == 0 {
                        Lit::pos(v)
                    } else {
                        Lit::neg(v)
                    }
                })
                .collect();
            let mut dedup = lits.clone();
            dedup.sort_by_key(|l| l.code());
            dedup.dedup();
            if dedup.len() != lits.len() {
                continue; // duplicate literal: add_clause paths diverge
            }
            a.add_clause(lits.iter().copied());
            b.add_clause(lits.iter().copied());
        }
        b.finish_deferred_big();
        for code in 0..vars * 2 {
            let lit = Lit::from_code(code as u32);
            let va: Vec<(Lit, ClauseId)> = a.binary_graph.get(lit).iter().copied().collect();
            let vb: Vec<(Lit, ClauseId)> = b.binary_graph.get(lit).iter().copied().collect();
            assert_eq!(
                va, vb,
                "deferred materialization diverged from incremental attach at code {code}"
            );
        }
    }
}
