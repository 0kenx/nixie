use super::*;
use num_bigint::BigInt;
use num_traits::ToPrimitive;

#[test]
fn test_solver_empty() {
    let mut solver = Solver::new();
    let mut manager = TermManager::new();
    assert_eq!(solver.check(&mut manager), SolverResult::Sat);
}

#[test]
fn test_solver_true() {
    let mut solver = Solver::new();
    let mut manager = TermManager::new();
    let t = manager.mk_true();
    solver.assert(t, &mut manager);
    assert_eq!(solver.check(&mut manager), SolverResult::Sat);
}

#[test]
fn test_solver_false() {
    let mut solver = Solver::new();
    let mut manager = TermManager::new();
    let f = manager.mk_false();
    solver.assert(f, &mut manager);
    assert_eq!(solver.check(&mut manager), SolverResult::Unsat);
}

#[test]
fn test_solver_push_pop() {
    let mut solver = Solver::new();
    let mut manager = TermManager::new();

    let t = manager.mk_true();
    solver.assert(t, &mut manager);
    solver.push();

    let f = manager.mk_false();
    solver.assert(f, &mut manager);
    assert_eq!(solver.check(&mut manager), SolverResult::Unsat);

    solver.pop();
    assert_eq!(solver.check(&mut manager), SolverResult::Sat);
}

#[test]
fn test_unsat_core_trivial() {
    let mut solver = Solver::new();
    let mut manager = TermManager::new();
    solver.set_produce_unsat_cores(true);

    let t = manager.mk_true();
    let f = manager.mk_false();

    solver.assert_named(t, "a1", &mut manager);
    solver.assert_named(f, "a2", &mut manager);
    solver.assert_named(t, "a3", &mut manager);

    assert_eq!(solver.check(&mut manager), SolverResult::Unsat);

    let core = solver.get_unsat_core();
    assert!(core.is_some());

    let core = core.expect("unsat core should be available after UNSAT result");
    assert!(!core.is_empty());
    assert!(core.names.contains(&"a2".to_string()));
}

#[test]
fn test_unsat_core_not_produced_when_sat() {
    let mut solver = Solver::new();
    let mut manager = TermManager::new();
    solver.set_produce_unsat_cores(true);

    let t = manager.mk_true();
    solver.assert_named(t, "a1", &mut manager);
    solver.assert_named(t, "a2", &mut manager);

    assert_eq!(solver.check(&mut manager), SolverResult::Sat);
    assert!(solver.get_unsat_core().is_none());
}

#[test]
fn test_unsat_core_disabled() {
    let mut solver = Solver::new();
    let mut manager = TermManager::new();
    // Don't enable unsat cores

    let f = manager.mk_false();
    solver.assert(f, &mut manager);
    assert_eq!(solver.check(&mut manager), SolverResult::Unsat);

    // Core should be None when not enabled
    assert!(solver.get_unsat_core().is_none());
}

#[test]
fn test_boolean_encoding_and() {
    let mut solver = Solver::new();
    let mut manager = TermManager::new();

    // Test: (p and q) should be SAT with p=true, q=true
    let p = manager.mk_var("p", manager.sorts.bool_sort);
    let q = manager.mk_var("q", manager.sorts.bool_sort);
    let and = manager.mk_and(vec![p, q]);

    solver.assert(and, &mut manager);
    assert_eq!(solver.check(&mut manager), SolverResult::Sat);

    // The model should have both p and q as true
    let model = solver.model().expect("Should have model");
    assert!(model.get(p).is_some());
    assert!(model.get(q).is_some());
}

#[test]
fn test_boolean_encoding_or() {
    let mut solver = Solver::new();
    let mut manager = TermManager::new();

    // Test: (p or q) and (not p) should be SAT with q=true
    let p = manager.mk_var("p", manager.sorts.bool_sort);
    let q = manager.mk_var("q", manager.sorts.bool_sort);
    let or = manager.mk_or(vec![p, q]);
    let not_p = manager.mk_not(p);

    solver.assert(or, &mut manager);
    solver.assert(not_p, &mut manager);
    assert_eq!(solver.check(&mut manager), SolverResult::Sat);
}

#[test]
fn test_boolean_encoding_implies() {
    let mut solver = Solver::new();
    let mut manager = TermManager::new();

    // Test: (p => q) and p and (not q) should be UNSAT
    let p = manager.mk_var("p", manager.sorts.bool_sort);
    let q = manager.mk_var("q", manager.sorts.bool_sort);
    let implies = manager.mk_implies(p, q);
    let not_q = manager.mk_not(q);

    solver.assert(implies, &mut manager);
    solver.assert(p, &mut manager);
    solver.assert(not_q, &mut manager);
    assert_eq!(solver.check(&mut manager), SolverResult::Unsat);
}

#[test]
fn test_boolean_encoding_distinct() {
    let mut solver = Solver::new();
    let mut manager = TermManager::new();

    // Test: distinct(p, q, r) and p and q should be UNSAT (since p=q)
    let p = manager.mk_var("p", manager.sorts.bool_sort);
    let q = manager.mk_var("q", manager.sorts.bool_sort);
    let r = manager.mk_var("r", manager.sorts.bool_sort);
    let distinct = manager.mk_distinct(vec![p, q, r]);

    solver.assert(distinct, &mut manager);
    solver.assert(p, &mut manager);
    solver.assert(q, &mut manager);
    assert_eq!(solver.check(&mut manager), SolverResult::Unsat);
}

#[test]
fn test_model_evaluation_bool() {
    let mut solver = Solver::new();
    let mut manager = TermManager::new();

    let p = manager.mk_var("p", manager.sorts.bool_sort);
    let q = manager.mk_var("q", manager.sorts.bool_sort);

    // Assert p and not q
    solver.assert(p, &mut manager);
    solver.assert(manager.mk_not(q), &mut manager);
    assert_eq!(solver.check(&mut manager), SolverResult::Sat);

    let model = solver.model().expect("Should have model");

    // Evaluate p (should be true)
    let p_val = model.eval(p, &mut manager);
    assert_eq!(p_val, manager.mk_true());

    // Evaluate q (should be false)
    let q_val = model.eval(q, &mut manager);
    assert_eq!(q_val, manager.mk_false());

    // Evaluate (p and q) - should be false
    let and_term = manager.mk_and(vec![p, q]);
    let and_val = model.eval(and_term, &mut manager);
    assert_eq!(and_val, manager.mk_false());

    // Evaluate (p or q) - should be true
    let or_term = manager.mk_or(vec![p, q]);
    let or_val = model.eval(or_term, &mut manager);
    assert_eq!(or_val, manager.mk_true());
}

#[test]
fn test_model_evaluation_ite() {
    let mut solver = Solver::new();
    let mut manager = TermManager::new();

    let p = manager.mk_var("p", manager.sorts.bool_sort);
    let q = manager.mk_var("q", manager.sorts.bool_sort);
    let r = manager.mk_var("r", manager.sorts.bool_sort);

    // Assert p
    solver.assert(p, &mut manager);
    assert_eq!(solver.check(&mut manager), SolverResult::Sat);

    let model = solver.model().expect("Should have model");

    // Evaluate (ite p q r) - should evaluate to q since p is true
    let ite_term = manager.mk_ite(p, q, r);
    let ite_val = model.eval(ite_term, &mut manager);
    // The result should be q's value (whatever it is in the model)
    let q_val = model.eval(q, &mut manager);
    assert_eq!(ite_val, q_val);
}

#[test]
fn test_model_evaluation_implies() {
    let mut solver = Solver::new();
    let mut manager = TermManager::new();

    let p = manager.mk_var("p", manager.sorts.bool_sort);
    let q = manager.mk_var("q", manager.sorts.bool_sort);

    // Assert not p
    solver.assert(manager.mk_not(p), &mut manager);
    assert_eq!(solver.check(&mut manager), SolverResult::Sat);

    let model = solver.model().expect("Should have model");

    // Evaluate (p => q) - should be true since p is false
    let implies_term = manager.mk_implies(p, q);
    let implies_val = model.eval(implies_term, &mut manager);
    assert_eq!(implies_val, manager.mk_true());
}

/// Test BV comparison model extraction: 5 < x < 10 should give x in [6, 9].
///
/// Regression test for the BV comparison wrong-model bug: the solver returns SAT
/// for `5 <_u x ∧ x <_u 10`, but model extraction used to yield a non-satisfying
/// value for `x` (122, violating `x <_u 10`). The BV comparison variable is
/// registered in both `BvSolver` and `ArithSolver`; the BV comparison path
/// allocates *unpinned* bits for the constant operands, so `bv.get_value`
/// returned an arbitrary value ignoring the bound, while the `ArithSolver` (which
/// parses the constants) held the real bounds. `model_builder::build_model` now
/// establishes sort/usage-based theory ownership: for a comparison-only BV
/// problem the ArithSolver value is authoritative, so `x` lands in `[6, 9]`.
#[test]
fn test_bv_comparison_model_generation() {
    // Test BV comparison: 5 < x < 10 should give x in range [6, 9]
    let mut solver = Solver::new();
    let mut manager = TermManager::new();

    solver.set_logic("QF_BV");

    // Create BitVec[8] variable
    let bv8_sort = manager.sorts.bitvec(8);
    let x = manager.mk_var("x", bv8_sort);

    // Create constants
    let five = manager.mk_bitvec(5i64, 8);
    let ten = manager.mk_bitvec(10i64, 8);

    // Assert: 5 < x (unsigned)
    let lt1 = manager.mk_bv_ult(five, x);
    solver.assert(lt1, &mut manager);

    // Assert: x < 10 (unsigned)
    let lt2 = manager.mk_bv_ult(x, ten);
    solver.assert(lt2, &mut manager);

    let result = solver.check(&mut manager);
    assert_eq!(result, SolverResult::Sat);

    // Check that we get a valid model
    let model = solver.model().expect("Should have model");

    // The model MUST assign x (a non-vacuous check): build_model always emits a
    // BitVecConst for every tracked BV term, so a missing or non-const value is
    // itself a regression, not a reason to skip the range assertion.
    let x_value_id = model.get(x).expect("model must assign a value to x");
    let x_term = manager
        .get(x_value_id)
        .expect("x's model value must be a live term");
    let TermKind::BitVecConst { value, .. } = &x_term.kind else {
        panic!(
            "x's model value must be a BitVecConst, got {:?}",
            x_term.kind
        );
    };
    let x_val = value.to_u64().expect("8-bit value fits in u64");
    // x should be in range [6, 9]
    assert!(
        (6..=9).contains(&x_val),
        "Expected x in [6,9], got {}",
        x_val
    );
}

#[test]
fn test_arithmetic_model_generation() {
    use num_bigint::BigInt;

    let mut solver = Solver::new();
    let mut manager = TermManager::new();

    // Create integer variables
    let x = manager.mk_var("x", manager.sorts.int_sort);
    let y = manager.mk_var("y", manager.sorts.int_sort);

    // Create constraints: x + y = 10, x >= 0, y >= 0
    let ten = manager.mk_int(BigInt::from(10));
    let zero = manager.mk_int(BigInt::from(0));
    let sum = manager.mk_add(vec![x, y]);

    let eq = manager.mk_eq(sum, ten);
    let x_ge_0 = manager.mk_ge(x, zero);
    let y_ge_0 = manager.mk_ge(y, zero);

    solver.assert(eq, &mut manager);
    solver.assert(x_ge_0, &mut manager);
    solver.assert(y_ge_0, &mut manager);

    assert_eq!(solver.check(&mut manager), SolverResult::Sat);

    // Check that we can get a model (even if the arithmetic values aren't fully computed yet)
    let model = solver.model();
    assert!(model.is_some(), "Should have a model for SAT result");
}

#[test]
fn test_lra_issue_6_negative_coefficient_mul() {
    // Regression for https://github.com/cool-japan/oxiz/issues/6
    // Assertions:
    //   (>= (* -3.0 x1) 3.0)   =>  x1 <= -1
    //   (=  (* 4.0 x1)  -1.0)  =>  x1 = -1/4
    // These are jointly unsatisfiable.  Previously Nixie answered `sat` with
    // x1 = 0 because `(* const var)` was silently dropped by the linear
    // extractor whenever the constant factor was the result of a negation or
    // when a negative numeric literal was encoded as an opaque symbol.
    use num_rational::Rational64;

    let mut solver = Solver::new();
    let mut manager = TermManager::new();

    let x1 = manager.mk_var("x1", manager.sorts.real_sort);

    // (* -3.0 x1) >= 3.0
    let neg_three = manager.mk_real(Rational64::new(-3, 1));
    let three = manager.mk_real(Rational64::new(3, 1));
    let lhs1 = manager.mk_mul([neg_three, x1]);
    let c1 = manager.mk_ge(lhs1, three);

    // (* 4.0 x1) = -1.0
    let four = manager.mk_real(Rational64::new(4, 1));
    let neg_one = manager.mk_real(Rational64::new(-1, 1));
    let lhs2 = manager.mk_mul([four, x1]);
    let c2 = manager.mk_eq(lhs2, neg_one);

    solver.assert(c1, &mut manager);
    solver.assert(c2, &mut manager);

    assert_eq!(
        solver.check(&mut manager),
        SolverResult::Unsat,
        "x1 <= -1 AND x1 = -1/4 must be UNSAT"
    );
}

#[test]
fn test_lra_issue_6_mul_with_negation_factor() {
    // Companion check: the constant factor appearing inside `Mul` as a
    // negation node `(- 3.0)` instead of a direct `RealConst(-3.0)` must also
    // be recognised as a pure constant by the linear extractor.
    use num_rational::Rational64;

    let mut solver = Solver::new();
    let mut manager = TermManager::new();

    let x1 = manager.mk_var("x1", manager.sorts.real_sort);

    let three = manager.mk_real(Rational64::new(3, 1));
    let neg_three = manager.mk_neg(three);
    let lhs = manager.mk_mul([neg_three, x1]);
    let c = manager.mk_ge(lhs, three);
    solver.assert(c, &mut manager);

    // x1 <= -1, additionally assert x1 = -1/4 to force UNSAT.
    let four = manager.mk_real(Rational64::new(4, 1));
    let neg_one = manager.mk_real(Rational64::new(-1, 1));
    let lhs2 = manager.mk_mul([four, x1]);
    let c2 = manager.mk_eq(lhs2, neg_one);
    solver.assert(c2, &mut manager);

    assert_eq!(solver.check(&mut manager), SolverResult::Unsat);
}

#[test]
fn test_model_pretty_print() {
    let mut solver = Solver::new();
    let mut manager = TermManager::new();

    let p = manager.mk_var("p", manager.sorts.bool_sort);
    let q = manager.mk_var("q", manager.sorts.bool_sort);

    solver.assert(p, &mut manager);
    solver.assert(manager.mk_not(q), &mut manager);
    assert_eq!(solver.check(&mut manager), SolverResult::Sat);

    let model = solver.model().expect("Should have model");
    let pretty = model.pretty_print(&manager);

    // Should contain the model structure
    assert!(pretty.contains("(model"));
    assert!(pretty.contains("define-fun"));
    // Should contain variable names
    assert!(pretty.contains("p") || pretty.contains("q"));
}

#[test]
fn test_trail_based_undo_assertions() {
    let mut solver = Solver::new();
    let mut manager = TermManager::new();

    let p = manager.mk_var("p", manager.sorts.bool_sort);
    let q = manager.mk_var("q", manager.sorts.bool_sort);

    // Initial state
    assert_eq!(solver.assertions.len(), 0);
    assert_eq!(solver.trail.len(), 0);

    // Assert p
    solver.assert(p, &mut manager);
    assert_eq!(solver.assertions.len(), 1);
    assert!(!solver.trail.is_empty());

    // Push and assert q
    solver.push();
    let trail_len_after_push = solver.trail.len();
    solver.assert(q, &mut manager);
    assert_eq!(solver.assertions.len(), 2);
    assert!(solver.trail.len() > trail_len_after_push);

    // Pop should undo the second assertion
    solver.pop();
    assert_eq!(solver.assertions.len(), 1);
    assert_eq!(solver.assertions[0], p);
}

#[test]
fn test_trail_based_undo_variables() {
    let mut solver = Solver::new();
    let mut manager = TermManager::new();

    let p = manager.mk_var("p", manager.sorts.bool_sort);
    let q = manager.mk_var("q", manager.sorts.bool_sort);

    // Assert p creates variables
    solver.assert(p, &mut manager);
    let initial_var_count = solver.term_to_var.len();

    // Push and assert q
    solver.push();
    solver.assert(q, &mut manager);
    assert!(solver.term_to_var.len() >= initial_var_count);

    // Pop should remove q's variable
    solver.pop();
    // Note: Some variables may remain due to encoding, but q should be removed
    assert_eq!(solver.assertions.len(), 1);
}

#[test]
fn test_trail_based_undo_constraints() {
    let mut solver = Solver::new();
    let mut manager = TermManager::new();

    let x = manager.mk_var("x", manager.sorts.int_sort);
    let zero = manager.mk_int(BigInt::from(0));

    // Assert x >= 0 creates a constraint
    let c1 = manager.mk_ge(x, zero);
    solver.assert(c1, &mut manager);
    let initial_constraint_count = solver.var_to_constraint.len();

    // Push and add another constraint
    solver.push();
    let ten = manager.mk_int(BigInt::from(10));
    let c2 = manager.mk_le(x, ten);
    solver.assert(c2, &mut manager);
    assert!(solver.var_to_constraint.len() >= initial_constraint_count);

    // Pop should remove the second constraint
    solver.pop();
    assert_eq!(solver.var_to_constraint.len(), initial_constraint_count);
}

#[test]
fn test_trail_based_undo_false_assertion() {
    let mut solver = Solver::new();
    let mut manager = TermManager::new();

    assert!(!solver.has_false_assertion);

    solver.push();
    solver.assert(manager.mk_false(), &mut manager);
    assert!(solver.has_false_assertion);

    solver.pop();
    assert!(!solver.has_false_assertion);
}

#[test]
fn test_trail_based_undo_named_assertions() {
    let mut solver = Solver::new();
    let mut manager = TermManager::new();
    solver.set_produce_unsat_cores(true);

    let p = manager.mk_var("p", manager.sorts.bool_sort);

    solver.assert_named(p, "assertion1", &mut manager);
    assert_eq!(solver.named_assertions.len(), 1);

    solver.push();
    let q = manager.mk_var("q", manager.sorts.bool_sort);
    solver.assert_named(q, "assertion2", &mut manager);
    assert_eq!(solver.named_assertions.len(), 2);

    solver.pop();
    assert_eq!(solver.named_assertions.len(), 1);
    assert_eq!(
        solver.named_assertions[0].name,
        Some("assertion1".to_string())
    );
}

#[test]
fn test_trail_based_undo_nested_push_pop() {
    let mut solver = Solver::new();
    let mut manager = TermManager::new();

    let p = manager.mk_var("p", manager.sorts.bool_sort);
    solver.assert(p, &mut manager);

    // First push
    solver.push();
    let q = manager.mk_var("q", manager.sorts.bool_sort);
    solver.assert(q, &mut manager);
    assert_eq!(solver.assertions.len(), 2);

    // Second push
    solver.push();
    let r = manager.mk_var("r", manager.sorts.bool_sort);
    solver.assert(r, &mut manager);
    assert_eq!(solver.assertions.len(), 3);

    // Pop once
    solver.pop();
    assert_eq!(solver.assertions.len(), 2);

    // Pop again
    solver.pop();
    assert_eq!(solver.assertions.len(), 1);
    assert_eq!(solver.assertions[0], p);
}

#[test]
fn test_config_presets() {
    // Test that all presets can be created without panicking
    let _fast = SolverConfig::fast();
    let _balanced = SolverConfig::balanced();
    let _thorough = SolverConfig::thorough();
    let _minimal = SolverConfig::minimal();
}

#[test]
fn test_config_fast_characteristics() {
    let config = SolverConfig::fast();

    // Fast config should disable expensive features
    assert!(!config.enable_variable_elimination);
    assert!(!config.enable_blocked_clause_elimination);
    assert!(!config.enable_symmetry_breaking);
    assert!(!config.enable_inprocessing);
    assert!(!config.enable_clause_subsumption);

    // But keep fast optimizations
    assert!(config.enable_clause_minimization);
    assert!(config.simplify);

    // Should use Geometric restarts (faster)
    assert_eq!(config.restart_strategy, RestartStrategy::Geometric);
}

#[test]
fn test_config_balanced_characteristics() {
    let config = SolverConfig::balanced();

    // Balanced should enable most features with moderate settings
    assert!(config.enable_variable_elimination);
    assert!(config.enable_blocked_clause_elimination);
    assert!(config.enable_inprocessing);
    assert!(config.enable_clause_minimization);
    assert!(config.enable_clause_subsumption);
    assert!(config.simplify);

    // But not the most expensive one
    assert!(!config.enable_symmetry_breaking);

    // Should use Glucose restarts (adaptive)
    assert_eq!(config.restart_strategy, RestartStrategy::Glucose);

    // Conservative limits
    assert_eq!(config.variable_elimination_limit, 1000);
    assert_eq!(config.inprocessing_interval, 10000);
}

#[test]
fn test_config_thorough_characteristics() {
    let config = SolverConfig::thorough();

    // Thorough should enable all features
    assert!(config.enable_variable_elimination);
    assert!(config.enable_blocked_clause_elimination);
    assert!(config.enable_symmetry_breaking); // Even this expensive one
    assert!(config.enable_inprocessing);
    assert!(config.enable_clause_minimization);
    assert!(config.enable_clause_subsumption);
    assert!(config.simplify);

    // Aggressive settings
    assert_eq!(config.variable_elimination_limit, 5000);
    assert_eq!(config.inprocessing_interval, 5000);
}

#[test]
fn test_config_minimal_characteristics() {
    let config = SolverConfig::minimal();

    // Minimal should disable everything optional
    assert!(!config.simplify);
    assert!(!config.enable_variable_elimination);
    assert!(!config.enable_blocked_clause_elimination);
    assert!(!config.enable_symmetry_breaking);
    assert!(!config.enable_inprocessing);
    assert!(!config.enable_clause_minimization);
    assert!(!config.enable_clause_subsumption);

    // Should use lazy theory mode for minimal overhead
    assert_eq!(config.theory_mode, TheoryMode::Lazy);

    // Single threaded
    assert_eq!(config.num_threads, 1);
}

#[test]
fn test_config_builder_pattern() {
    // Test the builder-style methods
    let config = SolverConfig::fast()
        .with_proof()
        .with_timeout(5000)
        .with_max_conflicts(1000)
        .with_max_decisions(2000)
        .with_parallel(8)
        .with_restart_strategy(RestartStrategy::Luby)
        .with_theory_mode(TheoryMode::Lazy);

    assert!(config.proof);
    assert_eq!(config.timeout_ms, 5000);
    assert_eq!(config.max_conflicts, 1000);
    assert_eq!(config.max_decisions, 2000);
    assert!(config.parallel);
    assert_eq!(config.num_threads, 8);
    assert_eq!(config.restart_strategy, RestartStrategy::Luby);
    assert_eq!(config.theory_mode, TheoryMode::Lazy);
}

#[test]
fn test_solver_with_different_configs() {
    let mut manager = TermManager::new();

    // Create solvers with different configs
    let mut solver_fast = Solver::with_config(SolverConfig::fast());
    let mut solver_balanced = Solver::with_config(SolverConfig::balanced());
    let mut solver_thorough = Solver::with_config(SolverConfig::thorough());
    let mut solver_minimal = Solver::with_config(SolverConfig::minimal());

    // They should all solve a simple problem correctly
    let t = manager.mk_true();
    solver_fast.assert(t, &mut manager);
    solver_balanced.assert(t, &mut manager);
    solver_thorough.assert(t, &mut manager);
    solver_minimal.assert(t, &mut manager);

    assert_eq!(solver_fast.check(&mut manager), SolverResult::Sat);
    assert_eq!(solver_balanced.check(&mut manager), SolverResult::Sat);
    assert_eq!(solver_thorough.check(&mut manager), SolverResult::Sat);
    assert_eq!(solver_minimal.check(&mut manager), SolverResult::Sat);
}

#[test]
fn test_config_default_is_balanced() {
    let default = SolverConfig::default();
    let balanced = SolverConfig::balanced();

    // Default should be the same as balanced
    assert_eq!(
        default.enable_variable_elimination,
        balanced.enable_variable_elimination
    );
    assert_eq!(
        default.enable_clause_minimization,
        balanced.enable_clause_minimization
    );
    assert_eq!(
        default.enable_symmetry_breaking,
        balanced.enable_symmetry_breaking
    );
    assert_eq!(default.restart_strategy, balanced.restart_strategy);
    assert_eq!(default.certification_mode, CertificationMode::Uncertified);
    for config in [
        SolverConfig::default(),
        SolverConfig::fast(),
        SolverConfig::balanced(),
        SolverConfig::thorough(),
        SolverConfig::minimal(),
    ] {
        assert_eq!(
            config.certification_mode,
            CertificationMode::Uncertified,
            "certified mode is opt-in; presets must leave it off"
        );
    }
    assert_eq!(
        SolverConfig::default().certified().certification_mode,
        CertificationMode::Certified
    );
}

#[test]
fn test_theory_combination_arith_solver() {
    use nixie_theories::arithmetic::ArithSolver;
    use nixie_theories::{EqualityNotification, TheoryCombination};

    let mut arith = ArithSolver::lra();
    let mut manager = TermManager::new();

    // Create two arithmetic variables
    let x = manager.mk_var("x", manager.sorts.int_sort);
    let y = manager.mk_var("y", manager.sorts.int_sort);

    // Intern them in the arithmetic solver
    let _x_var = arith.intern(x);
    let _y_var = arith.intern(y);

    // Test notify_equality with relevant terms
    let eq_notification = EqualityNotification {
        lhs: x,
        rhs: y,
        reason: None,
    };

    let accepted = arith.notify_equality(eq_notification);
    assert!(
        accepted,
        "ArithSolver should accept equality notification for known terms"
    );

    // Test is_relevant
    assert!(
        arith.is_relevant(x),
        "x should be relevant to arithmetic solver"
    );
    assert!(
        arith.is_relevant(y),
        "y should be relevant to arithmetic solver"
    );

    // Test with unknown term
    let z = manager.mk_var("z", manager.sorts.int_sort);
    assert!(
        !arith.is_relevant(z),
        "z should not be relevant (not interned)"
    );

    // Test notify_equality with unknown terms
    let eq_unknown = EqualityNotification {
        lhs: x,
        rhs: z,
        reason: None,
    };
    let accepted_unknown = arith.notify_equality(eq_unknown);
    assert!(
        !accepted_unknown,
        "ArithSolver should reject equality with unknown term"
    );
}

#[test]
fn test_theory_combination_get_shared_equalities() {
    use nixie_theories::TheoryCombination;

    let arith = ArithSolver::lra();

    // Test get_shared_equalities
    let shared = arith.get_shared_equalities();
    assert!(
        shared.is_empty(),
        "ArithSolver should return empty shared equalities (placeholder)"
    );
}

#[test]
fn test_equality_notification_fields() {
    use nixie_theories::EqualityNotification;

    let mut manager = TermManager::new();
    let x = manager.mk_var("x", manager.sorts.int_sort);
    let y = manager.mk_var("y", manager.sorts.int_sort);

    // Test with reason
    let eq1 = EqualityNotification {
        lhs: x,
        rhs: y,
        reason: Some(x),
    };
    assert_eq!(eq1.lhs, x);
    assert_eq!(eq1.rhs, y);
    assert_eq!(eq1.reason, Some(x));

    // Test without reason
    let eq2 = EqualityNotification {
        lhs: x,
        rhs: y,
        reason: None,
    };
    assert_eq!(eq2.reason, None);

    // Test equality and cloning
    let eq3 = eq1;
    assert_eq!(eq3.lhs, eq1.lhs);
    assert_eq!(eq3.rhs, eq1.rhs);
}

#[test]
fn test_assert_many() {
    let mut solver = Solver::new();
    let mut manager = TermManager::new();

    let p = manager.mk_var("p", manager.sorts.bool_sort);
    let q = manager.mk_var("q", manager.sorts.bool_sort);
    let r = manager.mk_var("r", manager.sorts.bool_sort);

    // Assert multiple terms at once
    solver.assert_many(&[p, q, r], &mut manager);

    assert_eq!(solver.num_assertions(), 3);
    assert_eq!(solver.check(&mut manager), SolverResult::Sat);
}

#[test]
fn test_num_assertions_and_variables() {
    let mut solver = Solver::new();
    let mut manager = TermManager::new();

    assert_eq!(solver.num_assertions(), 0);
    assert!(!solver.has_assertions());

    let p = manager.mk_var("p", manager.sorts.bool_sort);
    let q = manager.mk_var("q", manager.sorts.bool_sort);

    solver.assert(p, &mut manager);
    assert_eq!(solver.num_assertions(), 1);
    assert!(solver.has_assertions());

    solver.assert(q, &mut manager);
    assert_eq!(solver.num_assertions(), 2);

    // Variables are created during encoding
    assert!(solver.num_variables() > 0);
}

#[test]
fn test_context_level() {
    let mut solver = Solver::new();

    assert_eq!(solver.context_level(), 0);

    solver.push();
    assert_eq!(solver.context_level(), 1);

    solver.push();
    assert_eq!(solver.context_level(), 2);

    solver.pop();
    assert_eq!(solver.context_level(), 1);

    solver.pop();
    assert_eq!(solver.context_level(), 0);
}

// ======== Quantifier Tests ========

#[test]
fn test_quantifier_basic_forall() {
    let mut solver = Solver::new();
    let mut manager = TermManager::new();
    let bool_sort = manager.sorts.bool_sort;

    // Create: forall x. P(x)
    // This asserts P holds for all x
    let x = manager.mk_var("x", bool_sort);
    let p_x = manager.mk_apply("P", [x], bool_sort);
    let forall = manager.mk_forall([("x", bool_sort)], p_x);

    solver.assert(forall, &mut manager);

    // The solver should handle the quantifier (may return sat, unknown, or use MBQI)
    let result = solver.check(&mut manager);
    // Quantifiers without ground terms typically return sat (trivially satisfied)
    assert!(
        result == SolverResult::Sat || result == SolverResult::Unknown,
        "Basic forall should not be unsat"
    );
}

#[test]
fn test_quantifier_basic_exists() {
    let mut solver = Solver::new();
    let mut manager = TermManager::new();
    let bool_sort = manager.sorts.bool_sort;

    // Create: exists x. P(x)
    let x = manager.mk_var("x", bool_sort);
    let p_x = manager.mk_apply("P", [x], bool_sort);
    let exists = manager.mk_exists([("x", bool_sort)], p_x);

    solver.assert(exists, &mut manager);

    let result = solver.check(&mut manager);
    assert!(
        result == SolverResult::Sat || result == SolverResult::Unknown,
        "Basic exists should not be unsat"
    );
}

#[test]
fn test_quantifier_with_ground_terms() {
    let mut solver = Solver::new();
    let mut manager = TermManager::new();
    let int_sort = manager.sorts.int_sort;
    let bool_sort = manager.sorts.bool_sort;

    // Create ground terms for instantiation
    let zero = manager.mk_int(0);
    let one = manager.mk_int(1);

    // P(0) = true and P(1) = true
    let p_0 = manager.mk_apply("P", [zero], bool_sort);
    let p_1 = manager.mk_apply("P", [one], bool_sort);
    solver.assert(p_0, &mut manager);
    solver.assert(p_1, &mut manager);

    // forall x. P(x) - should be satisfiable with the given ground terms
    let x = manager.mk_var("x", int_sort);
    let p_x = manager.mk_apply("P", [x], bool_sort);
    let forall = manager.mk_forall([("x", int_sort)], p_x);
    solver.assert(forall, &mut manager);

    let result = solver.check(&mut manager);
    // MBQI should find that P(0) and P(1) satisfy the quantifier
    assert!(
        result == SolverResult::Sat || result == SolverResult::Unknown,
        "Quantifier with matching ground terms should be satisfiable"
    );
}

#[test]
fn test_quantifier_instantiation() {
    let mut solver = Solver::new();
    let mut manager = TermManager::new();
    let int_sort = manager.sorts.int_sort;
    let bool_sort = manager.sorts.bool_sort;

    // Create a ground term
    let c = manager.mk_apply("c", [], int_sort);

    // Assert: forall x. f(x) > 0
    let x = manager.mk_var("x", int_sort);
    let f_x = manager.mk_apply("f", [x], int_sort);
    let zero = manager.mk_int(0);
    let f_x_gt_0 = manager.mk_gt(f_x, zero);
    let forall = manager.mk_forall([("x", int_sort)], f_x_gt_0);
    solver.assert(forall, &mut manager);

    // Assert: f(c) exists (provides instantiation candidate)
    let f_c = manager.mk_apply("f", [c], int_sort);
    let f_c_exists = manager.mk_apply("exists_f_c", [f_c], bool_sort);
    solver.assert(f_c_exists, &mut manager);

    let result = solver.check(&mut manager);
    // MBQI should instantiate the quantifier with c
    assert!(
        result == SolverResult::Sat || result == SolverResult::Unknown,
        "Quantifier instantiation test"
    );
}

#[test]
fn test_quantifier_mbqi_solver_integration() {
    use crate::mbqi::MBQIIntegration;

    let mut mbqi = MBQIIntegration::new();
    let mut manager = TermManager::new();
    let int_sort = manager.sorts.int_sort;

    // Create a universal quantifier
    let x = manager.mk_var("x", int_sort);
    let zero = manager.mk_int(0);
    let x_gt_0 = manager.mk_gt(x, zero);
    let forall = manager.mk_forall([("x", int_sort)], x_gt_0);

    // Add the quantifier to MBQI
    mbqi.add_quantifier(forall, &manager);

    // Add some candidate terms
    let one = manager.mk_int(1);
    let two = manager.mk_int(2);
    mbqi.add_candidate(one, int_sort);
    mbqi.add_candidate(two, int_sort);

    // Check that MBQI tracks the quantifier
    assert!(mbqi.is_enabled(), "MBQI should be enabled by default");
}

#[test]
fn test_quantifier_pattern_matching() {
    let mut solver = Solver::new();
    let mut manager = TermManager::new();
    let int_sort = manager.sorts.int_sort;

    // Create: forall x. (f(x) = g(x)) with pattern f(x)
    let x = manager.mk_var("x", int_sort);
    let f_x = manager.mk_apply("f", [x], int_sort);
    let g_x = manager.mk_apply("g", [x], int_sort);
    let body = manager.mk_eq(f_x, g_x);

    // Create pattern
    let pattern: smallvec::SmallVec<[_; 2]> = smallvec::smallvec![f_x];
    let patterns: smallvec::SmallVec<[_; 2]> = smallvec::smallvec![pattern];

    let forall = manager.mk_forall_with_patterns([("x", int_sort)], body, patterns);
    solver.assert(forall, &mut manager);

    // Add ground term f(c) to trigger pattern matching
    let c = manager.mk_apply("c", [], int_sort);
    let f_c = manager.mk_apply("f", [c], int_sort);
    let f_c_eq_c = manager.mk_eq(f_c, c);
    solver.assert(f_c_eq_c, &mut manager);

    let result = solver.check(&mut manager);
    assert!(
        result == SolverResult::Sat || result == SolverResult::Unknown,
        "Pattern matching should allow instantiation"
    );
}

#[test]
fn test_quantifier_multiple() {
    let mut solver = Solver::new();
    let mut manager = TermManager::new();
    let int_sort = manager.sorts.int_sort;

    // Create: forall x. forall y. x + y = y + x (commutativity)
    let x = manager.mk_var("x", int_sort);
    let y = manager.mk_var("y", int_sort);
    let x_plus_y = manager.mk_add([x, y]);
    let y_plus_x = manager.mk_add([y, x]);
    let commutative = manager.mk_eq(x_plus_y, y_plus_x);

    let inner_forall = manager.mk_forall([("y", int_sort)], commutative);
    let outer_forall = manager.mk_forall([("x", int_sort)], inner_forall);

    solver.assert(outer_forall, &mut manager);

    let result = solver.check(&mut manager);
    assert!(
        result == SolverResult::Sat || result == SolverResult::Unknown,
        "Nested forall should be handled"
    );
}

#[test]
fn test_quantifier_with_model() {
    let mut solver = Solver::new();
    let mut manager = TermManager::new();
    let bool_sort = manager.sorts.bool_sort;

    // Simple satisfiable formula with quantifier
    let p = manager.mk_var("p", bool_sort);
    solver.assert(p, &mut manager);

    // Add a trivial quantifier (x OR NOT x is always true)
    let x = manager.mk_var("x", bool_sort);
    let not_x = manager.mk_not(x);
    let x_or_not_x = manager.mk_or([x, not_x]);
    let tautology = manager.mk_forall([("x", bool_sort)], x_or_not_x);
    solver.assert(tautology, &mut manager);

    let result = solver.check(&mut manager);
    assert!(
        result == SolverResult::Sat || result == SolverResult::Unknown,
        "Tautology in quantifier should be SAT or Unknown (MBQI in progress)"
    );

    // Check that we can get a model if Sat
    if result == SolverResult::Sat
        && let Some(model) = solver.model()
    {
        assert!(model.size() > 0, "Model should have assignments");
    }
}

#[test]
fn test_quantifier_push_pop() {
    let mut solver = Solver::new();
    let mut manager = TermManager::new();
    let int_sort = manager.sorts.int_sort;

    // Assert base formula
    let x = manager.mk_var("x", int_sort);
    let zero = manager.mk_int(0);
    let x_gt_0 = manager.mk_gt(x, zero);
    let forall = manager.mk_forall([("x", int_sort)], x_gt_0);

    solver.push();
    solver.assert(forall, &mut manager);

    let result1 = solver.check(&mut manager);
    // forall x. x > 0 is invalid (counterexample: x = 0 or x = -1)
    // So the solver should return Unsat or Unknown
    assert!(
        result1 == SolverResult::Unsat || result1 == SolverResult::Unknown,
        "forall x. x > 0 should be Unsat or Unknown, got {:?}",
        result1
    );

    solver.pop();

    // After pop, the quantifier assertion should be gone
    let result2 = solver.check(&mut manager);
    assert_eq!(
        result2,
        SolverResult::Sat,
        "After pop, should be trivially SAT"
    );
}

/// Test that integer contradictions are correctly detected as UNSAT.
///
/// This tests that strict inequalities are properly handled for LIA (integers):
/// - x >= 0 AND x < 0 should be UNSAT
/// - For integers, x < 0 is equivalent to x <= -1
#[test]
fn test_integer_contradiction_unsat() {
    let mut solver = Solver::new();
    let mut manager = TermManager::new();

    // Create integer variable x
    let x = manager.mk_var("x", manager.sorts.int_sort);
    let zero = manager.mk_int(BigInt::from(0));

    // Assert x >= 0
    let x_ge_0 = manager.mk_ge(x, zero);
    solver.assert(x_ge_0, &mut manager);

    // Assert x < 0 (contradicts x >= 0)
    let x_lt_0 = manager.mk_lt(x, zero);
    solver.assert(x_lt_0, &mut manager);

    // Should be UNSAT because x cannot be both >= 0 and < 0
    let result = solver.check(&mut manager);
    assert_eq!(
        result,
        SolverResult::Unsat,
        "x >= 0 AND x < 0 should be UNSAT"
    );
}

/// Test the specific bug case: x > 5 AND x < 6 should be UNSAT for integers.
///
/// For integers, there is no value in the open interval (5, 6).
/// The fix transforms strict inequalities for LIA:
/// - x > 5 becomes x >= 6
/// - x < 6 becomes x <= 5
///
/// Together: x >= 6 AND x <= 5, which is impossible.
#[test]
fn test_lia_empty_interval_unsat() {
    let mut solver = Solver::new();
    let mut manager = TermManager::new();

    solver.set_logic("QF_LIA");

    // Create integer variable x
    let x = manager.mk_var("x", manager.sorts.int_sort);
    let five = manager.mk_int(BigInt::from(5));
    let six = manager.mk_int(BigInt::from(6));

    // Assert x > 5 (for integers, becomes x >= 6)
    let x_gt_5 = manager.mk_gt(x, five);
    solver.assert(x_gt_5, &mut manager);

    // Assert x < 6 (for integers, becomes x <= 5)
    let x_lt_6 = manager.mk_lt(x, six);
    solver.assert(x_lt_6, &mut manager);

    // Should be UNSAT: no integer in (5, 6)
    let result = solver.check(&mut manager);
    assert_eq!(
        result,
        SolverResult::Unsat,
        "x > 5 AND x < 6 should be UNSAT for integers (no integer in open interval)"
    );
}

#[test]
fn test_fp_constraint_data_not_empty() {
    use super::types::FpConstraintData;

    let mut data = FpConstraintData::new();
    data.equalities.push((TermId::new(1), TermId::new(2)));
    assert!(!data.is_empty());
}

// ========  ========

// Task 2: Model Cache Tests
// ========  ========

#[test]
fn test_model_cache_basic() {
    use super::types::ModelCache;

    let _manager = TermManager::new();
    let model = Model::new();
    let cache = ModelCache::new(model);

    assert_eq!(cache.cache_size(), 0);
    assert_eq!(cache.model_size(), 0);
}

#[test]
fn test_model_cache_lazy_eval() {
    use super::types::ModelCache;

    let mut manager = TermManager::new();
    let mut model = Model::new();

    let t = manager.mk_true();
    let p = manager.mk_var("p", manager.sorts.bool_sort);
    model.set(p, t);

    let mut cache = ModelCache::new(model);

    // First eval should miss cache
    let result = cache.eval_lazy(p, &mut manager);
    assert_eq!(result, t);
    assert_eq!(cache.cache_stats(), (0, 1)); // 0 hits, 1 miss

    // Second eval should hit cache
    let result2 = cache.eval_lazy(p, &mut manager);
    assert_eq!(result2, t);
    assert_eq!(cache.cache_stats(), (1, 1)); // 1 hit, 1 miss
}

#[test]
fn test_model_cache_invalidate() {
    use super::types::ModelCache;

    let mut manager = TermManager::new();
    let mut model = Model::new();

    let t = manager.mk_true();
    let p = manager.mk_var("p", manager.sorts.bool_sort);
    model.set(p, t);

    let mut cache = ModelCache::new(model);
    let _ = cache.eval_lazy(p, &mut manager);
    assert_eq!(cache.cache_size(), 1);

    cache.invalidate();
    assert_eq!(cache.cache_size(), 0);
}

#[test]
fn test_model_cache_is_cached() {
    use super::types::ModelCache;

    let mut manager = TermManager::new();
    let model = Model::new();
    let mut cache = ModelCache::new(model);

    let t = manager.mk_true();
    assert!(!cache.is_cached(t));

    let _ = cache.eval_lazy(t, &mut manager);
    assert!(cache.is_cached(t));
}

#[test]
fn test_model_cache_batch_eval() {
    use super::types::ModelCache;

    let mut manager = TermManager::new();
    let mut model = Model::new();

    let t = manager.mk_true();
    let f = manager.mk_false();
    let p = manager.mk_var("p", manager.sorts.bool_sort);
    let q = manager.mk_var("q", manager.sorts.bool_sort);
    model.set(p, t);
    model.set(q, f);

    let mut cache = ModelCache::new(model);
    let results = cache.eval_batch(&[p, q], &mut manager);
    assert_eq!(results.len(), 2);
    assert_eq!(results[0], t);
    assert_eq!(results[1], f);
}

// ========  ========

// Task 3: Parallel Theory Checking Tests
// (feature-gated - these test the data structures that support parallel checking)
// ========  ========

// Task 5: Lazy Evaluation Tests

// Task 1: Additional FP cache tests

#[test]
fn test_fp_constraint_cache_empty_on_new_solver() {
    let solver = Solver::new();
    assert!(solver.fp_constraint_cache.is_empty());
}

#[test]
fn test_fp_constraint_cache_cleared_on_assert() {
    let mut solver = Solver::new();
    let mut manager = TermManager::new();
    let t = manager.mk_true();
    solver.assert(t, &mut manager);
    assert!(solver.fp_constraint_cache.is_empty());
}

#[test]
fn test_fp_constraint_data_new_is_empty() {
    use super::types::FpConstraintData;
    let data = FpConstraintData::new();
    assert!(data.is_empty());
    assert!(data.equalities.is_empty());
    assert!(data.gt_comparisons.is_empty());
}

#[test]
fn test_fp_constraint_data_merge_combines() {
    use super::types::FpConstraintData;
    let mut data1 = FpConstraintData::new();
    let mut data2 = FpConstraintData::new();
    let t1 = TermId::new(10);
    let t2 = TermId::new(20);
    data1.equalities.push((t1, t2));
    data2.gt_comparisons.push((t1, t2));
    data1.merge(&data2);
    assert_eq!(data1.equalities.len(), 1);
    assert_eq!(data1.gt_comparisons.len(), 1);
}

#[test]
fn test_fp_constraint_data_literals_merge() {
    use super::types::FpConstraintData;
    let mut data1 = FpConstraintData::new();
    let mut data2 = FpConstraintData::new();
    data1.literals.insert(TermId::new(1), 1.0);
    data2.literals.insert(TermId::new(2), 2.0);
    data1.merge(&data2);
    assert_eq!(data1.literals.len(), 2);
}

// Task 2: Additional Model Cache tests

#[test]
fn test_model_cache_into_model() {
    use super::types::ModelCache;
    let model = Model::new();
    let cache = ModelCache::new(model);
    let _model_back = cache.into_model();
}

#[test]
fn test_model_cache_stats_initial() {
    use super::types::ModelCache;
    let model = Model::new();
    let cache = ModelCache::new(model);
    assert_eq!(cache.cache_stats(), (0, 0));
    assert_eq!(cache.cache_size(), 0);
}

// Task 3: Parallel theory tests

#[test]
fn test_parallel_theories_eq_diseq_contradiction() {
    let mut solver = Solver::new();
    let mut manager = TermManager::new();
    let x = manager.mk_var("x", manager.sorts.int_sort);
    let y = manager.mk_var("y", manager.sorts.int_sort);
    let eq = manager.mk_eq(x, y);
    let neq = manager.mk_not(eq);
    solver.assert(eq, &mut manager);
    solver.assert(neq, &mut manager);
    assert_eq!(solver.check(&mut manager), SolverResult::Unsat);
}

#[test]
fn test_parallel_theories_arith_bounds_unsat() {
    let mut solver = Solver::new();
    let mut manager = TermManager::new();
    let x = manager.mk_var("x", manager.sorts.int_sort);
    let five = manager.mk_int(5i64);
    let three = manager.mk_int(3i64);
    let ge5 = manager.mk_ge(x, five);
    let lt3 = manager.mk_lt(x, three);
    solver.assert(ge5, &mut manager);
    solver.assert(lt3, &mut manager);
    assert_eq!(solver.check(&mut manager), SolverResult::Unsat);
}

#[test]
fn test_parallel_theories_mixed_sat() {
    let mut solver = Solver::new();
    let mut manager = TermManager::new();
    let x = manager.mk_var("x", manager.sorts.int_sort);
    let five = manager.mk_int(5i64);
    let p = manager.mk_var("p", manager.sorts.bool_sort);
    let ge = manager.mk_ge(x, five);
    solver.assert(ge, &mut manager);
    solver.assert(p, &mut manager);
    assert_eq!(solver.check(&mut manager), SolverResult::Sat);
}

#[test]
fn test_parallel_theories_lazy_mode() {
    let mut solver = Solver::new();
    solver.config.theory_mode = TheoryMode::Lazy;
    let mut manager = TermManager::new();
    let t = manager.mk_true();
    solver.assert(t, &mut manager);
    assert_eq!(solver.check(&mut manager), SolverResult::Sat);
}

#[test]
fn test_parallel_theories_eager_mode() {
    let mut solver = Solver::new();
    solver.config.theory_mode = TheoryMode::Eager;
    let mut manager = TermManager::new();
    let t = manager.mk_true();
    solver.assert(t, &mut manager);
    assert_eq!(solver.check(&mut manager), SolverResult::Sat);
}

// Task 5: Lazy eval tests

#[test]
fn test_lazy_eval_and_simplification() {
    let mut solver = Solver::new();
    let mut manager = TermManager::new();
    let t = manager.mk_true();
    let p = manager.mk_var("p", manager.sorts.bool_sort);
    let and = manager.mk_and(vec![t, p]);
    solver.assert(and, &mut manager);
    assert_eq!(solver.check(&mut manager), SolverResult::Sat);
}

#[test]
fn test_lazy_eval_or_with_false() {
    let mut solver = Solver::new();
    let mut manager = TermManager::new();
    let f = manager.mk_false();
    let p = manager.mk_var("p", manager.sorts.bool_sort);
    let or = manager.mk_or(vec![f, p]);
    solver.assert(or, &mut manager);
    assert_eq!(solver.check(&mut manager), SolverResult::Sat);
}

#[test]
fn test_lazy_eval_ite_true_branch() {
    let mut solver = Solver::new();
    let mut manager = TermManager::new();
    let t = manager.mk_true();
    let x = manager.mk_var("x", manager.sorts.bool_sort);
    let y = manager.mk_var("y", manager.sorts.bool_sort);
    let ite = manager.mk_ite(t, x, y);
    solver.assert(ite, &mut manager);
    assert_eq!(solver.check(&mut manager), SolverResult::Sat);
}

#[test]
fn test_lazy_eval_double_negation() {
    let mut solver = Solver::new();
    let mut manager = TermManager::new();
    let p = manager.mk_var("p", manager.sorts.bool_sort);
    let not_p = manager.mk_not(p);
    let not_not_p = manager.mk_not(not_p);
    solver.assert(not_not_p, &mut manager);
    assert_eq!(solver.check(&mut manager), SolverResult::Sat);
}

#[test]
fn test_lazy_eval_eq_reflexive() {
    let mut solver = Solver::new();
    let mut manager = TermManager::new();
    let x = manager.mk_var("x", manager.sorts.int_sort);
    let eq = manager.mk_eq(x, x);
    solver.assert(eq, &mut manager);
    assert_eq!(solver.check(&mut manager), SolverResult::Sat);
}

// ========  ========
// Regression: GitHub issue #12 – `distinct` / `not (= t 0)` over Int/Real must
// reach the arithmetic theory, and the reported model must actually satisfy it.
//
// Two independent defects produced the wrong `Sat` with `x = 0`:
//   1. `Distinct` never generated the arithmetic ordering split, so the
//      disequality was invisible to `ArithSolver`; and
//   2. the LRA model read back only the real part of the delta-rational
//      assignment, reporting a variable pinned at a strict bound *on* the bound.
// ========  ========

/// Read the Int value a model assigns to `term`, failing the test if the model
/// has no concrete integer for it.
fn model_int_value(solver: &Solver, term: TermId, manager: &TermManager) -> i64 {
    let model = solver
        .model()
        .expect("solver must expose a model after Sat");
    let value_term = model.get(term).expect("model must assign the term");
    let kind = &manager
        .get(value_term)
        .expect("model value must be a valid term")
        .kind;
    match kind {
        TermKind::IntConst(n) => n.to_i64().expect("model value must fit in i64"),
        other => panic!("expected IntConst in model, got {other:?}"),
    }
}

#[test]
fn test_issue_12_distinct_int_disequality() {
    let mut solver = Solver::new();
    let mut manager = TermManager::new();

    let x = manager.mk_var("x", manager.sorts.int_sort);
    let zero = manager.mk_int(0u32);

    // x >= 0 and x != 0, so x must be >= 1.
    let ge = manager.mk_ge(x, zero);
    solver.assert(ge, &mut manager);
    let distinct = manager.mk_distinct([x, zero]);
    solver.assert(distinct, &mut manager);

    assert_eq!(solver.check(&mut manager), SolverResult::Sat);
    let value = model_int_value(&solver, x, &manager);
    assert!(
        value >= 1,
        "model x = {value} violates (>= x 0) and (distinct x 0)"
    );
}

#[test]
fn test_issue_12_not_eq_int() {
    let mut solver = Solver::new();
    let mut manager = TermManager::new();

    let x = manager.mk_var("x", manager.sorts.int_sort);
    let zero = manager.mk_int(0u32);

    let ge = manager.mk_ge(x, zero);
    solver.assert(ge, &mut manager);
    let eq = manager.mk_eq(x, zero);
    let ne = manager.mk_not(eq);
    solver.assert(ne, &mut manager);

    assert_eq!(solver.check(&mut manager), SolverResult::Sat);
    let value = model_int_value(&solver, x, &manager);
    assert!(
        value >= 1,
        "model x = {value} violates (>= x 0) and (not (= x 0))"
    );
}

#[test]
fn test_issue_12_distinct_sum() {
    let mut solver = Solver::new();
    let mut manager = TermManager::new();

    let x = manager.mk_var("x", manager.sorts.int_sort);
    let y = manager.mk_var("y", manager.sorts.int_sort);
    let zero = manager.mk_int(0u32);

    let ge_x = manager.mk_ge(x, zero);
    solver.assert(ge_x, &mut manager);
    let ge_y = manager.mk_ge(y, zero);
    solver.assert(ge_y, &mut manager);
    let sum = manager.mk_add(vec![x, y]);
    let distinct = manager.mk_distinct([sum, zero]);
    solver.assert(distinct, &mut manager);

    assert_eq!(solver.check(&mut manager), SolverResult::Sat);
    let vx = model_int_value(&solver, x, &manager);
    let vy = model_int_value(&solver, y, &manager);
    assert!(
        vx >= 0 && vy >= 0,
        "model x = {vx}, y = {vy} violates the lower bounds"
    );
    assert_ne!(
        vx + vy,
        0,
        "model x = {vx}, y = {vy} violates (distinct (+ x y) 0)"
    );
}

/// The disequality must be strong enough to refute an over-constrained system:
/// `x >= 0 && x <= 0 && distinct(x, 0)` has no model.
#[test]
fn test_issue_12_distinct_pinned_value_is_unsat() {
    let mut solver = Solver::new();
    let mut manager = TermManager::new();

    let x = manager.mk_var("x", manager.sorts.int_sort);
    let zero = manager.mk_int(0u32);

    let ge = manager.mk_ge(x, zero);
    solver.assert(ge, &mut manager);
    let le = manager.mk_le(x, zero);
    solver.assert(le, &mut manager);
    let distinct = manager.mk_distinct([x, zero]);
    solver.assert(distinct, &mut manager);

    assert_eq!(solver.check(&mut manager), SolverResult::Unsat);
}

/// The ordering split must stay *guarded* by the equality atom: a disequality
/// nested under a disjunction may be discharged through the other disjunct, so
/// it must not force `x != 0` unconditionally.
#[test]
fn test_issue_12_diseq_under_disjunction_stays_sat() {
    for use_distinct in [false, true] {
        let mut solver = Solver::new();
        let mut manager = TermManager::new();

        let x = manager.mk_var("x", manager.sorts.int_sort);
        let p = manager.mk_var("p", manager.sorts.bool_sort);
        let zero = manager.mk_int(0u32);

        let ge = manager.mk_ge(x, zero);
        solver.assert(ge, &mut manager);
        let le = manager.mk_le(x, zero);
        solver.assert(le, &mut manager);

        let diseq = if use_distinct {
            manager.mk_distinct([x, zero])
        } else {
            let eq = manager.mk_eq(x, zero);
            manager.mk_not(eq)
        };
        let disjunction = manager.mk_or(vec![p, diseq]);
        solver.assert(disjunction, &mut manager);

        assert_eq!(
            solver.check(&mut manager),
            SolverResult::Sat,
            "satisfiable via p (use_distinct = {use_distinct})"
        );
    }
}

/// A strict bound must be witnessed strictly inside itself: `x > 0` may not be
/// reported as `x = 0` (the delta-rational assignment needs instantiation).
#[test]
fn test_issue_12_strict_lower_bound_model() {
    let mut solver = Solver::new();
    let mut manager = TermManager::new();

    let x = manager.mk_var("x", manager.sorts.int_sort);
    let zero = manager.mk_int(0u32);

    let ge = manager.mk_ge(x, zero);
    solver.assert(ge, &mut manager);
    let gt = manager.mk_gt(x, zero);
    solver.assert(gt, &mut manager);

    assert_eq!(solver.check(&mut manager), SolverResult::Sat);
    let value = model_int_value(&solver, x, &manager);
    assert!(value >= 1, "model x = {value} violates (> x 0)");
}

// Incremental scope restoration: every fact derived from an assertion must be
// undone by the matching `pop`.  State that survives keeps a retracted
// assertion alive and produces a wrong verdict for whatever is asserted next.

/// `(= v A)` inside a scope pinned `v` to constructor `A` in
/// `dt_var_constructors` with no undo, so the `(= v B)` asserted after the
/// `pop` looked mutually exclusive with a retracted fact: `sat` then `unsat`
/// where z3 answers `sat` twice.
#[test]
fn test_dt_constructor_state_restored_on_pop() {
    let mut solver = Solver::new();
    let mut manager = TermManager::new();

    let c_sort = manager.sorts.mk_datatype_sort("C");
    let v = manager.mk_var("v", c_sort);
    let ctor_a = manager.mk_dt_constructor("a", [], c_sort);
    let ctor_b = manager.mk_dt_constructor("b", [], c_sort);
    solver.push();
    let v_is_a = manager.mk_eq(v, ctor_a);
    solver.assert(v_is_a, &mut manager);
    assert_eq!(solver.check(&mut manager), SolverResult::Sat);
    solver.pop();

    assert!(
        solver.dt_var_constructors.is_empty(),
        "constructor pinned inside the popped scope outlived it"
    );
    let v_is_b = manager.mk_eq(v, ctor_b);
    solver.assert(v_is_b, &mut manager);
    assert_eq!(
        solver.check(&mut manager),
        SolverResult::Sat,
        "(= v b) alone is satisfiable once (= v a) has been popped"
    );
}

/// Control for the fix above: without a `pop`, two different constructors for
/// the same variable must still be detected as mutually exclusive.
#[test]
fn test_dt_constructor_conflict_detected_without_pop() {
    let mut solver = Solver::new();
    let mut manager = TermManager::new();

    let c_sort = manager.sorts.mk_datatype_sort("C");
    let v = manager.mk_var("v", c_sort);
    let ctor_a = manager.mk_dt_constructor("a", [], c_sort);
    let ctor_b = manager.mk_dt_constructor("b", [], c_sort);
    let v_is_a = manager.mk_eq(v, ctor_a);
    solver.assert(v_is_a, &mut manager);
    let v_is_b = manager.mk_eq(v, ctor_b);
    solver.assert(v_is_b, &mut manager);
    assert_eq!(solver.check(&mut manager), SolverResult::Unsat);
}

/// A quantifier asserted inside a scope stayed registered with MBQI and the
/// e-matching engine, and the ground lemmas its instantiation committed to the
/// theory solvers were never retracted either: `f(k) = 2` after the `pop`
/// contradicted the retracted `forall x. f(x) = 1` and answered `unsat`.
#[test]
fn test_mbqi_state_restored_on_pop() {
    let mut solver = Solver::new();
    let mut manager = TermManager::new();
    let int_sort = manager.sorts.int_sort;

    let k = manager.mk_var("k", int_sort);
    let seven = manager.mk_int(7);
    let k_is_7 = manager.mk_eq(k, seven);
    solver.assert(k_is_7, &mut manager);
    solver.push();
    let x = manager.mk_var("x", int_sort);
    let f_x = manager.mk_apply("f", [x], int_sort);
    let one = manager.mk_int(1);
    let body = manager.mk_eq(f_x, one);
    let forall = manager.mk_forall([("x", int_sort)], body);
    solver.assert(forall, &mut manager);
    let _ = solver.check(&mut manager);
    solver.pop();

    assert_eq!(
        solver.mbqi.num_quantifiers(),
        0,
        "MBQI kept a popped forall"
    );
    let ematch_quantifiers = solver.ematch_engine.num_quantifiers();
    assert_eq!(ematch_quantifiers, 0, "e-matching kept a popped forall");
    assert!(!solver.has_quantifiers, "has_quantifiers survived the pop");
    let f_k = manager.mk_apply("f", [k], int_sort);
    let two = manager.mk_int(2);
    let f_k_is_2 = manager.mk_eq(f_k, two);
    solver.assert(f_k_is_2, &mut manager);
    assert_ne!(
        solver.check(&mut manager),
        SolverResult::Unsat,
        "(= (f k) 2) is satisfiable once the forall has been popped"
    );
}

/// Control for the fix above: while the quantifier is still asserted, its
/// instantiation must keep refuting the contradicting ground equality.
#[test]
fn test_mbqi_quantifier_active_without_pop() {
    let mut solver = Solver::new();
    let mut manager = TermManager::new();
    let int_sort = manager.sorts.int_sort;

    let k = manager.mk_var("k", int_sort);
    let seven = manager.mk_int(7);
    let k_is_7 = manager.mk_eq(k, seven);
    solver.assert(k_is_7, &mut manager);
    let x = manager.mk_var("x", int_sort);
    let f_x = manager.mk_apply("f", [x], int_sort);
    let one = manager.mk_int(1);
    let body = manager.mk_eq(f_x, one);
    let forall = manager.mk_forall([("x", int_sort)], body);
    solver.assert(forall, &mut manager);
    let f_k = manager.mk_apply("f", [k], int_sort);
    let two = manager.mk_int(2);
    let f_k_is_2 = manager.mk_eq(f_k, two);
    solver.assert(f_k_is_2, &mut manager);
    assert_eq!(solver.check(&mut manager), SolverResult::Unsat);
}

/// `tracked_compound_terms` memoises which compound terms `track_theory_vars`
/// already walked, but that walk's registrations (`arith_terms`, `bv_terms`)
/// are trail-undone.  Keeping the memo across a `pop` made the re-asserted
/// `(> (+ x y) 5)` skip the walk, so `x` and `y` were never re-interned and the
/// model came back without values for them.
#[test]
fn test_theory_var_tracking_restored_on_pop() {
    let mut solver = Solver::new();
    let mut manager = TermManager::new();
    let int_sort = manager.sorts.int_sort;

    let x = manager.mk_var("x", int_sort);
    let y = manager.mk_var("y", int_sort);
    let sum = manager.mk_add(vec![x, y]);
    let five = manager.mk_int(5);
    let sum_gt_5 = manager.mk_gt(sum, five);
    solver.push();
    solver.assert(sum_gt_5, &mut manager);
    assert_eq!(solver.check(&mut manager), SolverResult::Sat);
    solver.pop();

    assert!(
        solver.tracked_compound_terms.is_empty(),
        "traversal memo outlived the registrations it memoised"
    );
    assert!(
        solver.arith_terms.is_empty(),
        "arith terms outlived the pop"
    );
    solver.assert(sum_gt_5, &mut manager);
    assert_eq!(solver.check(&mut manager), SolverResult::Sat);
    let model = solver.model().expect("sat must produce a model");
    assert!(
        model.get(x).is_some() && model.get(y).is_some(),
        "re-asserted arithmetic variables must be tracked again after a pop"
    );
}

/// Every sticky flag and dedup table the encoder fills while processing an
/// assertion must be back to its push-time value afterwards.  A stale
/// `array_axiom_instances` entry, for instance, suppresses a lemma whose clause
/// the SAT core dropped with the scope.
#[test]
fn test_scope_derived_tables_restored_on_pop() {
    let mut solver = Solver::new();
    let mut manager = TermManager::new();
    let int_sort = manager.sorts.int_sort;
    let bv8 = manager.sorts.bitvec(8);
    let arr_sort = manager.sorts.array(int_sort, int_sort);
    solver.push();
    let a = manager.mk_var("a", arr_sort);
    let idx = manager.mk_int(0);
    let sel = manager.mk_select(a, idx);
    let three = manager.mk_int(3);
    let sel_gt_3 = manager.mk_gt(sel, three);
    solver.assert(sel_gt_3, &mut manager);
    let b = manager.mk_var("b", bv8);
    let c = manager.mk_var("c", bv8);
    let quot = manager.mk_bv_udiv(b, c);
    let bv_three = manager.mk_bitvec(3i64, 8);
    let quot_eq = manager.mk_eq(quot, bv_three);
    solver.assert(quot_eq, &mut manager);
    let x = manager.mk_var("x", int_sort);
    let zero = manager.mk_int(0);
    let x_ge_0 = manager.mk_ge(x, zero);
    solver.assert(x_ge_0, &mut manager);
    let _ = solver.check(&mut manager);
    solver.pop();

    assert!(!solver.has_array_ops, "has_array_ops survived the pop");
    assert!(!solver.has_bv_arith_ops, "has_bv_arith_ops survived");
    assert!(!solver.encode_depth_exceeded, "depth flag survived the pop");
    assert!(
        solver.array_axiom_instances.is_empty(),
        "array axiom dedup entries outlived the lemmas they guard"
    );
    assert!(
        solver.var_to_parsed_arith.is_empty(),
        "parsed arithmetic constraints outlived the pop"
    );
    assert!(
        solver.var_to_constraint.is_empty(),
        "theory constraints outlived the pop"
    );
    assert!(solver.bv_terms.is_empty(), "bv terms outlived the pop");
    assert!(solver.assertions.is_empty(), "assertions outlived the pop");
}

/// Deterministic 64-bit LCG: the differential test below must be reproducible
/// and free of any wall-clock or thread-scheduling input.
struct Lcg(u64);

impl Lcg {
    fn below(&mut self, n: u64) -> usize {
        self.0 = self
            .0
            .wrapping_mul(6_364_136_223_846_793_005)
            .wrapping_add(1_442_695_040_888_963_407);
        ((self.0 >> 33) % n) as usize
    }
}

/// Build one random linear-arithmetic / Boolean atom over `vars`.
fn random_atom(rng: &mut Lcg, vars: &[TermId], manager: &mut TermManager) -> TermId {
    let lhs = vars[rng.below(vars.len() as u64)];
    let rhs = if rng.below(2) == 0 {
        vars[rng.below(vars.len() as u64)]
    } else {
        manager.mk_int(rng.below(4) as i64)
    };
    let atom = match rng.below(5) {
        0 => manager.mk_eq(lhs, rhs),
        1 => manager.mk_lt(lhs, rhs),
        2 => manager.mk_le(lhs, rhs),
        3 => manager.mk_gt(lhs, rhs),
        _ => manager.mk_ge(lhs, rhs),
    };
    if rng.below(4) == 0 {
        manager.mk_not(atom)
    } else {
        atom
    }
}

/// Build a small random formula (an atom, or a binary and/or of two atoms).
fn random_formula(rng: &mut Lcg, vars: &[TermId], manager: &mut TermManager) -> TermId {
    let first = random_atom(rng, vars, manager);
    match rng.below(3) {
        0 => {
            let second = random_atom(rng, vars, manager);
            manager.mk_and(vec![first, second])
        }
        1 => {
            let second = random_atom(rng, vars, manager);
            manager.mk_or(vec![first, second])
        }
        _ => first,
    }
}

/// Randomised differential check on `push`/`pop`: solving a formula must give
/// the same answer whether or not an unrelated scope was pushed, checked and
/// popped beforehand.  Any state the popped scope leaves behind shows up as a
/// disagreement.  Fixed seed, no wall-clock input, so failures reproduce.
#[test]
fn test_random_push_pop_differential() {
    let mut rng = Lcg(0x0BAD_C0DE_1234_5678);

    for case in 0..64u32 {
        let mut manager = TermManager::new();
        let int_sort = manager.sorts.int_sort;
        let vars: Vec<TermId> = ["p", "q", "r"]
            .iter()
            .map(|n| manager.mk_var(n, int_sort))
            .collect();

        let prefix = random_formula(&mut rng, &vars, &mut manager);
        let distractor = random_formula(&mut rng, &vars, &mut manager);
        let main = random_formula(&mut rng, &vars, &mut manager);

        let mut plain = Solver::new();
        plain.assert(prefix, &mut manager);
        plain.assert(main, &mut manager);
        let expected = plain.check(&mut manager);

        let mut scoped = Solver::new();
        scoped.assert(prefix, &mut manager);
        scoped.push();
        scoped.assert(distractor, &mut manager);
        let _ = scoped.check(&mut manager);
        scoped.pop();
        scoped.assert(main, &mut manager);
        let actual = scoped.check(&mut manager);

        assert_eq!(
            expected, actual,
            "case {case}: a pushed-and-popped scope changed the verdict"
        );
    }
}

/// The structural assertion encoder (`emit_assertion_clauses`) flattens the
/// top-level Boolean skeleton of an assertion into clauses without auxiliary
/// Tseitin variables.  These tests pin its semantics against the previous
/// Tseitin-rooted shape: every combination of and/or/not/implies/true/false at
/// an assertion root must yield exactly the same verdict, including roots that
/// mix a flattenable skeleton with subformulas that still need encoding.
#[test]
fn structural_assertion_encoding_verdicts() {
    /// Builder for one structural-encoding test case.
    type CaseBuilder = Box<dyn Fn(&mut TermManager) -> TermId>;
    let cases: Vec<(&str, CaseBuilder, SolverResult)> = vec![
        (
            "and of complementary literals",
            Box::new(|m| {
                let a = m.mk_var("a", m.sorts.bool_sort);
                let na = m.mk_not(a);
                m.mk_and([a, na])
            }),
            SolverResult::Unsat,
        ),
        (
            "or of a literal with its negation",
            Box::new(|m| {
                let a = m.mk_var("a", m.sorts.bool_sort);
                let na = m.mk_not(a);
                m.mk_or([a, na])
            }),
            SolverResult::Sat,
        ),
        (
            "negated conjunction = clause",
            Box::new(|m| {
                let a = m.mk_var("a", m.sorts.bool_sort);
                let b = m.mk_var("b", m.sorts.bool_sort);
                let c = m.mk_var("c", m.sorts.bool_sort);
                // ¬(a ∧ b ∧ c) plus a, b, c themselves: unsat.
                let and = m.mk_and([a, b, c]);
                let nand = m.mk_not(and);
                m.mk_and([nand, a, b, c])
            }),
            SolverResult::Unsat,
        ),
        (
            "nested or flattens into one clause",
            Box::new(|m| {
                let a = m.mk_var("a", m.sorts.bool_sort);
                let b = m.mk_var("b", m.sorts.bool_sort);
                let c = m.mk_var("c", m.sorts.bool_sort);
                // (a ∨ ((b ∨ c))) with all three forced false.
                let inner = m.mk_or([b, c]);
                let na = m.mk_not(a);
                let nb = m.mk_not(b);
                let nc = m.mk_not(c);
                let outer = m.mk_or([a, inner]);
                m.mk_and([na, nb, nc, outer])
            }),
            SolverResult::Unsat,
        ),
        (
            "implies at the root",
            Box::new(|m| {
                let a = m.mk_var("a", m.sorts.bool_sort);
                let b = m.mk_var("b", m.sorts.bool_sort);
                // (a → b) ∧ a ∧ ¬b.
                let imp = m.mk_implies(a, b);
                let nb = m.mk_not(b);
                m.mk_and([imp, a, nb])
            }),
            SolverResult::Unsat,
        ),
        (
            "negated implies splits",
            Box::new(|m| {
                let a = m.mk_var("a", m.sorts.bool_sort);
                let b = m.mk_var("b", m.sorts.bool_sort);
                // ¬(a → b) = a ∧ ¬b, plus b: unsat.
                let impl_term = m.mk_implies(a, b);
                let nimpl = m.mk_not(impl_term);
                m.mk_and([nimpl, b])
            }),
            SolverResult::Unsat,
        ),
        (
            "true absorbs, false refutes",
            Box::new(|m| {
                let a = m.mk_var("a", m.sorts.bool_sort);
                let t = m.mk_true();
                let or_a_f = m.mk_or([a, m.mk_false()]);
                m.mk_and([t, a, or_a_f])
            }),
            SolverResult::Sat,
        ),
        (
            "not(true) at the root refutes",
            Box::new(|m| m.mk_not(m.mk_true())),
            SolverResult::Unsat,
        ),
        (
            "deeply nested and/or skeleton over an unsat core",
            Box::new(|m| {
                let xs: Vec<_> = (0..4)
                    .map(|i| m.mk_var(&format!("x{i}"), m.sorts.bool_sort))
                    .collect();
                // Every pairwise implication (xi → xj) plus x0 ∧ ¬x3.
                let mut conj: Vec<TermId> = Vec::new();
                for i in 0..4 {
                    for j in 0..4 {
                        if i < j {
                            conj.push(m.mk_implies(xs[i], xs[j]));
                        }
                    }
                }
                let nx3 = m.mk_not(xs[3]);
                conj.push(xs[0]);
                conj.push(nx3);
                m.mk_and(conj)
            }),
            SolverResult::Unsat,
        ),
    ];

    for (name, build, expected) in cases {
        let mut solver = Solver::new();
        let mut manager = TermManager::new();
        let t = build(&mut manager);
        solver.assert(t, &mut manager);
        let got = solver.check(&mut manager);
        assert_eq!(got, expected, "case `{name}`");
    }
}

/// The structural encoder must not mint an auxiliary variable for the
/// assertion root itself: the top-level skeleton is pure clause structure.
/// (Regression guard for the QF_UF quasigroup search-quality fix – the
/// Tseitin-encoded skeleton carried ~5× the Boolean variables of the atoms.)
#[test]
fn structural_assertion_encoding_mints_no_root_variable() {
    let mut solver = Solver::new();
    let mut manager = TermManager::new();
    let a = manager.mk_var("a", manager.sorts.bool_sort);
    let b = manager.mk_var("b", manager.sorts.bool_sort);
    let na = manager.mk_not(a);
    let nb = manager.mk_not(b);
    let or = manager.mk_or([a, b]);
    let root = manager.mk_and([or, na, nb]);
    solver.assert(root, &mut manager);
    // Only the two atom variables exist: the `or` and the `and` roots were
    // emitted structurally.
    assert_eq!(solver.sat.num_vars(), 2, "atom vars only, no Tseitin roots");
    assert_eq!(solver.check(&mut manager), SolverResult::Unsat);
}

/// A theory-equality atom inside the flattened skeleton keeps its theory
/// constraint (the watch-based propagation and EUF conflict paths depend on
/// `Constraint::Eq` being recorded for it).
#[test]
fn structural_assertion_keeps_theory_atoms_in_skeleton() {
    let mut solver = Solver::new();
    let mut manager = TermManager::new();
    let sort = manager.sorts.int_sort;
    let x = manager.mk_var("x", sort);
    let y = manager.mk_var("y", sort);
    let x_eq_y = manager.mk_eq(x, y);
    // (x = y ∧ ¬(x = y)) asserted as a conjunction: unsat, and the equality
    // atom inside the skeleton must still be a theory atom.
    let nx_eq_y = manager.mk_not(x_eq_y);
    let root = manager.mk_and([x_eq_y, nx_eq_y]);
    solver.assert(root, &mut manager);
    assert_eq!(solver.check(&mut manager), SolverResult::Unsat);
}

#[test]
fn set_config_propagates_search_fields_into_live_sat_engine() {
    // Regression for the portfolio wiring gap: `restart_strategy` (and the
    // inprocessing toggles) were stored on the SMT solver's config but never
    // consumed, because the SAT engine is built once at construction and
    // nothing pushed the new values in. `set_config` now propagates the
    // three live-consumed fields; the next solve's search must reflect them.
    use nixie_sat::RestartStrategy as SatRestart;
    let solver = Solver::with_config(crate::solver::SolverConfig {
        restart_strategy: crate::solver::RestartStrategy::Luby,
        ..Default::default()
    });
    assert_eq!(solver.sat.config().restart_strategy, SatRestart::Luby);

    let mut solver = solver;
    solver.set_config(crate::solver::SolverConfig {
        restart_strategy: crate::solver::RestartStrategy::Geometric,
        enable_inprocessing: true,
        inprocessing_interval: 1234,
        ..Default::default()
    });
    assert_eq!(
        solver.sat.config().restart_strategy,
        SatRestart::Geometric,
        "restart_strategy must reach the already-built SAT engine"
    );
    assert!(solver.sat.config().enable_inprocessing);
    assert_eq!(solver.sat.config().inprocessing_interval, 1234);
}
