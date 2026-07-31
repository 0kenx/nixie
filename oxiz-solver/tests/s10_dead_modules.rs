//! Integration coverage for the two modules that were physically present in
//! `oxiz-solver/src` but never declared in `lib.rs`, and therefore never
//! compiled: `debug/` (state visualization, event tracing, conflict
//! explanation, model minimization) and `invariants` (structural self-checks).
//!
//! These tests exercise them through the crate's *public* surface, which is
//! the point: before this file existed there was no build configuration in
//! which a single line of either module was type-checked.

use num_bigint::BigInt;
use oxiz_core::ast::TermManager;
use oxiz_solver::debug::{
    ActiveConflict, ConflictExplainer, DebugModelMinimizer, ModelAssignment, SolverStateSnapshot,
    SolverTracer, StatsSnapshot, TheoryConflictInfo, TraceEvent, TrailDecision, VarAssignment,
};
use oxiz_solver::invariants::check_all_invariants;
use oxiz_solver::{Solver, SolverResult};

#[test]
fn invariants_hold_across_a_mixed_theory_session() {
    let mut solver = Solver::new();
    let mut tm = TermManager::new();
    solver.set_logic("QF_LIA");

    let x = tm.mk_var("x", tm.sorts.int_sort);
    let y = tm.mk_var("y", tm.sorts.int_sort);
    let p = tm.mk_var("p", tm.sorts.bool_sort);

    let zero = tm.mk_int(BigInt::from(0));
    let ten = tm.mk_int(BigInt::from(10));

    let x_ge_zero = tm.mk_ge(x, zero);
    let x_le_ten = tm.mk_le(x, ten);
    let y_gt_x = tm.mk_gt(y, x);
    let guard = tm.mk_or(vec![p, y_gt_x]);

    solver.assert(x_ge_zero, &mut tm);
    assert_eq!(check_all_invariants(&solver), Ok(()));

    solver.assert(x_le_ten, &mut tm);
    solver.assert(guard, &mut tm);
    assert_eq!(solver.check(&mut tm), SolverResult::Sat);
    assert_eq!(check_all_invariants(&solver), Ok(()));

    solver.push();
    let not_p = tm.mk_not(p);
    solver.assert(not_p, &mut tm);
    assert_eq!(solver.check(&mut tm), SolverResult::Sat);
    assert_eq!(check_all_invariants(&solver), Ok(()));

    solver.pop();
    assert_eq!(check_all_invariants(&solver), Ok(()));
    assert_eq!(solver.check(&mut tm), SolverResult::Sat);
    assert_eq!(check_all_invariants(&solver), Ok(()));
}

#[test]
fn invariants_hold_after_an_unsat_result_with_cores() {
    let mut solver = Solver::new();
    solver.set_produce_unsat_cores(true);
    let mut tm = TermManager::new();
    solver.set_logic("QF_LIA");

    let x = tm.mk_var("x", tm.sorts.int_sort);
    let one = tm.mk_int(BigInt::from(1));
    let two = tm.mk_int(BigInt::from(2));
    let x_eq_one = tm.mk_eq(x, one);
    let x_eq_two = tm.mk_eq(x, two);

    solver.assert(x_eq_one, &mut tm);
    solver.assert(x_eq_two, &mut tm);

    assert_eq!(solver.check(&mut tm), SolverResult::Unsat);
    assert_eq!(check_all_invariants(&solver), Ok(()));
}

#[test]
fn debug_snapshot_renders_text_and_dot() {
    let mut snap = SolverStateSnapshot::new("integration");
    snap.set_statistics(StatsSnapshot {
        decisions: 4,
        conflicts: 1,
        propagations: 9,
        restarts: 0,
        learned_clauses: 1,
        theory_propagations: 2,
        theory_conflicts: 1,
    });
    snap.add_assignment(VarAssignment {
        var_id: 1,
        name: "x".to_string(),
        bool_value: None,
        theory_value: Some("7".to_string()),
        decision_level: 1,
    });
    snap.add_trail_entry(TrailDecision {
        var_id: 1,
        value: true,
        level: 0,
        is_propagation: false,
        reason_clause: None,
    });
    snap.add_trail_entry(TrailDecision {
        var_id: 2,
        value: false,
        level: 1,
        is_propagation: true,
        reason_clause: Some(3),
    });
    snap.add_conflict(ActiveConflict {
        clause_id: 3,
        literals: vec![1, -2],
        description: "LRA bound conflict".to_string(),
    });

    let text = snap.format_state_text();
    assert!(text.contains("Solver State: integration"));
    assert!(text.contains("theory=7"));
    assert!(text.contains("LRA bound conflict"));

    let dot = snap.format_state_dot();
    assert!(dot.starts_with("digraph solver_state {"));
    assert!(dot.trim_end().ends_with('}'));
    assert!(dot.contains("shape=octagon"));
}

#[test]
fn debug_tracer_emits_balanced_json() {
    let mut tracer = SolverTracer::with_defaults();
    tracer.record(TraceEvent::AssertionAdded {
        index: 0,
        description: "(> x \"0\")".to_string(),
    });
    tracer.record(TraceEvent::Decision {
        var: 1,
        value: true,
        level: 0,
    });
    tracer.record(TraceEvent::Conflict {
        conflicting_clause: 2,
        learned_clause: Some(4),
        learned_size: Some(2),
    });

    let json = tracer.write_trace_json();
    assert_eq!(json.matches('{').count(), json.matches('}').count());
    // The quote inside the description must be escaped, not emitted raw.
    assert!(json.contains(r#"(> x \"0\")"#), "{json}");
    assert_eq!(tracer.count_events_of_type("conflict"), 1);
}

#[test]
fn debug_explainer_builds_an_unsat_story() {
    let mut explainer = ConflictExplainer::new();
    explainer.register_assertion(0, "x = 1");
    explainer.register_assertion(1, "x = 2");
    explainer.record_conflict(
        7,
        vec![0, 1],
        Some(TheoryConflictInfo {
            theory: "LIA".to_string(),
            reason: "x cannot be both 1 and 2".to_string(),
            involved_terms: vec!["x".to_string()],
        }),
    );

    assert_eq!(explainer.assertion_description(1), Some("x = 2"));
    let unsat = explainer.explain_unsat();
    assert_eq!(unsat.all_assertions, vec![0, 1]);
    let text = unsat.format();
    assert!(text.contains("LIA"));
    assert!(text.contains("x cannot be both 1 and 2"));
}

#[test]
fn debug_model_minimizer_separates_essential_from_optional() {
    let mut minimizer = DebugModelMinimizer::new();
    for id in 0..6u32 {
        minimizer.add_assignment(ModelAssignment {
            var_id: id,
            name: format!("v{id}"),
            value: "true".to_string(),
            is_bool: true,
        });
    }

    // Only variables 2 and 5 matter.
    let result = minimizer.minimize_binary(|assignments| {
        let has = |id: u32| assignments.iter().any(|(v, _)| *v == id);
        has(2) && has(5)
    });

    let essential: Vec<u32> = result.essential_vars.iter().map(|v| v.var_id).collect();
    assert!(essential.contains(&2), "{essential:?}");
    assert!(essential.contains(&5), "{essential:?}");
    assert_eq!(result.total_vars(), 6);
    assert!(result.format().contains("Model Minimization Result"));
}
