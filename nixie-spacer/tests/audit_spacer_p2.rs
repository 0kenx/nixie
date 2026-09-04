//! Regression tests for the spacer-p2 audit findings.
//!
//! Each test pins a soundness fix in the Spacer/PDR, BMC, parser and Houdini
//! code paths:
//!   1. `is_init_reachable` really intersects Init  → Unsafe at level 0.
//!   2. `is_transition_feasible` / model-based predecessor search → multi-step
//!      Unsafe is reachable.
//!   3. `is_lemma_inductive` with primed-state renaming → a genuine invariant
//!      is proved Safe (and not fabricated).
//!   4. `ChcParser` preserves predicate applications (no erasure to `true`).
//!   5. BMC treats multiple transition rules as a DISJUNCTION (nondeterminism).
//!   6. Houdini filters candidates with real SMT queries (contradictory guesses
//!      are dropped, not returned as invariants).

use nixie_core::TermManager;
use nixie_spacer::bmc::{Bmc, BmcConfig, BmcResult};
use nixie_spacer::chc::{ChcSystem, PredicateApp, RuleHead};
use nixie_spacer::invariant::{InferenceResult, InvariantInference};
use nixie_spacer::parser::ChcParser;
use nixie_spacer::pdr::{Spacer, SpacerResult};

// ========  ========
// Finding 1: is_init_reachable – Unsafe must be detectable at level 0
// ========  ========

#[test]
fn spacer_reports_unsafe_when_bad_is_initial() {
    let mut terms = TermManager::new();
    let mut system = ChcSystem::new();

    let inv = system.declare_predicate("Inv", [terms.sorts.int_sort]);
    let x = terms.mk_var("x", terms.sorts.int_sort);
    let zero = terms.mk_int(0);

    // Init: x = 0 => Inv(x)
    let init_c = terms.mk_eq(x, zero);
    system.add_init_rule([("x".to_string(), terms.sorts.int_sort)], init_c, inv, [x]);

    // Query: Inv(x) /\ x = 0 => false   (bad state IS the initial state)
    let bad_c = terms.mk_eq(x, zero);
    system.add_query(
        [("x".to_string(), terms.sorts.int_sort)],
        [PredicateApp::new(inv, [x])],
        bad_c,
    );

    let mut spacer = Spacer::new(&mut terms, &system);
    let result = spacer.solve().expect("solve should not error");
    assert_eq!(
        result,
        SpacerResult::Unsafe,
        "an initial bad state must be reported Unsafe"
    );
}

// ========  ========
// Finding 2: model-based predecessor search – multi-step Unsafe is reachable
// ========  ========

#[test]
fn spacer_reports_unsafe_multistep() {
    let mut terms = TermManager::new();
    let mut system = ChcSystem::new();

    let inv = system.declare_predicate("Inv", [terms.sorts.int_sort]);
    let x = terms.mk_var("x", terms.sorts.int_sort);
    let xp = terms.mk_var("x_next", terms.sorts.int_sort);
    let zero = terms.mk_int(0);
    let one = terms.mk_int(1);
    let two = terms.mk_int(2);

    // Init: x = 0
    let init_c = terms.mk_eq(x, zero);
    system.add_init_rule([("x".to_string(), terms.sorts.int_sort)], init_c, inv, [x]);

    // Trans: Inv(x) /\ x' = x + 1 => Inv(x')   (unbounded increment)
    let x_plus_1 = terms.mk_add([x, one]);
    let trans_c = terms.mk_eq(xp, x_plus_1);
    system.add_transition_rule(
        [
            ("x".to_string(), terms.sorts.int_sort),
            ("x_next".to_string(), terms.sorts.int_sort),
        ],
        [PredicateApp::new(inv, [x])],
        trans_c,
        inv,
        [xp],
    );

    // Query: Inv(x) /\ x = 2 => false   (reachable only after two steps)
    let bad_c = terms.mk_eq(x, two);
    system.add_query(
        [("x".to_string(), terms.sorts.int_sort)],
        [PredicateApp::new(inv, [x])],
        bad_c,
    );

    let mut spacer = Spacer::new(&mut terms, &system);
    let result = spacer.solve().expect("solve should not error");
    assert_eq!(
        result,
        SpacerResult::Unsafe,
        "x = 2 is reachable in two steps and must be reported Unsafe"
    );
}

// ========  ========
// Finding 3: is_lemma_inductive – a real invariant proves Safe (not fabricated)
// ========  ========

#[test]
fn spacer_reports_safe_for_real_invariant() {
    let mut terms = TermManager::new();
    let mut system = ChcSystem::new();

    let inv = system.declare_predicate("Inv", [terms.sorts.int_sort]);
    let x = terms.mk_var("x", terms.sorts.int_sort);
    let xp = terms.mk_var("x_next", terms.sorts.int_sort);
    let zero = terms.mk_int(0);
    let one = terms.mk_int(1);
    let ten = terms.mk_int(10);

    // Init: x = 0
    let init_c = terms.mk_eq(x, zero);
    system.add_init_rule([("x".to_string(), terms.sorts.int_sort)], init_c, inv, [x]);

    // Trans: Inv(x) /\ x' = x + 1 /\ x' < 10 => Inv(x')
    let x_plus_1 = terms.mk_add([x, one]);
    let trans_eq = terms.mk_eq(xp, x_plus_1);
    let bound = terms.mk_lt(xp, ten);
    let trans_c = terms.mk_and([trans_eq, bound]);
    system.add_transition_rule(
        [
            ("x".to_string(), terms.sorts.int_sort),
            ("x_next".to_string(), terms.sorts.int_sort),
        ],
        [PredicateApp::new(inv, [x])],
        trans_c,
        inv,
        [xp],
    );

    // Query: Inv(x) /\ x < 0 => false   (x >= 0 is invariant -> Safe)
    let bad_c = terms.mk_lt(x, zero);
    system.add_query(
        [("x".to_string(), terms.sorts.int_sort)],
        [PredicateApp::new(inv, [x])],
        bad_c,
    );

    let mut spacer = Spacer::new(&mut terms, &system);
    let result = spacer.solve().expect("solve should not error");
    assert_eq!(
        result,
        SpacerResult::Safe,
        "x >= 0 is inductive, so the system is Safe"
    );
}

// ========  ========
// Finding 4: ChcParser preserves predicate applications
// ========  ========

#[test]
fn parser_preserves_predicate_applications() {
    let mut terms = TermManager::new();
    let mut parser = ChcParser::new(&mut terms);

    let input = "(set-logic HORN)\n\
                 (declare-fun Inv (Int) Bool)\n\
                 (assert (forall ((x Int)) (=> (= x 0) (Inv x))))\n\
                 (assert (forall ((x Int)) (=> (Inv x) false)))";
    let system = parser.parse(input).expect("parse should succeed");

    let mut head_pred_seen = false;
    let mut query_body_pred_seen = false;
    for rule in system.rules() {
        if let RuleHead::Predicate(app) = &rule.head {
            head_pred_seen = true;
            assert_eq!(
                app.args.len(),
                1,
                "Inv application must retain its argument"
            );
        }
        if rule.head.is_query() && !rule.body.predicates.is_empty() {
            query_body_pred_seen = true;
        }
    }

    assert!(
        head_pred_seen,
        "predicate application in the rule head must be preserved (not erased to `true`)"
    );
    assert!(
        query_body_pred_seen,
        "predicate application in the query body must be preserved (not erased to `true`)"
    );
}

// ========  ========
// Finding 5: BMC disjoins multiple transition rules (nondeterminism)
// ========  ========

#[test]
fn bmc_disjoins_nondeterministic_rules() {
    let mut terms = TermManager::new();
    let mut system = ChcSystem::new();

    let inv = system.declare_predicate("Inv", [terms.sorts.int_sort]);
    let x = terms.mk_var("x", terms.sorts.int_sort);
    let xp = terms.mk_var("x_next", terms.sorts.int_sort);
    let zero = terms.mk_int(0);
    let one = terms.mk_int(1);
    let two = terms.mk_int(2);

    // Init: x = 0
    let init_c = terms.mk_eq(x, zero);
    system.add_init_rule([("x".to_string(), terms.sorts.int_sort)], init_c, inv, [x]);

    // Rule A: x' = x + 1
    let x_plus_1 = terms.mk_add([x, one]);
    let trans_a = terms.mk_eq(xp, x_plus_1);
    system.add_transition_rule(
        [
            ("x".to_string(), terms.sorts.int_sort),
            ("x_next".to_string(), terms.sorts.int_sort),
        ],
        [PredicateApp::new(inv, [x])],
        trans_a,
        inv,
        [xp],
    );

    // Rule B: x' = x - 1   (contradicts Rule A if conjoined)
    let x_minus_1 = terms.mk_sub(x, one);
    let trans_b = terms.mk_eq(xp, x_minus_1);
    system.add_transition_rule(
        [
            ("x".to_string(), terms.sorts.int_sort),
            ("x_next".to_string(), terms.sorts.int_sort),
        ],
        [PredicateApp::new(inv, [x])],
        trans_b,
        inv,
        [xp],
    );

    // Query: Inv(x) /\ x = 2 => false   (reachable via +1,+1 at depth 2)
    let bad_c = terms.mk_eq(x, two);
    system.add_query(
        [("x".to_string(), terms.sorts.int_sort)],
        [PredicateApp::new(inv, [x])],
        bad_c,
    );

    let config = BmcConfig {
        max_depth: 5,
        use_kinduction: false,
        verbosity: 0,
    };
    let mut bmc = Bmc::with_config(&mut terms, &system, config);
    let result = bmc.check().expect("BMC should not error");
    // The key regression: with the two rules DISJOINED, x = 2 is reachable, so
    // BMC must report Unsafe.  Conjoining them (the bug) makes every step
    // contradictory (x'=x+1 ∧ x'=x-1) and yields a spurious Safe.  The exact
    // depth the underlying solver reports can vary (its LIA search over
    // disjunctions is incomplete), so we only require that a counterexample is
    // found – never Safe.
    assert!(
        matches!(result, BmcResult::Unsafe(_)),
        "with rules disjoined, x = 2 is reachable and BMC must report Unsafe, got {:?}",
        result
    );
}

// ========  ========
// Finding 6: Houdini drops contradictory candidates via real SMT queries
// ========  ========

#[test]
fn houdini_drops_non_inductive_candidates() {
    let mut terms = TermManager::new();
    let mut system = ChcSystem::new();

    let inv = system.declare_predicate("Inv", [terms.sorts.int_sort]);
    let x = terms.mk_var("x", terms.sorts.int_sort);
    let xp = terms.mk_var("x_next", terms.sorts.int_sort);
    let zero = terms.mk_int(0);
    let one = terms.mk_int(1);

    // Init: x = 0
    let init_c = terms.mk_eq(x, zero);
    system.add_init_rule([("x".to_string(), terms.sorts.int_sort)], init_c, inv, [x]);

    // Trans: Inv(x) /\ x' = x + 1 => Inv(x')
    let x_plus_1 = terms.mk_add([x, one]);
    let trans_c = terms.mk_eq(xp, x_plus_1);
    system.add_transition_rule(
        [
            ("x".to_string(), terms.sorts.int_sort),
            ("x_next".to_string(), terms.sorts.int_sort),
        ],
        [PredicateApp::new(inv, [x])],
        trans_c,
        inv,
        [xp],
    );

    let mut inference = InvariantInference::default();
    let result = inference.infer(&system, &mut terms);

    let invariants = match result {
        InferenceResult::Success(map) => map,
        InferenceResult::Partial { found, .. } => found,
        other => panic!("expected Success/Partial, got {:?}", other),
    };
    let inv_formulas = invariants.get(&inv).cloned().unwrap_or_default();

    // Reconstruct the canonical current-state variable that Houdini uses.
    let canon = terms.mk_var(&format!("__sp_c#{}#0", inv.raw()), terms.sorts.int_sort);
    let ge0 = terms.mk_ge(canon, zero);
    let le0 = terms.mk_le(canon, zero);
    let eq0 = terms.mk_eq(canon, zero);

    // x <= 0 and x = 0 are NOT inductive for x := x + 1 and must be filtered.
    assert!(
        !inv_formulas.contains(&le0),
        "x <= 0 is not inductive and must be dropped by Houdini"
    );
    assert!(
        !inv_formulas.contains(&eq0),
        "x = 0 is not inductive and must be dropped by Houdini"
    );
    // x >= 0 is inductive and should survive as a verified invariant.
    assert!(
        inv_formulas.contains(&ge0),
        "x >= 0 is inductive and should be retained; got {:?}",
        inv_formulas
    );
}
