//! Level-checking tests.
//!
//! Two properties matter and they pull in opposite directions: the checker
//! must **compute the right level** for ordinary definitions, and it must
//! **not reject correct specifications**. `tests/corpus.rs` covers the second
//! over ~900 real files; these cover the first, plus the violations it does
//! catch.

use nixie_tla_syntax::{Level, check_module, parse_file};

fn levels(src: &str) -> nixie_tla_syntax::LevelReport {
    let parsed = match parse_file(src) {
        Ok(p) => p,
        Err(e) => panic!("failed to parse: {e}"),
    };
    check_module(&parsed.module)
}

const COUNTER: &str = r"
---- MODULE Counter ----
EXTENDS Naturals
CONSTANT N
VARIABLES x, q

vars == <<x, q>>
TypeOK == x \in 0..N
Init == /\ x = 0
        /\ q = <<>>
Inc == /\ x < N
       /\ x' = x + 1
       /\ UNCHANGED q
Enabled1 == ENABLED Inc
Live == []<>(x = N)
Spec == Init /\ [][Inc]_vars /\ WF_vars(Inc)
Lead == (x = 0) ~> (x = N)
====
";

#[test]
fn levels_of_a_realistic_module() {
    let r = levels(COUNTER);
    assert_eq!(
        r.level_of("vars"),
        Some(Level::State),
        "a tuple of variables"
    );
    assert_eq!(r.level_of("TypeOK"), Some(Level::State));
    assert_eq!(r.level_of("Init"), Some(Level::State));
    assert_eq!(r.level_of("Inc"), Some(Level::Action), "contains `'`");
    assert_eq!(
        r.level_of("Enabled1"),
        Some(Level::State),
        "`ENABLED` of an action is a state predicate"
    );
    assert_eq!(r.level_of("Live"), Some(Level::Temporal));
    assert_eq!(r.level_of("Spec"), Some(Level::Temporal));
    assert_eq!(r.level_of("Lead"), Some(Level::Temporal), "`~>`");
    assert!(r.errors.is_empty(), "a correct spec has no violations");
}

#[test]
fn constants_and_variables_get_their_declared_levels() {
    let r =
        levels("---- MODULE M ----\nCONSTANT c\nVARIABLE v\nA == c\nB == v\nC == c = 1\n====\n");
    assert_eq!(r.level_of("A"), Some(Level::Constant));
    assert_eq!(r.level_of("B"), Some(Level::State));
    assert_eq!(r.level_of("C"), Some(Level::Constant));
}

#[test]
fn bound_variables_are_constant_level() {
    // The bound `i` is constant level even though it ranges over a state
    // expression; only the domain contributes.
    let r = levels(
        "---- MODULE M ----\nVARIABLE v\nA == \\A i \\in {1, 2} : i = 1\nB == \\A i \\in v : i = 1\n====\n",
    );
    assert_eq!(r.level_of("A"), Some(Level::Constant));
    assert_eq!(
        r.level_of("B"),
        Some(Level::State),
        "the domain is a variable"
    );
}

#[test]
fn let_definitions_are_scoped_and_levelled() {
    let r = levels(
        "---- MODULE M ----\nVARIABLE v\nA == LET y == v' IN y\nB == LET y == 1 IN y\n====\n",
    );
    assert_eq!(r.level_of("A"), Some(Level::Action));
    assert_eq!(r.level_of("B"), Some(Level::Constant));
}

#[test]
fn operator_levels_propagate_to_applications() {
    let r = levels("---- MODULE M ----\nVARIABLE v\nStep == v' = v\nUses == Step /\\ TRUE\n====\n");
    assert_eq!(r.level_of("Step"), Some(Level::Action));
    assert_eq!(r.level_of("Uses"), Some(Level::Action));
}

// ---- violations -----------------------------------------------------------

fn violation(src: &str) -> String {
    let r = levels(src);
    assert!(
        !r.errors.is_empty(),
        "expected a level violation, got none (unresolved: {:?})",
        r.unresolved
    );
    r.errors[0].kind.to_string()
}

#[test]
fn double_priming_is_a_violation() {
    let msg = violation("---- MODULE M ----\nVARIABLE v\nA == (v')'\n====\n");
    assert!(msg.contains("`'`"), "got {msg}");
}

#[test]
fn enabled_of_a_temporal_formula_is_a_violation() {
    let msg = violation("---- MODULE M ----\nVARIABLE v\nA == ENABLED ([] (v = 0))\n====\n");
    assert!(msg.contains("ENABLED"), "got {msg}");
}

#[test]
fn unchanged_of_an_action_is_a_violation() {
    let msg = violation("---- MODULE M ----\nVARIABLE v\nA == UNCHANGED (v')\n====\n");
    assert!(msg.contains("UNCHANGED"), "got {msg}");
}

#[test]
fn priming_a_temporal_formula_is_a_violation() {
    let msg = violation("---- MODULE M ----\nVARIABLE v\nA == ([] (v = 0))'\n====\n");
    assert!(msg.contains("`'`"), "got {msg}");
}

// ---- the deliberate under-reporting contract ------------------------------

#[test]
fn violations_depending_on_unresolved_names_are_not_reported() {
    // `Foo` comes from an unresolved `EXTENDS`. Its level is unknown, so
    // `Foo''` must NOT be reported: guessing would reject correct specs whose
    // imports this crate cannot yet follow. The name is surfaced instead.
    let r = levels("---- MODULE M ----\nEXTENDS Other\nA == (Foo')'\n====\n");
    assert!(
        r.errors.is_empty(),
        "must not report a violation that depends on an unresolved name: {:?}",
        r.errors
    );
    assert!(
        r.unresolved.iter().any(|n| n == "Foo"),
        "the unresolved name is surfaced: {:?}",
        r.unresolved
    );
}

#[test]
fn standard_module_operators_resolve() {
    // Without these, almost everything would be tainted and the checker would
    // report nothing at all.
    let r = levels(
        "---- MODULE M ----\nEXTENDS Naturals, Sequences\nVARIABLE q\nA == Len(q) \\in Nat\n====\n",
    );
    assert_eq!(r.level_of("A"), Some(Level::State));
    assert!(!r.unresolved.iter().any(|n| n == "Len" || n == "Nat"));
}

#[test]
fn deep_expressions_do_not_overflow_the_stack() {
    // The walk carries its own stack, per AGENTS.md. Build a deep tree via the
    // parser's own limit and check the level walk survives it.
    let depth = 300;
    let src = format!(
        "---- MODULE M ----\nVARIABLE v\nA == {}v{}\n====\n",
        "(".repeat(depth),
        ")".repeat(depth)
    );
    let r = levels(&src);
    assert_eq!(r.level_of("A"), Some(Level::State));
}
