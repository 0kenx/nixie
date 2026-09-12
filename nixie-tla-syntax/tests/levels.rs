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

// ---- rules found by the SANY parity run -----------------------------------

#[test]
fn fairness_is_temporal() {
    // Missing this rule made every `Fairness == WF_vars(A)` come out action
    // level; the SANY parity run caught it across ten specifications.
    let r = levels(
        "---- MODULE M ----\nVARIABLE v\nA == v' = v\nF == WF_v(A)\nG == SF_v(A) /\\ WF_v(A)\n====\n",
    );
    assert_eq!(r.level_of("F"), Some(Level::Temporal));
    assert_eq!(r.level_of("G"), Some(Level::Temporal));
}

#[test]
fn subscripted_actions_are_actions() {
    let r = levels("---- MODULE M ----\nVARIABLE v\nA == v' = v\nB == [A]_v\nC == <<A>>_v\n====\n");
    assert_eq!(r.level_of("B"), Some(Level::Action));
    assert_eq!(r.level_of("C"), Some(Level::Action));
}

#[test]
fn temporal_quantifiers_are_temporal() {
    // `\AA` / `\EE` quantify over behaviours. Plain `\A` / `\E` do not and
    // must keep preserving the body's level.
    let r = levels(
        "---- MODULE M ----\nVARIABLE v\nA == \\EE x : x = 1\nB == \\AA x : x = 1\nC == \\E x : x = v\n====\n",
    );
    assert_eq!(r.level_of("A"), Some(Level::Temporal));
    assert_eq!(r.level_of("B"), Some(Level::Temporal));
    assert_eq!(r.level_of("C"), Some(Level::State));
}

#[test]
fn subscripted_action_violations() {
    // The body of `[A]_v` must be an action, and the subscript a state
    // expression. Both error kinds existed but were never wired up until the
    // parity run made their absence visible.
    let msg = violation("---- MODULE M ----\nVARIABLE v\nA == [[] (v = 0)]_v\n====\n");
    assert!(msg.contains("subscripted action"), "got {msg}");

    let msg = violation("---- MODULE M ----\nVARIABLE v\nA == [v' = v]_(v')\n====\n");
    assert!(msg.contains("subscript"), "got {msg}");
}

#[test]
fn fairness_of_a_temporal_formula_is_a_violation() {
    let msg = violation("---- MODULE M ----\nVARIABLE v\nA == WF_v([] (v = 0))\n====\n");
    assert!(msg.contains("WF_"), "got {msg}");
}

#[test]
fn operator_levels_are_a_function_of_their_arguments_not_a_maximum() {
    // The max rule is wrong for operators in two ways, both found by the SANY
    // parity run, and both fixed by computing each parameter's level function.

    // 1. An operator that *caps* a level. `B(d) == ENABLED d` is a state
    //    predicate however high `d` goes, so `C == B(A)` is state even though
    //    `A` is an action. `test57a.tla` is the corpus case.
    let r = levels(
        "---- MODULE M ----\nVARIABLES u, v\n\
         A == (u' = u) /\\ (v' = v)\nB(d) == ENABLED d\nC == B(A)\nD == ENABLED A\n====\n",
    );
    assert_eq!(r.trusted_level_of("C"), Some(Level::State));
    assert_eq!(r.trusted_level_of("D"), Some(Level::State));

    // 2. An operator that *ignores* a parameter. `SVGElemToString(elem) ==
    //    TRUE` stays constant however high the argument goes; the max rule
    //    made `EWD840_anim.tla`'s `Animation` state level.
    let r = levels("---- MODULE M ----\nVARIABLE v\nIgnore(e) == TRUE\nA == Ignore(v)\n====\n");
    assert_eq!(r.trusted_level_of("A"), Some(Level::Constant));

    // A parameter that is genuinely passed through still raises the level.
    let r = levels("---- MODULE M ----\nVARIABLE v\nId(e) == e\nA == Id(v)\nB == Id(v')\n====\n");
    assert_eq!(r.trusted_level_of("A"), Some(Level::State));
    assert_eq!(r.trusted_level_of("B"), Some(Level::Action));
}

#[test]
fn operator_parameters_invoked_in_operator_position() {
    // `BoxTest(-._) == -(x = 0)` applies its parameter as a prefix operator,
    // so `BoxTest([])` is temporal. The spelling is a bound name, not a
    // built-in, and treating it as a built-in silently ignored the parameter.
    let r = levels(
        "---- MODULE M ----\nVARIABLE x\nBoxTest(-._) == -(x = 0)\n         Foo1 == BoxTest([])\nFoo2 == BoxTest(<>)\n====\n",
    );
    assert_eq!(r.level_of("Foo1"), Some(Level::Temporal));
    assert_eq!(r.level_of("Foo2"), Some(Level::Temporal));
}

#[test]
fn parameter_level_functions_cross_extends() {
    // An importer that learns only the level cannot apply an ignored-parameter
    // operator correctly, so the exports carry the level functions too.
    let dir = std::env::temp_dir().join(format!("nixie-tla-lvl-{}", std::process::id()));
    std::fs::create_dir_all(&dir).expect("temp dir");
    std::fs::write(
        dir.join("Helper.tla"),
        "---- MODULE Helper ----
Ignore(e) == TRUE
Id(e) == e
====
",
    )
    .expect("write Helper");
    std::fs::write(
        dir.join("Main.tla"),
        "---- MODULE Main ----
EXTENDS Helper
VARIABLE v
A == Ignore(v)
B == Id(v)
====
",
    )
    .expect("write Main");

    let spec = nixie_tla_syntax::Loader::new()
        .load(&dir.join("Main.tla"))
        .expect("spec loads");
    let reports = nixie_tla_syntax::check_spec(&spec);
    let root = reports
        .iter()
        .find(|(n, _)| n == "Main")
        .map(|(_, r)| r)
        .expect("root report");
    assert_eq!(root.trusted_level_of("A"), Some(Level::Constant));
    assert_eq!(root.trusted_level_of("B"), Some(Level::State));
    let _ = std::fs::remove_dir_all(&dir);
}

#[test]
fn untrusted_levels_are_distinguishable_from_established_ones() {
    let r = levels("---- MODULE M ----\nEXTENDS Other\nVARIABLE v\nA == v = 1\nB == Foo\n====\n");
    assert_eq!(r.trusted_level_of("A"), Some(Level::State));
    assert_eq!(
        r.trusted_level_of("B"),
        None,
        "B depends on an unresolved name"
    );
    assert_eq!(
        r.level_of("B"),
        Some(Level::Constant),
        "best effort is still available"
    );
    assert_eq!(r.trusted_count(), 1);
}
