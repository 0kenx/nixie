//! Checking a specification the way its `.cfg` configures it.
//!
//! Without the file a `CONSTANT N` is an arbitrary integer, `1..N` has no
//! enumerable member list, and the checker asks a strictly harder question
//! than the author did. These pin what reading it changes — and, just as
//! important, what it must *not* silently change.

use nixie_core::TermManager;
use nixie_tla_check::bmc::{Bmc, Outcome, Roles, SetupError};

fn roles<'r>(init: &'r str, next: &'r str, inv: &'r str) -> Roles<'r> {
    Roles {
        init,
        next,
        inv,
        constraints: &[],
    }
}
use nixie_tla_syntax::parse_config;

fn run(src: &str, cfg: &str, init: &str, next: &str, inv: &str, depth: u32) -> Outcome {
    let parsed = nixie_tla_syntax::parse_file(src).expect("parses");
    let spec = nixie_tla_syntax::LoadedSpec::single(parsed);
    let module = spec.root_module().expect("has a root module");
    let config = parse_config(cfg).expect("config parses");
    let mut tm = TermManager::new();
    let mut bmc = Bmc::prepare_with_config(&spec, module, roles(init, next, inv), &config, &mut tm)
        .expect("prepares");
    bmc.check(depth, &mut tm).expect("checks")
}

fn setup_err(src: &str, cfg: &str, init: &str, next: &str, inv: &str) -> SetupError {
    let parsed = nixie_tla_syntax::parse_file(src).expect("parses");
    let spec = nixie_tla_syntax::LoadedSpec::single(parsed);
    let module = spec.root_module().expect("has a root module");
    let config = parse_config(cfg).expect("config parses");
    let mut tm = TermManager::new();
    Bmc::prepare_with_config(&spec, module, roles(init, next, inv), &config, &mut tm)
        .err()
        .expect("should not prepare")
}

// ---- CONSTANT assignments ----

/// The headline case. `1..N` has no candidate list while `N` is arbitrary; the
/// `.cfg` is what makes it finite.
const BOUNDED: &str = r"
---- MODULE Bounded ----
EXTENDS Integers
CONSTANT N
VARIABLE x
Init == x = 1
Next == x' = IF x = N THEN 1 ELSE x + 1
Inv  == x \in 1..N
====
";

#[test]
fn a_constant_assignment_makes_a_range_enumerable() {
    assert_eq!(
        run(BOUNDED, "CONSTANT N = 3", "Init", "Next", "Inv", 4),
        Outcome::NoViolationWithin(4)
    );
}

/// …and without it the same specification cannot be prepared at all, because
/// nothing pins `N`. The point is that the difference is *reported*, not that
/// a plausible bound is invented.
#[test]
fn without_the_assignment_the_same_spec_is_refused() {
    let parsed = nixie_tla_syntax::parse_file(BOUNDED).expect("parses");
    let spec = nixie_tla_syntax::LoadedSpec::single(parsed);
    let module = spec.root_module().expect("has a root module");
    let mut tm = TermManager::new();
    let mut bmc =
        Bmc::prepare(&spec, module, "Init", "Next", "Inv", &[], &mut tm).expect("prepares");
    assert!(
        bmc.check(4, &mut tm).is_err(),
        "an unpinned `N` must be refused, not guessed"
    );
}

/// A different value is a different specification, and the checker has to
/// notice: with `N = 2` the invariant `x \in 1..3` is violated.
#[test]
fn the_assigned_value_is_the_one_used() {
    const OFF: &str = r"
---- MODULE Off ----
EXTENDS Integers
CONSTANT N
VARIABLE x
Init == x = N
Next == x' = x
Inv  == x = 3
====
";
    assert_eq!(
        run(OFF, "CONSTANT N = 3", "Init", "Next", "Inv", 1),
        Outcome::NoViolationWithin(1)
    );
    assert_eq!(
        run(OFF, "CONSTANT N = 2", "Init", "Next", "Inv", 1),
        Outcome::Violation { step: 0 }
    );
}

#[test]
fn a_set_of_model_values() {
    const PROCS: &str = r"
---- MODULE Procs ----
CONSTANT Proc
VARIABLE p
Init == p \in Proc
Next == p' \in Proc
Inv  == p \in Proc
====
";
    assert_eq!(
        run(PROCS, "CONSTANT Proc = {p1, p2}", "Init", "Next", "Inv", 2),
        Outcome::NoViolationWithin(2)
    );
}

/// Model values are **distinct** — that is their whole content. A checker that
/// let two of them be equal would miss counterexamples that depend on telling
/// processes apart.
#[test]
fn distinct_model_values_are_distinct() {
    const TWO: &str = r"
---- MODULE Two ----
CONSTANT a, b
VARIABLE x
Init == x = a
Next == x' = x
Inv  == x /= b
====
";
    // `a` and `b` are different model values, so `x = a` never equals `b`.
    assert_eq!(
        run(TWO, "CONSTANTS a = m1  b = m2", "Init", "Next", "Inv", 1),
        Outcome::NoViolationWithin(1)
    );
    // ...and when the config says they are the *same* model value, they are.
    assert_eq!(
        run(TWO, "CONSTANTS a = m1  b = m1", "Init", "Next", "Inv", 1),
        Outcome::Violation { step: 0 }
    );
}

/// A model value is not the string that spells it. `ModelValue_n1` and `"n1"`
/// are different values, and the reserved prefix is what keeps them apart.
#[test]
fn a_model_value_is_not_the_string_of_its_name() {
    const S: &str = r#"
---- MODULE S ----
CONSTANT c
VARIABLE x
Init == x = c
Next == x' = x
Inv  == x /= "n1"
====
"#;
    assert_eq!(
        run(S, "CONSTANT c = n1", "Init", "Next", "Inv", 1),
        Outcome::NoViolationWithin(1)
    );
}

#[test]
fn booleans_and_strings_and_wide_integers() {
    const V: &str = r#"
---- MODULE V ----
EXTENDS Integers
CONSTANT b, s, n
VARIABLE x
Init == x = n
Next == x' = x
Inv  == b /\ (s = "yes") /\ (x = 123456789012345678901234567890)
====
"#;
    assert_eq!(
        run(
            V,
            "CONSTANTS b = TRUE  s = \"yes\"  n = 123456789012345678901234567890",
            "Init",
            "Next",
            "Inv",
            1
        ),
        Outcome::NoViolationWithin(1)
    );
}

// ---- replacements ----

/// `MCBallot <- …` is how a model-checking harness makes an infinite
/// specification finite, and it is a rebinding of the name space rather than a
/// substitution pass — which is why it works for a `CONSTANT` too.
#[test]
fn a_replacement_rebinds_a_definition() {
    const R: &str = r"
---- MODULE R ----
EXTENDS Integers
VARIABLE x
Ballot   == 0..9
MCBallot == 0..2
Init == x = 0
Next == x' = x
Inv  == \A b \in Ballot : b < 3
====
";
    // Without the replacement `Ballot` is `0..9` and the invariant fails.
    assert_eq!(
        run(R, "INVARIANT Inv", "Init", "Next", "Inv", 1),
        Outcome::Violation { step: 0 }
    );
    // With it, `Ballot` *is* `MCBallot`.
    assert_eq!(
        run(R, "CONSTANT Ballot <- MCBallot", "Init", "Next", "Inv", 1),
        Outcome::NoViolationWithin(1)
    );
}

/// A replacement naming something the module does not have is reported, not
/// skipped: proceeding without it checks a different specification.
#[test]
fn a_replacement_of_a_missing_definition_is_reported() {
    const R: &str = r"
---- MODULE R2 ----
VARIABLE x
Init == x = 0
Next == x' = x
Inv  == x = 0
====
";
    assert!(matches!(
        setup_err(R, "CONSTANT Ballot <- NotThere", "Init", "Next", "Inv"),
        SetupError::Replacement { .. }
    ));
}

/// A module-qualified replacement needs `INSTANCE` substitution, which the
/// lowering does not do. Listed rather than treated as the unqualified form —
/// the two are different specifications.
#[test]
fn a_module_qualified_replacement_is_listed_not_applied() {
    const R: &str = r"
---- MODULE R3 ----
VARIABLE x
Init == x = 0
Next == x' = x
Inv  == x = 0
====
";
    let parsed = nixie_tla_syntax::parse_file(R).expect("parses");
    let spec = nixie_tla_syntax::LoadedSpec::single(parsed);
    let module = spec.root_module().expect("has a root module");
    let config = parse_config("CONSTANT Ballot <- [Voting]MCBallot").expect("config parses");
    let mut tm = TermManager::new();
    let bmc = Bmc::prepare_with_config(
        &spec,
        module,
        roles("Init", "Next", "Inv"),
        &config,
        &mut tm,
    )
    .expect("prepares");
    assert_eq!(bmc.unapplied_config().len(), 1);
    assert!(bmc.unapplied_config()[0].contains("Voting"));
}

// ---- constraints ----

/// A `CONSTRAINT` bounds the state space the author intended. Asserting it
/// *narrows* the search; ignoring it explores states outside the configured
/// model and can report a counterexample that is not in it.
#[test]
fn a_state_constraint_bounds_the_search() {
    const C: &str = r"
---- MODULE C ----
EXTENDS Integers
VARIABLE x
Init  == x = 0
Next  == x' = x + 1
Bound == x < 3
Inv   == x < 3
====
";
    // Unconstrained, `x` reaches 3 and the invariant fails at step 3.
    assert_eq!(
        run(C, "INVARIANT Inv", "Init", "Next", "Inv", 5),
        Outcome::Violation { step: 3 }
    );
    // The constraint excludes exactly that state.
    assert_eq!(
        run(C, "CONSTRAINT Bound", "Init", "Next", "Inv", 5),
        Outcome::NoViolationWithin(5)
    );
}

// ---- what must not change ----

/// An empty configuration must leave the verdict exactly where it was: the
/// `.cfg` path and the convention path are the same code, and a default
/// configuration has to be a no-op.
#[test]
fn an_empty_config_changes_nothing() {
    const COUNTER: &str = r"
---- MODULE Counter ----
EXTENDS Integers
VARIABLE x
Init == x = 0
Next == x' = x + 1
Inv  == x < 3
====
";
    let parsed = nixie_tla_syntax::parse_file(COUNTER).expect("parses");
    let spec = nixie_tla_syntax::LoadedSpec::single(parsed);
    let module = spec.root_module().expect("has a root module");
    let mut tm = TermManager::new();
    let mut plain =
        Bmc::prepare(&spec, module, "Init", "Next", "Inv", &[], &mut tm).expect("prepares");
    let want = plain.check(6, &mut tm).expect("checks");
    assert_eq!(want, Outcome::Violation { step: 3 });
    assert_eq!(run(COUNTER, "", "Init", "Next", "Inv", 6), want);
    assert!(plain.unapplied_config().is_empty());
}

/// Options the checker reads and does not act on are reported, so a caller can
/// say what it set aside instead of the fact disappearing.
#[test]
fn ignored_options_reach_the_caller() {
    const C: &str = r"
---- MODULE Sym ----
VARIABLE x
Init == x = 0
Next == x' = x
Inv  == x = 0
Perm == {}
====
";
    let parsed = nixie_tla_syntax::parse_file(C).expect("parses");
    let spec = nixie_tla_syntax::LoadedSpec::single(parsed);
    let module = spec.root_module().expect("has a root module");
    let config = parse_config("SYMMETRY Perm").expect("config parses");
    let mut tm = TermManager::new();
    let bmc = Bmc::prepare_with_config(
        &spec,
        module,
        roles("Init", "Next", "Inv"),
        &config,
        &mut tm,
    )
    .expect("prepares");
    assert_eq!(bmc.unapplied_config(), ["SYMMETRY"]);
}

// ---- ConstInit ----
//
// Apalache's `--cinit=CInit` convention pins the constants from inside the
// module rather than from a `.cfg`. It is a **substitution** for exactly the
// reason a `.cfg` assignment is: asserting `replicas = {"n1", "n2"}` reaches
// the solver, but the encoder needs the members before the solver runs —
// `[replicas -> S]` has no candidate list until `replicas` is literally a set
// of two things.

const CINIT: &str = r#"
---- MODULE Cinit ----
EXTENDS Integers
CONSTANT Nodes
VARIABLE x
CInit == Nodes = {"n1", "n2"}
Init == x \in Nodes
Next == UNCHANGED x
Inv  == x \in Nodes
====
"#;

#[test]
fn a_const_init_substitutes_rather_than_assumes() {
    let parsed = nixie_tla_syntax::parse_file(CINIT).expect("parses");
    let spec = nixie_tla_syntax::LoadedSpec::single(parsed);
    let module = spec.root_module().expect("has a root module");
    let mut tm = TermManager::new();
    let mut bmc = Bmc::prepare(&spec, module, "Init", "Next", "Inv", &["CInit"], &mut tm)
        .expect("prepares with the constants substituted");
    assert_eq!(
        bmc.check(2, &mut tm).expect("checks"),
        Outcome::NoViolationWithin(2)
    );
}

/// And a claim that is false about the substituted value is found, so the one
/// above is not passing because nothing is constrained.
#[test]
fn a_const_init_value_is_the_one_that_is_checked() {
    let src = r#"
---- MODULE CinitBad ----
EXTENDS Integers
CONSTANT Nodes
VARIABLE x
CInit == Nodes = {"n1", "n2"}
Init == x \in Nodes
Next == UNCHANGED x
Inv  == x = "n1"
====
"#;
    let parsed = nixie_tla_syntax::parse_file(src).expect("parses");
    let spec = nixie_tla_syntax::LoadedSpec::single(parsed);
    let module = spec.root_module().expect("has a root module");
    let mut tm = TermManager::new();
    let mut bmc =
        Bmc::prepare(&spec, module, "Init", "Next", "Inv", &["CInit"], &mut tm).expect("prepares");
    assert_eq!(
        bmc.check(2, &mut tm).expect("checks"),
        Outcome::Violation { step: 0 },
        "`x` may be `n2`"
    );
}

/// Without the `ConstInit` the constant is arbitrary, which is a strictly
/// harder question. Where the answer does not depend on *which* set it is, the
/// harder question still has an answer — `x \in Nodes` holds for every
/// `Nodes` — so the test uses a construct that genuinely needs the members: a
/// quantifier is instantiated per candidate, and an opaque set has no
/// candidates to instantiate over.
#[test]
fn without_a_const_init_the_members_are_not_known() {
    let src = r#"
---- MODULE NeedsMembers ----
EXTENDS Integers
CONSTANT Nodes
VARIABLE x
CInit == Nodes = {"n1", "n2"}
Init == x \in Nodes
Next == UNCHANGED x
Inv  == \A n \in Nodes : n # "z"
====
"#;
    let parsed = nixie_tla_syntax::parse_file(src).expect("parses");
    let spec = nixie_tla_syntax::LoadedSpec::single(parsed);
    let module = spec.root_module().expect("has a root module");

    let mut tm = TermManager::new();
    let with = Bmc::prepare(&spec, module, "Init", "Next", "Inv", &["CInit"], &mut tm)
        .expect("prepares")
        .check(2, &mut tm)
        .expect("checks");
    assert_eq!(with, Outcome::NoViolationWithin(2));

    let mut tm = TermManager::new();
    let outcome = Bmc::prepare(&spec, module, "Init", "Next", "Inv", &[], &mut tm)
        .map(|mut b| b.check(2, &mut tm));
    assert!(
        matches!(&outcome, Err(_) | Ok(Err(_))),
        "an arbitrary `Nodes` has no members to quantify over, got {outcome:?}"
    );
}

/// And the shape that found the congruence bug: `x \in Nodes` is preserved by
/// a step that changes nothing, for *every* `Nodes`. This needs no
/// `ConstInit` at all, and it used to be reported as violated at step 1 —
/// membership was a free Boolean per element, so `x@1 = x@0` said nothing
/// about it. See `nixie-solver`'s `equal_elements_are_in_the_same_sets`.
#[test]
fn membership_survives_a_step_that_changes_nothing() {
    let src = r"
---- MODULE Preserved ----
EXTENDS Integers
CONSTANT Nodes
VARIABLE x
Init == x \in Nodes
Next == UNCHANGED x
Inv  == x \in Nodes
====
";
    let parsed = nixie_tla_syntax::parse_file(src).expect("parses");
    let spec = nixie_tla_syntax::LoadedSpec::single(parsed);
    let module = spec.root_module().expect("has a root module");
    let mut tm = TermManager::new();
    let mut bmc =
        Bmc::prepare(&spec, module, "Init", "Next", "Inv", &[], &mut tm).expect("prepares");
    assert_eq!(
        bmc.check(3, &mut tm).expect("checks"),
        Outcome::NoViolationWithin(3)
    );
}

/// A constant pinned by something less direct than `name = expr` is left to
/// the solver, which is where it belongs: there is nothing to substitute.
/// It must not be mistaken for a binding.
#[test]
fn an_indirect_constraint_is_not_a_substitution() {
    let src = r"
---- MODULE Indirect ----
EXTENDS Integers, FiniteSets
CONSTANT N
VARIABLE x
CInit == N > 3
Init == x = 0
Next == UNCHANGED x
Inv  == x = 0
====
";
    let parsed = nixie_tla_syntax::parse_file(src).expect("parses");
    let spec = nixie_tla_syntax::LoadedSpec::single(parsed);
    let module = spec.root_module().expect("has a root module");
    let mut tm = TermManager::new();
    let mut bmc =
        Bmc::prepare(&spec, module, "Init", "Next", "Inv", &["CInit"], &mut tm).expect("prepares");
    assert_eq!(
        bmc.check(2, &mut tm).expect("checks"),
        Outcome::NoViolationWithin(2)
    );
}
