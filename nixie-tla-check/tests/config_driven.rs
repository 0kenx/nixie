//! Checking a specification the way its `.cfg` configures it.
//!
//! Without the file a `CONSTANT N` is an arbitrary integer, `1..N` has no
//! enumerable member list, and the checker asks a strictly harder question
//! than the author did. These pin what reading it changes – and, just as
//! important, what it must *not* silently change.

use nixie_core::TermManager;
use nixie_tla_check::bmc::{Bmc, Outcome, Roles, SetupError};

/// One invariant, the common case. Built inline at each call site's option,
/// because the slice has to borrow from the caller's `&'r str` and a helper
/// returning `Roles<'r>` would have to conjure that borrow out of its own
/// parameter slot.
macro_rules! roles {
    ($init:expr, $next:expr, $inv:expr) => {
        Roles {
            init: $init,
            next: $next,
            inv: &[$inv],
            constraints: &[],
        }
    };
}
use nixie_tla_syntax::parse_config;

fn run(src: &str, cfg: &str, init: &str, next: &str, inv: &str, depth: u32) -> Outcome {
    let parsed = nixie_tla_syntax::parse_file(src).expect("parses");
    let spec = nixie_tla_syntax::LoadedSpec::single(parsed);
    let module = spec.root_module().expect("has a root module");
    let config = parse_config(cfg).expect("config parses");
    let mut tm = TermManager::new();
    let mut bmc =
        Bmc::prepare_with_config(&spec, module, roles!(init, next, inv), &config, &mut tm)
            .expect("prepares");
    bmc.check(depth, &mut tm).expect("checks")
}

fn setup_err(src: &str, cfg: &str, init: &str, next: &str, inv: &str) -> SetupError {
    let parsed = nixie_tla_syntax::parse_file(src).expect("parses");
    let spec = nixie_tla_syntax::LoadedSpec::single(parsed);
    let module = spec.root_module().expect("has a root module");
    let config = parse_config(cfg).expect("config parses");
    let mut tm = TermManager::new();
    Bmc::prepare_with_config(&spec, module, roles!(init, next, inv), &config, &mut tm)
        .err()
        .expect("should not prepare")
}

// ======== CONSTANT assignments ========

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

/// …and without it, the specification as written leaves `N` arbitrary. The
/// checker answers for that specification – and the answer is a violation,
/// because the invariant only holds for the pinned `N` the author meant. The
/// difference is *answered*, not papered over with an invented bound.
#[test]
fn without_the_assignment_the_same_spec_is_refused() {
    // Since range *membership* became a comparison (issue #22), an unpinned
    // `N` no longer makes the encoding refuse: the query is answered for the
    // arbitrary `N` the specification actually leaves open – and the answer
    // is that the invariant does not hold (a small `N` breaks it), which is
    // the true verdict about the specification as written, not a guess.
    let parsed = nixie_tla_syntax::parse_file(BOUNDED).expect("parses");
    let spec = nixie_tla_syntax::LoadedSpec::single(parsed);
    let module = spec.root_module().expect("has a root module");
    let mut tm = TermManager::new();
    let mut bmc =
        Bmc::prepare(&spec, module, "Init", "Next", "Inv", &[], &mut tm).expect("prepares");
    let out = bmc.check(4, &mut tm).expect("checks");
    assert_eq!(
        out,
        Outcome::Violation { step: 0 },
        "with `N` free, x = 1 leaves `x \\in 1..N` when N = 0"
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

/// Model values are **distinct** – that is their whole content. A checker that
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

// ======== replacements ========

/// `MCBallot <- …` is how a model-checking harness makes an infinite
/// specification finite, and it is a rebinding of the name space rather than a
/// substitution pass – which is why it works for a `CONSTANT` too.
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
/// lowering does not do. Listed rather than treated as the unqualified form –
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
        roles!("Init", "Next", "Inv"),
        &config,
        &mut tm,
    )
    .expect("prepares");
    assert_eq!(bmc.unapplied_config().len(), 1);
    assert!(bmc.unapplied_config()[0].contains("Voting"));
}

// ======== constraints ========

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
    // The constraint excludes exactly that state – and, since the
    // constrained behaviours all stop at `x = 2`, the deadlock check
    // (on since issue #26) reports the stuck state rather than a clean
    // bound. The *violation* is still excluded, which is the point.
    assert_eq!(
        run(C, "CONSTRAINT Bound", "Init", "Next", "Inv", 5),
        Outcome::Deadlock { step: 2 }
    );
}

// ======== what must not change ========

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
        roles!("Init", "Next", "Inv"),
        &config,
        &mut tm,
    )
    .expect("prepares");
    assert_eq!(bmc.unapplied_config(), ["SYMMETRY"]);
}

// ======== ConstInit ========
//
// Apalache's `--cinit=CInit` convention pins the constants from inside the
// module rather than from a `.cfg`. It is a **substitution** for exactly the
// reason a `.cfg` assignment is: asserting `replicas = {"n1", "n2"}` reaches
// the solver, but the encoder needs the members before the solver runs –
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
/// harder question still has an answer – `x \in Nodes` holds for every
/// `Nodes` – so the test uses a construct that genuinely needs the members: a
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
/// `ConstInit` at all, and it used to be reported as violated at step 1 –
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

// ======== `SPECIFICATION` (issue #46) ========

/// `SPECIFICATION Spec` checks what `INIT Init` / `NEXT Next` check: the
/// decomposition names the two roles and the rest of the preparation is
/// unchanged – same verdict, for a configuration more than half the corpus
/// is written in.
#[test]
fn a_specification_is_prepared_as_its_init_and_next() {
    const S: &str = r"
---- MODULE S ----
EXTENDS Integers
CONSTANT N
VARIABLE x
Init == x = 0
Next == x' = IF x = N THEN 0 ELSE x + 1
Spec == Init /\ [][Next]_x
Inv  == x \in 0..N
Bad  == x < N
====
";
    let parsed = nixie_tla_syntax::parse_file(S).expect("parses");
    let spec = nixie_tla_syntax::LoadedSpec::single(parsed);
    let module = spec.root_module().expect("has a root module");
    let config =
        parse_config("CONSTANT N = 2\nSPECIFICATION Spec\nINVARIANT Inv\n").expect("config parses");
    let nixie_tla_syntax::BehaviorSpec::Temporal(name) = &config.behavior else {
        panic!("the config names a specification");
    };
    let form =
        nixie_tla_syntax::safety_form(&spec, module, &nixie_tla_syntax::check_spec(&spec), name)
            .expect("decomposes");
    assert_eq!((form.init.as_str(), form.next.as_str()), ("Init", "Next"));
    assert!(std::ptr::eq(form.home, module));

    let mut tm = TermManager::new();
    let scope = nixie_tla_check::bmc::Scope {
        root: module,
        home: form.home,
    };
    let mut bmc = Bmc::prepare_with_config_in(
        &spec,
        scope,
        roles!(&form.init, &form.next, "Inv"),
        &config,
        &mut tm,
    )
    .expect("prepares");
    assert_eq!(
        bmc.check(3, &mut tm).expect("checks"),
        Outcome::NoViolationWithin(3)
    );
    // And the answer is the answer `INIT Init` / `NEXT Next` gives.
    let config = parse_config("CONSTANT N = 2\nINIT Init\nNEXT Next\nINVARIANT Inv\n")
        .expect("config parses");
    let mut tm = TermManager::new();
    let mut bmc = Bmc::prepare_with_config(
        &spec,
        module,
        roles!("Init", "Next", "Inv"),
        &config,
        &mut tm,
    )
    .expect("prepares");
    assert_eq!(
        bmc.check(3, &mut tm).expect("checks"),
        Outcome::NoViolationWithin(3)
    );
}

/// A scratch directory holding a set of modules, removed on drop.
struct Scratch(std::path::PathBuf);

impl Scratch {
    fn new(tag: &str, files: &[(&str, &str)]) -> Self {
        let dir = std::env::temp_dir().join(format!(
            "nixie-tla-cfg-{tag}-{}-{:?}",
            std::process::id(),
            std::thread::current().id()
        ));
        let _ = std::fs::remove_dir_all(&dir);
        std::fs::create_dir_all(&dir).expect("scratch dir");
        for (name, body) in files {
            std::fs::write(dir.join(name), body).expect("write module");
        }
        Self(dir)
    }
}

impl Drop for Scratch {
    fn drop(&mut self) {
        let _ = std::fs::remove_dir_all(&self.0);
    }
}

/// The model-file shape: `MC.tla` EXTENDS the specification; the roles, the
/// formula and the constants all live in the extended module; and the roles
/// a `SPECIFICATION` names are read **there**. `MC.tla`'s own `Init`
/// override is what `INIT Init` names and not what `Spec` says – two
/// configurations, two specifications, two verdicts.
#[test]
fn a_specification_in_an_extended_module_is_read_in_that_module() {
    let s = Scratch::new(
        "spec-extends",
        &[
            (
                "Base.tla",
                r"
---- MODULE Base ----
EXTENDS Integers
CONSTANT N
VARIABLE x
Init == x = 0
Next == x' = IF x = N THEN 0 ELSE x + 1
Spec == Init /\ [][Next]_x
Inv  == x \in 0..N
====
",
            ),
            (
                "MC.tla",
                r"
---- MODULE MC ----
EXTENDS Base
CONSTANT N
ASSUME N \in Nat
Init == x = 100
====
",
            ),
        ],
    );
    let spec = nixie_tla_syntax::Loader::new()
        .load(&s.0.join("MC.tla"))
        .expect("loads");
    let module = spec.root_module().expect("root");
    let reports = nixie_tla_syntax::check_spec(&spec);
    let form = nixie_tla_syntax::safety_form(&spec, module, &reports, "Spec").expect("decomposes");
    assert_eq!(form.home.name.name, "Base");

    let config =
        parse_config("CONSTANT N = 2\nSPECIFICATION Spec\nINVARIANT Inv\n").expect("config parses");
    let mut tm = TermManager::new();
    let mut bmc = Bmc::prepare_with_config_in(
        &spec,
        nixie_tla_check::bmc::Scope {
            root: module,
            home: form.home,
        },
        roles!(&form.init, &form.next, "Inv"),
        &config,
        &mut tm,
    )
    .expect("prepares");
    assert_eq!(
        bmc.check(3, &mut tm).expect("checks"),
        Outcome::NoViolationWithin(3),
        "`Spec` starts at Base's `Init`, x = 0"
    );

    // `INIT Init` names MC's override: x = 100 is outside `0..2`.
    let config = parse_config("CONSTANT N = 2\nINIT Init\nNEXT Next\nINVARIANT Inv\n")
        .expect("config parses");
    let mut tm = TermManager::new();
    let mut bmc = Bmc::prepare_with_config(
        &spec,
        module,
        roles!("Init", "Next", "Inv"),
        &config,
        &mut tm,
    )
    .expect("prepares");
    assert_eq!(
        bmc.check(3, &mut tm).expect("checks"),
        Outcome::Violation { step: 0 },
        "the root's `Init` override, x = 100"
    );
}

/// A role defined in an extended module resolves through `INIT`/`NEXT` too,
/// with the configuration's constants and replacements applied inside it.
#[test]
fn roles_in_an_extended_module_resolve_with_the_configuration_applied() {
    let s = Scratch::new(
        "roles-extends",
        &[
            (
                "Spec.tla",
                r#"
---- MODULE Spec ----
EXTENDS Integers
CONSTANT Nodes
VARIABLE x
Init == x \in Nodes
Next == x' \in Nodes
Max  == CHOOSE n \in Nodes : \A m \in Nodes : m <= n
TypeInv == x \in Nodes
Inv == x <= Max
Low == x <= 2
====
"#,
            ),
            (
                "MC.tla",
                r#"
---- MODULE MC ----
EXTENDS Spec
CONSTANT Nodes
Small == {1, 2, 3}
====
"#,
            ),
        ],
    );
    let spec = nixie_tla_syntax::Loader::new()
        .load(&s.0.join("MC.tla"))
        .expect("loads");
    let module = spec.root_module().expect("root");
    // A `.cfg` replacement (`CONSTANT Nodes <- Small`) and a plain assignment
    // both reach the extended module's bodies: `Max` is the largest node
    // either way, and `x <= Max` holds over two steps.
    for cfg in [
        "CONSTANT Nodes <- Small\nINIT Init\nNEXT Next\nINVARIANT Inv\n",
        "CONSTANT Nodes = {1, 2, 3}\nINIT Init\nNEXT Next\nINVARIANT Inv\n",
    ] {
        let config = parse_config(cfg).expect("config parses");
        let mut tm = TermManager::new();
        let mut bmc = Bmc::prepare_with_config(
            &spec,
            module,
            roles!("Init", "Next", "Inv"),
            &config,
            &mut tm,
        )
        .unwrap_or_else(|e| panic!("{cfg}: {e}"));
        assert_eq!(
            bmc.check(2, &mut tm).expect("checks"),
            Outcome::NoViolationWithin(2),
            "{cfg}"
        );
    }
    // And the nodes really are `Small`'s: `x <= 2` breaks at step 0, since
    // `Init` may pick 3.
    let config = parse_config("CONSTANT Nodes <- Small\nINIT Init\nNEXT Next\nINVARIANT Low\n")
        .expect("config parses");
    let mut tm = TermManager::new();
    let mut bmc = Bmc::prepare_with_config(
        &spec,
        module,
        roles!("Init", "Next", "Low"),
        &config,
        &mut tm,
    )
    .expect("prepares");
    assert_eq!(
        bmc.check(2, &mut tm).expect("checks"),
        Outcome::Violation { step: 0 }
    );
}

/// Levels are read with `EXTENDS` followed: an **action** invariant defined
/// in an extended module is checked over step pairs. Classified by an
/// untrusted level it was taken for a state invariant, and a state-invariant
/// query asserts no transition into the step it tests – so the free next
/// state satisfied the negated action and the checker reported a violation
/// the specification cannot produce.
#[test]
fn an_action_invariant_in_an_extended_module_is_checked_over_step_pairs() {
    let s = Scratch::new(
        "action-inv-extends",
        &[
            (
                "Base.tla",
                r"
---- MODULE Base ----
EXTENDS Integers
VARIABLE x
Init == x = 0
Next == x' = x + 1
NoJump == x' <= x + 1
====
",
            ),
            ("MC.tla", "---- MODULE MC ----\nEXTENDS Base\n====\n"),
        ],
    );
    let spec = nixie_tla_syntax::Loader::new()
        .load(&s.0.join("MC.tla"))
        .expect("loads");
    let module = spec.root_module().expect("root");
    let mut tm = TermManager::new();
    let mut bmc = Bmc::prepare_with_config(
        &spec,
        module,
        roles!("Init", "Next", "NoJump"),
        &nixie_tla_syntax::TlcConfig::default(),
        &mut tm,
    )
    .expect("prepares");
    assert_eq!(
        bmc.check(3, &mut tm).expect("checks"),
        Outcome::NoViolationWithin(3)
    );
}
