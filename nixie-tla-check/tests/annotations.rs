//! `@type:` annotations (issue #15).
//!
//! Apalache *requires* annotations, so a drop-in has to read them. These
//! tests pin the three halves that landed: attachment (including
//! interleaved comments inside one `VARIABLES` block — Test1226's shape),
//! the Type1 grammar subset, and seeding — where an annotation is
//! **checked, never trusted**: it unifies with what inference derives, and
//! a conflict is the type error it is.

use nixie_core::TermManager;
use nixie_tla_check::bmc::{Bmc, Outcome, Roles};

fn claim(spec: &str, inv: &str) -> Outcome {
    let parsed = nixie_tla_syntax::parse_file(spec).expect("parses");
    let spec = nixie_tla_syntax::LoadedSpec::single(parsed);
    let module = spec.root_module().expect("has a root module");
    let mut tm = TermManager::new();
    let mut bmc = Bmc::prepare_with_config(
        &spec,
        module,
        Roles {
            init: "Init",
            next: "Next",
            inv: &[inv],
            constraints: &[],
        },
        &nixie_tla_syntax::TlcConfig::default(),
        &mut tm,
    )
    .expect("prepares");
    bmc.check(0, &mut tm).expect("checks")
}

fn types_err(spec: &str, inv: &str) -> String {
    let parsed = nixie_tla_syntax::parse_file(spec).expect("parses");
    let spec = nixie_tla_syntax::LoadedSpec::single(parsed);
    let module = spec.root_module().expect("has a root module");
    let mut tm = TermManager::new();
    Bmc::prepare_with_config(
        &spec,
        module,
        Roles {
            init: "Init",
            next: "Next",
            inv: &[inv],
            constraints: &[],
        },
        &nixie_tla_syntax::TlcConfig::default(),
        &mut tm,
    )
    .err()
    .map_or_else(
        || panic!("a conflicting annotation must not prepare"),
        |e: nixie_tla_check::bmc::SetupError| e.to_string(),
    )
}

// ---- attachment ----

/// Interleaved comments inside one `VARIABLES` block annotate the *next*
/// name each — Test1226's shape, and the attachment bug's reproducer.
#[test]
fn interleaved_comments_annotate_the_next_name() {
    let src = r#"
---- MODULE Interleaved ----
EXTENDS Integers
VARIABLES
    \* @type: Str -> Int;
    strToInt,
    \* @type: Set(Int) -> Int;
    intsToInt
Init == strToInt = [x \in {"a"} |-> 1] /\ intsToInt = {7}
Next == UNCHANGED <<strToInt, intsToInt>>
Inv == strToInt["a"] = 1
====
"#;
    let parsed = nixie_tla_syntax::parse_file(src).expect("parses");
    let spec = nixie_tla_syntax::LoadedSpec::single(parsed);
    let by_name: Vec<(String, String)> = spec
        .annotations
        .iter()
        .map(|a| (a.name.clone(), a.text.clone()))
        .collect();
    assert_eq!(
        by_name,
        vec![
            ("strToInt".to_string(), "Str -> Int;".to_string()),
            ("intsToInt".to_string(), "Set(Int) -> Int;".to_string()),
        ],
        "each annotation binds to the name that follows it"
    );
}

// ---- seeding: the annotation settles the shape ----

/// An annotated variable whose only uses would leave its shape ambiguous
/// gets it from the annotation: here `f` is written once and read only
/// through `DOMAIN`, and without the annotation its element type is an
/// unconstrained variable.
#[test]
fn an_annotation_settles_a_functions_shape() {
    let src = r#"
---- MODULE Settled ----
EXTENDS Integers, FiniteSets
VARIABLE
    \* @type: Str -> Int;
    f
Init == f = [x \in {"a", "b"} |-> 1]
Next == UNCHANGED f
Inv == Cardinality(DOMAIN f) = 2
====
"#;
    assert_eq!(claim(src, "Inv"), Outcome::NoViolationWithin(0));
}

/// The issue's own named defect, pinned as it stands: `f["b"]` rebinds `f`
/// to an open record *despite* the `Str -> Int` annotation (the field-access
/// preference unifies Fun with Rec). What the annotation guarantees today is
/// that this cannot become a **wrong verdict**: the merged shape has no SMT
/// sort and the check refuses (exit 120) — the remaining piece of this
/// issue, recorded where it will be seen.
#[test]
fn a_field_access_against_the_annotation_refuses_rather_than_guesses() {
    let src = r#"
---- MODULE FieldAgainst ----
EXTENDS Integers
VARIABLE
    \* @type: Str -> Int;
    f
Init == f = [x \in {"a", "b"} |-> 1]
Next == UNCHANGED f
Inv == f["b"] = 1
====
"#;
    let err = types_err(src, "Inv");
    assert!(
        err.contains("does not type check") || err.contains("no SMT sort"),
        "a refusal, never a wrong verdict: {err}"
    );
}

/// A **conflicting** annotation is a type error (exit 120), never a silent
/// override — the issue's "contradictory annotations accepted silently"
/// defect.
#[test]
fn a_conflicting_annotation_is_a_type_error() {
    let src = r#"
---- MODULE Conflict ----
EXTENDS Integers
VARIABLE
    \* @type: Int;
    x
Init == x = "a string"
Next == UNCHANGED x
Inv == x = x
====
"#;
    let err = types_err(src, "Inv");
    assert!(err.contains("does not type check"), "{err}");
}

// ---- the grammar ----

/// The Type1 subset: Int/Bool/Str, Set/Seq, function arrows
/// (right-associative), tuples, records.
#[test]
fn the_type1_subset_parses() {
    use nixie_tla::Type;
    use nixie_tla::annotations::parse_type1;
    let round = |s: &str, want: Type| {
        let got = parse_type1(s).expect("parses");
        assert_eq!(got.0, want, "`{s}`");
    };
    round("Int", Type::Int);
    round("Bool", Type::Bool);
    round("Str", Type::Str);
    round("Set(Int)", Type::Set(Box::new(Type::Int)));
    round("Seq(Str)", Type::Seq(Box::new(Type::Str)));
    round(
        "Str -> Int",
        Type::Fun(Box::new(Type::Str), Box::new(Type::Int)),
    );
    // Right-associative: a -> b -> c is a -> (b -> c).
    round(
        "Int -> Int -> Int",
        Type::Fun(
            Box::new(Type::Int),
            Box::new(Type::Fun(Box::new(Type::Int), Box::new(Type::Int))),
        ),
    );
    round("<<Int, Str>>", Type::Tuple(vec![Type::Int, Type::Str]));
    round(
        "{a: Int}",
        Type::Rec {
            fields: [("a".to_string(), Type::Int)].into_iter().collect(),
            open: false,
        },
    );
    // Apalache's annotations end with `;` more often than not.
    round(
        "Str -> Int;",
        Type::Fun(Box::new(Type::Str), Box::new(Type::Int)),
    );
}

/// What the grammar has no type for is refused by name: variants and
/// operator types (the variants sub-issue) — never silently accepted.
#[test]
fn unsupported_forms_are_refused_by_name() {
    use nixie_tla::annotations::parse_type1;
    let err = match parse_type1("Tag(Int) | other") {
        Ok(_) => panic!("variants must be refused"),
        Err(e) => e,
    };
    assert!(err.to_string().contains("does not parse"), "{err}");
    let err = match parse_type1("(Int) => Bool") {
        Ok(_) => panic!("operator types must be refused"),
        Err(e) => e,
    };
    // Refused by name either way: the trailing `=>` input is named in the
    // message, and the class is the annotation error, never a silent pass.
    assert!(
        err.to_string().contains("does not parse") || err.to_string().contains("no type for yet"),
        "{err}"
    );
}

// ---- uninterpreted types ----

/// An uppercase name is an uninterpreted type: its own base, one per NAME,
/// never Int or Str. Two annotated names sharing `T` share the type, and a
/// model value of `T` stays apart from strings by the model-value prefix.
#[test]
fn an_uninterpreted_type_is_its_own_base() {
    let src = r#"
---- MODULE Uni ----
EXTENDS Integers
CONSTANT
    \* @type: T;
    token
VARIABLE
    \* @type: Set(T);
    seen
Init == seen = {}
Next == seen' = seen \union {token}
Inv == Cardinality(seen) <= 1
====
"#;
    // The token never re-enters a set it was never in: clean at depth 2.
    let parsed = nixie_tla_syntax::parse_file(src).expect("parses");
    let spec = nixie_tla_syntax::LoadedSpec::single(parsed);
    let module = spec.root_module().expect("has a root module");
    let mut tm = TermManager::new();
    let mut bmc = Bmc::prepare_with_config(
        &spec,
        module,
        Roles {
            init: "Init",
            next: "Next",
            inv: &["Inv"],
            constraints: &[],
        },
        &nixie_tla_syntax::TlcConfig::default(),
        &mut tm,
    )
    .expect("prepares");
    assert_eq!(
        bmc.check(2, &mut tm).expect("checks"),
        Outcome::NoViolationWithin(2)
    );
}
